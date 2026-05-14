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
lean_object* v_ref_1642_; lean_object* v___x_1643_; lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1689_; 
v_ref_1642_ = lean_ctor_get(v___y_1639_, 5);
v___x_1643_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1689_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1689_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v_traceState_1649_; lean_object* v_env_1650_; lean_object* v_nextMacroScope_1651_; lean_object* v_ngen_1652_; lean_object* v_auxDeclNGen_1653_; lean_object* v_cache_1654_; lean_object* v_messages_1655_; lean_object* v_infoState_1656_; lean_object* v_snapshotTasks_1657_; lean_object* v_newDecls_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1688_; 
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
v_newDecls_1658_ = lean_ctor_get(v___x_1648_, 9);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1660_ = v___x_1648_;
v_isShared_1661_ = v_isSharedCheck_1688_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_newDecls_1658_);
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
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1688_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
uint64_t v_tid_1662_; lean_object* v_traces_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1687_; 
v_tid_1662_ = lean_ctor_get_uint64(v_traceState_1649_, sizeof(void*)*1);
v_traces_1663_ = lean_ctor_get(v_traceState_1649_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_traceState_1649_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1665_ = v_traceState_1649_;
v_isShared_1666_ = v_isSharedCheck_1687_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_traces_1663_);
lean_dec(v_traceState_1649_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1687_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; double v___x_1668_; uint8_t v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1667_ = lean_box(0);
v___x_1668_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_1669_ = 0;
v___x_1670_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_1671_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1671_, 0, v_cls_1635_);
lean_ctor_set(v___x_1671_, 1, v___x_1667_);
lean_ctor_set(v___x_1671_, 2, v___x_1670_);
lean_ctor_set_float(v___x_1671_, sizeof(void*)*3, v___x_1668_);
lean_ctor_set_float(v___x_1671_, sizeof(void*)*3 + 8, v___x_1668_);
lean_ctor_set_uint8(v___x_1671_, sizeof(void*)*3 + 16, v___x_1669_);
v___x_1672_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_1673_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v_a_1644_);
lean_ctor_set(v___x_1673_, 2, v___x_1672_);
lean_inc(v_ref_1642_);
v___x_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1674_, 0, v_ref_1642_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = l_Lean_PersistentArray_push___redArg(v_traces_1663_, v___x_1674_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1675_);
v___x_1677_ = v___x_1665_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1675_);
lean_ctor_set_uint64(v_reuseFailAlloc_1686_, sizeof(void*)*1, v_tid_1662_);
v___x_1677_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1679_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 4, v___x_1677_);
v___x_1679_ = v___x_1660_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_env_1650_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_nextMacroScope_1651_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_ngen_1652_);
lean_ctor_set(v_reuseFailAlloc_1685_, 3, v_auxDeclNGen_1653_);
lean_ctor_set(v_reuseFailAlloc_1685_, 4, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1685_, 5, v_cache_1654_);
lean_ctor_set(v_reuseFailAlloc_1685_, 6, v_messages_1655_);
lean_ctor_set(v_reuseFailAlloc_1685_, 7, v_infoState_1656_);
lean_ctor_set(v_reuseFailAlloc_1685_, 8, v_snapshotTasks_1657_);
lean_ctor_set(v_reuseFailAlloc_1685_, 9, v_newDecls_1658_);
v___x_1679_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1680_ = lean_st_ref_set(v___y_1640_, v___x_1679_);
v___x_1681_ = lean_box(0);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1681_);
v___x_1683_ = v___x_1646_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(lean_object* v_cls_1690_, lean_object* v_msg_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v_cls_1690_, v_msg_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
return v_res_1697_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__2));
v___x_1707_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__4));
v___x_1708_ = l_Lean_Name_append(v___x_1707_, v___x_1706_);
return v___x_1708_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__6));
v___x_1711_ = l_Lean_stringToMessageData(v___x_1710_);
return v___x_1711_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__8));
v___x_1714_ = l_Lean_stringToMessageData(v___x_1713_);
return v___x_1714_;
}
}
static uint64_t _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__10(void){
_start:
{
uint8_t v___x_1715_; uint64_t v___x_1716_; 
v___x_1715_ = 1;
v___x_1716_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1715_);
return v___x_1716_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__11));
v___x_1719_ = l_Lean_stringToMessageData(v___x_1718_);
return v___x_1719_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__14(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__13));
v___x_1722_ = l_Lean_stringToMessageData(v___x_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object* v_e_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
if (lean_obj_tag(v_e_1723_) == 11)
{
lean_object* v_typeName_1735_; lean_object* v_idx_1736_; lean_object* v_struct_1737_; lean_object* v___x_1738_; lean_object* v_env_1739_; lean_object* v___x_1740_; 
v_typeName_1735_ = lean_ctor_get(v_e_1723_, 0);
v_idx_1736_ = lean_ctor_get(v_e_1723_, 1);
v_struct_1737_ = lean_ctor_get(v_e_1723_, 2);
v___x_1738_ = lean_st_ref_get(v___y_1727_);
v_env_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc_ref(v_env_1739_);
lean_dec(v___x_1738_);
lean_inc(v_typeName_1735_);
v___x_1740_ = l_Lean_getStructureInfo_x3f(v_env_1739_, v_typeName_1735_);
if (lean_obj_tag(v___x_1740_) == 1)
{
lean_object* v_val_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1840_; 
v_val_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1840_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_val_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1840_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v_fieldNames_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v_fieldNames_1745_ = lean_ctor_get(v_val_1741_, 1);
lean_inc_ref(v_fieldNames_1745_);
lean_dec(v_val_1741_);
v___x_1746_ = lean_array_get_size(v_fieldNames_1745_);
v___x_1747_ = lean_nat_dec_lt(v_idx_1736_, v___x_1746_);
if (v___x_1747_ == 0)
{
lean_object* v_options_1748_; uint8_t v_hasTrace_1749_; 
lean_dec_ref(v_fieldNames_1745_);
v_options_1748_ = lean_ctor_get(v___y_1726_, 2);
v_hasTrace_1749_ = lean_ctor_get_uint8(v_options_1748_, sizeof(void*)*1);
if (v_hasTrace_1749_ == 0)
{
lean_del_object(v___x_1743_);
goto v___jp_1729_;
}
else
{
lean_object* v_inheritedTraceOptions_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v_inheritedTraceOptions_1750_ = lean_ctor_get(v___y_1726_, 13);
v___x_1751_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__2));
v___x_1752_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__5, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__5_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__5);
v___x_1753_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1750_, v_options_1748_, v___x_1752_);
if (v___x_1753_ == 0)
{
lean_del_object(v___x_1743_);
goto v___jp_1729_;
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1754_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__7, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__7);
lean_inc(v_idx_1736_);
v___x_1755_ = l_Nat_reprFast(v_idx_1736_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set_tag(v___x_1743_, 3);
lean_ctor_set(v___x_1743_, 0, v___x_1755_);
v___x_1757_ = v___x_1743_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1758_ = l_Lean_MessageData_ofFormat(v___x_1757_);
v___x_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1754_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__9, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__9);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1759_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
lean_inc_ref(v_e_1723_);
v___x_1762_ = l_Lean_indentExpr(v_e_1723_);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_1751_, v___x_1763_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_dec_ref(v___x_1764_);
goto v___jp_1729_;
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec_ref(v_e_1723_);
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1774_; uint8_t v_foApprox_1775_; uint8_t v_ctxApprox_1776_; uint8_t v_quasiPatternApprox_1777_; uint8_t v_constApprox_1778_; uint8_t v_isDefEqStuckEx_1779_; uint8_t v_unificationHints_1780_; uint8_t v_proofIrrelevance_1781_; uint8_t v_assignSyntheticOpaque_1782_; uint8_t v_offsetCnstrs_1783_; uint8_t v_etaStruct_1784_; uint8_t v_univApprox_1785_; uint8_t v_iota_1786_; uint8_t v_beta_1787_; uint8_t v_proj_1788_; uint8_t v_zeta_1789_; uint8_t v_zetaDelta_1790_; uint8_t v_zetaUnused_1791_; uint8_t v_zetaHave_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1839_; 
lean_inc_ref(v_struct_1737_);
lean_inc(v_idx_1736_);
lean_dec_ref(v_e_1723_);
v___x_1774_ = l_Lean_Meta_Context_config(v___y_1724_);
v_foApprox_1775_ = lean_ctor_get_uint8(v___x_1774_, 0);
v_ctxApprox_1776_ = lean_ctor_get_uint8(v___x_1774_, 1);
v_quasiPatternApprox_1777_ = lean_ctor_get_uint8(v___x_1774_, 2);
v_constApprox_1778_ = lean_ctor_get_uint8(v___x_1774_, 3);
v_isDefEqStuckEx_1779_ = lean_ctor_get_uint8(v___x_1774_, 4);
v_unificationHints_1780_ = lean_ctor_get_uint8(v___x_1774_, 5);
v_proofIrrelevance_1781_ = lean_ctor_get_uint8(v___x_1774_, 6);
v_assignSyntheticOpaque_1782_ = lean_ctor_get_uint8(v___x_1774_, 7);
v_offsetCnstrs_1783_ = lean_ctor_get_uint8(v___x_1774_, 8);
v_etaStruct_1784_ = lean_ctor_get_uint8(v___x_1774_, 10);
v_univApprox_1785_ = lean_ctor_get_uint8(v___x_1774_, 11);
v_iota_1786_ = lean_ctor_get_uint8(v___x_1774_, 12);
v_beta_1787_ = lean_ctor_get_uint8(v___x_1774_, 13);
v_proj_1788_ = lean_ctor_get_uint8(v___x_1774_, 14);
v_zeta_1789_ = lean_ctor_get_uint8(v___x_1774_, 15);
v_zetaDelta_1790_ = lean_ctor_get_uint8(v___x_1774_, 16);
v_zetaUnused_1791_ = lean_ctor_get_uint8(v___x_1774_, 17);
v_zetaHave_1792_ = lean_ctor_get_uint8(v___x_1774_, 18);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1794_ = v___x_1774_;
v_isShared_1795_ = v_isSharedCheck_1839_;
goto v_resetjp_1793_;
}
else
{
lean_dec(v___x_1774_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1839_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
uint8_t v_trackZetaDelta_1796_; lean_object* v_zetaDeltaSet_1797_; lean_object* v_lctx_1798_; lean_object* v_localInstances_1799_; lean_object* v_defEqCtx_x3f_1800_; lean_object* v_synthPendingDepth_1801_; lean_object* v_canUnfold_x3f_1802_; uint8_t v_univApprox_1803_; uint8_t v_inTypeClassResolution_1804_; uint8_t v_cacheInferType_1805_; uint8_t v___x_1806_; lean_object* v_config_1808_; 
v_trackZetaDelta_1796_ = lean_ctor_get_uint8(v___y_1724_, sizeof(void*)*7);
v_zetaDeltaSet_1797_ = lean_ctor_get(v___y_1724_, 1);
v_lctx_1798_ = lean_ctor_get(v___y_1724_, 2);
v_localInstances_1799_ = lean_ctor_get(v___y_1724_, 3);
v_defEqCtx_x3f_1800_ = lean_ctor_get(v___y_1724_, 4);
v_synthPendingDepth_1801_ = lean_ctor_get(v___y_1724_, 5);
v_canUnfold_x3f_1802_ = lean_ctor_get(v___y_1724_, 6);
v_univApprox_1803_ = lean_ctor_get_uint8(v___y_1724_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1804_ = lean_ctor_get_uint8(v___y_1724_, sizeof(void*)*7 + 2);
v_cacheInferType_1805_ = lean_ctor_get_uint8(v___y_1724_, sizeof(void*)*7 + 3);
v___x_1806_ = 1;
if (v_isShared_1795_ == 0)
{
v_config_1808_ = v___x_1794_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 0, v_foApprox_1775_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 1, v_ctxApprox_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 2, v_quasiPatternApprox_1777_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 3, v_constApprox_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 4, v_isDefEqStuckEx_1779_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 5, v_unificationHints_1780_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 6, v_proofIrrelevance_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 7, v_assignSyntheticOpaque_1782_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 8, v_offsetCnstrs_1783_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 10, v_etaStruct_1784_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 11, v_univApprox_1785_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 12, v_iota_1786_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 13, v_beta_1787_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 14, v_proj_1788_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 15, v_zeta_1789_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 16, v_zetaDelta_1790_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 17, v_zetaUnused_1791_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, 18, v_zetaHave_1792_);
v_config_1808_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
uint64_t v___x_1809_; uint64_t v___x_1810_; uint64_t v___x_1811_; lean_object* v___x_1812_; uint64_t v___x_1813_; uint64_t v___x_1814_; uint64_t v_key_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_ctor_set_uint8(v_config_1808_, 9, v___x_1806_);
v___x_1809_ = l_Lean_Meta_Context_configKey(v___y_1724_);
v___x_1810_ = 2ULL;
v___x_1811_ = lean_uint64_shift_right(v___x_1809_, v___x_1810_);
v___x_1812_ = lean_array_fget(v_fieldNames_1745_, v_idx_1736_);
lean_dec(v_idx_1736_);
lean_dec_ref(v_fieldNames_1745_);
v___x_1813_ = lean_uint64_shift_left(v___x_1811_, v___x_1810_);
v___x_1814_ = lean_uint64_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__10, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__10_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__10);
v_key_1815_ = lean_uint64_lor(v___x_1813_, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1816_, 0, v_config_1808_);
lean_ctor_set_uint64(v___x_1816_, sizeof(void*)*1, v_key_1815_);
lean_inc(v_canUnfold_x3f_1802_);
lean_inc(v_synthPendingDepth_1801_);
lean_inc(v_defEqCtx_x3f_1800_);
lean_inc_ref(v_localInstances_1799_);
lean_inc_ref(v_lctx_1798_);
lean_inc(v_zetaDeltaSet_1797_);
v___x_1817_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
lean_ctor_set(v___x_1817_, 1, v_zetaDeltaSet_1797_);
lean_ctor_set(v___x_1817_, 2, v_lctx_1798_);
lean_ctor_set(v___x_1817_, 3, v_localInstances_1799_);
lean_ctor_set(v___x_1817_, 4, v_defEqCtx_x3f_1800_);
lean_ctor_set(v___x_1817_, 5, v_synthPendingDepth_1801_);
lean_ctor_set(v___x_1817_, 6, v_canUnfold_x3f_1802_);
lean_ctor_set_uint8(v___x_1817_, sizeof(void*)*7, v_trackZetaDelta_1796_);
lean_ctor_set_uint8(v___x_1817_, sizeof(void*)*7 + 1, v_univApprox_1803_);
lean_ctor_set_uint8(v___x_1817_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1804_);
lean_ctor_set_uint8(v___x_1817_, sizeof(void*)*7 + 3, v_cacheInferType_1805_);
v___x_1818_ = l_Lean_Meta_mkProjection(v_struct_1737_, v___x_1812_, v___x_1817_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec_ref(v___x_1817_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1829_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1829_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1829_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v_a_1819_);
v___x_1824_ = v___x_1743_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1826_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1824_);
v___x_1826_ = v___x_1821_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_del_object(v___x_1743_);
v_a_1830_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1818_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1818_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
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
lean_object* v_options_1841_; uint8_t v_hasTrace_1842_; 
lean_dec(v___x_1740_);
v_options_1841_ = lean_ctor_get(v___y_1726_, 2);
v_hasTrace_1842_ = lean_ctor_get_uint8(v_options_1841_, sizeof(void*)*1);
if (v_hasTrace_1842_ == 0)
{
goto v___jp_1732_;
}
else
{
lean_object* v_inheritedTraceOptions_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v_inheritedTraceOptions_1843_ = lean_ctor_get(v___y_1726_, 13);
v___x_1844_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__2));
v___x_1845_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__5, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__5_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__5);
v___x_1846_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1843_, v_options_1841_, v___x_1845_);
if (v___x_1846_ == 0)
{
goto v___jp_1732_;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1847_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__12, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__12);
lean_inc(v_typeName_1735_);
v___x_1848_ = l_Lean_MessageData_ofName(v_typeName_1735_);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__14, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__14_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__14);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
lean_inc_ref(v_e_1723_);
v___x_1852_ = l_Lean_indentExpr(v_e_1723_);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_1844_, v___x_1853_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_dec_ref(v___x_1854_);
goto v___jp_1732_;
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec_ref(v_e_1723_);
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1854_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1854_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v_e_1723_);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
return v___x_1864_;
}
v___jp_1729_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_e_1723_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
v___jp_1732_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v_e_1723_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object* v_e_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Meta_Sym_foldProjs___lam__0(v_e_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object* v_x_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object* v_x_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_Meta_Sym_foldProjs___lam__1(v_x_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec_ref(v_x_1880_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs(lean_object* v_e_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___f_1896_; lean_object* v___x_1897_; 
v___f_1896_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__0));
v___x_1897_ = lean_find_expr(v___f_1896_, v_e_1890_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v_e_1890_);
return v___x_1898_;
}
else
{
lean_object* v_post_1899_; lean_object* v___f_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; 
lean_dec_ref(v___x_1897_);
v_post_1899_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__1));
v___f_1900_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__2));
v___x_1901_ = 0;
v___x_1902_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_1890_, v___f_1900_, v_post_1899_, v___x_1901_, v___x_1901_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
return v___x_1902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___boxed(lean_object* v_e_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Meta_Sym_foldProjs(v_e_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(lean_object* v_e_1910_, lean_object* v___y_1911_){
_start:
{
uint8_t v___x_1913_; 
v___x_1913_ = l_Lean_Expr_hasMVar(v_e_1910_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_e_1910_);
return v___x_1914_;
}
else
{
lean_object* v___x_1915_; lean_object* v_mctx_1916_; lean_object* v___x_1917_; lean_object* v_fst_1918_; lean_object* v_snd_1919_; lean_object* v___x_1920_; lean_object* v_cache_1921_; lean_object* v_zetaDeltaFVarIds_1922_; lean_object* v_postponed_1923_; lean_object* v_diag_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1933_; 
v___x_1915_ = lean_st_ref_get(v___y_1911_);
v_mctx_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc_ref(v_mctx_1916_);
lean_dec(v___x_1915_);
v___x_1917_ = l_Lean_instantiateMVarsCore(v_mctx_1916_, v_e_1910_);
v_fst_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_fst_1918_);
v_snd_1919_ = lean_ctor_get(v___x_1917_, 1);
lean_inc(v_snd_1919_);
lean_dec_ref(v___x_1917_);
v___x_1920_ = lean_st_ref_take(v___y_1911_);
v_cache_1921_ = lean_ctor_get(v___x_1920_, 1);
v_zetaDeltaFVarIds_1922_ = lean_ctor_get(v___x_1920_, 2);
v_postponed_1923_ = lean_ctor_get(v___x_1920_, 3);
v_diag_1924_ = lean_ctor_get(v___x_1920_, 4);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; 
v_unused_1934_ = lean_ctor_get(v___x_1920_, 0);
lean_dec(v_unused_1934_);
v___x_1926_ = v___x_1920_;
v_isShared_1927_ = v_isSharedCheck_1933_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_diag_1924_);
lean_inc(v_postponed_1923_);
lean_inc(v_zetaDeltaFVarIds_1922_);
lean_inc(v_cache_1921_);
lean_dec(v___x_1920_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1933_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v_snd_1919_);
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_snd_1919_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_cache_1921_);
lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_zetaDeltaFVarIds_1922_);
lean_ctor_set(v_reuseFailAlloc_1932_, 3, v_postponed_1923_);
lean_ctor_set(v_reuseFailAlloc_1932_, 4, v_diag_1924_);
v___x_1929_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = lean_st_ref_set(v___y_1911_, v___x_1929_);
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v_fst_1918_);
return v___x_1931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg___boxed(lean_object* v_e_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_1935_, v___y_1936_);
lean_dec(v___y_1936_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0(lean_object* v_e_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_1939_, v___y_1943_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___boxed(lean_object* v_e_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0(v_e_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(lean_object* v_e_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v___x_1965_; lean_object* v_a_1966_; lean_object* v___x_1967_; 
v___x_1965_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_1957_, v_a_1961_);
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref(v___x_1965_);
v___x_1967_ = l_Lean_Meta_Sym_unfoldReducible(v_a_1966_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1969_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref(v___x_1967_);
v___x_1969_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1968_, v_a_1959_);
return v___x_1969_;
}
else
{
return v___x_1967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr___boxed(lean_object* v_e_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_e_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1979_, lean_object* v_x_1980_, lean_object* v_x_1981_, lean_object* v_x_1982_){
_start:
{
lean_object* v_ks_1983_; lean_object* v_vs_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2008_; 
v_ks_1983_ = lean_ctor_get(v_x_1979_, 0);
v_vs_1984_ = lean_ctor_get(v_x_1979_, 1);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_x_1979_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1986_ = v_x_1979_;
v_isShared_1987_ = v_isSharedCheck_2008_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_vs_1984_);
lean_inc(v_ks_1983_);
lean_dec(v_x_1979_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2008_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1988_ = lean_array_get_size(v_ks_1983_);
v___x_1989_ = lean_nat_dec_lt(v_x_1980_, v___x_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1993_; 
lean_dec(v_x_1980_);
v___x_1990_ = lean_array_push(v_ks_1983_, v_x_1981_);
v___x_1991_ = lean_array_push(v_vs_1984_, v_x_1982_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 1, v___x_1991_);
lean_ctor_set(v___x_1986_, 0, v___x_1990_);
v___x_1993_ = v___x_1986_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
else
{
lean_object* v_k_x27_1995_; uint8_t v___x_1996_; 
v_k_x27_1995_ = lean_array_fget_borrowed(v_ks_1983_, v_x_1980_);
v___x_1996_ = l_Lean_instBEqFVarId_beq(v_x_1981_, v_k_x27_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1998_; 
if (v_isShared_1987_ == 0)
{
v___x_1998_ = v___x_1986_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_ks_1983_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_vs_1984_);
v___x_1998_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_unsigned_to_nat(1u);
v___x_2000_ = lean_nat_add(v_x_1980_, v___x_1999_);
lean_dec(v_x_1980_);
v_x_1979_ = v___x_1998_;
v_x_1980_ = v___x_2000_;
goto _start;
}
}
else
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2003_ = lean_array_fset(v_ks_1983_, v_x_1980_, v_x_1981_);
v___x_2004_ = lean_array_fset(v_vs_1984_, v_x_1980_, v_x_1982_);
lean_dec(v_x_1980_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 1, v___x_2004_);
lean_ctor_set(v___x_1986_, 0, v___x_2003_);
v___x_2006_ = v___x_1986_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2009_, lean_object* v_k_2010_, lean_object* v_v_2011_){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_unsigned_to_nat(0u);
v___x_2013_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_n_2009_, v___x_2012_, v_k_2010_, v_v_2011_);
return v___x_2013_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_2014_; size_t v___x_2015_; size_t v___x_2016_; 
v___x_2014_ = ((size_t)5ULL);
v___x_2015_ = ((size_t)1ULL);
v___x_2016_ = lean_usize_shift_left(v___x_2015_, v___x_2014_);
return v___x_2016_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2017_; size_t v___x_2018_; size_t v___x_2019_; 
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0);
v___x_2019_ = lean_usize_sub(v___x_2018_, v___x_2017_);
return v___x_2019_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(lean_object* v_x_2021_, size_t v_x_2022_, size_t v_x_2023_, lean_object* v_x_2024_, lean_object* v_x_2025_){
_start:
{
if (lean_obj_tag(v_x_2021_) == 0)
{
lean_object* v_es_2026_; size_t v___x_2027_; size_t v___x_2028_; size_t v___x_2029_; size_t v___x_2030_; lean_object* v_j_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_es_2026_ = lean_ctor_get(v_x_2021_, 0);
v___x_2027_ = ((size_t)5ULL);
v___x_2028_ = ((size_t)1ULL);
v___x_2029_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
v___x_2030_ = lean_usize_land(v_x_2022_, v___x_2029_);
v_j_2031_ = lean_usize_to_nat(v___x_2030_);
v___x_2032_ = lean_array_get_size(v_es_2026_);
v___x_2033_ = lean_nat_dec_lt(v_j_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_dec(v_j_2031_);
lean_dec(v_x_2025_);
lean_dec(v_x_2024_);
return v_x_2021_;
}
else
{
lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2070_; 
lean_inc_ref(v_es_2026_);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_x_2021_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; 
v_unused_2071_ = lean_ctor_get(v_x_2021_, 0);
lean_dec(v_unused_2071_);
v___x_2035_ = v_x_2021_;
v_isShared_2036_ = v_isSharedCheck_2070_;
goto v_resetjp_2034_;
}
else
{
lean_dec(v_x_2021_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2070_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v_v_2037_; lean_object* v___x_2038_; lean_object* v_xs_x27_2039_; lean_object* v___y_2041_; 
v_v_2037_ = lean_array_fget(v_es_2026_, v_j_2031_);
v___x_2038_ = lean_box(0);
v_xs_x27_2039_ = lean_array_fset(v_es_2026_, v_j_2031_, v___x_2038_);
switch(lean_obj_tag(v_v_2037_))
{
case 0:
{
lean_object* v_key_2046_; lean_object* v_val_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2057_; 
v_key_2046_ = lean_ctor_get(v_v_2037_, 0);
v_val_2047_ = lean_ctor_get(v_v_2037_, 1);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_v_2037_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2049_ = v_v_2037_;
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_val_2047_);
lean_inc(v_key_2046_);
lean_dec(v_v_2037_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
uint8_t v___x_2051_; 
v___x_2051_ = l_Lean_instBEqFVarId_beq(v_x_2024_, v_key_2046_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_del_object(v___x_2049_);
v___x_2052_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2046_, v_val_2047_, v_x_2024_, v_x_2025_);
v___x_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
v___y_2041_ = v___x_2053_;
goto v___jp_2040_;
}
else
{
lean_object* v___x_2055_; 
lean_dec(v_val_2047_);
lean_dec(v_key_2046_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 1, v_x_2025_);
lean_ctor_set(v___x_2049_, 0, v_x_2024_);
v___x_2055_ = v___x_2049_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_x_2024_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_x_2025_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
v___y_2041_ = v___x_2055_;
goto v___jp_2040_;
}
}
}
}
case 1:
{
lean_object* v_node_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2068_; 
v_node_2058_ = lean_ctor_get(v_v_2037_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v_v_2037_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2060_ = v_v_2037_;
v_isShared_2061_ = v_isSharedCheck_2068_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_node_2058_);
lean_dec(v_v_2037_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2068_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
size_t v___x_2062_; size_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2062_ = lean_usize_shift_right(v_x_2022_, v___x_2027_);
v___x_2063_ = lean_usize_add(v_x_2023_, v___x_2028_);
v___x_2064_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_node_2058_, v___x_2062_, v___x_2063_, v_x_2024_, v_x_2025_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2064_);
v___x_2066_ = v___x_2060_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
v___y_2041_ = v___x_2066_;
goto v___jp_2040_;
}
}
}
default: 
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_x_2024_);
lean_ctor_set(v___x_2069_, 1, v_x_2025_);
v___y_2041_ = v___x_2069_;
goto v___jp_2040_;
}
}
v___jp_2040_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = lean_array_fset(v_xs_x27_2039_, v_j_2031_, v___y_2041_);
lean_dec(v_j_2031_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2042_);
v___x_2044_ = v___x_2035_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
else
{
lean_object* v_ks_2072_; lean_object* v_vs_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2093_; 
v_ks_2072_ = lean_ctor_get(v_x_2021_, 0);
v_vs_2073_ = lean_ctor_get(v_x_2021_, 1);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_x_2021_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2075_ = v_x_2021_;
v_isShared_2076_ = v_isSharedCheck_2093_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_vs_2073_);
lean_inc(v_ks_2072_);
lean_dec(v_x_2021_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2093_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_ks_2072_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_vs_2073_);
v___x_2078_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v_newNode_2079_; uint8_t v___y_2081_; size_t v___x_2087_; uint8_t v___x_2088_; 
v_newNode_2079_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v___x_2078_, v_x_2024_, v_x_2025_);
v___x_2087_ = ((size_t)7ULL);
v___x_2088_ = lean_usize_dec_le(v___x_2087_, v_x_2023_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2089_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2079_);
v___x_2090_ = lean_unsigned_to_nat(4u);
v___x_2091_ = lean_nat_dec_lt(v___x_2089_, v___x_2090_);
lean_dec(v___x_2089_);
v___y_2081_ = v___x_2091_;
goto v___jp_2080_;
}
else
{
v___y_2081_ = v___x_2088_;
goto v___jp_2080_;
}
v___jp_2080_:
{
if (v___y_2081_ == 0)
{
lean_object* v_ks_2082_; lean_object* v_vs_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v_ks_2082_ = lean_ctor_get(v_newNode_2079_, 0);
lean_inc_ref(v_ks_2082_);
v_vs_2083_ = lean_ctor_get(v_newNode_2079_, 1);
lean_inc_ref(v_vs_2083_);
lean_dec_ref(v_newNode_2079_);
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2);
v___x_2086_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_x_2023_, v_ks_2082_, v_vs_2083_, v___x_2084_, v___x_2085_);
lean_dec_ref(v_vs_2083_);
lean_dec_ref(v_ks_2082_);
return v___x_2086_;
}
else
{
return v_newNode_2079_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(size_t v_depth_2094_, lean_object* v_keys_2095_, lean_object* v_vals_2096_, lean_object* v_i_2097_, lean_object* v_entries_2098_){
_start:
{
lean_object* v___x_2099_; uint8_t v___x_2100_; 
v___x_2099_ = lean_array_get_size(v_keys_2095_);
v___x_2100_ = lean_nat_dec_lt(v_i_2097_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_dec(v_i_2097_);
return v_entries_2098_;
}
else
{
lean_object* v_k_2101_; lean_object* v_v_2102_; uint64_t v___x_2103_; size_t v_h_2104_; size_t v___x_2105_; lean_object* v___x_2106_; size_t v___x_2107_; size_t v___x_2108_; size_t v___x_2109_; size_t v_h_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v_k_2101_ = lean_array_fget_borrowed(v_keys_2095_, v_i_2097_);
v_v_2102_ = lean_array_fget_borrowed(v_vals_2096_, v_i_2097_);
v___x_2103_ = l_Lean_instHashableFVarId_hash(v_k_2101_);
v_h_2104_ = lean_uint64_to_usize(v___x_2103_);
v___x_2105_ = ((size_t)5ULL);
v___x_2106_ = lean_unsigned_to_nat(1u);
v___x_2107_ = ((size_t)1ULL);
v___x_2108_ = lean_usize_sub(v_depth_2094_, v___x_2107_);
v___x_2109_ = lean_usize_mul(v___x_2105_, v___x_2108_);
v_h_2110_ = lean_usize_shift_right(v_h_2104_, v___x_2109_);
v___x_2111_ = lean_nat_add(v_i_2097_, v___x_2106_);
lean_dec(v_i_2097_);
lean_inc(v_v_2102_);
lean_inc(v_k_2101_);
v___x_2112_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_entries_2098_, v_h_2110_, v_depth_2094_, v_k_2101_, v_v_2102_);
v_i_2097_ = v___x_2111_;
v_entries_2098_ = v___x_2112_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2114_, lean_object* v_keys_2115_, lean_object* v_vals_2116_, lean_object* v_i_2117_, lean_object* v_entries_2118_){
_start:
{
size_t v_depth_boxed_2119_; lean_object* v_res_2120_; 
v_depth_boxed_2119_ = lean_unbox_usize(v_depth_2114_);
lean_dec(v_depth_2114_);
v_res_2120_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2119_, v_keys_2115_, v_vals_2116_, v_i_2117_, v_entries_2118_);
lean_dec_ref(v_vals_2116_);
lean_dec_ref(v_keys_2115_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___boxed(lean_object* v_x_2121_, lean_object* v_x_2122_, lean_object* v_x_2123_, lean_object* v_x_2124_, lean_object* v_x_2125_){
_start:
{
size_t v_x_9235__boxed_2126_; size_t v_x_9236__boxed_2127_; lean_object* v_res_2128_; 
v_x_9235__boxed_2126_ = lean_unbox_usize(v_x_2122_);
lean_dec(v_x_2122_);
v_x_9236__boxed_2127_ = lean_unbox_usize(v_x_2123_);
lean_dec(v_x_2123_);
v_res_2128_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_2121_, v_x_9235__boxed_2126_, v_x_9236__boxed_2127_, v_x_2124_, v_x_2125_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(lean_object* v_x_2129_, lean_object* v_x_2130_, lean_object* v_x_2131_){
_start:
{
uint64_t v___x_2132_; size_t v___x_2133_; size_t v___x_2134_; lean_object* v___x_2135_; 
v___x_2132_ = l_Lean_instHashableFVarId_hash(v_x_2130_);
v___x_2133_ = lean_uint64_to_usize(v___x_2132_);
v___x_2134_ = ((size_t)1ULL);
v___x_2135_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_2129_, v___x_2133_, v___x_2134_, v_x_2130_, v_x_2131_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(lean_object* v_as_2136_, size_t v_sz_2137_, size_t v_i_2138_, lean_object* v_b_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
uint8_t v___x_2147_; 
v___x_2147_ = lean_usize_dec_lt(v_i_2138_, v_sz_2137_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_b_2139_);
return v___x_2148_;
}
else
{
lean_object* v_snd_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2254_; 
v_snd_2149_ = lean_ctor_get(v_b_2139_, 1);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_b_2139_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; 
v_unused_2255_ = lean_ctor_get(v_b_2139_, 0);
lean_dec(v_unused_2255_);
v___x_2151_ = v_b_2139_;
v_isShared_2152_ = v_isSharedCheck_2254_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_snd_2149_);
lean_dec(v_b_2139_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2254_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; lean_object* v_a_2155_; lean_object* v_a_2162_; 
v___x_2153_ = lean_box(0);
v_a_2162_ = lean_array_uget(v_as_2136_, v_i_2138_);
if (lean_obj_tag(v_a_2162_) == 0)
{
v_a_2155_ = v_snd_2149_;
goto v___jp_2154_;
}
else
{
lean_object* v_snd_2163_; lean_object* v_val_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2253_; 
v_snd_2163_ = lean_ctor_get(v_snd_2149_, 1);
lean_inc(v_snd_2163_);
v_val_2164_ = lean_ctor_get(v_a_2162_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_a_2162_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2166_ = v_a_2162_;
v_isShared_2167_ = v_isSharedCheck_2253_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_val_2164_);
lean_dec(v_a_2162_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2253_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v_fst_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2251_; 
v_fst_2168_ = lean_ctor_get(v_snd_2149_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v_snd_2149_);
if (v_isSharedCheck_2251_ == 0)
{
lean_object* v_unused_2252_; 
v_unused_2252_ = lean_ctor_get(v_snd_2149_, 1);
lean_dec(v_unused_2252_);
v___x_2170_ = v_snd_2149_;
v_isShared_2171_ = v_isSharedCheck_2251_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_fst_2168_);
lean_dec(v_snd_2149_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2251_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v_fst_2172_; lean_object* v_snd_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2250_; 
v_fst_2172_ = lean_ctor_get(v_snd_2163_, 0);
v_snd_2173_ = lean_ctor_get(v_snd_2163_, 1);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_snd_2163_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2175_ = v_snd_2163_;
v_isShared_2176_ = v_isSharedCheck_2250_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_snd_2173_);
lean_inc(v_fst_2172_);
lean_dec(v_snd_2163_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2250_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v_decl_2178_; 
if (lean_obj_tag(v_val_2164_) == 0)
{
lean_object* v_fvarId_2193_; lean_object* v_userName_2194_; lean_object* v_type_2195_; uint8_t v_bi_2196_; uint8_t v_kind_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2214_; 
v_fvarId_2193_ = lean_ctor_get(v_val_2164_, 1);
v_userName_2194_ = lean_ctor_get(v_val_2164_, 2);
v_type_2195_ = lean_ctor_get(v_val_2164_, 3);
v_bi_2196_ = lean_ctor_get_uint8(v_val_2164_, sizeof(void*)*4);
v_kind_2197_ = lean_ctor_get_uint8(v_val_2164_, sizeof(void*)*4 + 1);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_val_2164_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; 
v_unused_2215_ = lean_ctor_get(v_val_2164_, 0);
lean_dec(v_unused_2215_);
v___x_2199_ = v_val_2164_;
v_isShared_2200_ = v_isSharedCheck_2214_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_type_2195_);
lean_inc(v_userName_2194_);
lean_inc(v_fvarId_2193_);
lean_dec(v_val_2164_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2214_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; 
v___x_2201_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2195_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2204_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref(v___x_2201_);
lean_inc(v_snd_2173_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 3, v_a_2202_);
lean_ctor_set(v___x_2199_, 0, v_snd_2173_);
v___x_2204_ = v___x_2199_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_snd_2173_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_fvarId_2193_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_userName_2194_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_a_2202_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*4, v_bi_2196_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*4 + 1, v_kind_2197_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
v_decl_2178_ = v___x_2204_;
goto v___jp_2177_;
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_del_object(v___x_2199_);
lean_dec(v_userName_2194_);
lean_dec(v_fvarId_2193_);
lean_del_object(v___x_2175_);
lean_dec(v_snd_2173_);
lean_dec(v_fst_2172_);
lean_del_object(v___x_2170_);
lean_dec(v_fst_2168_);
lean_del_object(v___x_2166_);
lean_del_object(v___x_2151_);
v_a_2206_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2201_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2201_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2216_; lean_object* v_userName_2217_; lean_object* v_type_2218_; lean_object* v_value_2219_; uint8_t v_nondep_2220_; uint8_t v_kind_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2248_; 
v_fvarId_2216_ = lean_ctor_get(v_val_2164_, 1);
v_userName_2217_ = lean_ctor_get(v_val_2164_, 2);
v_type_2218_ = lean_ctor_get(v_val_2164_, 3);
v_value_2219_ = lean_ctor_get(v_val_2164_, 4);
v_nondep_2220_ = lean_ctor_get_uint8(v_val_2164_, sizeof(void*)*5);
v_kind_2221_ = lean_ctor_get_uint8(v_val_2164_, sizeof(void*)*5 + 1);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_val_2164_);
if (v_isSharedCheck_2248_ == 0)
{
lean_object* v_unused_2249_; 
v_unused_2249_ = lean_ctor_get(v_val_2164_, 0);
lean_dec(v_unused_2249_);
v___x_2223_ = v_val_2164_;
v_isShared_2224_ = v_isSharedCheck_2248_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_value_2219_);
lean_inc(v_type_2218_);
lean_inc(v_userName_2217_);
lean_inc(v_fvarId_2216_);
lean_dec(v_val_2164_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2248_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; 
v___x_2225_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2218_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2227_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2226_);
lean_dec_ref(v___x_2225_);
v___x_2227_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2219_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2230_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref(v___x_2227_);
lean_inc(v_snd_2173_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 4, v_a_2228_);
lean_ctor_set(v___x_2223_, 3, v_a_2226_);
lean_ctor_set(v___x_2223_, 0, v_snd_2173_);
v___x_2230_ = v___x_2223_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_snd_2173_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_fvarId_2216_);
lean_ctor_set(v_reuseFailAlloc_2231_, 2, v_userName_2217_);
lean_ctor_set(v_reuseFailAlloc_2231_, 3, v_a_2226_);
lean_ctor_set(v_reuseFailAlloc_2231_, 4, v_a_2228_);
lean_ctor_set_uint8(v_reuseFailAlloc_2231_, sizeof(void*)*5, v_nondep_2220_);
lean_ctor_set_uint8(v_reuseFailAlloc_2231_, sizeof(void*)*5 + 1, v_kind_2221_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
v_decl_2178_ = v___x_2230_;
goto v___jp_2177_;
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec(v_a_2226_);
lean_del_object(v___x_2223_);
lean_dec(v_userName_2217_);
lean_dec(v_fvarId_2216_);
lean_del_object(v___x_2175_);
lean_dec(v_snd_2173_);
lean_dec(v_fst_2172_);
lean_del_object(v___x_2170_);
lean_dec(v_fst_2168_);
lean_del_object(v___x_2166_);
lean_del_object(v___x_2151_);
v_a_2232_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2227_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2227_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_del_object(v___x_2223_);
lean_dec_ref(v_value_2219_);
lean_dec(v_userName_2217_);
lean_dec(v_fvarId_2216_);
lean_del_object(v___x_2175_);
lean_dec(v_snd_2173_);
lean_dec(v_fst_2172_);
lean_del_object(v___x_2170_);
lean_dec(v_fst_2168_);
lean_del_object(v___x_2166_);
lean_del_object(v___x_2151_);
v_a_2240_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2225_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2225_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
v___jp_2177_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2179_ = lean_unsigned_to_nat(1u);
v___x_2180_ = lean_nat_add(v_snd_2173_, v___x_2179_);
lean_dec(v_snd_2173_);
lean_inc_ref(v_decl_2178_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v_decl_2178_);
v___x_2182_ = v___x_2166_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_decl_2178_);
v___x_2182_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2183_ = l_Lean_PersistentArray_push___redArg(v_fst_2172_, v___x_2182_);
v___x_2184_ = l_Lean_LocalDecl_fvarId(v_decl_2178_);
v___x_2185_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2168_, v___x_2184_, v_decl_2178_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 1, v___x_2180_);
lean_ctor_set(v___x_2175_, 0, v___x_2183_);
v___x_2187_ = v___x_2175_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v___x_2180_);
v___x_2187_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2189_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 1, v___x_2187_);
lean_ctor_set(v___x_2170_, 0, v___x_2185_);
v___x_2189_ = v___x_2170_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
v_a_2155_ = v___x_2189_;
goto v___jp_2154_;
}
}
}
}
}
}
}
}
v___jp_2154_:
{
lean_object* v___x_2157_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v_a_2155_);
lean_ctor_set(v___x_2151_, 0, v___x_2153_);
v___x_2157_ = v___x_2151_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_a_2155_);
v___x_2157_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
size_t v___x_2158_; size_t v___x_2159_; 
v___x_2158_ = ((size_t)1ULL);
v___x_2159_ = lean_usize_add(v_i_2138_, v___x_2158_);
v_i_2138_ = v___x_2159_;
v_b_2139_ = v___x_2157_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_as_2256_, lean_object* v_sz_2257_, lean_object* v_i_2258_, lean_object* v_b_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
size_t v_sz_boxed_2267_; size_t v_i_boxed_2268_; lean_object* v_res_2269_; 
v_sz_boxed_2267_ = lean_unbox_usize(v_sz_2257_);
lean_dec(v_sz_2257_);
v_i_boxed_2268_ = lean_unbox_usize(v_i_2258_);
lean_dec(v_i_2258_);
v_res_2269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_2256_, v_sz_boxed_2267_, v_i_boxed_2268_, v_b_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v_as_2256_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(lean_object* v_as_2270_, size_t v_sz_2271_, size_t v_i_2272_, lean_object* v_b_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_usize_dec_lt(v_i_2272_, v_sz_2271_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; 
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v_b_2273_);
return v___x_2282_;
}
else
{
lean_object* v_snd_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2388_; 
v_snd_2283_ = lean_ctor_get(v_b_2273_, 1);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_b_2273_);
if (v_isSharedCheck_2388_ == 0)
{
lean_object* v_unused_2389_; 
v_unused_2389_ = lean_ctor_get(v_b_2273_, 0);
lean_dec(v_unused_2389_);
v___x_2285_ = v_b_2273_;
v_isShared_2286_ = v_isSharedCheck_2388_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_snd_2283_);
lean_dec(v_b_2273_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2388_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v_a_2289_; lean_object* v_a_2296_; 
v___x_2287_ = lean_box(0);
v_a_2296_ = lean_array_uget(v_as_2270_, v_i_2272_);
if (lean_obj_tag(v_a_2296_) == 0)
{
v_a_2289_ = v_snd_2283_;
goto v___jp_2288_;
}
else
{
lean_object* v_snd_2297_; lean_object* v_val_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2387_; 
v_snd_2297_ = lean_ctor_get(v_snd_2283_, 1);
lean_inc(v_snd_2297_);
v_val_2298_ = lean_ctor_get(v_a_2296_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_a_2296_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2300_ = v_a_2296_;
v_isShared_2301_ = v_isSharedCheck_2387_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_val_2298_);
lean_dec(v_a_2296_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2387_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v_fst_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2385_; 
v_fst_2302_ = lean_ctor_get(v_snd_2283_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_snd_2283_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; 
v_unused_2386_ = lean_ctor_get(v_snd_2283_, 1);
lean_dec(v_unused_2386_);
v___x_2304_ = v_snd_2283_;
v_isShared_2305_ = v_isSharedCheck_2385_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_fst_2302_);
lean_dec(v_snd_2283_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2385_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v_fst_2306_; lean_object* v_snd_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2384_; 
v_fst_2306_ = lean_ctor_get(v_snd_2297_, 0);
v_snd_2307_ = lean_ctor_get(v_snd_2297_, 1);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_snd_2297_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2309_ = v_snd_2297_;
v_isShared_2310_ = v_isSharedCheck_2384_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_snd_2307_);
lean_inc(v_fst_2306_);
lean_dec(v_snd_2297_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2384_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v_decl_2312_; 
if (lean_obj_tag(v_val_2298_) == 0)
{
lean_object* v_fvarId_2327_; lean_object* v_userName_2328_; lean_object* v_type_2329_; uint8_t v_bi_2330_; uint8_t v_kind_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2348_; 
v_fvarId_2327_ = lean_ctor_get(v_val_2298_, 1);
v_userName_2328_ = lean_ctor_get(v_val_2298_, 2);
v_type_2329_ = lean_ctor_get(v_val_2298_, 3);
v_bi_2330_ = lean_ctor_get_uint8(v_val_2298_, sizeof(void*)*4);
v_kind_2331_ = lean_ctor_get_uint8(v_val_2298_, sizeof(void*)*4 + 1);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_val_2298_);
if (v_isSharedCheck_2348_ == 0)
{
lean_object* v_unused_2349_; 
v_unused_2349_ = lean_ctor_get(v_val_2298_, 0);
lean_dec(v_unused_2349_);
v___x_2333_ = v_val_2298_;
v_isShared_2334_ = v_isSharedCheck_2348_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_type_2329_);
lean_inc(v_userName_2328_);
lean_inc(v_fvarId_2327_);
lean_dec(v_val_2298_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2348_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; 
v___x_2335_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2329_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref(v___x_2335_);
lean_inc(v_snd_2307_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 3, v_a_2336_);
lean_ctor_set(v___x_2333_, 0, v_snd_2307_);
v___x_2338_ = v___x_2333_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_snd_2307_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_fvarId_2327_);
lean_ctor_set(v_reuseFailAlloc_2339_, 2, v_userName_2328_);
lean_ctor_set(v_reuseFailAlloc_2339_, 3, v_a_2336_);
lean_ctor_set_uint8(v_reuseFailAlloc_2339_, sizeof(void*)*4, v_bi_2330_);
lean_ctor_set_uint8(v_reuseFailAlloc_2339_, sizeof(void*)*4 + 1, v_kind_2331_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
v_decl_2312_ = v___x_2338_;
goto v___jp_2311_;
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_del_object(v___x_2333_);
lean_dec(v_userName_2328_);
lean_dec(v_fvarId_2327_);
lean_del_object(v___x_2309_);
lean_dec(v_snd_2307_);
lean_dec(v_fst_2306_);
lean_del_object(v___x_2304_);
lean_dec(v_fst_2302_);
lean_del_object(v___x_2300_);
lean_del_object(v___x_2285_);
v_a_2340_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2335_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2335_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2350_; lean_object* v_userName_2351_; lean_object* v_type_2352_; lean_object* v_value_2353_; uint8_t v_nondep_2354_; uint8_t v_kind_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2382_; 
v_fvarId_2350_ = lean_ctor_get(v_val_2298_, 1);
v_userName_2351_ = lean_ctor_get(v_val_2298_, 2);
v_type_2352_ = lean_ctor_get(v_val_2298_, 3);
v_value_2353_ = lean_ctor_get(v_val_2298_, 4);
v_nondep_2354_ = lean_ctor_get_uint8(v_val_2298_, sizeof(void*)*5);
v_kind_2355_ = lean_ctor_get_uint8(v_val_2298_, sizeof(void*)*5 + 1);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_val_2298_);
if (v_isSharedCheck_2382_ == 0)
{
lean_object* v_unused_2383_; 
v_unused_2383_ = lean_ctor_get(v_val_2298_, 0);
lean_dec(v_unused_2383_);
v___x_2357_ = v_val_2298_;
v_isShared_2358_ = v_isSharedCheck_2382_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_value_2353_);
lean_inc(v_type_2352_);
lean_inc(v_userName_2351_);
lean_inc(v_fvarId_2350_);
lean_dec(v_val_2298_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2382_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2359_; 
v___x_2359_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2352_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2361_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref(v___x_2359_);
v___x_2361_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2353_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref(v___x_2361_);
lean_inc(v_snd_2307_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 4, v_a_2362_);
lean_ctor_set(v___x_2357_, 3, v_a_2360_);
lean_ctor_set(v___x_2357_, 0, v_snd_2307_);
v___x_2364_ = v___x_2357_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_snd_2307_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_fvarId_2350_);
lean_ctor_set(v_reuseFailAlloc_2365_, 2, v_userName_2351_);
lean_ctor_set(v_reuseFailAlloc_2365_, 3, v_a_2360_);
lean_ctor_set(v_reuseFailAlloc_2365_, 4, v_a_2362_);
lean_ctor_set_uint8(v_reuseFailAlloc_2365_, sizeof(void*)*5, v_nondep_2354_);
lean_ctor_set_uint8(v_reuseFailAlloc_2365_, sizeof(void*)*5 + 1, v_kind_2355_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
v_decl_2312_ = v___x_2364_;
goto v___jp_2311_;
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_a_2360_);
lean_del_object(v___x_2357_);
lean_dec(v_userName_2351_);
lean_dec(v_fvarId_2350_);
lean_del_object(v___x_2309_);
lean_dec(v_snd_2307_);
lean_dec(v_fst_2306_);
lean_del_object(v___x_2304_);
lean_dec(v_fst_2302_);
lean_del_object(v___x_2300_);
lean_del_object(v___x_2285_);
v_a_2366_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2361_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2361_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_del_object(v___x_2357_);
lean_dec_ref(v_value_2353_);
lean_dec(v_userName_2351_);
lean_dec(v_fvarId_2350_);
lean_del_object(v___x_2309_);
lean_dec(v_snd_2307_);
lean_dec(v_fst_2306_);
lean_del_object(v___x_2304_);
lean_dec(v_fst_2302_);
lean_del_object(v___x_2300_);
lean_del_object(v___x_2285_);
v_a_2374_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2359_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2359_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
v___jp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2313_ = lean_unsigned_to_nat(1u);
v___x_2314_ = lean_nat_add(v_snd_2307_, v___x_2313_);
lean_dec(v_snd_2307_);
lean_inc_ref(v_decl_2312_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v_decl_2312_);
v___x_2316_ = v___x_2300_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_decl_2312_);
v___x_2316_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2317_ = l_Lean_PersistentArray_push___redArg(v_fst_2306_, v___x_2316_);
v___x_2318_ = l_Lean_LocalDecl_fvarId(v_decl_2312_);
v___x_2319_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2302_, v___x_2318_, v_decl_2312_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 1, v___x_2314_);
lean_ctor_set(v___x_2309_, 0, v___x_2317_);
v___x_2321_ = v___x_2309_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v___x_2314_);
v___x_2321_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2323_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 1, v___x_2321_);
lean_ctor_set(v___x_2304_, 0, v___x_2319_);
v___x_2323_ = v___x_2304_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2319_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
v_a_2289_ = v___x_2323_;
goto v___jp_2288_;
}
}
}
}
}
}
}
}
v___jp_2288_:
{
lean_object* v___x_2291_; 
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 1, v_a_2289_);
lean_ctor_set(v___x_2285_, 0, v___x_2287_);
v___x_2291_ = v___x_2285_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v_a_2289_);
v___x_2291_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
size_t v___x_2292_; size_t v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = ((size_t)1ULL);
v___x_2293_ = lean_usize_add(v_i_2272_, v___x_2292_);
v___x_2294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_2270_, v_sz_2271_, v___x_2293_, v___x_2291_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
return v___x_2294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6___boxed(lean_object* v_as_2390_, lean_object* v_sz_2391_, lean_object* v_i_2392_, lean_object* v_b_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
size_t v_sz_boxed_2401_; size_t v_i_boxed_2402_; lean_object* v_res_2403_; 
v_sz_boxed_2401_ = lean_unbox_usize(v_sz_2391_);
lean_dec(v_sz_2391_);
v_i_boxed_2402_ = lean_unbox_usize(v_i_2392_);
lean_dec(v_i_2392_);
v_res_2403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_as_2390_, v_sz_boxed_2401_, v_i_boxed_2402_, v_b_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec_ref(v_as_2390_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(lean_object* v_init_2404_, lean_object* v_n_2405_, lean_object* v_b_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
if (lean_obj_tag(v_n_2405_) == 0)
{
lean_object* v_cs_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; size_t v_sz_2417_; size_t v___x_2418_; lean_object* v___x_2419_; 
v_cs_2414_ = lean_ctor_get(v_n_2405_, 0);
v___x_2415_ = lean_box(0);
v___x_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
lean_ctor_set(v___x_2416_, 1, v_b_2406_);
v_sz_2417_ = lean_array_size(v_cs_2414_);
v___x_2418_ = ((size_t)0ULL);
v___x_2419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_2404_, v_cs_2414_, v_sz_2417_, v___x_2418_, v___x_2416_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2434_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2434_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2434_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v_fst_2424_; 
v_fst_2424_ = lean_ctor_get(v_a_2420_, 0);
if (lean_obj_tag(v_fst_2424_) == 0)
{
lean_object* v_snd_2425_; lean_object* v___x_2426_; lean_object* v___x_2428_; 
v_snd_2425_ = lean_ctor_get(v_a_2420_, 1);
lean_inc(v_snd_2425_);
lean_dec(v_a_2420_);
v___x_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2426_, 0, v_snd_2425_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2426_);
v___x_2428_ = v___x_2422_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
else
{
lean_object* v_val_2430_; lean_object* v___x_2432_; 
lean_inc_ref(v_fst_2424_);
lean_dec(v_a_2420_);
v_val_2430_ = lean_ctor_get(v_fst_2424_, 0);
lean_inc(v_val_2430_);
lean_dec_ref(v_fst_2424_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v_val_2430_);
v___x_2432_ = v___x_2422_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_val_2430_);
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
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
v_a_2435_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2419_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2419_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
else
{
lean_object* v_vs_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; size_t v_sz_2446_; size_t v___x_2447_; lean_object* v___x_2448_; 
v_vs_2443_ = lean_ctor_get(v_n_2405_, 0);
v___x_2444_ = lean_box(0);
v___x_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
lean_ctor_set(v___x_2445_, 1, v_b_2406_);
v_sz_2446_ = lean_array_size(v_vs_2443_);
v___x_2447_ = ((size_t)0ULL);
v___x_2448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_vs_2443_, v_sz_2446_, v___x_2447_, v___x_2445_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2463_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2451_ = v___x_2448_;
v_isShared_2452_ = v_isSharedCheck_2463_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2463_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v_fst_2453_; 
v_fst_2453_ = lean_ctor_get(v_a_2449_, 0);
if (lean_obj_tag(v_fst_2453_) == 0)
{
lean_object* v_snd_2454_; lean_object* v___x_2455_; lean_object* v___x_2457_; 
v_snd_2454_ = lean_ctor_get(v_a_2449_, 1);
lean_inc(v_snd_2454_);
lean_dec(v_a_2449_);
v___x_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2455_, 0, v_snd_2454_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 0, v___x_2455_);
v___x_2457_ = v___x_2451_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
else
{
lean_object* v_val_2459_; lean_object* v___x_2461_; 
lean_inc_ref(v_fst_2453_);
lean_dec(v_a_2449_);
v_val_2459_ = lean_ctor_get(v_fst_2453_, 0);
lean_inc(v_val_2459_);
lean_dec_ref(v_fst_2453_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 0, v_val_2459_);
v___x_2461_ = v___x_2451_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_val_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
v_a_2464_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2448_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2448_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(lean_object* v_init_2472_, lean_object* v_as_2473_, size_t v_sz_2474_, size_t v_i_2475_, lean_object* v_b_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
uint8_t v___x_2484_; 
v___x_2484_ = lean_usize_dec_lt(v_i_2475_, v_sz_2474_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_b_2476_);
return v___x_2485_;
}
else
{
lean_object* v_snd_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2520_; 
v_snd_2486_ = lean_ctor_get(v_b_2476_, 1);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_b_2476_);
if (v_isSharedCheck_2520_ == 0)
{
lean_object* v_unused_2521_; 
v_unused_2521_ = lean_ctor_get(v_b_2476_, 0);
lean_dec(v_unused_2521_);
v___x_2488_ = v_b_2476_;
v_isShared_2489_ = v_isSharedCheck_2520_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_snd_2486_);
lean_dec(v_b_2476_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2520_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v_a_2490_; lean_object* v___x_2491_; 
v_a_2490_ = lean_array_uget_borrowed(v_as_2473_, v_i_2475_);
lean_inc(v_snd_2486_);
v___x_2491_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_2472_, v_a_2490_, v_snd_2486_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2511_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2511_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2511_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
if (lean_obj_tag(v_a_2492_) == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2498_; 
v___x_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2496_, 0, v_a_2492_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v___x_2496_);
v___x_2498_ = v___x_2488_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_snd_2486_);
v___x_2498_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
lean_object* v___x_2500_; 
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2498_);
v___x_2500_ = v___x_2494_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; 
lean_del_object(v___x_2494_);
lean_dec(v_snd_2486_);
v_a_2503_ = lean_ctor_get(v_a_2492_, 0);
lean_inc(v_a_2503_);
lean_dec_ref(v_a_2492_);
v___x_2504_ = lean_box(0);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 1, v_a_2503_);
lean_ctor_set(v___x_2488_, 0, v___x_2504_);
v___x_2506_ = v___x_2488_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_a_2503_);
v___x_2506_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
size_t v___x_2507_; size_t v___x_2508_; 
v___x_2507_ = ((size_t)1ULL);
v___x_2508_ = lean_usize_add(v_i_2475_, v___x_2507_);
v_i_2475_ = v___x_2508_;
v_b_2476_ = v___x_2506_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_del_object(v___x_2488_);
lean_dec(v_snd_2486_);
v_a_2512_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2491_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2491_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_init_2522_, lean_object* v_as_2523_, lean_object* v_sz_2524_, lean_object* v_i_2525_, lean_object* v_b_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
size_t v_sz_boxed_2534_; size_t v_i_boxed_2535_; lean_object* v_res_2536_; 
v_sz_boxed_2534_ = lean_unbox_usize(v_sz_2524_);
lean_dec(v_sz_2524_);
v_i_boxed_2535_ = lean_unbox_usize(v_i_2525_);
lean_dec(v_i_2525_);
v_res_2536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_2522_, v_as_2523_, v_sz_boxed_2534_, v_i_boxed_2535_, v_b_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec_ref(v_as_2523_);
lean_dec_ref(v_init_2522_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2___boxed(lean_object* v_init_2537_, lean_object* v_n_2538_, lean_object* v_b_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_2537_, v_n_2538_, v_b_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec_ref(v_n_2538_);
lean_dec_ref(v_init_2537_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(lean_object* v_as_2548_, size_t v_sz_2549_, size_t v_i_2550_, lean_object* v_b_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
uint8_t v___x_2559_; 
v___x_2559_ = lean_usize_dec_lt(v_i_2550_, v_sz_2549_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_b_2551_);
return v___x_2560_;
}
else
{
lean_object* v_snd_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2666_; 
v_snd_2561_ = lean_ctor_get(v_b_2551_, 1);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_b_2551_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v_b_2551_, 0);
lean_dec(v_unused_2667_);
v___x_2563_ = v_b_2551_;
v_isShared_2564_ = v_isSharedCheck_2666_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_snd_2561_);
lean_dec(v_b_2551_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2666_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2565_; lean_object* v_a_2567_; lean_object* v_a_2574_; 
v___x_2565_ = lean_box(0);
v_a_2574_ = lean_array_uget(v_as_2548_, v_i_2550_);
if (lean_obj_tag(v_a_2574_) == 0)
{
v_a_2567_ = v_snd_2561_;
goto v___jp_2566_;
}
else
{
lean_object* v_snd_2575_; lean_object* v_val_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2665_; 
v_snd_2575_ = lean_ctor_get(v_snd_2561_, 1);
lean_inc(v_snd_2575_);
v_val_2576_ = lean_ctor_get(v_a_2574_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_a_2574_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2578_ = v_a_2574_;
v_isShared_2579_ = v_isSharedCheck_2665_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_val_2576_);
lean_dec(v_a_2574_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2665_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v_fst_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2663_; 
v_fst_2580_ = lean_ctor_get(v_snd_2561_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v_snd_2561_);
if (v_isSharedCheck_2663_ == 0)
{
lean_object* v_unused_2664_; 
v_unused_2664_ = lean_ctor_get(v_snd_2561_, 1);
lean_dec(v_unused_2664_);
v___x_2582_ = v_snd_2561_;
v_isShared_2583_ = v_isSharedCheck_2663_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_fst_2580_);
lean_dec(v_snd_2561_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2663_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v_fst_2584_; lean_object* v_snd_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2662_; 
v_fst_2584_ = lean_ctor_get(v_snd_2575_, 0);
v_snd_2585_ = lean_ctor_get(v_snd_2575_, 1);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_snd_2575_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2587_ = v_snd_2575_;
v_isShared_2588_ = v_isSharedCheck_2662_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_snd_2585_);
lean_inc(v_fst_2584_);
lean_dec(v_snd_2575_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2662_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v_decl_2590_; 
if (lean_obj_tag(v_val_2576_) == 0)
{
lean_object* v_fvarId_2605_; lean_object* v_userName_2606_; lean_object* v_type_2607_; uint8_t v_bi_2608_; uint8_t v_kind_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2626_; 
v_fvarId_2605_ = lean_ctor_get(v_val_2576_, 1);
v_userName_2606_ = lean_ctor_get(v_val_2576_, 2);
v_type_2607_ = lean_ctor_get(v_val_2576_, 3);
v_bi_2608_ = lean_ctor_get_uint8(v_val_2576_, sizeof(void*)*4);
v_kind_2609_ = lean_ctor_get_uint8(v_val_2576_, sizeof(void*)*4 + 1);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_val_2576_);
if (v_isSharedCheck_2626_ == 0)
{
lean_object* v_unused_2627_; 
v_unused_2627_ = lean_ctor_get(v_val_2576_, 0);
lean_dec(v_unused_2627_);
v___x_2611_ = v_val_2576_;
v_isShared_2612_ = v_isSharedCheck_2626_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_type_2607_);
lean_inc(v_userName_2606_);
lean_inc(v_fvarId_2605_);
lean_dec(v_val_2576_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2626_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; 
v___x_2613_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2607_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2616_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref(v___x_2613_);
lean_inc(v_snd_2585_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 3, v_a_2614_);
lean_ctor_set(v___x_2611_, 0, v_snd_2585_);
v___x_2616_ = v___x_2611_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_snd_2585_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_fvarId_2605_);
lean_ctor_set(v_reuseFailAlloc_2617_, 2, v_userName_2606_);
lean_ctor_set(v_reuseFailAlloc_2617_, 3, v_a_2614_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*4, v_bi_2608_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*4 + 1, v_kind_2609_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
v_decl_2590_ = v___x_2616_;
goto v___jp_2589_;
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_del_object(v___x_2611_);
lean_dec(v_userName_2606_);
lean_dec(v_fvarId_2605_);
lean_del_object(v___x_2587_);
lean_dec(v_snd_2585_);
lean_dec(v_fst_2584_);
lean_del_object(v___x_2582_);
lean_dec(v_fst_2580_);
lean_del_object(v___x_2578_);
lean_del_object(v___x_2563_);
v_a_2618_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2613_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2613_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2628_; lean_object* v_userName_2629_; lean_object* v_type_2630_; lean_object* v_value_2631_; uint8_t v_nondep_2632_; uint8_t v_kind_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2660_; 
v_fvarId_2628_ = lean_ctor_get(v_val_2576_, 1);
v_userName_2629_ = lean_ctor_get(v_val_2576_, 2);
v_type_2630_ = lean_ctor_get(v_val_2576_, 3);
v_value_2631_ = lean_ctor_get(v_val_2576_, 4);
v_nondep_2632_ = lean_ctor_get_uint8(v_val_2576_, sizeof(void*)*5);
v_kind_2633_ = lean_ctor_get_uint8(v_val_2576_, sizeof(void*)*5 + 1);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_val_2576_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; 
v_unused_2661_ = lean_ctor_get(v_val_2576_, 0);
lean_dec(v_unused_2661_);
v___x_2635_ = v_val_2576_;
v_isShared_2636_ = v_isSharedCheck_2660_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_value_2631_);
lean_inc(v_type_2630_);
lean_inc(v_userName_2629_);
lean_inc(v_fvarId_2628_);
lean_dec(v_val_2576_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2660_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; 
v___x_2637_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2630_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v___x_2639_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref(v___x_2637_);
v___x_2639_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2631_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2642_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref(v___x_2639_);
lean_inc(v_snd_2585_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 4, v_a_2640_);
lean_ctor_set(v___x_2635_, 3, v_a_2638_);
lean_ctor_set(v___x_2635_, 0, v_snd_2585_);
v___x_2642_ = v___x_2635_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_snd_2585_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_fvarId_2628_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v_userName_2629_);
lean_ctor_set(v_reuseFailAlloc_2643_, 3, v_a_2638_);
lean_ctor_set(v_reuseFailAlloc_2643_, 4, v_a_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*5, v_nondep_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*5 + 1, v_kind_2633_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
v_decl_2590_ = v___x_2642_;
goto v___jp_2589_;
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v_a_2638_);
lean_del_object(v___x_2635_);
lean_dec(v_userName_2629_);
lean_dec(v_fvarId_2628_);
lean_del_object(v___x_2587_);
lean_dec(v_snd_2585_);
lean_dec(v_fst_2584_);
lean_del_object(v___x_2582_);
lean_dec(v_fst_2580_);
lean_del_object(v___x_2578_);
lean_del_object(v___x_2563_);
v_a_2644_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2639_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2639_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_del_object(v___x_2635_);
lean_dec_ref(v_value_2631_);
lean_dec(v_userName_2629_);
lean_dec(v_fvarId_2628_);
lean_del_object(v___x_2587_);
lean_dec(v_snd_2585_);
lean_dec(v_fst_2584_);
lean_del_object(v___x_2582_);
lean_dec(v_fst_2580_);
lean_del_object(v___x_2578_);
lean_del_object(v___x_2563_);
v_a_2652_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2637_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2637_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
v___jp_2589_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2591_ = lean_unsigned_to_nat(1u);
v___x_2592_ = lean_nat_add(v_snd_2585_, v___x_2591_);
lean_dec(v_snd_2585_);
lean_inc_ref(v_decl_2590_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 0, v_decl_2590_);
v___x_2594_ = v___x_2578_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_decl_2590_);
v___x_2594_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2595_ = l_Lean_PersistentArray_push___redArg(v_fst_2584_, v___x_2594_);
v___x_2596_ = l_Lean_LocalDecl_fvarId(v_decl_2590_);
v___x_2597_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2580_, v___x_2596_, v_decl_2590_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 1, v___x_2592_);
lean_ctor_set(v___x_2587_, 0, v___x_2595_);
v___x_2599_ = v___x_2587_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v___x_2592_);
v___x_2599_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2601_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 1, v___x_2599_);
lean_ctor_set(v___x_2582_, 0, v___x_2597_);
v___x_2601_ = v___x_2582_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
v_a_2567_ = v___x_2601_;
goto v___jp_2566_;
}
}
}
}
}
}
}
}
v___jp_2566_:
{
lean_object* v___x_2569_; 
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 1, v_a_2567_);
lean_ctor_set(v___x_2563_, 0, v___x_2565_);
v___x_2569_ = v___x_2563_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2565_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_a_2567_);
v___x_2569_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
size_t v___x_2570_; size_t v___x_2571_; 
v___x_2570_ = ((size_t)1ULL);
v___x_2571_ = lean_usize_add(v_i_2550_, v___x_2570_);
v_i_2550_ = v___x_2571_;
v_b_2551_ = v___x_2569_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8___boxed(lean_object* v_as_2668_, lean_object* v_sz_2669_, lean_object* v_i_2670_, lean_object* v_b_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
size_t v_sz_boxed_2679_; size_t v_i_boxed_2680_; lean_object* v_res_2681_; 
v_sz_boxed_2679_ = lean_unbox_usize(v_sz_2669_);
lean_dec(v_sz_2669_);
v_i_boxed_2680_ = lean_unbox_usize(v_i_2670_);
lean_dec(v_i_2670_);
v_res_2681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_2668_, v_sz_boxed_2679_, v_i_boxed_2680_, v_b_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec_ref(v_as_2668_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(lean_object* v_as_2682_, size_t v_sz_2683_, size_t v_i_2684_, lean_object* v_b_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
uint8_t v___x_2693_; 
v___x_2693_ = lean_usize_dec_lt(v_i_2684_, v_sz_2683_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2694_, 0, v_b_2685_);
return v___x_2694_;
}
else
{
lean_object* v_snd_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2800_; 
v_snd_2695_ = lean_ctor_get(v_b_2685_, 1);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_b_2685_);
if (v_isSharedCheck_2800_ == 0)
{
lean_object* v_unused_2801_; 
v_unused_2801_ = lean_ctor_get(v_b_2685_, 0);
lean_dec(v_unused_2801_);
v___x_2697_ = v_b_2685_;
v_isShared_2698_ = v_isSharedCheck_2800_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_snd_2695_);
lean_dec(v_b_2685_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2800_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2699_; lean_object* v_a_2701_; lean_object* v_a_2708_; 
v___x_2699_ = lean_box(0);
v_a_2708_ = lean_array_uget(v_as_2682_, v_i_2684_);
if (lean_obj_tag(v_a_2708_) == 0)
{
v_a_2701_ = v_snd_2695_;
goto v___jp_2700_;
}
else
{
lean_object* v_snd_2709_; lean_object* v_val_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2799_; 
v_snd_2709_ = lean_ctor_get(v_snd_2695_, 1);
lean_inc(v_snd_2709_);
v_val_2710_ = lean_ctor_get(v_a_2708_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_a_2708_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2712_ = v_a_2708_;
v_isShared_2713_ = v_isSharedCheck_2799_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_val_2710_);
lean_dec(v_a_2708_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2799_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v_fst_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2797_; 
v_fst_2714_ = lean_ctor_get(v_snd_2695_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v_snd_2695_);
if (v_isSharedCheck_2797_ == 0)
{
lean_object* v_unused_2798_; 
v_unused_2798_ = lean_ctor_get(v_snd_2695_, 1);
lean_dec(v_unused_2798_);
v___x_2716_ = v_snd_2695_;
v_isShared_2717_ = v_isSharedCheck_2797_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_fst_2714_);
lean_dec(v_snd_2695_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2797_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v_fst_2718_; lean_object* v_snd_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2796_; 
v_fst_2718_ = lean_ctor_get(v_snd_2709_, 0);
v_snd_2719_ = lean_ctor_get(v_snd_2709_, 1);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_snd_2709_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2721_ = v_snd_2709_;
v_isShared_2722_ = v_isSharedCheck_2796_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_snd_2719_);
lean_inc(v_fst_2718_);
lean_dec(v_snd_2709_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2796_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v_decl_2724_; 
if (lean_obj_tag(v_val_2710_) == 0)
{
lean_object* v_fvarId_2739_; lean_object* v_userName_2740_; lean_object* v_type_2741_; uint8_t v_bi_2742_; uint8_t v_kind_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2760_; 
v_fvarId_2739_ = lean_ctor_get(v_val_2710_, 1);
v_userName_2740_ = lean_ctor_get(v_val_2710_, 2);
v_type_2741_ = lean_ctor_get(v_val_2710_, 3);
v_bi_2742_ = lean_ctor_get_uint8(v_val_2710_, sizeof(void*)*4);
v_kind_2743_ = lean_ctor_get_uint8(v_val_2710_, sizeof(void*)*4 + 1);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_val_2710_);
if (v_isSharedCheck_2760_ == 0)
{
lean_object* v_unused_2761_; 
v_unused_2761_ = lean_ctor_get(v_val_2710_, 0);
lean_dec(v_unused_2761_);
v___x_2745_ = v_val_2710_;
v_isShared_2746_ = v_isSharedCheck_2760_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_type_2741_);
lean_inc(v_userName_2740_);
lean_inc(v_fvarId_2739_);
lean_dec(v_val_2710_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2760_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; 
v___x_2747_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2741_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2750_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
lean_dec_ref(v___x_2747_);
lean_inc(v_snd_2719_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 3, v_a_2748_);
lean_ctor_set(v___x_2745_, 0, v_snd_2719_);
v___x_2750_ = v___x_2745_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_snd_2719_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_fvarId_2739_);
lean_ctor_set(v_reuseFailAlloc_2751_, 2, v_userName_2740_);
lean_ctor_set(v_reuseFailAlloc_2751_, 3, v_a_2748_);
lean_ctor_set_uint8(v_reuseFailAlloc_2751_, sizeof(void*)*4, v_bi_2742_);
lean_ctor_set_uint8(v_reuseFailAlloc_2751_, sizeof(void*)*4 + 1, v_kind_2743_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
v_decl_2724_ = v___x_2750_;
goto v___jp_2723_;
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_del_object(v___x_2745_);
lean_dec(v_userName_2740_);
lean_dec(v_fvarId_2739_);
lean_del_object(v___x_2721_);
lean_dec(v_snd_2719_);
lean_dec(v_fst_2718_);
lean_del_object(v___x_2716_);
lean_dec(v_fst_2714_);
lean_del_object(v___x_2712_);
lean_del_object(v___x_2697_);
v_a_2752_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2747_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2747_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2762_; lean_object* v_userName_2763_; lean_object* v_type_2764_; lean_object* v_value_2765_; uint8_t v_nondep_2766_; uint8_t v_kind_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2794_; 
v_fvarId_2762_ = lean_ctor_get(v_val_2710_, 1);
v_userName_2763_ = lean_ctor_get(v_val_2710_, 2);
v_type_2764_ = lean_ctor_get(v_val_2710_, 3);
v_value_2765_ = lean_ctor_get(v_val_2710_, 4);
v_nondep_2766_ = lean_ctor_get_uint8(v_val_2710_, sizeof(void*)*5);
v_kind_2767_ = lean_ctor_get_uint8(v_val_2710_, sizeof(void*)*5 + 1);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_val_2710_);
if (v_isSharedCheck_2794_ == 0)
{
lean_object* v_unused_2795_; 
v_unused_2795_ = lean_ctor_get(v_val_2710_, 0);
lean_dec(v_unused_2795_);
v___x_2769_ = v_val_2710_;
v_isShared_2770_ = v_isSharedCheck_2794_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_value_2765_);
lean_inc(v_type_2764_);
lean_inc(v_userName_2763_);
lean_inc(v_fvarId_2762_);
lean_dec(v_val_2710_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2794_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; 
v___x_2771_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2764_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2773_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref(v___x_2771_);
v___x_2773_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2765_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2776_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref(v___x_2773_);
lean_inc(v_snd_2719_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 4, v_a_2774_);
lean_ctor_set(v___x_2769_, 3, v_a_2772_);
lean_ctor_set(v___x_2769_, 0, v_snd_2719_);
v___x_2776_ = v___x_2769_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_snd_2719_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_fvarId_2762_);
lean_ctor_set(v_reuseFailAlloc_2777_, 2, v_userName_2763_);
lean_ctor_set(v_reuseFailAlloc_2777_, 3, v_a_2772_);
lean_ctor_set(v_reuseFailAlloc_2777_, 4, v_a_2774_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, sizeof(void*)*5, v_nondep_2766_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, sizeof(void*)*5 + 1, v_kind_2767_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
v_decl_2724_ = v___x_2776_;
goto v___jp_2723_;
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec(v_a_2772_);
lean_del_object(v___x_2769_);
lean_dec(v_userName_2763_);
lean_dec(v_fvarId_2762_);
lean_del_object(v___x_2721_);
lean_dec(v_snd_2719_);
lean_dec(v_fst_2718_);
lean_del_object(v___x_2716_);
lean_dec(v_fst_2714_);
lean_del_object(v___x_2712_);
lean_del_object(v___x_2697_);
v_a_2778_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2773_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2773_);
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
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_del_object(v___x_2769_);
lean_dec_ref(v_value_2765_);
lean_dec(v_userName_2763_);
lean_dec(v_fvarId_2762_);
lean_del_object(v___x_2721_);
lean_dec(v_snd_2719_);
lean_dec(v_fst_2718_);
lean_del_object(v___x_2716_);
lean_dec(v_fst_2714_);
lean_del_object(v___x_2712_);
lean_del_object(v___x_2697_);
v_a_2786_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2771_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2771_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
v___jp_2723_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2725_ = lean_unsigned_to_nat(1u);
v___x_2726_ = lean_nat_add(v_snd_2719_, v___x_2725_);
lean_dec(v_snd_2719_);
lean_inc_ref(v_decl_2724_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v_decl_2724_);
v___x_2728_ = v___x_2712_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_decl_2724_);
v___x_2728_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2729_ = l_Lean_PersistentArray_push___redArg(v_fst_2718_, v___x_2728_);
v___x_2730_ = l_Lean_LocalDecl_fvarId(v_decl_2724_);
v___x_2731_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2714_, v___x_2730_, v_decl_2724_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 1, v___x_2726_);
lean_ctor_set(v___x_2721_, 0, v___x_2729_);
v___x_2733_ = v___x_2721_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2729_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v___x_2726_);
v___x_2733_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2735_; 
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 1, v___x_2733_);
lean_ctor_set(v___x_2716_, 0, v___x_2731_);
v___x_2735_ = v___x_2716_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
v_a_2701_ = v___x_2735_;
goto v___jp_2700_;
}
}
}
}
}
}
}
}
v___jp_2700_:
{
lean_object* v___x_2703_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v_a_2701_);
lean_ctor_set(v___x_2697_, 0, v___x_2699_);
v___x_2703_ = v___x_2697_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_a_2701_);
v___x_2703_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
size_t v___x_2704_; size_t v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = ((size_t)1ULL);
v___x_2705_ = lean_usize_add(v_i_2684_, v___x_2704_);
v___x_2706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_2682_, v_sz_2683_, v___x_2705_, v___x_2703_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
return v___x_2706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3___boxed(lean_object* v_as_2802_, lean_object* v_sz_2803_, lean_object* v_i_2804_, lean_object* v_b_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
size_t v_sz_boxed_2813_; size_t v_i_boxed_2814_; lean_object* v_res_2815_; 
v_sz_boxed_2813_ = lean_unbox_usize(v_sz_2803_);
lean_dec(v_sz_2803_);
v_i_boxed_2814_ = lean_unbox_usize(v_i_2804_);
lean_dec(v_i_2804_);
v_res_2815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_as_2802_, v_sz_boxed_2813_, v_i_boxed_2814_, v_b_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec_ref(v_as_2802_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(lean_object* v_t_2816_, lean_object* v_init_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v_root_2825_; lean_object* v_tail_2826_; lean_object* v___x_2827_; 
v_root_2825_ = lean_ctor_get(v_t_2816_, 0);
v_tail_2826_ = lean_ctor_get(v_t_2816_, 1);
lean_inc_ref(v_init_2817_);
v___x_2827_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_2817_, v_root_2825_, v_init_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec_ref(v_init_2817_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2864_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2864_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2864_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
if (lean_obj_tag(v_a_2828_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2834_; 
v_a_2832_ = lean_ctor_get(v_a_2828_, 0);
lean_inc(v_a_2832_);
lean_dec_ref(v_a_2828_);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v_a_2832_);
v___x_2834_ = v___x_2830_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; size_t v_sz_2839_; size_t v___x_2840_; lean_object* v___x_2841_; 
lean_del_object(v___x_2830_);
v_a_2836_ = lean_ctor_get(v_a_2828_, 0);
lean_inc(v_a_2836_);
lean_dec_ref(v_a_2828_);
v___x_2837_ = lean_box(0);
v___x_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
lean_ctor_set(v___x_2838_, 1, v_a_2836_);
v_sz_2839_ = lean_array_size(v_tail_2826_);
v___x_2840_ = ((size_t)0ULL);
v___x_2841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_tail_2826_, v_sz_2839_, v___x_2840_, v___x_2838_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2855_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2855_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2855_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v_fst_2846_; 
v_fst_2846_ = lean_ctor_get(v_a_2842_, 0);
if (lean_obj_tag(v_fst_2846_) == 0)
{
lean_object* v_snd_2847_; lean_object* v___x_2849_; 
v_snd_2847_ = lean_ctor_get(v_a_2842_, 1);
lean_inc(v_snd_2847_);
lean_dec(v_a_2842_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v_snd_2847_);
v___x_2849_ = v___x_2844_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_snd_2847_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
else
{
lean_object* v_val_2851_; lean_object* v___x_2853_; 
lean_inc_ref(v_fst_2846_);
lean_dec(v_a_2842_);
v_val_2851_ = lean_ctor_get(v_fst_2846_, 0);
lean_inc(v_val_2851_);
lean_dec_ref(v_fst_2846_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v_val_2851_);
v___x_2853_ = v___x_2844_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_val_2851_);
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
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
v_a_2856_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2841_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2841_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
v_a_2865_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2827_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2827_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1___boxed(lean_object* v_t_2873_, lean_object* v_init_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_t_2873_, v_init_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec_ref(v_t_2873_);
return v_res_2882_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0(void){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2883_ = lean_unsigned_to_nat(32u);
v___x_2884_ = lean_mk_empty_array_with_capacity(v___x_2883_);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
return v___x_2885_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1(void){
_start:
{
size_t v___x_2886_; lean_object* v_index_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v_decls_2891_; 
v___x_2886_ = ((size_t)5ULL);
v_index_2887_ = lean_unsigned_to_nat(0u);
v___x_2888_ = lean_unsigned_to_nat(32u);
v___x_2889_ = lean_mk_empty_array_with_capacity(v___x_2888_);
v___x_2890_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0);
v_decls_2891_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_decls_2891_, 0, v___x_2890_);
lean_ctor_set(v_decls_2891_, 1, v___x_2889_);
lean_ctor_set(v_decls_2891_, 2, v_index_2887_);
lean_ctor_set(v_decls_2891_, 3, v_index_2887_);
lean_ctor_set_usize(v_decls_2891_, 4, v___x_2886_);
return v_decls_2891_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2(void){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2892_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3(void){
_start:
{
lean_object* v___x_2893_; lean_object* v_fvarIdToDecl_2894_; 
v___x_2893_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2);
v_fvarIdToDecl_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fvarIdToDecl_2894_, 0, v___x_2893_);
return v_fvarIdToDecl_2894_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4(void){
_start:
{
lean_object* v_index_2895_; lean_object* v_decls_2896_; lean_object* v___x_2897_; 
v_index_2895_ = lean_unsigned_to_nat(0u);
v_decls_2896_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1);
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v_decls_2896_);
lean_ctor_set(v___x_2897_, 1, v_index_2895_);
return v___x_2897_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5(void){
_start:
{
lean_object* v___x_2898_; lean_object* v_fvarIdToDecl_2899_; lean_object* v___x_2900_; 
v___x_2898_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4);
v_fvarIdToDecl_2899_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3);
v___x_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2900_, 0, v_fvarIdToDecl_2899_);
lean_ctor_set(v___x_2900_, 1, v___x_2898_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(lean_object* v_lctx_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_decls_2909_; lean_object* v_auxDeclToFullName_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2938_; 
v_decls_2909_ = lean_ctor_get(v_lctx_2901_, 1);
v_auxDeclToFullName_2910_ = lean_ctor_get(v_lctx_2901_, 2);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_lctx_2901_);
if (v_isSharedCheck_2938_ == 0)
{
lean_object* v_unused_2939_; 
v_unused_2939_ = lean_ctor_get(v_lctx_2901_, 0);
lean_dec(v_unused_2939_);
v___x_2912_ = v_lctx_2901_;
v_isShared_2913_ = v_isSharedCheck_2938_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_auxDeclToFullName_2910_);
lean_inc(v_decls_2909_);
lean_dec(v_lctx_2901_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2938_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5);
v___x_2915_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_decls_2909_, v___x_2914_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
lean_dec_ref(v_decls_2909_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2929_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2918_ = v___x_2915_;
v_isShared_2919_ = v_isSharedCheck_2929_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2915_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2929_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v_snd_2920_; lean_object* v_fst_2921_; lean_object* v_fst_2922_; lean_object* v___x_2924_; 
v_snd_2920_ = lean_ctor_get(v_a_2916_, 1);
lean_inc(v_snd_2920_);
v_fst_2921_ = lean_ctor_get(v_a_2916_, 0);
lean_inc(v_fst_2921_);
lean_dec(v_a_2916_);
v_fst_2922_ = lean_ctor_get(v_snd_2920_, 0);
lean_inc(v_fst_2922_);
lean_dec(v_snd_2920_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 1, v_fst_2922_);
lean_ctor_set(v___x_2912_, 0, v_fst_2921_);
v___x_2924_ = v___x_2912_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_fst_2921_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_fst_2922_);
lean_ctor_set(v_reuseFailAlloc_2928_, 2, v_auxDeclToFullName_2910_);
v___x_2924_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2926_; 
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v___x_2924_);
v___x_2926_ = v___x_2918_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2924_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_del_object(v___x_2912_);
lean_dec(v_auxDeclToFullName_2910_);
v_a_2930_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2915_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2915_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___boxed(lean_object* v_lctx_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0(lean_object* v_00_u03b2_2949_, lean_object* v_x_2950_, lean_object* v_x_2951_, lean_object* v_x_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_x_2950_, v_x_2951_, v_x_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(lean_object* v_00_u03b2_2954_, lean_object* v_x_2955_, size_t v_x_2956_, size_t v_x_2957_, lean_object* v_x_2958_, lean_object* v_x_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_2955_, v_x_2956_, v_x_2957_, v_x_2958_, v_x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2961_, lean_object* v_x_2962_, lean_object* v_x_2963_, lean_object* v_x_2964_, lean_object* v_x_2965_, lean_object* v_x_2966_){
_start:
{
size_t v_x_10744__boxed_2967_; size_t v_x_10745__boxed_2968_; lean_object* v_res_2969_; 
v_x_10744__boxed_2967_ = lean_unbox_usize(v_x_2963_);
lean_dec(v_x_2963_);
v_x_10745__boxed_2968_ = lean_unbox_usize(v_x_2964_);
lean_dec(v_x_2964_);
v_res_2969_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(v_00_u03b2_2961_, v_x_2962_, v_x_10744__boxed_2967_, v_x_10745__boxed_2968_, v_x_2965_, v_x_2966_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2970_, lean_object* v_n_2971_, lean_object* v_k_2972_, lean_object* v_v_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v_n_2971_, v_k_2972_, v_v_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2975_, size_t v_depth_2976_, lean_object* v_keys_2977_, lean_object* v_vals_2978_, lean_object* v_heq_2979_, lean_object* v_i_2980_, lean_object* v_entries_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_2976_, v_keys_2977_, v_vals_2978_, v_i_2980_, v_entries_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2983_, lean_object* v_depth_2984_, lean_object* v_keys_2985_, lean_object* v_vals_2986_, lean_object* v_heq_2987_, lean_object* v_i_2988_, lean_object* v_entries_2989_){
_start:
{
size_t v_depth_boxed_2990_; lean_object* v_res_2991_; 
v_depth_boxed_2990_ = lean_unbox_usize(v_depth_2984_);
lean_dec(v_depth_2984_);
v_res_2991_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(v_00_u03b2_2983_, v_depth_boxed_2990_, v_keys_2985_, v_vals_2986_, v_heq_2987_, v_i_2988_, v_entries_2989_);
lean_dec_ref(v_vals_2986_);
lean_dec_ref(v_keys_2985_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2992_, lean_object* v_x_2993_, lean_object* v_x_2994_, lean_object* v_x_2995_, lean_object* v_x_2996_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2993_, v_x_2994_, v_x_2995_, v_x_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2998_, lean_object* v_x_2999_, lean_object* v_x_3000_, lean_object* v_x_3001_){
_start:
{
lean_object* v_ks_3002_; lean_object* v_vs_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3027_; 
v_ks_3002_ = lean_ctor_get(v_x_2998_, 0);
v_vs_3003_ = lean_ctor_get(v_x_2998_, 1);
v_isSharedCheck_3027_ = !lean_is_exclusive(v_x_2998_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3005_ = v_x_2998_;
v_isShared_3006_ = v_isSharedCheck_3027_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_vs_3003_);
lean_inc(v_ks_3002_);
lean_dec(v_x_2998_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3027_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3007_ = lean_array_get_size(v_ks_3002_);
v___x_3008_ = lean_nat_dec_lt(v_x_2999_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3012_; 
lean_dec(v_x_2999_);
v___x_3009_ = lean_array_push(v_ks_3002_, v_x_3000_);
v___x_3010_ = lean_array_push(v_vs_3003_, v_x_3001_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 1, v___x_3010_);
lean_ctor_set(v___x_3005_, 0, v___x_3009_);
v___x_3012_ = v___x_3005_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3009_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
else
{
lean_object* v_k_x27_3014_; uint8_t v___x_3015_; 
v_k_x27_3014_ = lean_array_fget_borrowed(v_ks_3002_, v_x_2999_);
v___x_3015_ = l_Lean_instBEqMVarId_beq(v_x_3000_, v_k_x27_3014_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3017_; 
if (v_isShared_3006_ == 0)
{
v___x_3017_ = v___x_3005_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_ks_3002_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_vs_3003_);
v___x_3017_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_unsigned_to_nat(1u);
v___x_3019_ = lean_nat_add(v_x_2999_, v___x_3018_);
lean_dec(v_x_2999_);
v_x_2998_ = v___x_3017_;
v_x_2999_ = v___x_3019_;
goto _start;
}
}
else
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3022_ = lean_array_fset(v_ks_3002_, v_x_2999_, v_x_3000_);
v___x_3023_ = lean_array_fset(v_vs_3003_, v_x_2999_, v_x_3001_);
lean_dec(v_x_2999_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 1, v___x_3023_);
lean_ctor_set(v___x_3005_, 0, v___x_3022_);
v___x_3025_ = v___x_3005_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3022_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_3028_, lean_object* v_k_3029_, lean_object* v_v_3030_){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = lean_unsigned_to_nat(0u);
v___x_3032_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_3028_, v___x_3031_, v_k_3029_, v_v_3030_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3033_, size_t v_x_3034_, size_t v_x_3035_, lean_object* v_x_3036_, lean_object* v_x_3037_){
_start:
{
if (lean_obj_tag(v_x_3033_) == 0)
{
lean_object* v_es_3038_; size_t v___x_3039_; size_t v___x_3040_; size_t v___x_3041_; size_t v___x_3042_; lean_object* v_j_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; 
v_es_3038_ = lean_ctor_get(v_x_3033_, 0);
v___x_3039_ = ((size_t)5ULL);
v___x_3040_ = ((size_t)1ULL);
v___x_3041_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
v___x_3042_ = lean_usize_land(v_x_3034_, v___x_3041_);
v_j_3043_ = lean_usize_to_nat(v___x_3042_);
v___x_3044_ = lean_array_get_size(v_es_3038_);
v___x_3045_ = lean_nat_dec_lt(v_j_3043_, v___x_3044_);
if (v___x_3045_ == 0)
{
lean_dec(v_j_3043_);
lean_dec(v_x_3037_);
lean_dec(v_x_3036_);
return v_x_3033_;
}
else
{
lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3082_; 
lean_inc_ref(v_es_3038_);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_x_3033_);
if (v_isSharedCheck_3082_ == 0)
{
lean_object* v_unused_3083_; 
v_unused_3083_ = lean_ctor_get(v_x_3033_, 0);
lean_dec(v_unused_3083_);
v___x_3047_ = v_x_3033_;
v_isShared_3048_ = v_isSharedCheck_3082_;
goto v_resetjp_3046_;
}
else
{
lean_dec(v_x_3033_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3082_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v_v_3049_; lean_object* v___x_3050_; lean_object* v_xs_x27_3051_; lean_object* v___y_3053_; 
v_v_3049_ = lean_array_fget(v_es_3038_, v_j_3043_);
v___x_3050_ = lean_box(0);
v_xs_x27_3051_ = lean_array_fset(v_es_3038_, v_j_3043_, v___x_3050_);
switch(lean_obj_tag(v_v_3049_))
{
case 0:
{
lean_object* v_key_3058_; lean_object* v_val_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3069_; 
v_key_3058_ = lean_ctor_get(v_v_3049_, 0);
v_val_3059_ = lean_ctor_get(v_v_3049_, 1);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_v_3049_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3061_ = v_v_3049_;
v_isShared_3062_ = v_isSharedCheck_3069_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_val_3059_);
lean_inc(v_key_3058_);
lean_dec(v_v_3049_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3069_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
uint8_t v___x_3063_; 
v___x_3063_ = l_Lean_instBEqMVarId_beq(v_x_3036_, v_key_3058_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_del_object(v___x_3061_);
v___x_3064_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3058_, v_val_3059_, v_x_3036_, v_x_3037_);
v___x_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
v___y_3053_ = v___x_3065_;
goto v___jp_3052_;
}
else
{
lean_object* v___x_3067_; 
lean_dec(v_val_3059_);
lean_dec(v_key_3058_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 1, v_x_3037_);
lean_ctor_set(v___x_3061_, 0, v_x_3036_);
v___x_3067_ = v___x_3061_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_x_3036_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_x_3037_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
v___y_3053_ = v___x_3067_;
goto v___jp_3052_;
}
}
}
}
case 1:
{
lean_object* v_node_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3080_; 
v_node_3070_ = lean_ctor_get(v_v_3049_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v_v_3049_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3072_ = v_v_3049_;
v_isShared_3073_ = v_isSharedCheck_3080_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_node_3070_);
lean_dec(v_v_3049_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3080_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
size_t v___x_3074_; size_t v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3074_ = lean_usize_shift_right(v_x_3034_, v___x_3039_);
v___x_3075_ = lean_usize_add(v_x_3035_, v___x_3040_);
v___x_3076_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_node_3070_, v___x_3074_, v___x_3075_, v_x_3036_, v_x_3037_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3076_);
v___x_3078_ = v___x_3072_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
v___y_3053_ = v___x_3078_;
goto v___jp_3052_;
}
}
}
default: 
{
lean_object* v___x_3081_; 
v___x_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3081_, 0, v_x_3036_);
lean_ctor_set(v___x_3081_, 1, v_x_3037_);
v___y_3053_ = v___x_3081_;
goto v___jp_3052_;
}
}
v___jp_3052_:
{
lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3054_ = lean_array_fset(v_xs_x27_3051_, v_j_3043_, v___y_3053_);
lean_dec(v_j_3043_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3054_);
v___x_3056_ = v___x_3047_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
else
{
lean_object* v_ks_3084_; lean_object* v_vs_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3105_; 
v_ks_3084_ = lean_ctor_get(v_x_3033_, 0);
v_vs_3085_ = lean_ctor_get(v_x_3033_, 1);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_x_3033_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3087_ = v_x_3033_;
v_isShared_3088_ = v_isSharedCheck_3105_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_vs_3085_);
lean_inc(v_ks_3084_);
lean_dec(v_x_3033_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3105_;
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
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_ks_3084_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_vs_3085_);
v___x_3090_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v_newNode_3091_; uint8_t v___y_3093_; size_t v___x_3099_; uint8_t v___x_3100_; 
v_newNode_3091_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v___x_3090_, v_x_3036_, v_x_3037_);
v___x_3099_ = ((size_t)7ULL);
v___x_3100_ = lean_usize_dec_le(v___x_3099_, v_x_3035_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3101_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3091_);
v___x_3102_ = lean_unsigned_to_nat(4u);
v___x_3103_ = lean_nat_dec_lt(v___x_3101_, v___x_3102_);
lean_dec(v___x_3101_);
v___y_3093_ = v___x_3103_;
goto v___jp_3092_;
}
else
{
v___y_3093_ = v___x_3100_;
goto v___jp_3092_;
}
v___jp_3092_:
{
if (v___y_3093_ == 0)
{
lean_object* v_ks_3094_; lean_object* v_vs_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v_ks_3094_ = lean_ctor_get(v_newNode_3091_, 0);
lean_inc_ref(v_ks_3094_);
v_vs_3095_ = lean_ctor_get(v_newNode_3091_, 1);
lean_inc_ref(v_vs_3095_);
lean_dec_ref(v_newNode_3091_);
v___x_3096_ = lean_unsigned_to_nat(0u);
v___x_3097_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2);
v___x_3098_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3035_, v_ks_3094_, v_vs_3095_, v___x_3096_, v___x_3097_);
lean_dec_ref(v_vs_3095_);
lean_dec_ref(v_ks_3094_);
return v___x_3098_;
}
else
{
return v_newNode_3091_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_3106_, lean_object* v_keys_3107_, lean_object* v_vals_3108_, lean_object* v_i_3109_, lean_object* v_entries_3110_){
_start:
{
lean_object* v___x_3111_; uint8_t v___x_3112_; 
v___x_3111_ = lean_array_get_size(v_keys_3107_);
v___x_3112_ = lean_nat_dec_lt(v_i_3109_, v___x_3111_);
if (v___x_3112_ == 0)
{
lean_dec(v_i_3109_);
return v_entries_3110_;
}
else
{
lean_object* v_k_3113_; lean_object* v_v_3114_; uint64_t v___x_3115_; size_t v_h_3116_; size_t v___x_3117_; lean_object* v___x_3118_; size_t v___x_3119_; size_t v___x_3120_; size_t v___x_3121_; size_t v_h_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v_k_3113_ = lean_array_fget_borrowed(v_keys_3107_, v_i_3109_);
v_v_3114_ = lean_array_fget_borrowed(v_vals_3108_, v_i_3109_);
v___x_3115_ = l_Lean_instHashableMVarId_hash(v_k_3113_);
v_h_3116_ = lean_uint64_to_usize(v___x_3115_);
v___x_3117_ = ((size_t)5ULL);
v___x_3118_ = lean_unsigned_to_nat(1u);
v___x_3119_ = ((size_t)1ULL);
v___x_3120_ = lean_usize_sub(v_depth_3106_, v___x_3119_);
v___x_3121_ = lean_usize_mul(v___x_3117_, v___x_3120_);
v_h_3122_ = lean_usize_shift_right(v_h_3116_, v___x_3121_);
v___x_3123_ = lean_nat_add(v_i_3109_, v___x_3118_);
lean_dec(v_i_3109_);
lean_inc(v_v_3114_);
lean_inc(v_k_3113_);
v___x_3124_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_entries_3110_, v_h_3122_, v_depth_3106_, v_k_3113_, v_v_3114_);
v_i_3109_ = v___x_3123_;
v_entries_3110_ = v___x_3124_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_3126_, lean_object* v_keys_3127_, lean_object* v_vals_3128_, lean_object* v_i_3129_, lean_object* v_entries_3130_){
_start:
{
size_t v_depth_boxed_3131_; lean_object* v_res_3132_; 
v_depth_boxed_3131_ = lean_unbox_usize(v_depth_3126_);
lean_dec(v_depth_3126_);
v_res_3132_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_3131_, v_keys_3127_, v_vals_3128_, v_i_3129_, v_entries_3130_);
lean_dec_ref(v_vals_3128_);
lean_dec_ref(v_keys_3127_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3133_, lean_object* v_x_3134_, lean_object* v_x_3135_, lean_object* v_x_3136_, lean_object* v_x_3137_){
_start:
{
size_t v_x_2256__boxed_3138_; size_t v_x_2257__boxed_3139_; lean_object* v_res_3140_; 
v_x_2256__boxed_3138_ = lean_unbox_usize(v_x_3134_);
lean_dec(v_x_3134_);
v_x_2257__boxed_3139_ = lean_unbox_usize(v_x_3135_);
lean_dec(v_x_3135_);
v_res_3140_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_3133_, v_x_2256__boxed_3138_, v_x_2257__boxed_3139_, v_x_3136_, v_x_3137_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(lean_object* v_x_3141_, lean_object* v_x_3142_, lean_object* v_x_3143_){
_start:
{
uint64_t v___x_3144_; size_t v___x_3145_; size_t v___x_3146_; lean_object* v___x_3147_; 
v___x_3144_ = l_Lean_instHashableMVarId_hash(v_x_3142_);
v___x_3145_ = lean_uint64_to_usize(v___x_3144_);
v___x_3146_ = ((size_t)1ULL);
v___x_3147_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_3141_, v___x_3145_, v___x_3146_, v_x_3142_, v_x_3143_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(lean_object* v_mvarId_3148_, lean_object* v_val_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v___x_3152_; lean_object* v_mctx_3153_; lean_object* v_cache_3154_; lean_object* v_zetaDeltaFVarIds_3155_; lean_object* v_postponed_3156_; lean_object* v_diag_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3185_; 
v___x_3152_ = lean_st_ref_take(v___y_3150_);
v_mctx_3153_ = lean_ctor_get(v___x_3152_, 0);
v_cache_3154_ = lean_ctor_get(v___x_3152_, 1);
v_zetaDeltaFVarIds_3155_ = lean_ctor_get(v___x_3152_, 2);
v_postponed_3156_ = lean_ctor_get(v___x_3152_, 3);
v_diag_3157_ = lean_ctor_get(v___x_3152_, 4);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3159_ = v___x_3152_;
v_isShared_3160_ = v_isSharedCheck_3185_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_diag_3157_);
lean_inc(v_postponed_3156_);
lean_inc(v_zetaDeltaFVarIds_3155_);
lean_inc(v_cache_3154_);
lean_inc(v_mctx_3153_);
lean_dec(v___x_3152_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3185_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v_depth_3161_; lean_object* v_levelAssignDepth_3162_; lean_object* v_lmvarCounter_3163_; lean_object* v_mvarCounter_3164_; lean_object* v_lDecls_3165_; lean_object* v_decls_3166_; lean_object* v_userNames_3167_; lean_object* v_lAssignment_3168_; lean_object* v_eAssignment_3169_; lean_object* v_dAssignment_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3184_; 
v_depth_3161_ = lean_ctor_get(v_mctx_3153_, 0);
v_levelAssignDepth_3162_ = lean_ctor_get(v_mctx_3153_, 1);
v_lmvarCounter_3163_ = lean_ctor_get(v_mctx_3153_, 2);
v_mvarCounter_3164_ = lean_ctor_get(v_mctx_3153_, 3);
v_lDecls_3165_ = lean_ctor_get(v_mctx_3153_, 4);
v_decls_3166_ = lean_ctor_get(v_mctx_3153_, 5);
v_userNames_3167_ = lean_ctor_get(v_mctx_3153_, 6);
v_lAssignment_3168_ = lean_ctor_get(v_mctx_3153_, 7);
v_eAssignment_3169_ = lean_ctor_get(v_mctx_3153_, 8);
v_dAssignment_3170_ = lean_ctor_get(v_mctx_3153_, 9);
v_isSharedCheck_3184_ = !lean_is_exclusive(v_mctx_3153_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3172_ = v_mctx_3153_;
v_isShared_3173_ = v_isSharedCheck_3184_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_dAssignment_3170_);
lean_inc(v_eAssignment_3169_);
lean_inc(v_lAssignment_3168_);
lean_inc(v_userNames_3167_);
lean_inc(v_decls_3166_);
lean_inc(v_lDecls_3165_);
lean_inc(v_mvarCounter_3164_);
lean_inc(v_lmvarCounter_3163_);
lean_inc(v_levelAssignDepth_3162_);
lean_inc(v_depth_3161_);
lean_dec(v_mctx_3153_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3184_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v___x_3176_; 
v___x_3174_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_eAssignment_3169_, v_mvarId_3148_, v_val_3149_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 8, v___x_3174_);
v___x_3176_ = v___x_3172_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_depth_3161_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_levelAssignDepth_3162_);
lean_ctor_set(v_reuseFailAlloc_3183_, 2, v_lmvarCounter_3163_);
lean_ctor_set(v_reuseFailAlloc_3183_, 3, v_mvarCounter_3164_);
lean_ctor_set(v_reuseFailAlloc_3183_, 4, v_lDecls_3165_);
lean_ctor_set(v_reuseFailAlloc_3183_, 5, v_decls_3166_);
lean_ctor_set(v_reuseFailAlloc_3183_, 6, v_userNames_3167_);
lean_ctor_set(v_reuseFailAlloc_3183_, 7, v_lAssignment_3168_);
lean_ctor_set(v_reuseFailAlloc_3183_, 8, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3183_, 9, v_dAssignment_3170_);
v___x_3176_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
lean_object* v___x_3178_; 
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 0, v___x_3176_);
v___x_3178_ = v___x_3159_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_cache_3154_);
lean_ctor_set(v_reuseFailAlloc_3182_, 2, v_zetaDeltaFVarIds_3155_);
lean_ctor_set(v_reuseFailAlloc_3182_, 3, v_postponed_3156_);
lean_ctor_set(v_reuseFailAlloc_3182_, 4, v_diag_3157_);
v___x_3178_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = lean_st_ref_set(v___y_3150_, v___x_3178_);
v___x_3180_ = lean_box(0);
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
return v___x_3181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg___boxed(lean_object* v_mvarId_3186_, lean_object* v_val_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_3186_, v_val_3187_, v___y_3188_);
lean_dec(v___y_3188_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object* v_mvarId_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_){
_start:
{
lean_object* v___x_3199_; 
lean_inc(v_mvarId_3191_);
v___x_3199_ = l_Lean_MVarId_getDecl(v_mvarId_3191_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v_userName_3201_; lean_object* v_lctx_3202_; lean_object* v_type_3203_; lean_object* v_localInstances_3204_; lean_object* v___x_3205_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref(v___x_3199_);
v_userName_3201_ = lean_ctor_get(v_a_3200_, 0);
lean_inc(v_userName_3201_);
v_lctx_3202_ = lean_ctor_get(v_a_3200_, 1);
lean_inc_ref(v_lctx_3202_);
v_type_3203_ = lean_ctor_get(v_a_3200_, 2);
lean_inc_ref(v_type_3203_);
v_localInstances_3204_ = lean_ctor_get(v_a_3200_, 4);
lean_inc_ref(v_localInstances_3204_);
lean_dec(v_a_3200_);
v___x_3205_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_3202_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3207_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_a_3206_);
lean_dec_ref(v___x_3205_);
v___x_3207_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_3203_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; uint8_t v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref(v___x_3207_);
v___x_3209_ = 2;
v___x_3210_ = lean_unsigned_to_nat(0u);
v___x_3211_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_3206_, v_localInstances_3204_, v_a_3208_, v___x_3209_, v_userName_3201_, v___x_3210_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3221_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc_n(v_a_3212_, 2);
lean_dec_ref(v___x_3211_);
v___x_3213_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_3191_, v_a_3212_, v_a_3195_);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; 
v_unused_3222_ = lean_ctor_get(v___x_3213_, 0);
lean_dec(v_unused_3222_);
v___x_3215_ = v___x_3213_;
v_isShared_3216_ = v_isSharedCheck_3221_;
goto v_resetjp_3214_;
}
else
{
lean_dec(v___x_3213_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3221_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3217_ = l_Lean_Expr_mvarId_x21(v_a_3212_);
lean_dec(v_a_3212_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 0, v___x_3217_);
v___x_3219_ = v___x_3215_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_dec(v_mvarId_3191_);
v_a_3223_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3211_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3211_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
lean_dec(v_a_3206_);
lean_dec_ref(v_localInstances_3204_);
lean_dec(v_userName_3201_);
lean_dec(v_mvarId_3191_);
v_a_3231_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v___x_3207_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3207_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3231_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_dec_ref(v_localInstances_3204_);
lean_dec_ref(v_type_3203_);
lean_dec(v_userName_3201_);
lean_dec(v_mvarId_3191_);
v_a_3239_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3205_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3205_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_dec(v_mvarId_3191_);
v_a_3247_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3199_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3199_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar___boxed(lean_object* v_mvarId_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
lean_dec(v_a_3259_);
lean_dec_ref(v_a_3258_);
lean_dec(v_a_3257_);
lean_dec_ref(v_a_3256_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(lean_object* v_mvarId_3264_, lean_object* v_val_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_3264_, v_val_3265_, v___y_3269_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___boxed(lean_object* v_mvarId_3274_, lean_object* v_val_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(v_mvarId_3274_, v_val_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0(lean_object* v_00_u03b2_3284_, lean_object* v_x_3285_, lean_object* v_x_3286_, lean_object* v_x_3287_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_x_3285_, v_x_3286_, v_x_3287_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3289_, lean_object* v_x_3290_, size_t v_x_3291_, size_t v_x_3292_, lean_object* v_x_3293_, lean_object* v_x_3294_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_3290_, v_x_3291_, v_x_3292_, v_x_3293_, v_x_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3296_, lean_object* v_x_3297_, lean_object* v_x_3298_, lean_object* v_x_3299_, lean_object* v_x_3300_, lean_object* v_x_3301_){
_start:
{
size_t v_x_2610__boxed_3302_; size_t v_x_2611__boxed_3303_; lean_object* v_res_3304_; 
v_x_2610__boxed_3302_ = lean_unbox_usize(v_x_3298_);
lean_dec(v_x_3298_);
v_x_2611__boxed_3303_ = lean_unbox_usize(v_x_3299_);
lean_dec(v_x_3299_);
v_res_3304_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(v_00_u03b2_3296_, v_x_3297_, v_x_2610__boxed_3302_, v_x_2611__boxed_3303_, v_x_3300_, v_x_3301_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3305_, lean_object* v_n_3306_, lean_object* v_k_3307_, lean_object* v_v_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v_n_3306_, v_k_3307_, v_v_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3310_, size_t v_depth_3311_, lean_object* v_keys_3312_, lean_object* v_vals_3313_, lean_object* v_heq_3314_, lean_object* v_i_3315_, lean_object* v_entries_3316_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_3311_, v_keys_3312_, v_vals_3313_, v_i_3315_, v_entries_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3318_, lean_object* v_depth_3319_, lean_object* v_keys_3320_, lean_object* v_vals_3321_, lean_object* v_heq_3322_, lean_object* v_i_3323_, lean_object* v_entries_3324_){
_start:
{
size_t v_depth_boxed_3325_; lean_object* v_res_3326_; 
v_depth_boxed_3325_ = lean_unbox_usize(v_depth_3319_);
lean_dec(v_depth_3319_);
v_res_3326_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3318_, v_depth_boxed_3325_, v_keys_3320_, v_vals_3321_, v_heq_3322_, v_i_3323_, v_entries_3324_);
lean_dec_ref(v_vals_3321_);
lean_dec_ref(v_keys_3320_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3327_, lean_object* v_x_3328_, lean_object* v_x_3329_, lean_object* v_x_3330_, lean_object* v_x_3331_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_3328_, v_x_3329_, v_x_3330_, v_x_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(lean_object* v_msg_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v_ref_3339_; lean_object* v___x_3340_; lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3349_; 
v_ref_3339_ = lean_ctor_get(v___y_3336_, 5);
v___x_3340_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3343_ = v___x_3340_;
v_isShared_3344_ = v_isSharedCheck_3349_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3340_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3349_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3345_; lean_object* v___x_3347_; 
lean_inc(v_ref_3339_);
v___x_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3345_, 0, v_ref_3339_);
lean_ctor_set(v___x_3345_, 1, v_a_3341_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set_tag(v___x_3343_, 1);
lean_ctor_set(v___x_3343_, 0, v___x_3345_);
v___x_3347_ = v___x_3343_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg___boxed(lean_object* v_msg_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
return v_res_3356_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1(void){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0));
v___x_3359_ = l_Lean_stringToMessageData(v___x_3358_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(lean_object* v_msg_3362_, lean_object* v_e_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v___y_3372_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
v___x_3379_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3380_ = lean_string_dec_eq(v_msg_3362_, v___x_3379_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3381_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2));
v___x_3382_ = lean_string_append(v___x_3381_, v_msg_3362_);
lean_dec_ref(v_msg_3362_);
v___x_3383_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3));
v___x_3384_ = lean_string_append(v___x_3382_, v___x_3383_);
v___y_3372_ = v___x_3384_;
goto v___jp_3371_;
}
else
{
v___y_3372_ = v_msg_3362_;
goto v___jp_3371_;
}
v___jp_3371_:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3373_ = l_Lean_stringToMessageData(v___y_3372_);
v___x_3374_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1);
v___x_3375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3373_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = l_Lean_indentExpr(v_e_3363_);
v___x_3377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3375_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v___x_3377_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___boxed(lean_object* v_msg_3385_, lean_object* v_e_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3385_, v_e_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(lean_object* v_00_u03b1_3395_, lean_object* v_msg_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_3396_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___boxed(lean_object* v_00_u03b1_3405_, lean_object* v_msg_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(v_00_u03b1_3405_, v_msg_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3415_, lean_object* v_vals_3416_, lean_object* v_i_3417_, lean_object* v_k_3418_){
_start:
{
lean_object* v___x_3419_; uint8_t v___x_3420_; 
v___x_3419_ = lean_array_get_size(v_keys_3415_);
v___x_3420_ = lean_nat_dec_lt(v_i_3417_, v___x_3419_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; 
lean_dec_ref(v_k_3418_);
lean_dec(v_i_3417_);
v___x_3421_ = lean_box(0);
return v___x_3421_;
}
else
{
lean_object* v_k_x27_3422_; uint8_t v___x_3423_; 
v_k_x27_3422_ = lean_array_fget_borrowed(v_keys_3415_, v_i_3417_);
lean_inc(v_k_x27_3422_);
lean_inc_ref(v_k_3418_);
v___x_3423_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_3418_, v_k_x27_3422_);
if (v___x_3423_ == 0)
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = lean_unsigned_to_nat(1u);
v___x_3425_ = lean_nat_add(v_i_3417_, v___x_3424_);
lean_dec(v_i_3417_);
v_i_3417_ = v___x_3425_;
goto _start;
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
lean_dec_ref(v_k_3418_);
v___x_3427_ = lean_array_fget_borrowed(v_vals_3416_, v_i_3417_);
lean_dec(v_i_3417_);
lean_inc(v___x_3427_);
lean_inc(v_k_x27_3422_);
v___x_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3428_, 0, v_k_x27_3422_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v___x_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
return v___x_3429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3430_, lean_object* v_vals_3431_, lean_object* v_i_3432_, lean_object* v_k_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_3430_, v_vals_3431_, v_i_3432_, v_k_3433_);
lean_dec_ref(v_vals_3431_);
lean_dec_ref(v_keys_3430_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(lean_object* v_x_3435_, size_t v_x_3436_, lean_object* v_x_3437_){
_start:
{
if (lean_obj_tag(v_x_3435_) == 0)
{
lean_object* v_es_3438_; lean_object* v___x_3439_; size_t v___x_3440_; size_t v___x_3441_; size_t v___x_3442_; lean_object* v_j_3443_; lean_object* v___x_3444_; 
v_es_3438_ = lean_ctor_get(v_x_3435_, 0);
lean_inc_ref(v_es_3438_);
lean_dec_ref(v_x_3435_);
v___x_3439_ = lean_box(2);
v___x_3440_ = ((size_t)5ULL);
v___x_3441_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
v___x_3442_ = lean_usize_land(v_x_3436_, v___x_3441_);
v_j_3443_ = lean_usize_to_nat(v___x_3442_);
v___x_3444_ = lean_array_get(v___x_3439_, v_es_3438_, v_j_3443_);
lean_dec(v_j_3443_);
lean_dec_ref(v_es_3438_);
switch(lean_obj_tag(v___x_3444_))
{
case 0:
{
lean_object* v_key_3445_; lean_object* v_val_3446_; uint8_t v___x_3447_; 
v_key_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc_n(v_key_3445_, 2);
v_val_3446_ = lean_ctor_get(v___x_3444_, 1);
lean_inc(v_val_3446_);
lean_dec_ref(v___x_3444_);
v___x_3447_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_3437_, v_key_3445_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; 
lean_dec(v_val_3446_);
lean_dec(v_key_3445_);
v___x_3448_ = lean_box(0);
return v___x_3448_;
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3449_, 0, v_key_3445_);
lean_ctor_set(v___x_3449_, 1, v_val_3446_);
v___x_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
return v___x_3450_;
}
}
case 1:
{
lean_object* v_node_3451_; size_t v___x_3452_; 
v_node_3451_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_node_3451_);
lean_dec_ref(v___x_3444_);
v___x_3452_ = lean_usize_shift_right(v_x_3436_, v___x_3440_);
v_x_3435_ = v_node_3451_;
v_x_3436_ = v___x_3452_;
goto _start;
}
default: 
{
lean_object* v___x_3454_; 
lean_dec_ref(v_x_3437_);
v___x_3454_ = lean_box(0);
return v___x_3454_;
}
}
}
else
{
lean_object* v_ks_3455_; lean_object* v_vs_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v_ks_3455_ = lean_ctor_get(v_x_3435_, 0);
lean_inc_ref(v_ks_3455_);
v_vs_3456_ = lean_ctor_get(v_x_3435_, 1);
lean_inc_ref(v_vs_3456_);
lean_dec_ref(v_x_3435_);
v___x_3457_ = lean_unsigned_to_nat(0u);
v___x_3458_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_ks_3455_, v_vs_3456_, v___x_3457_, v_x_3437_);
lean_dec_ref(v_vs_3456_);
lean_dec_ref(v_ks_3455_);
return v___x_3458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_3459_, lean_object* v_x_3460_, lean_object* v_x_3461_){
_start:
{
size_t v_x_7444__boxed_3462_; lean_object* v_res_3463_; 
v_x_7444__boxed_3462_ = lean_unbox_usize(v_x_3460_);
lean_dec(v_x_3460_);
v_res_3463_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3459_, v_x_7444__boxed_3462_, v_x_3461_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(lean_object* v_x_3464_, lean_object* v_x_3465_){
_start:
{
uint64_t v___x_3466_; size_t v___x_3467_; lean_object* v___x_3468_; 
v___x_3466_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3465_);
v___x_3467_ = lean_uint64_to_usize(v___x_3466_);
lean_inc_ref(v_x_3464_);
v___x_3468_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3464_, v___x_3467_, v_x_3465_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg___boxed(lean_object* v_x_3469_, lean_object* v_x_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_3469_, v_x_3470_);
lean_dec_ref(v_x_3469_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0(lean_object* v_msg_3472_, lean_object* v_e_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v___y_3486_; lean_object* v___x_3495_; lean_object* v_share_3496_; lean_object* v___x_3497_; 
v___x_3495_ = lean_st_ref_get(v___y_3475_);
v_share_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc_ref(v_share_3496_);
lean_dec(v___x_3495_);
lean_inc_ref(v_e_3473_);
v___x_3497_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_share_3496_, v_e_3473_);
lean_dec_ref(v_share_3496_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v___x_3498_; 
v___x_3498_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3472_, v_e_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
v___y_3486_ = v___x_3498_;
goto v___jp_3485_;
}
else
{
lean_object* v_val_3499_; lean_object* v_fst_3500_; uint8_t v___x_3501_; 
v_val_3499_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_val_3499_);
lean_dec_ref(v___x_3497_);
v_fst_3500_ = lean_ctor_get(v_val_3499_, 0);
lean_inc(v_fst_3500_);
lean_dec(v_val_3499_);
v___x_3501_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_3500_, v_e_3473_);
lean_dec(v_fst_3500_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3502_; 
v___x_3502_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3472_, v_e_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
v___y_3486_ = v___x_3502_;
goto v___jp_3485_;
}
else
{
lean_dec_ref(v_e_3473_);
lean_dec_ref(v_msg_3472_);
goto v___jp_3481_;
}
}
v___jp_3481_:
{
uint8_t v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3482_ = 1;
v___x_3483_ = lean_box(v___x_3482_);
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
return v___x_3484_;
}
v___jp_3485_:
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
v_a_3487_ = lean_ctor_get(v___y_3486_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___y_3486_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___y_3486_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___y_3486_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0___boxed(lean_object* v_msg_3503_, lean_object* v_e_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_Expr_checkMaxShared___lam__0(v_msg_3503_, v_e_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
return v_res_3512_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(lean_object* v_a_3513_, lean_object* v_x_3514_){
_start:
{
if (lean_obj_tag(v_x_3514_) == 0)
{
uint8_t v___x_3515_; 
v___x_3515_ = 0;
return v___x_3515_;
}
else
{
lean_object* v_key_3516_; lean_object* v_tail_3517_; uint8_t v___x_3518_; 
v_key_3516_ = lean_ctor_get(v_x_3514_, 0);
v_tail_3517_ = lean_ctor_get(v_x_3514_, 2);
v___x_3518_ = lean_expr_eqv(v_key_3516_, v_a_3513_);
if (v___x_3518_ == 0)
{
v_x_3514_ = v_tail_3517_;
goto _start;
}
else
{
return v___x_3518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_a_3520_, lean_object* v_x_3521_){
_start:
{
uint8_t v_res_3522_; lean_object* v_r_3523_; 
v_res_3522_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3520_, v_x_3521_);
lean_dec(v_x_3521_);
lean_dec_ref(v_a_3520_);
v_r_3523_ = lean_box(v_res_3522_);
return v_r_3523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(lean_object* v_a_3524_, lean_object* v_b_3525_, lean_object* v_x_3526_){
_start:
{
if (lean_obj_tag(v_x_3526_) == 0)
{
lean_dec(v_b_3525_);
lean_dec_ref(v_a_3524_);
return v_x_3526_;
}
else
{
lean_object* v_key_3527_; lean_object* v_value_3528_; lean_object* v_tail_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3541_; 
v_key_3527_ = lean_ctor_get(v_x_3526_, 0);
v_value_3528_ = lean_ctor_get(v_x_3526_, 1);
v_tail_3529_ = lean_ctor_get(v_x_3526_, 2);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_x_3526_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3531_ = v_x_3526_;
v_isShared_3532_ = v_isSharedCheck_3541_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_tail_3529_);
lean_inc(v_value_3528_);
lean_inc(v_key_3527_);
lean_dec(v_x_3526_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3541_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
uint8_t v___x_3533_; 
v___x_3533_ = lean_expr_eqv(v_key_3527_, v_a_3524_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3534_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3524_, v_b_3525_, v_tail_3529_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 2, v___x_3534_);
v___x_3536_ = v___x_3531_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_key_3527_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_value_3528_);
lean_ctor_set(v_reuseFailAlloc_3537_, 2, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
else
{
lean_object* v___x_3539_; 
lean_dec(v_value_3528_);
lean_dec(v_key_3527_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 1, v_b_3525_);
lean_ctor_set(v___x_3531_, 0, v_a_3524_);
v___x_3539_ = v___x_3531_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3524_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_b_3525_);
lean_ctor_set(v_reuseFailAlloc_3540_, 2, v_tail_3529_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(lean_object* v_x_3542_, lean_object* v_x_3543_){
_start:
{
if (lean_obj_tag(v_x_3543_) == 0)
{
return v_x_3542_;
}
else
{
lean_object* v_key_3544_; lean_object* v_value_3545_; lean_object* v_tail_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3569_; 
v_key_3544_ = lean_ctor_get(v_x_3543_, 0);
v_value_3545_ = lean_ctor_get(v_x_3543_, 1);
v_tail_3546_ = lean_ctor_get(v_x_3543_, 2);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_x_3543_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3548_ = v_x_3543_;
v_isShared_3549_ = v_isSharedCheck_3569_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_tail_3546_);
lean_inc(v_value_3545_);
lean_inc(v_key_3544_);
lean_dec(v_x_3543_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3569_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3550_; uint64_t v___x_3551_; uint64_t v___x_3552_; uint64_t v___x_3553_; uint64_t v_fold_3554_; uint64_t v___x_3555_; uint64_t v___x_3556_; uint64_t v___x_3557_; size_t v___x_3558_; size_t v___x_3559_; size_t v___x_3560_; size_t v___x_3561_; size_t v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3565_; 
v___x_3550_ = lean_array_get_size(v_x_3542_);
v___x_3551_ = l_Lean_Expr_hash(v_key_3544_);
v___x_3552_ = 32ULL;
v___x_3553_ = lean_uint64_shift_right(v___x_3551_, v___x_3552_);
v_fold_3554_ = lean_uint64_xor(v___x_3551_, v___x_3553_);
v___x_3555_ = 16ULL;
v___x_3556_ = lean_uint64_shift_right(v_fold_3554_, v___x_3555_);
v___x_3557_ = lean_uint64_xor(v_fold_3554_, v___x_3556_);
v___x_3558_ = lean_uint64_to_usize(v___x_3557_);
v___x_3559_ = lean_usize_of_nat(v___x_3550_);
v___x_3560_ = ((size_t)1ULL);
v___x_3561_ = lean_usize_sub(v___x_3559_, v___x_3560_);
v___x_3562_ = lean_usize_land(v___x_3558_, v___x_3561_);
v___x_3563_ = lean_array_uget_borrowed(v_x_3542_, v___x_3562_);
lean_inc(v___x_3563_);
if (v_isShared_3549_ == 0)
{
lean_ctor_set(v___x_3548_, 2, v___x_3563_);
v___x_3565_ = v___x_3548_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_key_3544_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_value_3545_);
lean_ctor_set(v_reuseFailAlloc_3568_, 2, v___x_3563_);
v___x_3565_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_array_uset(v_x_3542_, v___x_3562_, v___x_3565_);
v_x_3542_ = v___x_3566_;
v_x_3543_ = v_tail_3546_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(lean_object* v_i_3570_, lean_object* v_source_3571_, lean_object* v_target_3572_){
_start:
{
lean_object* v___x_3573_; uint8_t v___x_3574_; 
v___x_3573_ = lean_array_get_size(v_source_3571_);
v___x_3574_ = lean_nat_dec_lt(v_i_3570_, v___x_3573_);
if (v___x_3574_ == 0)
{
lean_dec_ref(v_source_3571_);
lean_dec(v_i_3570_);
return v_target_3572_;
}
else
{
lean_object* v_es_3575_; lean_object* v___x_3576_; lean_object* v_source_3577_; lean_object* v_target_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v_es_3575_ = lean_array_fget(v_source_3571_, v_i_3570_);
v___x_3576_ = lean_box(0);
v_source_3577_ = lean_array_fset(v_source_3571_, v_i_3570_, v___x_3576_);
v_target_3578_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_target_3572_, v_es_3575_);
v___x_3579_ = lean_unsigned_to_nat(1u);
v___x_3580_ = lean_nat_add(v_i_3570_, v___x_3579_);
lean_dec(v_i_3570_);
v_i_3570_ = v___x_3580_;
v_source_3571_ = v_source_3577_;
v_target_3572_ = v_target_3578_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(lean_object* v_data_3582_){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v_nbuckets_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3583_ = lean_array_get_size(v_data_3582_);
v___x_3584_ = lean_unsigned_to_nat(2u);
v_nbuckets_3585_ = lean_nat_mul(v___x_3583_, v___x_3584_);
v___x_3586_ = lean_unsigned_to_nat(0u);
v___x_3587_ = lean_box(0);
v___x_3588_ = lean_mk_array(v_nbuckets_3585_, v___x_3587_);
v___x_3589_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v___x_3586_, v_data_3582_, v___x_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(lean_object* v_m_3590_, lean_object* v_a_3591_, lean_object* v_b_3592_){
_start:
{
lean_object* v_size_3593_; lean_object* v_buckets_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3637_; 
v_size_3593_ = lean_ctor_get(v_m_3590_, 0);
v_buckets_3594_ = lean_ctor_get(v_m_3590_, 1);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_m_3590_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3596_ = v_m_3590_;
v_isShared_3597_ = v_isSharedCheck_3637_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_buckets_3594_);
lean_inc(v_size_3593_);
lean_dec(v_m_3590_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3637_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3598_; uint64_t v___x_3599_; uint64_t v___x_3600_; uint64_t v___x_3601_; uint64_t v_fold_3602_; uint64_t v___x_3603_; uint64_t v___x_3604_; uint64_t v___x_3605_; size_t v___x_3606_; size_t v___x_3607_; size_t v___x_3608_; size_t v___x_3609_; size_t v___x_3610_; lean_object* v_bkt_3611_; uint8_t v___x_3612_; 
v___x_3598_ = lean_array_get_size(v_buckets_3594_);
v___x_3599_ = l_Lean_Expr_hash(v_a_3591_);
v___x_3600_ = 32ULL;
v___x_3601_ = lean_uint64_shift_right(v___x_3599_, v___x_3600_);
v_fold_3602_ = lean_uint64_xor(v___x_3599_, v___x_3601_);
v___x_3603_ = 16ULL;
v___x_3604_ = lean_uint64_shift_right(v_fold_3602_, v___x_3603_);
v___x_3605_ = lean_uint64_xor(v_fold_3602_, v___x_3604_);
v___x_3606_ = lean_uint64_to_usize(v___x_3605_);
v___x_3607_ = lean_usize_of_nat(v___x_3598_);
v___x_3608_ = ((size_t)1ULL);
v___x_3609_ = lean_usize_sub(v___x_3607_, v___x_3608_);
v___x_3610_ = lean_usize_land(v___x_3606_, v___x_3609_);
v_bkt_3611_ = lean_array_uget_borrowed(v_buckets_3594_, v___x_3610_);
v___x_3612_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3591_, v_bkt_3611_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; lean_object* v_size_x27_3614_; lean_object* v___x_3615_; lean_object* v_buckets_x27_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; uint8_t v___x_3622_; 
v___x_3613_ = lean_unsigned_to_nat(1u);
v_size_x27_3614_ = lean_nat_add(v_size_3593_, v___x_3613_);
lean_dec(v_size_3593_);
lean_inc(v_bkt_3611_);
v___x_3615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3615_, 0, v_a_3591_);
lean_ctor_set(v___x_3615_, 1, v_b_3592_);
lean_ctor_set(v___x_3615_, 2, v_bkt_3611_);
v_buckets_x27_3616_ = lean_array_uset(v_buckets_3594_, v___x_3610_, v___x_3615_);
v___x_3617_ = lean_unsigned_to_nat(4u);
v___x_3618_ = lean_nat_mul(v_size_x27_3614_, v___x_3617_);
v___x_3619_ = lean_unsigned_to_nat(3u);
v___x_3620_ = lean_nat_div(v___x_3618_, v___x_3619_);
lean_dec(v___x_3618_);
v___x_3621_ = lean_array_get_size(v_buckets_x27_3616_);
v___x_3622_ = lean_nat_dec_le(v___x_3620_, v___x_3621_);
lean_dec(v___x_3620_);
if (v___x_3622_ == 0)
{
lean_object* v_val_3623_; lean_object* v___x_3625_; 
v_val_3623_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_buckets_x27_3616_);
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 1, v_val_3623_);
lean_ctor_set(v___x_3596_, 0, v_size_x27_3614_);
v___x_3625_ = v___x_3596_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_size_x27_3614_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_val_3623_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
else
{
lean_object* v___x_3628_; 
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 1, v_buckets_x27_3616_);
lean_ctor_set(v___x_3596_, 0, v_size_x27_3614_);
v___x_3628_ = v___x_3596_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_size_x27_3614_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v_buckets_x27_3616_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
else
{
lean_object* v___x_3630_; lean_object* v_buckets_x27_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3635_; 
lean_inc(v_bkt_3611_);
v___x_3630_ = lean_box(0);
v_buckets_x27_3631_ = lean_array_uset(v_buckets_3594_, v___x_3610_, v___x_3630_);
v___x_3632_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3591_, v_b_3592_, v_bkt_3611_);
v___x_3633_ = lean_array_uset(v_buckets_x27_3631_, v___x_3610_, v___x_3632_);
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 1, v___x_3633_);
v___x_3635_ = v___x_3596_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_size_3593_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(lean_object* v_a_3638_, lean_object* v_x_3639_){
_start:
{
if (lean_obj_tag(v_x_3639_) == 0)
{
lean_object* v___x_3640_; 
v___x_3640_ = lean_box(0);
return v___x_3640_;
}
else
{
lean_object* v_key_3641_; lean_object* v_value_3642_; lean_object* v_tail_3643_; uint8_t v___x_3644_; 
v_key_3641_ = lean_ctor_get(v_x_3639_, 0);
v_value_3642_ = lean_ctor_get(v_x_3639_, 1);
v_tail_3643_ = lean_ctor_get(v_x_3639_, 2);
v___x_3644_ = lean_expr_eqv(v_key_3641_, v_a_3638_);
if (v___x_3644_ == 0)
{
v_x_3639_ = v_tail_3643_;
goto _start;
}
else
{
lean_object* v___x_3646_; 
lean_inc(v_value_3642_);
v___x_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3646_, 0, v_value_3642_);
return v___x_3646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_3647_, lean_object* v_x_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3647_, v_x_3648_);
lean_dec(v_x_3648_);
lean_dec_ref(v_a_3647_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(lean_object* v_m_3650_, lean_object* v_a_3651_){
_start:
{
lean_object* v_buckets_3652_; lean_object* v___x_3653_; uint64_t v___x_3654_; uint64_t v___x_3655_; uint64_t v___x_3656_; uint64_t v_fold_3657_; uint64_t v___x_3658_; uint64_t v___x_3659_; uint64_t v___x_3660_; size_t v___x_3661_; size_t v___x_3662_; size_t v___x_3663_; size_t v___x_3664_; size_t v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v_buckets_3652_ = lean_ctor_get(v_m_3650_, 1);
v___x_3653_ = lean_array_get_size(v_buckets_3652_);
v___x_3654_ = l_Lean_Expr_hash(v_a_3651_);
v___x_3655_ = 32ULL;
v___x_3656_ = lean_uint64_shift_right(v___x_3654_, v___x_3655_);
v_fold_3657_ = lean_uint64_xor(v___x_3654_, v___x_3656_);
v___x_3658_ = 16ULL;
v___x_3659_ = lean_uint64_shift_right(v_fold_3657_, v___x_3658_);
v___x_3660_ = lean_uint64_xor(v_fold_3657_, v___x_3659_);
v___x_3661_ = lean_uint64_to_usize(v___x_3660_);
v___x_3662_ = lean_usize_of_nat(v___x_3653_);
v___x_3663_ = ((size_t)1ULL);
v___x_3664_ = lean_usize_sub(v___x_3662_, v___x_3663_);
v___x_3665_ = lean_usize_land(v___x_3661_, v___x_3664_);
v___x_3666_ = lean_array_uget_borrowed(v_buckets_3652_, v___x_3665_);
v___x_3667_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3651_, v___x_3666_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg___boxed(lean_object* v_m_3668_, lean_object* v_a_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_3668_, v_a_3669_);
lean_dec_ref(v_a_3669_);
lean_dec_ref(v_m_3668_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(lean_object* v_g_3671_, lean_object* v_e_3672_, lean_object* v_a_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v_a_3682_; lean_object* v___y_3688_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3690_ = lean_st_ref_get(v_a_3673_);
v___x_3691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v___x_3690_, v_e_3672_);
lean_dec(v___x_3690_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v___x_3692_; 
lean_inc_ref(v_g_3671_);
lean_inc(v___y_3679_);
lean_inc_ref(v___y_3678_);
lean_inc(v___y_3677_);
lean_inc_ref(v___y_3676_);
lean_inc(v___y_3675_);
lean_inc_ref(v___y_3674_);
lean_inc_ref(v_e_3672_);
v___x_3692_ = lean_apply_8(v_g_3671_, v_e_3672_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, lean_box(0));
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v_d_3695_; lean_object* v_b_3696_; lean_object* v___y_3697_; uint8_t v___x_3700_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref(v___x_3692_);
v___x_3700_ = lean_unbox(v_a_3693_);
lean_dec(v_a_3693_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; 
lean_dec_ref(v_g_3671_);
v___x_3701_ = lean_box(0);
v_a_3682_ = v___x_3701_;
goto v___jp_3681_;
}
else
{
switch(lean_obj_tag(v_e_3672_))
{
case 7:
{
lean_object* v_binderType_3702_; lean_object* v_body_3703_; 
v_binderType_3702_ = lean_ctor_get(v_e_3672_, 1);
v_body_3703_ = lean_ctor_get(v_e_3672_, 2);
lean_inc_ref(v_body_3703_);
lean_inc_ref(v_binderType_3702_);
v_d_3695_ = v_binderType_3702_;
v_b_3696_ = v_body_3703_;
v___y_3697_ = v_a_3673_;
goto v___jp_3694_;
}
case 6:
{
lean_object* v_binderType_3704_; lean_object* v_body_3705_; 
v_binderType_3704_ = lean_ctor_get(v_e_3672_, 1);
v_body_3705_ = lean_ctor_get(v_e_3672_, 2);
lean_inc_ref(v_body_3705_);
lean_inc_ref(v_binderType_3704_);
v_d_3695_ = v_binderType_3704_;
v_b_3696_ = v_body_3705_;
v___y_3697_ = v_a_3673_;
goto v___jp_3694_;
}
case 8:
{
lean_object* v_type_3706_; lean_object* v_value_3707_; lean_object* v_body_3708_; lean_object* v___x_3709_; 
v_type_3706_ = lean_ctor_get(v_e_3672_, 1);
v_value_3707_ = lean_ctor_get(v_e_3672_, 2);
v_body_3708_ = lean_ctor_get(v_e_3672_, 3);
lean_inc_ref(v_type_3706_);
lean_inc_ref(v_g_3671_);
v___x_3709_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3671_, v_type_3706_, v_a_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v___x_3710_; 
lean_dec_ref(v___x_3709_);
lean_inc_ref(v_value_3707_);
lean_inc_ref(v_g_3671_);
v___x_3710_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3671_, v_value_3707_, v_a_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v___x_3711_; 
lean_dec_ref(v___x_3710_);
lean_inc_ref(v_body_3708_);
v___x_3711_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3671_, v_body_3708_, v_a_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
v___y_3688_ = v___x_3711_;
goto v___jp_3687_;
}
else
{
lean_dec_ref(v_g_3671_);
v___y_3688_ = v___x_3710_;
goto v___jp_3687_;
}
}
else
{
lean_dec_ref(v_g_3671_);
v___y_3688_ = v___x_3709_;
goto v___jp_3687_;
}
}
case 5:
{
lean_object* v_fn_3712_; lean_object* v_arg_3713_; lean_object* v___x_3714_; 
v_fn_3712_ = lean_ctor_get(v_e_3672_, 0);
v_arg_3713_ = lean_ctor_get(v_e_3672_, 1);
lean_inc_ref(v_fn_3712_);
lean_inc_ref(v_g_3671_);
v___x_3714_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3671_, v_fn_3712_, v_a_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v___x_3715_; 
lean_dec_ref(v___x_3714_);
lean_inc_ref(v_arg_3713_);
v___x_3715_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3671_, v_arg_3713_, v_a_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
v___y_3688_ = v___x_3715_;
goto v___jp_3687_;
}
else
{
lean_dec_ref(v_g_3671_);
v___y_3688_ = v___x_3714_;
goto v___jp_3687_;
}
}
case 10:
{
lean_object* v_expr_3716_; lean_object* v___x_3717_; 
v_expr_3716_ = lean_ctor_get(v_e_3672_, 1);
lean_inc_ref(v_expr_3716_);
v___x_3717_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3671_, v_expr_3716_, v_a_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
v___y_3688_ = v___x_3717_;
goto v___jp_3687_;
}
case 11:
{
lean_object* v_struct_3718_; lean_object* v___x_3719_; 
v_struct_3718_ = lean_ctor_get(v_e_3672_, 2);
lean_inc_ref(v_struct_3718_);
v___x_3719_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3671_, v_struct_3718_, v_a_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
v___y_3688_ = v___x_3719_;
goto v___jp_3687_;
}
default: 
{
lean_object* v___x_3720_; 
lean_dec_ref(v_g_3671_);
v___x_3720_ = lean_box(0);
v_a_3682_ = v___x_3720_;
goto v___jp_3681_;
}
}
}
v___jp_3694_:
{
lean_object* v___x_3698_; 
lean_inc_ref(v_g_3671_);
v___x_3698_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3671_, v_d_3695_, v___y_3697_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v___x_3699_; 
lean_dec_ref(v___x_3698_);
v___x_3699_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3671_, v_b_3696_, v___y_3697_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
v___y_3688_ = v___x_3699_;
goto v___jp_3687_;
}
else
{
lean_dec_ref(v_b_3696_);
lean_dec_ref(v_g_3671_);
v___y_3688_ = v___x_3698_;
goto v___jp_3687_;
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_dec_ref(v_e_3672_);
lean_dec_ref(v_g_3671_);
v_a_3721_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3692_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3692_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
else
{
lean_object* v_val_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_dec_ref(v_e_3672_);
lean_dec_ref(v_g_3671_);
v_val_3729_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3691_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_val_3729_);
lean_dec(v___x_3691_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
lean_ctor_set_tag(v___x_3731_, 0);
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_val_3729_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
v___jp_3681_:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3683_ = lean_st_ref_take(v_a_3673_);
v___x_3684_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v___x_3683_, v_e_3672_, v_a_3682_);
v___x_3685_ = lean_st_ref_set(v_a_3673_, v___x_3684_);
v___x_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3686_, 0, v_a_3682_);
return v___x_3686_;
}
v___jp_3687_:
{
if (lean_obj_tag(v___y_3688_) == 0)
{
lean_object* v_a_3689_; 
v_a_3689_ = lean_ctor_get(v___y_3688_, 0);
lean_inc(v_a_3689_);
lean_dec_ref(v___y_3688_);
v_a_3682_ = v_a_3689_;
goto v___jp_3681_;
}
else
{
lean_dec_ref(v_e_3672_);
return v___y_3688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1___boxed(lean_object* v_g_3737_, lean_object* v_e_3738_, lean_object* v_a_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3737_, v_e_3738_, v_a_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v_a_3739_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared(lean_object* v_e_3748_, lean_object* v_msg_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_){
_start:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___f_3759_; lean_object* v___x_3760_; 
v___x_3757_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_3758_ = lean_st_mk_ref(v___x_3757_);
v___f_3759_ = lean_alloc_closure((void*)(l_Lean_Expr_checkMaxShared___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3759_, 0, v_msg_3749_);
v___x_3760_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v___f_3759_, v_e_3748_, v___x_3758_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_, v_a_3755_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3769_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3769_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3769_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3765_; lean_object* v___x_3767_; 
v___x_3765_ = lean_st_ref_get(v___x_3758_);
lean_dec(v___x_3758_);
lean_dec(v___x_3765_);
if (v_isShared_3764_ == 0)
{
v___x_3767_ = v___x_3763_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3761_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
else
{
lean_dec(v___x_3758_);
return v___x_3760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___boxed(lean_object* v_e_3770_, lean_object* v_msg_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l_Lean_Expr_checkMaxShared(v_e_3770_, v_msg_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
lean_dec(v_a_3777_);
lean_dec_ref(v_a_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(lean_object* v_00_u03b2_3780_, lean_object* v_x_3781_, lean_object* v_x_3782_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_3781_, v_x_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___boxed(lean_object* v_00_u03b2_3784_, lean_object* v_x_3785_, lean_object* v_x_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(v_00_u03b2_3784_, v_x_3785_, v_x_3786_);
lean_dec_ref(v_x_3785_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(lean_object* v_00_u03b2_3788_, lean_object* v_x_3789_, size_t v_x_3790_, lean_object* v_x_3791_){
_start:
{
lean_object* v___x_3792_; 
lean_inc_ref(v_x_3789_);
v___x_3792_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3789_, v_x_3790_, v_x_3791_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3793_, lean_object* v_x_3794_, lean_object* v_x_3795_, lean_object* v_x_3796_){
_start:
{
size_t v_x_8019__boxed_3797_; lean_object* v_res_3798_; 
v_x_8019__boxed_3797_ = lean_unbox_usize(v_x_3795_);
lean_dec(v_x_3795_);
v_res_3798_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(v_00_u03b2_3793_, v_x_3794_, v_x_8019__boxed_3797_, v_x_3796_);
lean_dec_ref(v_x_3794_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(lean_object* v_00_u03b2_3799_, lean_object* v_m_3800_, lean_object* v_a_3801_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_3800_, v_a_3801_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3803_, lean_object* v_m_3804_, lean_object* v_a_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(v_00_u03b2_3803_, v_m_3804_, v_a_3805_);
lean_dec_ref(v_a_3805_);
lean_dec_ref(v_m_3804_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(lean_object* v_00_u03b2_3807_, lean_object* v_m_3808_, lean_object* v_a_3809_, lean_object* v_b_3810_){
_start:
{
lean_object* v___x_3811_; 
v___x_3811_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v_m_3808_, v_a_3809_, v_b_3810_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3812_, lean_object* v_keys_3813_, lean_object* v_vals_3814_, lean_object* v_heq_3815_, lean_object* v_i_3816_, lean_object* v_k_3817_){
_start:
{
lean_object* v___x_3818_; 
v___x_3818_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_3813_, v_vals_3814_, v_i_3816_, v_k_3817_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3819_, lean_object* v_keys_3820_, lean_object* v_vals_3821_, lean_object* v_heq_3822_, lean_object* v_i_3823_, lean_object* v_k_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(v_00_u03b2_3819_, v_keys_3820_, v_vals_3821_, v_heq_3822_, v_i_3823_, v_k_3824_);
lean_dec_ref(v_vals_3821_);
lean_dec_ref(v_keys_3820_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3826_, lean_object* v_a_3827_, lean_object* v_x_3828_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3827_, v_x_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_3830_, lean_object* v_a_3831_, lean_object* v_x_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(v_00_u03b2_3830_, v_a_3831_, v_x_3832_);
lean_dec(v_x_3832_);
lean_dec_ref(v_a_3831_);
return v_res_3833_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_3834_, lean_object* v_a_3835_, lean_object* v_x_3836_){
_start:
{
uint8_t v___x_3837_; 
v___x_3837_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3835_, v_x_3836_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3838_, lean_object* v_a_3839_, lean_object* v_x_3840_){
_start:
{
uint8_t v_res_3841_; lean_object* v_r_3842_; 
v_res_3841_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(v_00_u03b2_3838_, v_a_3839_, v_x_3840_);
lean_dec(v_x_3840_);
lean_dec_ref(v_a_3839_);
v_r_3842_ = lean_box(v_res_3841_);
return v_r_3842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3843_, lean_object* v_data_3844_){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_data_3844_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_3846_, lean_object* v_a_3847_, lean_object* v_b_3848_, lean_object* v_x_3849_){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3847_, v_b_3848_, v_x_3849_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_3851_, lean_object* v_i_3852_, lean_object* v_source_3853_, lean_object* v_target_3854_){
_start:
{
lean_object* v___x_3855_; 
v___x_3855_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v_i_3852_, v_source_3853_, v_target_3854_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9(lean_object* v_00_u03b2_3856_, lean_object* v_x_3857_, lean_object* v_x_3858_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_x_3857_, v_x_3858_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared(lean_object* v_mvarId_3860_, lean_object* v_msg_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_){
_start:
{
lean_object* v___x_3869_; 
v___x_3869_ = l_Lean_MVarId_getDecl(v_mvarId_3860_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v_type_3871_; lean_object* v___x_3872_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref(v___x_3869_);
v_type_3871_ = lean_ctor_get(v_a_3870_, 2);
lean_inc_ref(v_type_3871_);
lean_dec(v_a_3870_);
v___x_3872_ = l_Lean_Expr_checkMaxShared(v_type_3871_, v_msg_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_);
return v___x_3872_;
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec_ref(v_msg_3861_);
v_a_3873_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3869_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3869_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared___boxed(lean_object* v_mvarId_3881_, lean_object* v_msg_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_MVarId_checkMaxShared(v_mvarId_3881_, v_msg_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_a_3886_);
lean_dec_ref(v_a_3885_);
lean_dec(v_a_3884_);
lean_dec_ref(v_a_3883_);
return v_res_3890_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(lean_object* v_x_3891_){
_start:
{
if (lean_obj_tag(v_x_3891_) == 0)
{
uint8_t v___x_3892_; 
v___x_3892_ = 0;
return v___x_3892_;
}
else
{
lean_object* v_head_3893_; lean_object* v_tail_3894_; uint8_t v___x_3895_; 
v_head_3893_ = lean_ctor_get(v_x_3891_, 0);
v_tail_3894_ = lean_ctor_get(v_x_3891_, 1);
v___x_3895_ = l_Lean_Level_isAlreadyNormalizedCheap(v_head_3893_);
if (v___x_3895_ == 0)
{
uint8_t v___x_3896_; 
v___x_3896_ = 1;
return v___x_3896_;
}
else
{
v_x_3891_ = v_tail_3894_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0___boxed(lean_object* v_x_3898_){
_start:
{
uint8_t v_res_3899_; lean_object* v_r_3900_; 
v_res_3899_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_x_3898_);
lean_dec(v_x_3898_);
v_r_3900_ = lean_box(v_res_3899_);
return v_r_3900_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(lean_object* v_x_3901_){
_start:
{
switch(lean_obj_tag(v_x_3901_))
{
case 4:
{
lean_object* v_us_3902_; uint8_t v___x_3903_; 
v_us_3902_ = lean_ctor_get(v_x_3901_, 1);
v___x_3903_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_us_3902_);
return v___x_3903_;
}
case 3:
{
lean_object* v_u_3904_; uint8_t v___x_3905_; 
v_u_3904_ = lean_ctor_get(v_x_3901_, 0);
v___x_3905_ = l_Lean_Level_isAlreadyNormalizedCheap(v_u_3904_);
if (v___x_3905_ == 0)
{
uint8_t v___x_3906_; 
v___x_3906_ = 1;
return v___x_3906_;
}
else
{
uint8_t v___x_3907_; 
v___x_3907_ = 0;
return v___x_3907_;
}
}
default: 
{
uint8_t v___x_3908_; 
v___x_3908_ = 0;
return v___x_3908_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed(lean_object* v_x_3909_){
_start:
{
uint8_t v_res_3910_; lean_object* v_r_3911_; 
v_res_3910_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(v_x_3909_);
lean_dec_ref(v_x_3909_);
v_r_3911_ = lean_box(v_res_3910_);
return v_r_3911_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(lean_object* v_e_3913_){
_start:
{
lean_object* v___f_3914_; lean_object* v___x_3915_; 
v___f_3914_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0));
v___x_3915_ = lean_find_expr(v___f_3914_, v_e_3913_);
if (lean_obj_tag(v___x_3915_) == 0)
{
uint8_t v___x_3916_; 
v___x_3916_ = 1;
return v___x_3916_;
}
else
{
uint8_t v___x_3917_; 
lean_dec_ref(v___x_3915_);
v___x_3917_ = 0;
return v___x_3917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___boxed(lean_object* v_e_3918_){
_start:
{
uint8_t v_res_3919_; lean_object* v_r_3920_; 
v_res_3919_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_3918_);
lean_dec_ref(v_e_3918_);
v_r_3920_ = lean_box(v_res_3919_);
return v_r_3920_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
if (lean_obj_tag(v_a_3921_) == 0)
{
lean_object* v___x_3923_; 
v___x_3923_ = l_List_reverse___redArg(v_a_3922_);
return v___x_3923_;
}
else
{
lean_object* v_head_3924_; lean_object* v_tail_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3934_; 
v_head_3924_ = lean_ctor_get(v_a_3921_, 0);
v_tail_3925_ = lean_ctor_get(v_a_3921_, 1);
v_isSharedCheck_3934_ = !lean_is_exclusive(v_a_3921_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3927_ = v_a_3921_;
v_isShared_3928_ = v_isSharedCheck_3934_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_tail_3925_);
lean_inc(v_head_3924_);
lean_dec(v_a_3921_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3934_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v___x_3931_; 
v___x_3929_ = l_Lean_Level_normalize(v_head_3924_);
lean_dec(v_head_3924_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 1, v_a_3922_);
lean_ctor_set(v___x_3927_, 0, v___x_3929_);
v___x_3931_ = v___x_3927_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3929_);
lean_ctor_set(v_reuseFailAlloc_3933_, 1, v_a_3922_);
v___x_3931_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
v_a_3921_ = v_tail_3925_;
v_a_3922_ = v___x_3931_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0(lean_object* v_e_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
lean_object* v___y_3940_; lean_object* v___y_3944_; 
switch(lean_obj_tag(v_e_3935_))
{
case 3:
{
lean_object* v_u_3947_; lean_object* v___x_3948_; size_t v___x_3949_; size_t v___x_3950_; uint8_t v___x_3951_; 
v_u_3947_ = lean_ctor_get(v_e_3935_, 0);
v___x_3948_ = l_Lean_Level_normalize(v_u_3947_);
v___x_3949_ = lean_ptr_addr(v_u_3947_);
v___x_3950_ = lean_ptr_addr(v___x_3948_);
v___x_3951_ = lean_usize_dec_eq(v___x_3949_, v___x_3950_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3952_; 
lean_dec_ref(v_e_3935_);
v___x_3952_ = l_Lean_Expr_sort___override(v___x_3948_);
v___y_3940_ = v___x_3952_;
goto v___jp_3939_;
}
else
{
lean_dec(v___x_3948_);
v___y_3940_ = v_e_3935_;
goto v___jp_3939_;
}
}
case 4:
{
lean_object* v_declName_3953_; lean_object* v_us_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; uint8_t v___x_3957_; 
v_declName_3953_ = lean_ctor_get(v_e_3935_, 0);
v_us_3954_ = lean_ctor_get(v_e_3935_, 1);
v___x_3955_ = lean_box(0);
lean_inc(v_us_3954_);
v___x_3956_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(v_us_3954_, v___x_3955_);
v___x_3957_ = l_ptrEqList___redArg(v_us_3954_, v___x_3956_);
if (v___x_3957_ == 0)
{
lean_object* v___x_3958_; 
lean_inc(v_declName_3953_);
lean_dec_ref(v_e_3935_);
v___x_3958_ = l_Lean_Expr_const___override(v_declName_3953_, v___x_3956_);
v___y_3944_ = v___x_3958_;
goto v___jp_3943_;
}
else
{
lean_dec(v___x_3956_);
v___y_3944_ = v_e_3935_;
goto v___jp_3943_;
}
}
default: 
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
lean_dec_ref(v_e_3935_);
v___x_3959_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
return v___x_3960_;
}
}
v___jp_3939_:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3941_, 0, v___y_3940_);
v___x_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3941_);
return v___x_3942_;
}
v___jp_3943_:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3945_, 0, v___y_3944_);
v___x_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
return v___x_3946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed(lean_object* v_e_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l_Lean_Meta_Sym_normalizeLevels___lam__0(v_e_3961_, v___y_3962_, v___y_3963_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1(lean_object* v_e_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3970_, 0, v_e_3966_);
v___x_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed(lean_object* v_e_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lean_Meta_Sym_normalizeLevels___lam__1(v_e_3972_, v___y_3973_, v___y_3974_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_ref_3977_){
_start:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3979_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3980_, 0, v_ref_3977_);
lean_ctor_set(v___x_3980_, 1, v___x_3979_);
v___x_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3980_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_ref_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_3982_);
return v_res_3984_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3985_ = lean_box(0);
v___x_3986_ = l_Lean_interruptExceptionId;
v___x_3987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
lean_ctor_set(v___x_3987_, 1, v___x_3985_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg(){
_start:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3989_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0);
v___x_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v___y_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(lean_object* v_x_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v___y_3999_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; uint8_t v___y_4023_; uint8_t v___y_4024_; lean_object* v_fileName_4029_; lean_object* v_fileMap_4030_; lean_object* v_options_4031_; lean_object* v_currRecDepth_4032_; lean_object* v_maxRecDepth_4033_; lean_object* v_ref_4034_; lean_object* v_currNamespace_4035_; lean_object* v_openDecls_4036_; lean_object* v_initHeartbeats_4037_; lean_object* v_maxHeartbeats_4038_; lean_object* v_quotContext_4039_; lean_object* v_currMacroScope_4040_; uint8_t v_diag_4041_; lean_object* v_cancelTk_x3f_4042_; uint8_t v_suppressElabErrors_4043_; lean_object* v_inheritedTraceOptions_4044_; 
v_fileName_4029_ = lean_ctor_get(v___y_3995_, 0);
v_fileMap_4030_ = lean_ctor_get(v___y_3995_, 1);
v_options_4031_ = lean_ctor_get(v___y_3995_, 2);
v_currRecDepth_4032_ = lean_ctor_get(v___y_3995_, 3);
v_maxRecDepth_4033_ = lean_ctor_get(v___y_3995_, 4);
v_ref_4034_ = lean_ctor_get(v___y_3995_, 5);
v_currNamespace_4035_ = lean_ctor_get(v___y_3995_, 6);
v_openDecls_4036_ = lean_ctor_get(v___y_3995_, 7);
v_initHeartbeats_4037_ = lean_ctor_get(v___y_3995_, 8);
v_maxHeartbeats_4038_ = lean_ctor_get(v___y_3995_, 9);
v_quotContext_4039_ = lean_ctor_get(v___y_3995_, 10);
v_currMacroScope_4040_ = lean_ctor_get(v___y_3995_, 11);
v_diag_4041_ = lean_ctor_get_uint8(v___y_3995_, sizeof(void*)*14);
v_cancelTk_x3f_4042_ = lean_ctor_get(v___y_3995_, 12);
v_suppressElabErrors_4043_ = lean_ctor_get_uint8(v___y_3995_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4044_ = lean_ctor_get(v___y_3995_, 13);
if (lean_obj_tag(v_cancelTk_x3f_4042_) == 1)
{
lean_object* v_val_4050_; uint8_t v___x_4051_; 
v_val_4050_ = lean_ctor_get(v_cancelTk_x3f_4042_, 0);
v___x_4051_ = l_IO_CancelToken_isSet(v_val_4050_);
if (v___x_4051_ == 0)
{
goto v___jp_4045_;
}
else
{
lean_object* v___x_4052_; lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
lean_dec_ref(v_x_3993_);
v___x_4052_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_4052_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4052_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
else
{
goto v___jp_4045_;
}
v___jp_3998_:
{
if (lean_obj_tag(v___y_3999_) == 0)
{
return v___y_3999_;
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
v_a_4000_ = lean_ctor_get(v___y_3999_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___y_3999_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___y_3999_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___y_3999_);
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
v___jp_4008_:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4025_ = lean_unsigned_to_nat(1u);
v___x_4026_ = lean_nat_add(v___y_4016_, v___x_4025_);
lean_inc_ref(v___y_4022_);
lean_inc(v___y_4011_);
lean_inc(v___y_4020_);
lean_inc(v___y_4012_);
lean_inc(v___y_4013_);
lean_inc(v___y_4009_);
lean_inc(v___y_4021_);
lean_inc(v___y_4019_);
lean_inc(v___y_4017_);
lean_inc_ref(v___y_4010_);
lean_inc_ref(v___y_4015_);
lean_inc_ref(v___y_4014_);
v___x_4027_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4027_, 0, v___y_4014_);
lean_ctor_set(v___x_4027_, 1, v___y_4015_);
lean_ctor_set(v___x_4027_, 2, v___y_4010_);
lean_ctor_set(v___x_4027_, 3, v___x_4026_);
lean_ctor_set(v___x_4027_, 4, v___y_4017_);
lean_ctor_set(v___x_4027_, 5, v___y_4018_);
lean_ctor_set(v___x_4027_, 6, v___y_4019_);
lean_ctor_set(v___x_4027_, 7, v___y_4021_);
lean_ctor_set(v___x_4027_, 8, v___y_4009_);
lean_ctor_set(v___x_4027_, 9, v___y_4013_);
lean_ctor_set(v___x_4027_, 10, v___y_4012_);
lean_ctor_set(v___x_4027_, 11, v___y_4020_);
lean_ctor_set(v___x_4027_, 12, v___y_4011_);
lean_ctor_set(v___x_4027_, 13, v___y_4022_);
lean_ctor_set_uint8(v___x_4027_, sizeof(void*)*14, v___y_4024_);
lean_ctor_set_uint8(v___x_4027_, sizeof(void*)*14 + 1, v___y_4023_);
lean_inc(v___y_3996_);
lean_inc(v___y_3994_);
v___x_4028_ = lean_apply_4(v_x_3993_, v___y_3994_, v___x_4027_, v___y_3996_, lean_box(0));
v___y_3999_ = v___x_4028_;
goto v___jp_3998_;
}
v___jp_4045_:
{
lean_object* v___x_4046_; uint8_t v___x_4047_; 
v___x_4046_ = lean_unsigned_to_nat(0u);
v___x_4047_ = lean_nat_dec_eq(v_maxRecDepth_4033_, v___x_4046_);
if (v___x_4047_ == 0)
{
uint8_t v___x_4048_; 
v___x_4048_ = lean_nat_dec_eq(v_currRecDepth_4032_, v_maxRecDepth_4033_);
if (v___x_4048_ == 0)
{
lean_inc(v_ref_4034_);
v___y_4009_ = v_initHeartbeats_4037_;
v___y_4010_ = v_options_4031_;
v___y_4011_ = v_cancelTk_x3f_4042_;
v___y_4012_ = v_quotContext_4039_;
v___y_4013_ = v_maxHeartbeats_4038_;
v___y_4014_ = v_fileName_4029_;
v___y_4015_ = v_fileMap_4030_;
v___y_4016_ = v_currRecDepth_4032_;
v___y_4017_ = v_maxRecDepth_4033_;
v___y_4018_ = v_ref_4034_;
v___y_4019_ = v_currNamespace_4035_;
v___y_4020_ = v_currMacroScope_4040_;
v___y_4021_ = v_openDecls_4036_;
v___y_4022_ = v_inheritedTraceOptions_4044_;
v___y_4023_ = v_suppressElabErrors_4043_;
v___y_4024_ = v_diag_4041_;
goto v___jp_4008_;
}
else
{
lean_object* v___x_4049_; 
lean_dec_ref(v_x_3993_);
lean_inc(v_ref_4034_);
v___x_4049_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_4034_);
v___y_3999_ = v___x_4049_;
goto v___jp_3998_;
}
}
else
{
lean_inc(v_ref_4034_);
v___y_4009_ = v_initHeartbeats_4037_;
v___y_4010_ = v_options_4031_;
v___y_4011_ = v_cancelTk_x3f_4042_;
v___y_4012_ = v_quotContext_4039_;
v___y_4013_ = v_maxHeartbeats_4038_;
v___y_4014_ = v_fileName_4029_;
v___y_4015_ = v_fileMap_4030_;
v___y_4016_ = v_currRecDepth_4032_;
v___y_4017_ = v_maxRecDepth_4033_;
v___y_4018_ = v_ref_4034_;
v___y_4019_ = v_currNamespace_4035_;
v___y_4020_ = v_currMacroScope_4040_;
v___y_4021_ = v_openDecls_4036_;
v___y_4022_ = v_inheritedTraceOptions_4044_;
v___y_4023_ = v_suppressElabErrors_4043_;
v___y_4024_ = v_diag_4041_;
goto v___jp_4008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_x_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v_x_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v___y_4062_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_4067_, lean_object* v_x_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = lean_apply_1(v_x_4068_, lean_box(0));
v___x_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_4074_, lean_object* v_x_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(v_00_u03b1_4074_, v_x_4075_, v___y_4076_, v___y_4077_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(lean_object* v_pre_4080_, lean_object* v_post_4081_, size_t v_sz_4082_, size_t v_i_4083_, lean_object* v_bs_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_){
_start:
{
uint8_t v___x_4089_; 
v___x_4089_ = lean_usize_dec_lt(v_i_4083_, v_sz_4082_);
if (v___x_4089_ == 0)
{
lean_object* v___x_4090_; 
lean_dec_ref(v_post_4081_);
lean_dec_ref(v_pre_4080_);
v___x_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4090_, 0, v_bs_4084_);
return v___x_4090_;
}
else
{
lean_object* v_v_4091_; lean_object* v___x_4092_; 
v_v_4091_ = lean_array_uget_borrowed(v_bs_4084_, v_i_4083_);
lean_inc(v_v_4091_);
lean_inc_ref(v_post_4081_);
lean_inc_ref(v_pre_4080_);
v___x_4092_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4080_, v_post_4081_, v_v_4091_, v___y_4085_, v___y_4086_, v___y_4087_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4094_; lean_object* v_bs_x27_4095_; size_t v___x_4096_; size_t v___x_4097_; lean_object* v___x_4098_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_a_4093_);
lean_dec_ref(v___x_4092_);
v___x_4094_ = lean_unsigned_to_nat(0u);
v_bs_x27_4095_ = lean_array_uset(v_bs_4084_, v_i_4083_, v___x_4094_);
v___x_4096_ = ((size_t)1ULL);
v___x_4097_ = lean_usize_add(v_i_4083_, v___x_4096_);
v___x_4098_ = lean_array_uset(v_bs_x27_4095_, v_i_4083_, v_a_4093_);
v_i_4083_ = v___x_4097_;
v_bs_4084_ = v___x_4098_;
goto _start;
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_dec_ref(v_bs_4084_);
lean_dec_ref(v_post_4081_);
lean_dec_ref(v_pre_4080_);
v_a_4100_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4092_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4092_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(lean_object* v_pre_4108_, lean_object* v_post_4109_, lean_object* v_x_4110_, lean_object* v_x_4111_, lean_object* v_x_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
if (lean_obj_tag(v_x_4110_) == 5)
{
lean_object* v_fn_4117_; lean_object* v_arg_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; 
v_fn_4117_ = lean_ctor_get(v_x_4110_, 0);
lean_inc_ref(v_fn_4117_);
v_arg_4118_ = lean_ctor_get(v_x_4110_, 1);
lean_inc_ref(v_arg_4118_);
lean_dec_ref(v_x_4110_);
v___x_4119_ = lean_array_set(v_x_4111_, v_x_4112_, v_arg_4118_);
v___x_4120_ = lean_unsigned_to_nat(1u);
v___x_4121_ = lean_nat_sub(v_x_4112_, v___x_4120_);
lean_dec(v_x_4112_);
v_x_4110_ = v_fn_4117_;
v_x_4111_ = v___x_4119_;
v_x_4112_ = v___x_4121_;
goto _start;
}
else
{
lean_object* v___x_4123_; 
lean_dec(v_x_4112_);
lean_inc_ref(v_post_4109_);
lean_inc_ref(v_pre_4108_);
v___x_4123_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4108_, v_post_4109_, v_x_4110_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; size_t v_sz_4125_; size_t v___x_4126_; lean_object* v___x_4127_; 
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
lean_inc(v_a_4124_);
lean_dec_ref(v___x_4123_);
v_sz_4125_ = lean_array_size(v_x_4111_);
v___x_4126_ = ((size_t)0ULL);
lean_inc_ref(v_post_4109_);
lean_inc_ref(v_pre_4108_);
v___x_4127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_4108_, v_post_4109_, v_sz_4125_, v___x_4126_, v_x_4111_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref(v___x_4127_);
v___x_4129_ = l_Lean_mkAppN(v_a_4124_, v_a_4128_);
lean_dec(v_a_4128_);
v___x_4130_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4108_, v_post_4109_, v___x_4129_, v___y_4113_, v___y_4114_, v___y_4115_);
return v___x_4130_;
}
else
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4138_; 
lean_dec(v_a_4124_);
lean_dec_ref(v_post_4109_);
lean_dec_ref(v_pre_4108_);
v_a_4131_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4133_ = v___x_4127_;
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4127_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4131_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
else
{
lean_dec_ref(v_x_4111_);
lean_dec_ref(v_post_4109_);
lean_dec_ref(v_pre_4108_);
return v___x_4123_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(lean_object* v___x_4139_, lean_object* v_pre_4140_, lean_object* v_e_4141_, lean_object* v_post_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v___y_4148_; uint8_t v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; uint8_t v___y_4155_; uint8_t v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; uint8_t v___y_4170_; uint8_t v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; uint8_t v___y_4183_; lean_object* v___x_4190_; 
v___x_4190_ = l_Lean_Core_checkSystem(v___x_4139_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v___x_4191_; 
lean_dec_ref(v___x_4190_);
lean_inc_ref(v_pre_4140_);
lean_inc(v___y_4145_);
lean_inc_ref(v___y_4144_);
lean_inc_ref(v_e_4141_);
v___x_4191_ = lean_apply_4(v_pre_4140_, v_e_4141_, v___y_4144_, v___y_4145_, lean_box(0));
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4281_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4194_ = v___x_4191_;
v_isShared_4195_ = v_isSharedCheck_4281_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4191_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4281_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___y_4197_; 
switch(lean_obj_tag(v_a_4192_))
{
case 0:
{
lean_object* v_e_4271_; lean_object* v___x_4273_; 
lean_dec_ref(v_post_4142_);
lean_dec_ref(v_e_4141_);
lean_dec_ref(v_pre_4140_);
v_e_4271_ = lean_ctor_get(v_a_4192_, 0);
lean_inc_ref(v_e_4271_);
lean_dec_ref(v_a_4192_);
if (v_isShared_4195_ == 0)
{
lean_ctor_set(v___x_4194_, 0, v_e_4271_);
v___x_4273_ = v___x_4194_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_e_4271_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
case 1:
{
lean_object* v_e_4275_; lean_object* v___x_4276_; 
lean_del_object(v___x_4194_);
lean_dec_ref(v_e_4141_);
v_e_4275_ = lean_ctor_get(v_a_4192_, 0);
lean_inc_ref(v_e_4275_);
lean_dec_ref(v_a_4192_);
lean_inc_ref(v_post_4142_);
lean_inc_ref(v_pre_4140_);
v___x_4276_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4140_, v_post_4142_, v_e_4275_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_a_4277_; lean_object* v___x_4278_; 
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc(v_a_4277_);
lean_dec_ref(v___x_4276_);
v___x_4278_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v_a_4277_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4278_;
}
else
{
lean_dec_ref(v_post_4142_);
lean_dec_ref(v_pre_4140_);
return v___x_4276_;
}
}
default: 
{
lean_object* v_e_x3f_4279_; 
lean_del_object(v___x_4194_);
v_e_x3f_4279_ = lean_ctor_get(v_a_4192_, 0);
lean_inc(v_e_x3f_4279_);
lean_dec_ref(v_a_4192_);
if (lean_obj_tag(v_e_x3f_4279_) == 0)
{
v___y_4197_ = v_e_4141_;
goto v___jp_4196_;
}
else
{
lean_object* v_val_4280_; 
lean_dec_ref(v_e_4141_);
v_val_4280_ = lean_ctor_get(v_e_x3f_4279_, 0);
lean_inc(v_val_4280_);
lean_dec_ref(v_e_x3f_4279_);
v___y_4197_ = v_val_4280_;
goto v___jp_4196_;
}
}
}
v___jp_4196_:
{
switch(lean_obj_tag(v___y_4197_))
{
case 7:
{
lean_object* v_binderName_4198_; lean_object* v_binderType_4199_; lean_object* v_body_4200_; uint8_t v_binderInfo_4201_; lean_object* v___x_4202_; 
v_binderName_4198_ = lean_ctor_get(v___y_4197_, 0);
lean_inc(v_binderName_4198_);
v_binderType_4199_ = lean_ctor_get(v___y_4197_, 1);
v_body_4200_ = lean_ctor_get(v___y_4197_, 2);
v_binderInfo_4201_ = lean_ctor_get_uint8(v___y_4197_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_4199_);
lean_inc_ref(v_post_4142_);
lean_inc_ref(v_pre_4140_);
v___x_4202_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4140_, v_post_4142_, v_binderType_4199_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4204_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref(v___x_4202_);
lean_inc_ref(v_body_4200_);
lean_inc_ref(v_post_4142_);
lean_inc_ref(v_pre_4140_);
v___x_4204_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4140_, v_post_4142_, v_body_4200_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; size_t v___x_4206_; size_t v___x_4207_; uint8_t v___x_4208_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4205_);
lean_dec_ref(v___x_4204_);
v___x_4206_ = lean_ptr_addr(v_binderType_4199_);
v___x_4207_ = lean_ptr_addr(v_a_4203_);
v___x_4208_ = lean_usize_dec_eq(v___x_4206_, v___x_4207_);
if (v___x_4208_ == 0)
{
v___y_4178_ = v_binderInfo_4201_;
v___y_4179_ = v___y_4197_;
v___y_4180_ = v_binderName_4198_;
v___y_4181_ = v_a_4203_;
v___y_4182_ = v_a_4205_;
v___y_4183_ = v___x_4208_;
goto v___jp_4177_;
}
else
{
size_t v___x_4209_; size_t v___x_4210_; uint8_t v___x_4211_; 
v___x_4209_ = lean_ptr_addr(v_body_4200_);
v___x_4210_ = lean_ptr_addr(v_a_4205_);
v___x_4211_ = lean_usize_dec_eq(v___x_4209_, v___x_4210_);
v___y_4178_ = v_binderInfo_4201_;
v___y_4179_ = v___y_4197_;
v___y_4180_ = v_binderName_4198_;
v___y_4181_ = v_a_4203_;
v___y_4182_ = v_a_4205_;
v___y_4183_ = v___x_4211_;
goto v___jp_4177_;
}
}
else
{
lean_dec(v_a_4203_);
lean_dec_ref(v___y_4197_);
lean_dec(v_binderName_4198_);
lean_dec_ref(v_post_4142_);
lean_dec_ref(v_pre_4140_);
return v___x_4204_;
}
}
else
{
lean_dec_ref(v___y_4197_);
lean_dec(v_binderName_4198_);
lean_dec_ref(v_post_4142_);
lean_dec_ref(v_pre_4140_);
return v___x_4202_;
}
}
case 6:
{
lean_object* v_binderName_4212_; lean_object* v_binderType_4213_; lean_object* v_body_4214_; uint8_t v_binderInfo_4215_; lean_object* v___x_4216_; 
v_binderName_4212_ = lean_ctor_get(v___y_4197_, 0);
lean_inc(v_binderName_4212_);
v_binderType_4213_ = lean_ctor_get(v___y_4197_, 1);
v_body_4214_ = lean_ctor_get(v___y_4197_, 2);
v_binderInfo_4215_ = lean_ctor_get_uint8(v___y_4197_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_4213_);
lean_inc_ref(v_post_4142_);
lean_inc_ref(v_pre_4140_);
v___x_4216_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4140_, v_post_4142_, v_binderType_4213_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v___x_4218_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
lean_dec_ref(v___x_4216_);
lean_inc_ref(v_body_4214_);
lean_inc_ref(v_post_4142_);
lean_inc_ref(v_pre_4140_);
v___x_4218_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4140_, v_post_4142_, v_body_4214_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v_a_4219_; size_t v___x_4220_; size_t v___x_4221_; uint8_t v___x_4222_; 
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
lean_inc(v_a_4219_);
lean_dec_ref(v___x_4218_);
v___x_4220_ = lean_ptr_addr(v_binderType_4213_);
v___x_4221_ = lean_ptr_addr(v_a_4217_);
v___x_4222_ = lean_usize_dec_eq(v___x_4220_, v___x_4221_);
if (v___x_4222_ == 0)
{
v___y_4165_ = v_binderInfo_4215_;
v___y_4166_ = v_a_4219_;
v___y_4167_ = v_a_4217_;
v___y_4168_ = v___y_4197_;
v___y_4169_ = v_binderName_4212_;
v___y_4170_ = v___x_4222_;
goto v___jp_4164_;
}
else
{
size_t v___x_4223_; size_t v___x_4224_; uint8_t v___x_4225_; 
v___x_4223_ = lean_ptr_addr(v_body_4214_);
v___x_4224_ = lean_ptr_addr(v_a_4219_);
v___x_4225_ = lean_usize_dec_eq(v___x_4223_, v___x_4224_);
v___y_4165_ = v_binderInfo_4215_;
v___y_4166_ = v_a_4219_;
v___y_4167_ = v_a_4217_;
v___y_4168_ = v___y_4197_;
v___y_4169_ = v_binderName_4212_;
v___y_4170_ = v___x_4225_;
goto v___jp_4164_;
}
}
else
{
lean_dec(v_a_4217_);
lean_dec(v_binderName_4212_);
lean_dec_ref(v___y_4197_);
lean_dec_ref(v_post_4142_);
lean_dec_ref(v_pre_4140_);
return v___x_4218_;
}
}
else
{
lean_dec(v_binderName_4212_);
lean_dec_ref(v___y_4197_);
lean_dec_ref(v_post_4142_);
lean_dec_ref(v_pre_4140_);
return v___x_4216_;
}
}
case 8:
{
lean_object* v_declName_4226_; lean_object* v_type_4227_; lean_object* v_value_4228_; lean_object* v_body_4229_; uint8_t v_nondep_4230_; lean_object* v___x_4231_; 
v_declName_4226_ = lean_ctor_get(v___y_4197_, 0);
lean_inc(v_declName_4226_);
v_type_4227_ = lean_ctor_get(v___y_4197_, 1);
v_value_4228_ = lean_ctor_get(v___y_4197_, 2);
v_body_4229_ = lean_ctor_get(v___y_4197_, 3);
lean_inc_ref(v_body_4229_);
v_nondep_4230_ = lean_ctor_get_uint8(v___y_4197_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_4227_);
lean_inc_ref(v_post_4142_);
lean_inc_ref(v_pre_4140_);
v___x_4231_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4140_, v_post_4142_, v_type_4227_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4233_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref(v___x_4231_);
lean_inc_ref(v_value_4228_);
lean_inc_ref(v_post_4142_);
lean_inc_ref(v_pre_4140_);
v___x_4233_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4140_, v_post_4142_, v_value_4228_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4235_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref(v___x_4233_);
lean_inc_ref(v_body_4229_);
lean_inc_ref(v_post_4142_);
lean_inc_ref(v_pre_4140_);
v___x_4235_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4140_, v_post_4142_, v_body_4229_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; size_t v___x_4237_; size_t v___x_4238_; uint8_t v___x_4239_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref(v___x_4235_);
v___x_4237_ = lean_ptr_addr(v_type_4227_);
v___x_4238_ = lean_ptr_addr(v_a_4232_);
v___x_4239_ = lean_usize_dec_eq(v___x_4237_, v___x_4238_);
if (v___x_4239_ == 0)
{
v___y_4148_ = v_a_4236_;
v___y_4149_ = v_nondep_4230_;
v___y_4150_ = v_a_4232_;
v___y_4151_ = v___y_4197_;
v___y_4152_ = v_a_4234_;
v___y_4153_ = v_declName_4226_;
v___y_4154_ = v_body_4229_;
v___y_4155_ = v___x_4239_;
goto v___jp_4147_;
}
else
{
size_t v___x_4240_; size_t v___x_4241_; uint8_t v___x_4242_; 
v___x_4240_ = lean_ptr_addr(v_value_4228_);
v___x_4241_ = lean_ptr_addr(v_a_4234_);
v___x_4242_ = lean_usize_dec_eq(v___x_4240_, v___x_4241_);
v___y_4148_ = v_a_4236_;
v___y_4149_ = v_nondep_4230_;
v___y_4150_ = v_a_4232_;
v___y_4151_ = v___y_4197_;
v___y_4152_ = v_a_4234_;
v___y_4153_ = v_declName_4226_;
v___y_4154_ = v_body_4229_;
v___y_4155_ = v___x_4242_;
goto v___jp_4147_;
}
}
else
{
lean_dec(v_a_4234_);
lean_dec(v_a_4232_);
lean_dec_ref(v_body_4229_);
lean_dec_ref(v___y_4197_);
lean_dec(v_declName_4226_);
lean_dec_ref(v_post_4142_);
lean_dec_ref(v_pre_4140_);
return v___x_4235_;
}
}
else
{
lean_dec(v_a_4232_);
lean_dec_ref(v_body_4229_);
lean_dec_ref(v___y_4197_);
lean_dec(v_declName_4226_);
lean_dec_ref(v_post_4142_);
lean_dec_ref(v_pre_4140_);
return v___x_4233_;
}
}
else
{
lean_dec_ref(v_body_4229_);
lean_dec_ref(v___y_4197_);
lean_dec(v_declName_4226_);
lean_dec_ref(v_post_4142_);
lean_dec_ref(v_pre_4140_);
return v___x_4231_;
}
}
case 5:
{
lean_object* v_dummy_4243_; lean_object* v_nargs_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v_dummy_4243_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_4244_ = l_Lean_Expr_getAppNumArgs(v___y_4197_);
lean_inc(v_nargs_4244_);
v___x_4245_ = lean_mk_array(v_nargs_4244_, v_dummy_4243_);
v___x_4246_ = lean_unsigned_to_nat(1u);
v___x_4247_ = lean_nat_sub(v_nargs_4244_, v___x_4246_);
lean_dec(v_nargs_4244_);
v___x_4248_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_4140_, v_post_4142_, v___y_4197_, v___x_4245_, v___x_4247_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4248_;
}
case 10:
{
lean_object* v_data_4249_; lean_object* v_expr_4250_; lean_object* v___x_4251_; 
v_data_4249_ = lean_ctor_get(v___y_4197_, 0);
v_expr_4250_ = lean_ctor_get(v___y_4197_, 1);
lean_inc_ref(v_expr_4250_);
lean_inc_ref(v_post_4142_);
lean_inc_ref(v_pre_4140_);
v___x_4251_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4140_, v_post_4142_, v_expr_4250_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v_a_4252_; size_t v___x_4253_; size_t v___x_4254_; uint8_t v___x_4255_; 
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_a_4252_);
lean_dec_ref(v___x_4251_);
v___x_4253_ = lean_ptr_addr(v_expr_4250_);
v___x_4254_ = lean_ptr_addr(v_a_4252_);
v___x_4255_ = lean_usize_dec_eq(v___x_4253_, v___x_4254_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
lean_inc(v_data_4249_);
lean_dec_ref(v___y_4197_);
v___x_4256_ = l_Lean_Expr_mdata___override(v_data_4249_, v_a_4252_);
v___x_4257_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v___x_4256_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4257_;
}
else
{
lean_object* v___x_4258_; 
lean_dec(v_a_4252_);
v___x_4258_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v___y_4197_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4258_;
}
}
else
{
lean_dec_ref(v___y_4197_);
lean_dec_ref(v_post_4142_);
lean_dec_ref(v_pre_4140_);
return v___x_4251_;
}
}
case 11:
{
lean_object* v_typeName_4259_; lean_object* v_idx_4260_; lean_object* v_struct_4261_; lean_object* v___x_4262_; 
v_typeName_4259_ = lean_ctor_get(v___y_4197_, 0);
v_idx_4260_ = lean_ctor_get(v___y_4197_, 1);
v_struct_4261_ = lean_ctor_get(v___y_4197_, 2);
lean_inc_ref(v_struct_4261_);
lean_inc_ref(v_post_4142_);
lean_inc_ref(v_pre_4140_);
v___x_4262_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4140_, v_post_4142_, v_struct_4261_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; size_t v___x_4264_; size_t v___x_4265_; uint8_t v___x_4266_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref(v___x_4262_);
v___x_4264_ = lean_ptr_addr(v_struct_4261_);
v___x_4265_ = lean_ptr_addr(v_a_4263_);
v___x_4266_ = lean_usize_dec_eq(v___x_4264_, v___x_4265_);
if (v___x_4266_ == 0)
{
lean_object* v___x_4267_; lean_object* v___x_4268_; 
lean_inc(v_idx_4260_);
lean_inc(v_typeName_4259_);
lean_dec_ref(v___y_4197_);
v___x_4267_ = l_Lean_Expr_proj___override(v_typeName_4259_, v_idx_4260_, v_a_4263_);
v___x_4268_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v___x_4267_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4268_;
}
else
{
lean_object* v___x_4269_; 
lean_dec(v_a_4263_);
v___x_4269_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v___y_4197_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4269_;
}
}
else
{
lean_dec_ref(v___y_4197_);
lean_dec_ref(v_post_4142_);
lean_dec_ref(v_pre_4140_);
return v___x_4262_;
}
}
default: 
{
lean_object* v___x_4270_; 
v___x_4270_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v___y_4197_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4270_;
}
}
}
}
}
else
{
lean_object* v_a_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4289_; 
lean_dec_ref(v_post_4142_);
lean_dec_ref(v_e_4141_);
lean_dec_ref(v_pre_4140_);
v_a_4282_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4284_ = v___x_4191_;
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_a_4282_);
lean_dec(v___x_4191_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4287_; 
if (v_isShared_4285_ == 0)
{
v___x_4287_ = v___x_4284_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_a_4282_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
}
}
}
}
else
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4297_; 
lean_dec_ref(v_post_4142_);
lean_dec_ref(v_e_4141_);
lean_dec_ref(v_pre_4140_);
v_a_4290_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4292_ = v___x_4190_;
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4190_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
if (v_isShared_4293_ == 0)
{
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4290_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
v___jp_4147_:
{
if (v___y_4155_ == 0)
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
lean_dec_ref(v___y_4154_);
lean_dec_ref(v___y_4151_);
v___x_4156_ = l_Lean_Expr_letE___override(v___y_4153_, v___y_4150_, v___y_4152_, v___y_4148_, v___y_4149_);
v___x_4157_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v___x_4156_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4157_;
}
else
{
size_t v___x_4158_; size_t v___x_4159_; uint8_t v___x_4160_; 
v___x_4158_ = lean_ptr_addr(v___y_4154_);
lean_dec_ref(v___y_4154_);
v___x_4159_ = lean_ptr_addr(v___y_4148_);
v___x_4160_ = lean_usize_dec_eq(v___x_4158_, v___x_4159_);
if (v___x_4160_ == 0)
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
lean_dec_ref(v___y_4151_);
v___x_4161_ = l_Lean_Expr_letE___override(v___y_4153_, v___y_4150_, v___y_4152_, v___y_4148_, v___y_4149_);
v___x_4162_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v___x_4161_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4162_;
}
else
{
lean_object* v___x_4163_; 
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec_ref(v___y_4150_);
lean_dec_ref(v___y_4148_);
v___x_4163_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v___y_4151_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4163_;
}
}
}
v___jp_4164_:
{
if (v___y_4170_ == 0)
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
lean_dec_ref(v___y_4168_);
v___x_4171_ = l_Lean_Expr_lam___override(v___y_4169_, v___y_4167_, v___y_4166_, v___y_4165_);
v___x_4172_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v___x_4171_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4172_;
}
else
{
uint8_t v___x_4173_; 
v___x_4173_ = l_Lean_instBEqBinderInfo_beq(v___y_4165_, v___y_4165_);
if (v___x_4173_ == 0)
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
lean_dec_ref(v___y_4168_);
v___x_4174_ = l_Lean_Expr_lam___override(v___y_4169_, v___y_4167_, v___y_4166_, v___y_4165_);
v___x_4175_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v___x_4174_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4175_;
}
else
{
lean_object* v___x_4176_; 
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4167_);
lean_dec_ref(v___y_4166_);
v___x_4176_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v___y_4168_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4176_;
}
}
}
v___jp_4177_:
{
if (v___y_4183_ == 0)
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_dec_ref(v___y_4179_);
v___x_4184_ = l_Lean_Expr_forallE___override(v___y_4180_, v___y_4181_, v___y_4182_, v___y_4178_);
v___x_4185_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v___x_4184_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4185_;
}
else
{
uint8_t v___x_4186_; 
v___x_4186_ = l_Lean_instBEqBinderInfo_beq(v___y_4178_, v___y_4178_);
if (v___x_4186_ == 0)
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
lean_dec_ref(v___y_4179_);
v___x_4187_ = l_Lean_Expr_forallE___override(v___y_4180_, v___y_4181_, v___y_4182_, v___y_4178_);
v___x_4188_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v___x_4187_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4188_;
}
else
{
lean_object* v___x_4189_; 
lean_dec_ref(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec(v___y_4180_);
v___x_4189_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4140_, v_post_4142_, v___y_4179_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4298_, lean_object* v_pre_4299_, lean_object* v_e_4300_, lean_object* v_post_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(v___x_4298_, v_pre_4299_, v_e_4300_, v_post_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___y_4302_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(lean_object* v_pre_4307_, lean_object* v_post_4308_, lean_object* v_e_4309_, lean_object* v_a_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; 
lean_inc(v_a_4310_);
v___x_4314_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4314_, 0, lean_box(0));
lean_closure_set(v___x_4314_, 1, lean_box(0));
lean_closure_set(v___x_4314_, 2, v_a_4310_);
v___x_4315_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___x_4314_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4347_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4318_ = v___x_4315_;
v_isShared_4319_ = v_isSharedCheck_4347_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4315_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4347_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4320_; 
v___x_4320_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_4316_, v_e_4309_);
lean_dec(v_a_4316_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v___x_4321_; lean_object* v___f_4322_; lean_object* v___x_4323_; 
lean_del_object(v___x_4318_);
v___x_4321_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_4309_);
v___f_4322_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed), 8, 4);
lean_closure_set(v___f_4322_, 0, v___x_4321_);
lean_closure_set(v___f_4322_, 1, v_pre_4307_);
lean_closure_set(v___f_4322_, 2, v_e_4309_);
lean_closure_set(v___f_4322_, 3, v_post_4308_);
v___x_4323_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v___f_4322_, v_a_4310_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___f_4325_; lean_object* v___x_4326_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc_n(v_a_4324_, 2);
lean_dec_ref(v___x_4323_);
lean_inc(v_a_4310_);
v___f_4325_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4325_, 0, v_a_4310_);
lean_closure_set(v___f_4325_, 1, v_e_4309_);
lean_closure_set(v___f_4325_, 2, v_a_4324_);
v___x_4326_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___f_4325_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4333_ == 0)
{
lean_object* v_unused_4334_; 
v_unused_4334_ = lean_ctor_get(v___x_4326_, 0);
lean_dec(v_unused_4334_);
v___x_4328_ = v___x_4326_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_dec(v___x_4326_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 0, v_a_4324_);
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4324_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
lean_dec(v_a_4324_);
v_a_4335_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4326_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4326_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
else
{
lean_dec_ref(v_e_4309_);
return v___x_4323_;
}
}
else
{
lean_object* v_val_4343_; lean_object* v___x_4345_; 
lean_dec_ref(v_e_4309_);
lean_dec_ref(v_post_4308_);
lean_dec_ref(v_pre_4307_);
v_val_4343_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_val_4343_);
lean_dec_ref(v___x_4320_);
if (v_isShared_4319_ == 0)
{
lean_ctor_set(v___x_4318_, 0, v_val_4343_);
v___x_4345_ = v___x_4318_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_val_4343_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
lean_dec_ref(v_e_4309_);
lean_dec_ref(v_post_4308_);
lean_dec_ref(v_pre_4307_);
v_a_4348_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4315_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4315_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(lean_object* v_pre_4356_, lean_object* v_post_4357_, lean_object* v_e_4358_, lean_object* v_a_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
lean_object* v___x_4363_; 
lean_inc_ref(v_post_4357_);
lean_inc(v___y_4361_);
lean_inc_ref(v___y_4360_);
lean_inc_ref(v_e_4358_);
v___x_4363_ = lean_apply_4(v_post_4357_, v_e_4358_, v___y_4360_, v___y_4361_, lean_box(0));
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4382_; 
v_a_4364_ = lean_ctor_get(v___x_4363_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4366_ = v___x_4363_;
v_isShared_4367_ = v_isSharedCheck_4382_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4363_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4382_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
switch(lean_obj_tag(v_a_4364_))
{
case 0:
{
lean_object* v_e_4368_; lean_object* v___x_4370_; 
lean_dec_ref(v_e_4358_);
lean_dec_ref(v_post_4357_);
lean_dec_ref(v_pre_4356_);
v_e_4368_ = lean_ctor_get(v_a_4364_, 0);
lean_inc_ref(v_e_4368_);
lean_dec_ref(v_a_4364_);
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 0, v_e_4368_);
v___x_4370_ = v___x_4366_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_e_4368_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
case 1:
{
lean_object* v_e_4372_; lean_object* v___x_4373_; 
lean_del_object(v___x_4366_);
lean_dec_ref(v_e_4358_);
v_e_4372_ = lean_ctor_get(v_a_4364_, 0);
lean_inc_ref(v_e_4372_);
lean_dec_ref(v_a_4364_);
v___x_4373_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4356_, v_post_4357_, v_e_4372_, v_a_4359_, v___y_4360_, v___y_4361_);
return v___x_4373_;
}
default: 
{
lean_object* v_e_x3f_4374_; 
lean_dec_ref(v_post_4357_);
lean_dec_ref(v_pre_4356_);
v_e_x3f_4374_ = lean_ctor_get(v_a_4364_, 0);
lean_inc(v_e_x3f_4374_);
lean_dec_ref(v_a_4364_);
if (lean_obj_tag(v_e_x3f_4374_) == 0)
{
lean_object* v___x_4376_; 
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 0, v_e_4358_);
v___x_4376_ = v___x_4366_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_e_4358_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
else
{
lean_object* v_val_4378_; lean_object* v___x_4380_; 
lean_dec_ref(v_e_4358_);
v_val_4378_ = lean_ctor_get(v_e_x3f_4374_, 0);
lean_inc(v_val_4378_);
lean_dec_ref(v_e_x3f_4374_);
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 0, v_val_4378_);
v___x_4380_ = v___x_4366_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_val_4378_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
}
}
}
else
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4390_; 
lean_dec_ref(v_e_4358_);
lean_dec_ref(v_post_4357_);
lean_dec_ref(v_pre_4356_);
v_a_4383_ = lean_ctor_get(v___x_4363_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4385_ = v___x_4363_;
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4363_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4391_, lean_object* v_post_4392_, lean_object* v_e_4393_, lean_object* v_a_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4391_, v_post_4392_, v_e_4393_, v_a_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v_a_4394_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4399_, lean_object* v_post_4400_, lean_object* v_sz_4401_, lean_object* v_i_4402_, lean_object* v_bs_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
size_t v_sz_boxed_4408_; size_t v_i_boxed_4409_; lean_object* v_res_4410_; 
v_sz_boxed_4408_ = lean_unbox_usize(v_sz_4401_);
lean_dec(v_sz_4401_);
v_i_boxed_4409_ = lean_unbox_usize(v_i_4402_);
lean_dec(v_i_4402_);
v_res_4410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_4399_, v_post_4400_, v_sz_boxed_4408_, v_i_boxed_4409_, v_bs_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___boxed(lean_object* v_pre_4411_, lean_object* v_post_4412_, lean_object* v_x_4413_, lean_object* v_x_4414_, lean_object* v_x_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_4411_, v_post_4412_, v_x_4413_, v_x_4414_, v_x_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
return v_res_4420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___boxed(lean_object* v_pre_4421_, lean_object* v_post_4422_, lean_object* v_e_4423_, lean_object* v_a_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4421_, v_post_4422_, v_e_4423_, v_a_4424_, v___y_4425_, v___y_4426_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v_a_4424_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_object* v_00_u03b1_4429_, lean_object* v_x_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4434_ = lean_apply_1(v_x_4430_, lean_box(0));
v___x_4435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0___boxed(lean_object* v_00_u03b1_4436_, lean_object* v_x_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(v_00_u03b1_4436_, v_x_4437_, v___y_4438_, v___y_4439_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(lean_object* v_input_4442_, lean_object* v_pre_4443_, lean_object* v_post_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v_a_4450_; lean_object* v___x_4451_; 
v___x_4448_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_4449_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_4448_, v___y_4445_, v___y_4446_);
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_a_4450_);
lean_dec_ref(v___x_4449_);
v___x_4451_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4443_, v_post_4444_, v_input_4442_, v_a_4450_, v___y_4445_, v___y_4446_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4461_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc(v_a_4452_);
lean_dec_ref(v___x_4451_);
v___x_4453_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4453_, 0, lean_box(0));
lean_closure_set(v___x_4453_, 1, lean_box(0));
lean_closure_set(v___x_4453_, 2, v_a_4450_);
v___x_4454_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_4453_, v___y_4445_, v___y_4446_);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4461_ == 0)
{
lean_object* v_unused_4462_; 
v_unused_4462_ = lean_ctor_get(v___x_4454_, 0);
lean_dec(v_unused_4462_);
v___x_4456_ = v___x_4454_;
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
else
{
lean_dec(v___x_4454_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4459_; 
if (v_isShared_4457_ == 0)
{
lean_ctor_set(v___x_4456_, 0, v_a_4452_);
v___x_4459_ = v___x_4456_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4452_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
else
{
lean_dec(v_a_4450_);
return v___x_4451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___boxed(lean_object* v_input_4463_, lean_object* v_pre_4464_, lean_object* v_post_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v_res_4469_; 
v_res_4469_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_input_4463_, v_pre_4464_, v_post_4465_, v___y_4466_, v___y_4467_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object* v_e_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_){
_start:
{
uint8_t v___x_4476_; 
v___x_4476_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_4472_);
if (v___x_4476_ == 0)
{
lean_object* v_pre_4477_; lean_object* v___f_4478_; lean_object* v___x_4479_; 
v_pre_4477_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__0));
v___f_4478_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__1));
v___x_4479_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_e_4472_, v_pre_4477_, v___f_4478_, v_a_4473_, v_a_4474_);
return v___x_4479_;
}
else
{
lean_object* v___x_4480_; 
v___x_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4480_, 0, v_e_4472_);
return v___x_4480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___boxed(lean_object* v_e_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_Lean_Meta_Sym_normalizeLevels(v_e_4481_, v_a_4482_, v_a_4483_);
lean_dec(v_a_4483_);
lean_dec_ref(v_a_4482_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4486_, lean_object* v_ref_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
lean_object* v___x_4491_; 
v___x_4491_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_4487_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4492_, lean_object* v_ref_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v_res_4497_; 
v_res_4497_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4492_, v_ref_4493_, v___y_4494_, v___y_4495_);
lean_dec(v___y_4495_);
lean_dec_ref(v___y_4494_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v___x_4502_; 
v___x_4502_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7(v_00_u03b1_4503_, v___y_4504_, v___y_4505_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(lean_object* v_00_u03b1_4508_, lean_object* v_x_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
lean_object* v___x_4514_; 
v___x_4514_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v_x_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b1_4515_, lean_object* v_x_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_00_u03b1_4515_, v_x_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
return v_res_4521_;
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
