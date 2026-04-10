// Lean compiler output
// Module: Lean.Meta.Sym.Util
// Imports: public import Lean.Meta.Sym.SymM public import Lean.Meta.Transform import Init.Grind.Util import Lean.Meta.WHNF import Lean.Util.ForEachExpr
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
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "term is not in the maximally shared table"};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1;
static const lean_string_object l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0_value)} };
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(lean_object* v_e_1608_, lean_object* v___y_1609_){
_start:
{
uint8_t v___x_1611_; 
v___x_1611_ = l_Lean_Expr_hasMVar(v_e_1608_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v_e_1608_);
return v___x_1612_;
}
else
{
lean_object* v___x_1613_; lean_object* v_mctx_1614_; lean_object* v___x_1615_; lean_object* v_fst_1616_; lean_object* v_snd_1617_; lean_object* v___x_1618_; lean_object* v_cache_1619_; lean_object* v_zetaDeltaFVarIds_1620_; lean_object* v_postponed_1621_; lean_object* v_diag_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1631_; 
v___x_1613_ = lean_st_ref_get(v___y_1609_);
v_mctx_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc_ref(v_mctx_1614_);
lean_dec(v___x_1613_);
v___x_1615_ = l_Lean_instantiateMVarsCore(v_mctx_1614_, v_e_1608_);
v_fst_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_fst_1616_);
v_snd_1617_ = lean_ctor_get(v___x_1615_, 1);
lean_inc(v_snd_1617_);
lean_dec_ref(v___x_1615_);
v___x_1618_ = lean_st_ref_take(v___y_1609_);
v_cache_1619_ = lean_ctor_get(v___x_1618_, 1);
v_zetaDeltaFVarIds_1620_ = lean_ctor_get(v___x_1618_, 2);
v_postponed_1621_ = lean_ctor_get(v___x_1618_, 3);
v_diag_1622_ = lean_ctor_get(v___x_1618_, 4);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; 
v_unused_1632_ = lean_ctor_get(v___x_1618_, 0);
lean_dec(v_unused_1632_);
v___x_1624_ = v___x_1618_;
v_isShared_1625_ = v_isSharedCheck_1631_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_diag_1622_);
lean_inc(v_postponed_1621_);
lean_inc(v_zetaDeltaFVarIds_1620_);
lean_inc(v_cache_1619_);
lean_dec(v___x_1618_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1631_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v_snd_1617_);
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_snd_1617_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_cache_1619_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_zetaDeltaFVarIds_1620_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_postponed_1621_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_diag_1622_);
v___x_1627_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = lean_st_ref_set(v___y_1609_, v___x_1627_);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_fst_1616_);
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg___boxed(lean_object* v_e_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_1633_, v___y_1634_);
lean_dec(v___y_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0(lean_object* v_e_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_1637_, v___y_1641_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___boxed(lean_object* v_e_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0(v_e_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(lean_object* v_e_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v___x_1663_; lean_object* v_a_1664_; lean_object* v___x_1665_; 
v___x_1663_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_1655_, v_a_1659_);
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref(v___x_1663_);
v___x_1665_ = l_Lean_Meta_Sym_unfoldReducible(v_a_1664_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref(v___x_1665_);
v___x_1667_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1666_, v_a_1657_);
return v___x_1667_;
}
else
{
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr___boxed(lean_object* v_e_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_e_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_){
_start:
{
lean_object* v_ks_1681_; lean_object* v_vs_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1706_; 
v_ks_1681_ = lean_ctor_get(v_x_1677_, 0);
v_vs_1682_ = lean_ctor_get(v_x_1677_, 1);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_x_1677_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1684_ = v_x_1677_;
v_isShared_1685_ = v_isSharedCheck_1706_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_vs_1682_);
lean_inc(v_ks_1681_);
lean_dec(v_x_1677_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1706_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1686_ = lean_array_get_size(v_ks_1681_);
v___x_1687_ = lean_nat_dec_lt(v_x_1678_, v___x_1686_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
lean_dec(v_x_1678_);
v___x_1688_ = lean_array_push(v_ks_1681_, v_x_1679_);
v___x_1689_ = lean_array_push(v_vs_1682_, v_x_1680_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v___x_1689_);
lean_ctor_set(v___x_1684_, 0, v___x_1688_);
v___x_1691_ = v___x_1684_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
else
{
lean_object* v_k_x27_1693_; uint8_t v___x_1694_; 
v_k_x27_1693_ = lean_array_fget_borrowed(v_ks_1681_, v_x_1678_);
v___x_1694_ = l_Lean_instBEqFVarId_beq(v_x_1679_, v_k_x27_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1696_; 
if (v_isShared_1685_ == 0)
{
v___x_1696_ = v___x_1684_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_ks_1681_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_vs_1682_);
v___x_1696_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_unsigned_to_nat(1u);
v___x_1698_ = lean_nat_add(v_x_1678_, v___x_1697_);
lean_dec(v_x_1678_);
v_x_1677_ = v___x_1696_;
v_x_1678_ = v___x_1698_;
goto _start;
}
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1701_ = lean_array_fset(v_ks_1681_, v_x_1678_, v_x_1679_);
v___x_1702_ = lean_array_fset(v_vs_1682_, v_x_1678_, v_x_1680_);
lean_dec(v_x_1678_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v___x_1702_);
lean_ctor_set(v___x_1684_, 0, v___x_1701_);
v___x_1704_ = v___x_1684_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1707_, lean_object* v_k_1708_, lean_object* v_v_1709_){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1707_, v___x_1710_, v_k_1708_, v_v_1709_);
return v___x_1711_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1712_; size_t v___x_1713_; size_t v___x_1714_; 
v___x_1712_ = ((size_t)5ULL);
v___x_1713_ = ((size_t)1ULL);
v___x_1714_ = lean_usize_shift_left(v___x_1713_, v___x_1712_);
return v___x_1714_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1715_; size_t v___x_1716_; size_t v___x_1717_; 
v___x_1715_ = ((size_t)1ULL);
v___x_1716_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0);
v___x_1717_ = lean_usize_sub(v___x_1716_, v___x_1715_);
return v___x_1717_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(lean_object* v_x_1719_, size_t v_x_1720_, size_t v_x_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_){
_start:
{
if (lean_obj_tag(v_x_1719_) == 0)
{
lean_object* v_es_1724_; size_t v___x_1725_; size_t v___x_1726_; size_t v___x_1727_; size_t v___x_1728_; lean_object* v_j_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v_es_1724_ = lean_ctor_get(v_x_1719_, 0);
v___x_1725_ = ((size_t)5ULL);
v___x_1726_ = ((size_t)1ULL);
v___x_1727_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
v___x_1728_ = lean_usize_land(v_x_1720_, v___x_1727_);
v_j_1729_ = lean_usize_to_nat(v___x_1728_);
v___x_1730_ = lean_array_get_size(v_es_1724_);
v___x_1731_ = lean_nat_dec_lt(v_j_1729_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_dec(v_j_1729_);
lean_dec(v_x_1723_);
lean_dec(v_x_1722_);
return v_x_1719_;
}
else
{
lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1768_; 
lean_inc_ref(v_es_1724_);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_x_1719_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v_x_1719_, 0);
lean_dec(v_unused_1769_);
v___x_1733_ = v_x_1719_;
v_isShared_1734_ = v_isSharedCheck_1768_;
goto v_resetjp_1732_;
}
else
{
lean_dec(v_x_1719_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1768_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v_v_1735_; lean_object* v___x_1736_; lean_object* v_xs_x27_1737_; lean_object* v___y_1739_; 
v_v_1735_ = lean_array_fget(v_es_1724_, v_j_1729_);
v___x_1736_ = lean_box(0);
v_xs_x27_1737_ = lean_array_fset(v_es_1724_, v_j_1729_, v___x_1736_);
switch(lean_obj_tag(v_v_1735_))
{
case 0:
{
lean_object* v_key_1744_; lean_object* v_val_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1755_; 
v_key_1744_ = lean_ctor_get(v_v_1735_, 0);
v_val_1745_ = lean_ctor_get(v_v_1735_, 1);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_v_1735_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1747_ = v_v_1735_;
v_isShared_1748_ = v_isSharedCheck_1755_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_val_1745_);
lean_inc(v_key_1744_);
lean_dec(v_v_1735_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1755_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
uint8_t v___x_1749_; 
v___x_1749_ = l_Lean_instBEqFVarId_beq(v_x_1722_, v_key_1744_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_del_object(v___x_1747_);
v___x_1750_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1744_, v_val_1745_, v_x_1722_, v_x_1723_);
v___x_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
v___y_1739_ = v___x_1751_;
goto v___jp_1738_;
}
else
{
lean_object* v___x_1753_; 
lean_dec(v_val_1745_);
lean_dec(v_key_1744_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 1, v_x_1723_);
lean_ctor_set(v___x_1747_, 0, v_x_1722_);
v___x_1753_ = v___x_1747_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_x_1722_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_x_1723_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
v___y_1739_ = v___x_1753_;
goto v___jp_1738_;
}
}
}
}
case 1:
{
lean_object* v_node_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1766_; 
v_node_1756_ = lean_ctor_get(v_v_1735_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v_v_1735_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1758_ = v_v_1735_;
v_isShared_1759_ = v_isSharedCheck_1766_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_node_1756_);
lean_dec(v_v_1735_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1766_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
size_t v___x_1760_; size_t v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1760_ = lean_usize_shift_right(v_x_1720_, v___x_1725_);
v___x_1761_ = lean_usize_add(v_x_1721_, v___x_1726_);
v___x_1762_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_node_1756_, v___x_1760_, v___x_1761_, v_x_1722_, v_x_1723_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1762_);
v___x_1764_ = v___x_1758_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
v___y_1739_ = v___x_1764_;
goto v___jp_1738_;
}
}
}
default: 
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_x_1722_);
lean_ctor_set(v___x_1767_, 1, v_x_1723_);
v___y_1739_ = v___x_1767_;
goto v___jp_1738_;
}
}
v___jp_1738_:
{
lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1740_ = lean_array_fset(v_xs_x27_1737_, v_j_1729_, v___y_1739_);
lean_dec(v_j_1729_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1740_);
v___x_1742_ = v___x_1733_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
else
{
lean_object* v_ks_1770_; lean_object* v_vs_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1791_; 
v_ks_1770_ = lean_ctor_get(v_x_1719_, 0);
v_vs_1771_ = lean_ctor_get(v_x_1719_, 1);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_x_1719_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1773_ = v_x_1719_;
v_isShared_1774_ = v_isSharedCheck_1791_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_vs_1771_);
lean_inc(v_ks_1770_);
lean_dec(v_x_1719_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1791_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_ks_1770_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_vs_1771_);
v___x_1776_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v_newNode_1777_; uint8_t v___y_1779_; size_t v___x_1785_; uint8_t v___x_1786_; 
v_newNode_1777_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v___x_1776_, v_x_1722_, v_x_1723_);
v___x_1785_ = ((size_t)7ULL);
v___x_1786_ = lean_usize_dec_le(v___x_1785_, v_x_1721_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1787_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1777_);
v___x_1788_ = lean_unsigned_to_nat(4u);
v___x_1789_ = lean_nat_dec_lt(v___x_1787_, v___x_1788_);
lean_dec(v___x_1787_);
v___y_1779_ = v___x_1789_;
goto v___jp_1778_;
}
else
{
v___y_1779_ = v___x_1786_;
goto v___jp_1778_;
}
v___jp_1778_:
{
if (v___y_1779_ == 0)
{
lean_object* v_ks_1780_; lean_object* v_vs_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_ks_1780_ = lean_ctor_get(v_newNode_1777_, 0);
lean_inc_ref(v_ks_1780_);
v_vs_1781_ = lean_ctor_get(v_newNode_1777_, 1);
lean_inc_ref(v_vs_1781_);
lean_dec_ref(v_newNode_1777_);
v___x_1782_ = lean_unsigned_to_nat(0u);
v___x_1783_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2);
v___x_1784_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_x_1721_, v_ks_1780_, v_vs_1781_, v___x_1782_, v___x_1783_);
lean_dec_ref(v_vs_1781_);
lean_dec_ref(v_ks_1780_);
return v___x_1784_;
}
else
{
return v_newNode_1777_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(size_t v_depth_1792_, lean_object* v_keys_1793_, lean_object* v_vals_1794_, lean_object* v_i_1795_, lean_object* v_entries_1796_){
_start:
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = lean_array_get_size(v_keys_1793_);
v___x_1798_ = lean_nat_dec_lt(v_i_1795_, v___x_1797_);
if (v___x_1798_ == 0)
{
lean_dec(v_i_1795_);
return v_entries_1796_;
}
else
{
lean_object* v_k_1799_; lean_object* v_v_1800_; uint64_t v___x_1801_; size_t v_h_1802_; size_t v___x_1803_; lean_object* v___x_1804_; size_t v___x_1805_; size_t v___x_1806_; size_t v___x_1807_; size_t v_h_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v_k_1799_ = lean_array_fget_borrowed(v_keys_1793_, v_i_1795_);
v_v_1800_ = lean_array_fget_borrowed(v_vals_1794_, v_i_1795_);
v___x_1801_ = l_Lean_instHashableFVarId_hash(v_k_1799_);
v_h_1802_ = lean_uint64_to_usize(v___x_1801_);
v___x_1803_ = ((size_t)5ULL);
v___x_1804_ = lean_unsigned_to_nat(1u);
v___x_1805_ = ((size_t)1ULL);
v___x_1806_ = lean_usize_sub(v_depth_1792_, v___x_1805_);
v___x_1807_ = lean_usize_mul(v___x_1803_, v___x_1806_);
v_h_1808_ = lean_usize_shift_right(v_h_1802_, v___x_1807_);
v___x_1809_ = lean_nat_add(v_i_1795_, v___x_1804_);
lean_dec(v_i_1795_);
lean_inc(v_v_1800_);
lean_inc(v_k_1799_);
v___x_1810_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_entries_1796_, v_h_1808_, v_depth_1792_, v_k_1799_, v_v_1800_);
v_i_1795_ = v___x_1809_;
v_entries_1796_ = v___x_1810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1812_, lean_object* v_keys_1813_, lean_object* v_vals_1814_, lean_object* v_i_1815_, lean_object* v_entries_1816_){
_start:
{
size_t v_depth_boxed_1817_; lean_object* v_res_1818_; 
v_depth_boxed_1817_ = lean_unbox_usize(v_depth_1812_);
lean_dec(v_depth_1812_);
v_res_1818_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1817_, v_keys_1813_, v_vals_1814_, v_i_1815_, v_entries_1816_);
lean_dec_ref(v_vals_1814_);
lean_dec_ref(v_keys_1813_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___boxed(lean_object* v_x_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_, lean_object* v_x_1823_){
_start:
{
size_t v_x_9233__boxed_1824_; size_t v_x_9234__boxed_1825_; lean_object* v_res_1826_; 
v_x_9233__boxed_1824_ = lean_unbox_usize(v_x_1820_);
lean_dec(v_x_1820_);
v_x_9234__boxed_1825_ = lean_unbox_usize(v_x_1821_);
lean_dec(v_x_1821_);
v_res_1826_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_1819_, v_x_9233__boxed_1824_, v_x_9234__boxed_1825_, v_x_1822_, v_x_1823_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(lean_object* v_x_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_){
_start:
{
uint64_t v___x_1830_; size_t v___x_1831_; size_t v___x_1832_; lean_object* v___x_1833_; 
v___x_1830_ = l_Lean_instHashableFVarId_hash(v_x_1828_);
v___x_1831_ = lean_uint64_to_usize(v___x_1830_);
v___x_1832_ = ((size_t)1ULL);
v___x_1833_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_1827_, v___x_1831_, v___x_1832_, v_x_1828_, v_x_1829_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(lean_object* v_as_1834_, size_t v_sz_1835_, size_t v_i_1836_, lean_object* v_b_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_usize_dec_lt(v_i_1836_, v_sz_1835_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v_b_1837_);
return v___x_1846_;
}
else
{
lean_object* v_snd_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1952_; 
v_snd_1847_ = lean_ctor_get(v_b_1837_, 1);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_b_1837_);
if (v_isSharedCheck_1952_ == 0)
{
lean_object* v_unused_1953_; 
v_unused_1953_ = lean_ctor_get(v_b_1837_, 0);
lean_dec(v_unused_1953_);
v___x_1849_ = v_b_1837_;
v_isShared_1850_ = v_isSharedCheck_1952_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_snd_1847_);
lean_dec(v_b_1837_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1952_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v_a_1853_; lean_object* v_a_1860_; 
v___x_1851_ = lean_box(0);
v_a_1860_ = lean_array_uget(v_as_1834_, v_i_1836_);
if (lean_obj_tag(v_a_1860_) == 0)
{
v_a_1853_ = v_snd_1847_;
goto v___jp_1852_;
}
else
{
lean_object* v_snd_1861_; lean_object* v_val_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1951_; 
v_snd_1861_ = lean_ctor_get(v_snd_1847_, 1);
lean_inc(v_snd_1861_);
v_val_1862_ = lean_ctor_get(v_a_1860_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_a_1860_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1864_ = v_a_1860_;
v_isShared_1865_ = v_isSharedCheck_1951_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_val_1862_);
lean_dec(v_a_1860_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1951_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_fst_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1949_; 
v_fst_1866_ = lean_ctor_get(v_snd_1847_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_snd_1847_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; 
v_unused_1950_ = lean_ctor_get(v_snd_1847_, 1);
lean_dec(v_unused_1950_);
v___x_1868_ = v_snd_1847_;
v_isShared_1869_ = v_isSharedCheck_1949_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_fst_1866_);
lean_dec(v_snd_1847_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1949_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v_fst_1870_; lean_object* v_snd_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1948_; 
v_fst_1870_ = lean_ctor_get(v_snd_1861_, 0);
v_snd_1871_ = lean_ctor_get(v_snd_1861_, 1);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_snd_1861_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1873_ = v_snd_1861_;
v_isShared_1874_ = v_isSharedCheck_1948_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_snd_1871_);
lean_inc(v_fst_1870_);
lean_dec(v_snd_1861_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1948_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v_decl_1876_; 
if (lean_obj_tag(v_val_1862_) == 0)
{
lean_object* v_fvarId_1891_; lean_object* v_userName_1892_; lean_object* v_type_1893_; uint8_t v_bi_1894_; uint8_t v_kind_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1912_; 
v_fvarId_1891_ = lean_ctor_get(v_val_1862_, 1);
v_userName_1892_ = lean_ctor_get(v_val_1862_, 2);
v_type_1893_ = lean_ctor_get(v_val_1862_, 3);
v_bi_1894_ = lean_ctor_get_uint8(v_val_1862_, sizeof(void*)*4);
v_kind_1895_ = lean_ctor_get_uint8(v_val_1862_, sizeof(void*)*4 + 1);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_val_1862_);
if (v_isSharedCheck_1912_ == 0)
{
lean_object* v_unused_1913_; 
v_unused_1913_ = lean_ctor_get(v_val_1862_, 0);
lean_dec(v_unused_1913_);
v___x_1897_ = v_val_1862_;
v_isShared_1898_ = v_isSharedCheck_1912_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_type_1893_);
lean_inc(v_userName_1892_);
lean_inc(v_fvarId_1891_);
lean_dec(v_val_1862_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1912_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; 
v___x_1899_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_1893_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1899_);
lean_inc(v_snd_1871_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 3, v_a_1900_);
lean_ctor_set(v___x_1897_, 0, v_snd_1871_);
v___x_1902_ = v___x_1897_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_snd_1871_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_fvarId_1891_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_userName_1892_);
lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_a_1900_);
lean_ctor_set_uint8(v_reuseFailAlloc_1903_, sizeof(void*)*4, v_bi_1894_);
lean_ctor_set_uint8(v_reuseFailAlloc_1903_, sizeof(void*)*4 + 1, v_kind_1895_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
v_decl_1876_ = v___x_1902_;
goto v___jp_1875_;
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_del_object(v___x_1897_);
lean_dec(v_userName_1892_);
lean_dec(v_fvarId_1891_);
lean_del_object(v___x_1873_);
lean_dec(v_snd_1871_);
lean_dec(v_fst_1870_);
lean_del_object(v___x_1868_);
lean_dec(v_fst_1866_);
lean_del_object(v___x_1864_);
lean_del_object(v___x_1849_);
v_a_1904_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1899_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1899_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
else
{
lean_object* v_fvarId_1914_; lean_object* v_userName_1915_; lean_object* v_type_1916_; lean_object* v_value_1917_; uint8_t v_nondep_1918_; uint8_t v_kind_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1946_; 
v_fvarId_1914_ = lean_ctor_get(v_val_1862_, 1);
v_userName_1915_ = lean_ctor_get(v_val_1862_, 2);
v_type_1916_ = lean_ctor_get(v_val_1862_, 3);
v_value_1917_ = lean_ctor_get(v_val_1862_, 4);
v_nondep_1918_ = lean_ctor_get_uint8(v_val_1862_, sizeof(void*)*5);
v_kind_1919_ = lean_ctor_get_uint8(v_val_1862_, sizeof(void*)*5 + 1);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_val_1862_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; 
v_unused_1947_ = lean_ctor_get(v_val_1862_, 0);
lean_dec(v_unused_1947_);
v___x_1921_ = v_val_1862_;
v_isShared_1922_ = v_isSharedCheck_1946_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_value_1917_);
lean_inc(v_type_1916_);
lean_inc(v_userName_1915_);
lean_inc(v_fvarId_1914_);
lean_dec(v_val_1862_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1946_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; 
v___x_1923_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_1916_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref(v___x_1923_);
v___x_1925_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_1917_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref(v___x_1925_);
lean_inc(v_snd_1871_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 4, v_a_1926_);
lean_ctor_set(v___x_1921_, 3, v_a_1924_);
lean_ctor_set(v___x_1921_, 0, v_snd_1871_);
v___x_1928_ = v___x_1921_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_snd_1871_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_fvarId_1914_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_userName_1915_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v_a_1924_);
lean_ctor_set(v_reuseFailAlloc_1929_, 4, v_a_1926_);
lean_ctor_set_uint8(v_reuseFailAlloc_1929_, sizeof(void*)*5, v_nondep_1918_);
lean_ctor_set_uint8(v_reuseFailAlloc_1929_, sizeof(void*)*5 + 1, v_kind_1919_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
v_decl_1876_ = v___x_1928_;
goto v___jp_1875_;
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v_a_1924_);
lean_del_object(v___x_1921_);
lean_dec(v_userName_1915_);
lean_dec(v_fvarId_1914_);
lean_del_object(v___x_1873_);
lean_dec(v_snd_1871_);
lean_dec(v_fst_1870_);
lean_del_object(v___x_1868_);
lean_dec(v_fst_1866_);
lean_del_object(v___x_1864_);
lean_del_object(v___x_1849_);
v_a_1930_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1925_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1925_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_del_object(v___x_1921_);
lean_dec_ref(v_value_1917_);
lean_dec(v_userName_1915_);
lean_dec(v_fvarId_1914_);
lean_del_object(v___x_1873_);
lean_dec(v_snd_1871_);
lean_dec(v_fst_1870_);
lean_del_object(v___x_1868_);
lean_dec(v_fst_1866_);
lean_del_object(v___x_1864_);
lean_del_object(v___x_1849_);
v_a_1938_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1923_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1923_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
v___jp_1875_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1877_ = lean_unsigned_to_nat(1u);
v___x_1878_ = lean_nat_add(v_snd_1871_, v___x_1877_);
lean_dec(v_snd_1871_);
lean_inc_ref(v_decl_1876_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v_decl_1876_);
v___x_1880_ = v___x_1864_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_decl_1876_);
v___x_1880_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1881_ = l_Lean_PersistentArray_push___redArg(v_fst_1870_, v___x_1880_);
v___x_1882_ = l_Lean_LocalDecl_fvarId(v_decl_1876_);
v___x_1883_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_1866_, v___x_1882_, v_decl_1876_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 1, v___x_1878_);
lean_ctor_set(v___x_1873_, 0, v___x_1881_);
v___x_1885_ = v___x_1873_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v___x_1878_);
v___x_1885_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v___x_1885_);
lean_ctor_set(v___x_1868_, 0, v___x_1883_);
v___x_1887_ = v___x_1868_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
v_a_1853_ = v___x_1887_;
goto v___jp_1852_;
}
}
}
}
}
}
}
}
v___jp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v_a_1853_);
lean_ctor_set(v___x_1849_, 0, v___x_1851_);
v___x_1855_ = v___x_1849_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_a_1853_);
v___x_1855_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
size_t v___x_1856_; size_t v___x_1857_; 
v___x_1856_ = ((size_t)1ULL);
v___x_1857_ = lean_usize_add(v_i_1836_, v___x_1856_);
v_i_1836_ = v___x_1857_;
v_b_1837_ = v___x_1855_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_as_1954_, lean_object* v_sz_1955_, lean_object* v_i_1956_, lean_object* v_b_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
size_t v_sz_boxed_1965_; size_t v_i_boxed_1966_; lean_object* v_res_1967_; 
v_sz_boxed_1965_ = lean_unbox_usize(v_sz_1955_);
lean_dec(v_sz_1955_);
v_i_boxed_1966_ = lean_unbox_usize(v_i_1956_);
lean_dec(v_i_1956_);
v_res_1967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_1954_, v_sz_boxed_1965_, v_i_boxed_1966_, v_b_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec_ref(v_as_1954_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(lean_object* v_as_1968_, size_t v_sz_1969_, size_t v_i_1970_, lean_object* v_b_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_usize_dec_lt(v_i_1970_, v_sz_1969_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1980_, 0, v_b_1971_);
return v___x_1980_;
}
else
{
lean_object* v_snd_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2086_; 
v_snd_1981_ = lean_ctor_get(v_b_1971_, 1);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_b_1971_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v_b_1971_, 0);
lean_dec(v_unused_2087_);
v___x_1983_ = v_b_1971_;
v_isShared_1984_ = v_isSharedCheck_2086_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_snd_1981_);
lean_dec(v_b_1971_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2086_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v_a_1987_; lean_object* v_a_1994_; 
v___x_1985_ = lean_box(0);
v_a_1994_ = lean_array_uget(v_as_1968_, v_i_1970_);
if (lean_obj_tag(v_a_1994_) == 0)
{
v_a_1987_ = v_snd_1981_;
goto v___jp_1986_;
}
else
{
lean_object* v_snd_1995_; lean_object* v_val_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2085_; 
v_snd_1995_ = lean_ctor_get(v_snd_1981_, 1);
lean_inc(v_snd_1995_);
v_val_1996_ = lean_ctor_get(v_a_1994_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_a_1994_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_1998_ = v_a_1994_;
v_isShared_1999_ = v_isSharedCheck_2085_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_val_1996_);
lean_dec(v_a_1994_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2085_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v_fst_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2083_; 
v_fst_2000_ = lean_ctor_get(v_snd_1981_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_snd_1981_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v_snd_1981_, 1);
lean_dec(v_unused_2084_);
v___x_2002_ = v_snd_1981_;
v_isShared_2003_ = v_isSharedCheck_2083_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_fst_2000_);
lean_dec(v_snd_1981_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2083_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v_fst_2004_; lean_object* v_snd_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2082_; 
v_fst_2004_ = lean_ctor_get(v_snd_1995_, 0);
v_snd_2005_ = lean_ctor_get(v_snd_1995_, 1);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_snd_1995_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2007_ = v_snd_1995_;
v_isShared_2008_ = v_isSharedCheck_2082_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_snd_2005_);
lean_inc(v_fst_2004_);
lean_dec(v_snd_1995_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2082_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v_decl_2010_; 
if (lean_obj_tag(v_val_1996_) == 0)
{
lean_object* v_fvarId_2025_; lean_object* v_userName_2026_; lean_object* v_type_2027_; uint8_t v_bi_2028_; uint8_t v_kind_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2046_; 
v_fvarId_2025_ = lean_ctor_get(v_val_1996_, 1);
v_userName_2026_ = lean_ctor_get(v_val_1996_, 2);
v_type_2027_ = lean_ctor_get(v_val_1996_, 3);
v_bi_2028_ = lean_ctor_get_uint8(v_val_1996_, sizeof(void*)*4);
v_kind_2029_ = lean_ctor_get_uint8(v_val_1996_, sizeof(void*)*4 + 1);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_val_1996_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v_val_1996_, 0);
lean_dec(v_unused_2047_);
v___x_2031_ = v_val_1996_;
v_isShared_2032_ = v_isSharedCheck_2046_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_type_2027_);
lean_inc(v_userName_2026_);
lean_inc(v_fvarId_2025_);
lean_dec(v_val_1996_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2046_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; 
v___x_2033_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2027_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2036_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
lean_inc(v_snd_2005_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 3, v_a_2034_);
lean_ctor_set(v___x_2031_, 0, v_snd_2005_);
v___x_2036_ = v___x_2031_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_snd_2005_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_fvarId_2025_);
lean_ctor_set(v_reuseFailAlloc_2037_, 2, v_userName_2026_);
lean_ctor_set(v_reuseFailAlloc_2037_, 3, v_a_2034_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*4, v_bi_2028_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*4 + 1, v_kind_2029_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
v_decl_2010_ = v___x_2036_;
goto v___jp_2009_;
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_del_object(v___x_2031_);
lean_dec(v_userName_2026_);
lean_dec(v_fvarId_2025_);
lean_del_object(v___x_2007_);
lean_dec(v_snd_2005_);
lean_dec(v_fst_2004_);
lean_del_object(v___x_2002_);
lean_dec(v_fst_2000_);
lean_del_object(v___x_1998_);
lean_del_object(v___x_1983_);
v_a_2038_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2033_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2033_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
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
lean_object* v_fvarId_2048_; lean_object* v_userName_2049_; lean_object* v_type_2050_; lean_object* v_value_2051_; uint8_t v_nondep_2052_; uint8_t v_kind_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2080_; 
v_fvarId_2048_ = lean_ctor_get(v_val_1996_, 1);
v_userName_2049_ = lean_ctor_get(v_val_1996_, 2);
v_type_2050_ = lean_ctor_get(v_val_1996_, 3);
v_value_2051_ = lean_ctor_get(v_val_1996_, 4);
v_nondep_2052_ = lean_ctor_get_uint8(v_val_1996_, sizeof(void*)*5);
v_kind_2053_ = lean_ctor_get_uint8(v_val_1996_, sizeof(void*)*5 + 1);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_val_1996_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; 
v_unused_2081_ = lean_ctor_get(v_val_1996_, 0);
lean_dec(v_unused_2081_);
v___x_2055_ = v_val_1996_;
v_isShared_2056_ = v_isSharedCheck_2080_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_value_2051_);
lean_inc(v_type_2050_);
lean_inc(v_userName_2049_);
lean_inc(v_fvarId_2048_);
lean_dec(v_val_1996_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2080_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2057_; 
v___x_2057_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2050_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2059_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v___x_2057_);
v___x_2059_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2051_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2060_);
lean_dec_ref(v___x_2059_);
lean_inc(v_snd_2005_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 4, v_a_2060_);
lean_ctor_set(v___x_2055_, 3, v_a_2058_);
lean_ctor_set(v___x_2055_, 0, v_snd_2005_);
v___x_2062_ = v___x_2055_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_snd_2005_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_fvarId_2048_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v_userName_2049_);
lean_ctor_set(v_reuseFailAlloc_2063_, 3, v_a_2058_);
lean_ctor_set(v_reuseFailAlloc_2063_, 4, v_a_2060_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*5, v_nondep_2052_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*5 + 1, v_kind_2053_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
v_decl_2010_ = v___x_2062_;
goto v___jp_2009_;
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec(v_a_2058_);
lean_del_object(v___x_2055_);
lean_dec(v_userName_2049_);
lean_dec(v_fvarId_2048_);
lean_del_object(v___x_2007_);
lean_dec(v_snd_2005_);
lean_dec(v_fst_2004_);
lean_del_object(v___x_2002_);
lean_dec(v_fst_2000_);
lean_del_object(v___x_1998_);
lean_del_object(v___x_1983_);
v_a_2064_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2059_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2059_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_del_object(v___x_2055_);
lean_dec_ref(v_value_2051_);
lean_dec(v_userName_2049_);
lean_dec(v_fvarId_2048_);
lean_del_object(v___x_2007_);
lean_dec(v_snd_2005_);
lean_dec(v_fst_2004_);
lean_del_object(v___x_2002_);
lean_dec(v_fst_2000_);
lean_del_object(v___x_1998_);
lean_del_object(v___x_1983_);
v_a_2072_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2057_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2057_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
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
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
v___jp_2009_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2011_ = lean_unsigned_to_nat(1u);
v___x_2012_ = lean_nat_add(v_snd_2005_, v___x_2011_);
lean_dec(v_snd_2005_);
lean_inc_ref(v_decl_2010_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v_decl_2010_);
v___x_2014_ = v___x_1998_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_decl_2010_);
v___x_2014_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2015_ = l_Lean_PersistentArray_push___redArg(v_fst_2004_, v___x_2014_);
v___x_2016_ = l_Lean_LocalDecl_fvarId(v_decl_2010_);
v___x_2017_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2000_, v___x_2016_, v_decl_2010_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 1, v___x_2012_);
lean_ctor_set(v___x_2007_, 0, v___x_2015_);
v___x_2019_ = v___x_2007_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___x_2012_);
v___x_2019_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2021_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 1, v___x_2019_);
lean_ctor_set(v___x_2002_, 0, v___x_2017_);
v___x_2021_ = v___x_2002_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
v_a_1987_ = v___x_2021_;
goto v___jp_1986_;
}
}
}
}
}
}
}
}
v___jp_1986_:
{
lean_object* v___x_1989_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 1, v_a_1987_);
lean_ctor_set(v___x_1983_, 0, v___x_1985_);
v___x_1989_ = v___x_1983_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_a_1987_);
v___x_1989_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
size_t v___x_1990_; size_t v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = ((size_t)1ULL);
v___x_1991_ = lean_usize_add(v_i_1970_, v___x_1990_);
v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_1968_, v_sz_1969_, v___x_1991_, v___x_1989_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
return v___x_1992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6___boxed(lean_object* v_as_2088_, lean_object* v_sz_2089_, lean_object* v_i_2090_, lean_object* v_b_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
size_t v_sz_boxed_2099_; size_t v_i_boxed_2100_; lean_object* v_res_2101_; 
v_sz_boxed_2099_ = lean_unbox_usize(v_sz_2089_);
lean_dec(v_sz_2089_);
v_i_boxed_2100_ = lean_unbox_usize(v_i_2090_);
lean_dec(v_i_2090_);
v_res_2101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_as_2088_, v_sz_boxed_2099_, v_i_boxed_2100_, v_b_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec_ref(v_as_2088_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(lean_object* v_init_2102_, lean_object* v_n_2103_, lean_object* v_b_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
if (lean_obj_tag(v_n_2103_) == 0)
{
lean_object* v_cs_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2146_; 
v_cs_2112_ = lean_ctor_get(v_n_2103_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_n_2103_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2114_ = v_n_2103_;
v_isShared_2115_ = v_isSharedCheck_2146_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_cs_2112_);
lean_dec(v_n_2103_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2146_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; size_t v_sz_2118_; size_t v___x_2119_; lean_object* v___x_2120_; 
v___x_2116_ = lean_box(0);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
lean_ctor_set(v___x_2117_, 1, v_b_2104_);
v_sz_2118_ = lean_array_size(v_cs_2112_);
v___x_2119_ = ((size_t)0ULL);
v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_2102_, v_cs_2112_, v_sz_2118_, v___x_2119_, v___x_2117_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec_ref(v_cs_2112_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2137_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2137_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2137_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v_fst_2125_; 
v_fst_2125_ = lean_ctor_get(v_a_2121_, 0);
if (lean_obj_tag(v_fst_2125_) == 0)
{
lean_object* v_snd_2126_; lean_object* v___x_2128_; 
v_snd_2126_ = lean_ctor_get(v_a_2121_, 1);
lean_inc(v_snd_2126_);
lean_dec(v_a_2121_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set_tag(v___x_2114_, 1);
lean_ctor_set(v___x_2114_, 0, v_snd_2126_);
v___x_2128_ = v___x_2114_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_snd_2126_);
v___x_2128_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2130_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2128_);
v___x_2130_ = v___x_2123_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
else
{
lean_object* v_val_2133_; lean_object* v___x_2135_; 
lean_inc_ref(v_fst_2125_);
lean_dec(v_a_2121_);
lean_del_object(v___x_2114_);
v_val_2133_ = lean_ctor_get(v_fst_2125_, 0);
lean_inc(v_val_2133_);
lean_dec_ref(v_fst_2125_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v_val_2133_);
v___x_2135_ = v___x_2123_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_val_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_del_object(v___x_2114_);
v_a_2138_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2120_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2120_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
else
{
lean_object* v_vs_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2181_; 
v_vs_2147_ = lean_ctor_get(v_n_2103_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_n_2103_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2149_ = v_n_2103_;
v_isShared_2150_ = v_isSharedCheck_2181_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_vs_2147_);
lean_dec(v_n_2103_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2181_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; size_t v_sz_2153_; size_t v___x_2154_; lean_object* v___x_2155_; 
v___x_2151_ = lean_box(0);
v___x_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v_b_2104_);
v_sz_2153_ = lean_array_size(v_vs_2147_);
v___x_2154_ = ((size_t)0ULL);
v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_vs_2147_, v_sz_2153_, v___x_2154_, v___x_2152_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec_ref(v_vs_2147_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2172_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2172_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2172_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v_fst_2160_; 
v_fst_2160_ = lean_ctor_get(v_a_2156_, 0);
if (lean_obj_tag(v_fst_2160_) == 0)
{
lean_object* v_snd_2161_; lean_object* v___x_2163_; 
v_snd_2161_ = lean_ctor_get(v_a_2156_, 1);
lean_inc(v_snd_2161_);
lean_dec(v_a_2156_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v_snd_2161_);
v___x_2163_ = v___x_2149_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_snd_2161_);
v___x_2163_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2165_; 
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2163_);
v___x_2165_ = v___x_2158_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
else
{
lean_object* v_val_2168_; lean_object* v___x_2170_; 
lean_inc_ref(v_fst_2160_);
lean_dec(v_a_2156_);
lean_del_object(v___x_2149_);
v_val_2168_ = lean_ctor_get(v_fst_2160_, 0);
lean_inc(v_val_2168_);
lean_dec_ref(v_fst_2160_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v_val_2168_);
v___x_2170_ = v___x_2158_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_val_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_del_object(v___x_2149_);
v_a_2173_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2155_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2155_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(lean_object* v_init_2182_, lean_object* v_as_2183_, size_t v_sz_2184_, size_t v_i_2185_, lean_object* v_b_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
uint8_t v___x_2194_; 
v___x_2194_ = lean_usize_dec_lt(v_i_2185_, v_sz_2184_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v_b_2186_);
return v___x_2195_;
}
else
{
lean_object* v_snd_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2230_; 
v_snd_2196_ = lean_ctor_get(v_b_2186_, 1);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_b_2186_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v_b_2186_, 0);
lean_dec(v_unused_2231_);
v___x_2198_ = v_b_2186_;
v_isShared_2199_ = v_isSharedCheck_2230_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_snd_2196_);
lean_dec(v_b_2186_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2230_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v_a_2200_; lean_object* v___x_2201_; 
v_a_2200_ = lean_array_uget_borrowed(v_as_2183_, v_i_2185_);
lean_inc(v_snd_2196_);
lean_inc(v_a_2200_);
v___x_2201_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_2182_, v_a_2200_, v_snd_2196_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2221_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2221_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2221_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
if (lean_obj_tag(v_a_2202_) == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2206_, 0, v_a_2202_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v___x_2206_);
v___x_2208_ = v___x_2198_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2206_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v_snd_2196_);
v___x_2208_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
lean_object* v___x_2210_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2208_);
v___x_2210_ = v___x_2204_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2214_; lean_object* v___x_2216_; 
lean_del_object(v___x_2204_);
lean_dec(v_snd_2196_);
v_a_2213_ = lean_ctor_get(v_a_2202_, 0);
lean_inc(v_a_2213_);
lean_dec_ref(v_a_2202_);
v___x_2214_ = lean_box(0);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 1, v_a_2213_);
lean_ctor_set(v___x_2198_, 0, v___x_2214_);
v___x_2216_ = v___x_2198_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_a_2213_);
v___x_2216_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
size_t v___x_2217_; size_t v___x_2218_; 
v___x_2217_ = ((size_t)1ULL);
v___x_2218_ = lean_usize_add(v_i_2185_, v___x_2217_);
v_i_2185_ = v___x_2218_;
v_b_2186_ = v___x_2216_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_del_object(v___x_2198_);
lean_dec(v_snd_2196_);
v_a_2222_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2201_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2201_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_init_2232_, lean_object* v_as_2233_, lean_object* v_sz_2234_, lean_object* v_i_2235_, lean_object* v_b_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
size_t v_sz_boxed_2244_; size_t v_i_boxed_2245_; lean_object* v_res_2246_; 
v_sz_boxed_2244_ = lean_unbox_usize(v_sz_2234_);
lean_dec(v_sz_2234_);
v_i_boxed_2245_ = lean_unbox_usize(v_i_2235_);
lean_dec(v_i_2235_);
v_res_2246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_2232_, v_as_2233_, v_sz_boxed_2244_, v_i_boxed_2245_, v_b_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v_as_2233_);
lean_dec_ref(v_init_2232_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2___boxed(lean_object* v_init_2247_, lean_object* v_n_2248_, lean_object* v_b_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_2247_, v_n_2248_, v_b_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec_ref(v_init_2247_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(lean_object* v_as_2258_, size_t v_sz_2259_, size_t v_i_2260_, lean_object* v_b_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
uint8_t v___x_2269_; 
v___x_2269_ = lean_usize_dec_lt(v_i_2260_, v_sz_2259_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; 
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v_b_2261_);
return v___x_2270_;
}
else
{
lean_object* v_snd_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2376_; 
v_snd_2271_ = lean_ctor_get(v_b_2261_, 1);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_b_2261_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v_b_2261_, 0);
lean_dec(v_unused_2377_);
v___x_2273_ = v_b_2261_;
v_isShared_2274_ = v_isSharedCheck_2376_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_snd_2271_);
lean_dec(v_b_2261_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2376_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v_a_2277_; lean_object* v_a_2284_; 
v___x_2275_ = lean_box(0);
v_a_2284_ = lean_array_uget(v_as_2258_, v_i_2260_);
if (lean_obj_tag(v_a_2284_) == 0)
{
v_a_2277_ = v_snd_2271_;
goto v___jp_2276_;
}
else
{
lean_object* v_snd_2285_; lean_object* v_val_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2375_; 
v_snd_2285_ = lean_ctor_get(v_snd_2271_, 1);
lean_inc(v_snd_2285_);
v_val_2286_ = lean_ctor_get(v_a_2284_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_a_2284_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2288_ = v_a_2284_;
v_isShared_2289_ = v_isSharedCheck_2375_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_val_2286_);
lean_dec(v_a_2284_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2375_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v_fst_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2373_; 
v_fst_2290_ = lean_ctor_get(v_snd_2271_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_snd_2271_);
if (v_isSharedCheck_2373_ == 0)
{
lean_object* v_unused_2374_; 
v_unused_2374_ = lean_ctor_get(v_snd_2271_, 1);
lean_dec(v_unused_2374_);
v___x_2292_ = v_snd_2271_;
v_isShared_2293_ = v_isSharedCheck_2373_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_fst_2290_);
lean_dec(v_snd_2271_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2373_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v_fst_2294_; lean_object* v_snd_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2372_; 
v_fst_2294_ = lean_ctor_get(v_snd_2285_, 0);
v_snd_2295_ = lean_ctor_get(v_snd_2285_, 1);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_snd_2285_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2297_ = v_snd_2285_;
v_isShared_2298_ = v_isSharedCheck_2372_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_snd_2295_);
lean_inc(v_fst_2294_);
lean_dec(v_snd_2285_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2372_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v_decl_2300_; 
if (lean_obj_tag(v_val_2286_) == 0)
{
lean_object* v_fvarId_2315_; lean_object* v_userName_2316_; lean_object* v_type_2317_; uint8_t v_bi_2318_; uint8_t v_kind_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2336_; 
v_fvarId_2315_ = lean_ctor_get(v_val_2286_, 1);
v_userName_2316_ = lean_ctor_get(v_val_2286_, 2);
v_type_2317_ = lean_ctor_get(v_val_2286_, 3);
v_bi_2318_ = lean_ctor_get_uint8(v_val_2286_, sizeof(void*)*4);
v_kind_2319_ = lean_ctor_get_uint8(v_val_2286_, sizeof(void*)*4 + 1);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_val_2286_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; 
v_unused_2337_ = lean_ctor_get(v_val_2286_, 0);
lean_dec(v_unused_2337_);
v___x_2321_ = v_val_2286_;
v_isShared_2322_ = v_isSharedCheck_2336_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_type_2317_);
lean_inc(v_userName_2316_);
lean_inc(v_fvarId_2315_);
lean_dec(v_val_2286_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2336_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; 
v___x_2323_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2317_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2326_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref(v___x_2323_);
lean_inc(v_snd_2295_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 3, v_a_2324_);
lean_ctor_set(v___x_2321_, 0, v_snd_2295_);
v___x_2326_ = v___x_2321_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_snd_2295_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_fvarId_2315_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_userName_2316_);
lean_ctor_set(v_reuseFailAlloc_2327_, 3, v_a_2324_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*4, v_bi_2318_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*4 + 1, v_kind_2319_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
v_decl_2300_ = v___x_2326_;
goto v___jp_2299_;
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_del_object(v___x_2321_);
lean_dec(v_userName_2316_);
lean_dec(v_fvarId_2315_);
lean_del_object(v___x_2297_);
lean_dec(v_snd_2295_);
lean_dec(v_fst_2294_);
lean_del_object(v___x_2292_);
lean_dec(v_fst_2290_);
lean_del_object(v___x_2288_);
lean_del_object(v___x_2273_);
v_a_2328_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2323_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2323_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2338_; lean_object* v_userName_2339_; lean_object* v_type_2340_; lean_object* v_value_2341_; uint8_t v_nondep_2342_; uint8_t v_kind_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2370_; 
v_fvarId_2338_ = lean_ctor_get(v_val_2286_, 1);
v_userName_2339_ = lean_ctor_get(v_val_2286_, 2);
v_type_2340_ = lean_ctor_get(v_val_2286_, 3);
v_value_2341_ = lean_ctor_get(v_val_2286_, 4);
v_nondep_2342_ = lean_ctor_get_uint8(v_val_2286_, sizeof(void*)*5);
v_kind_2343_ = lean_ctor_get_uint8(v_val_2286_, sizeof(void*)*5 + 1);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_val_2286_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; 
v_unused_2371_ = lean_ctor_get(v_val_2286_, 0);
lean_dec(v_unused_2371_);
v___x_2345_ = v_val_2286_;
v_isShared_2346_ = v_isSharedCheck_2370_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_value_2341_);
lean_inc(v_type_2340_);
lean_inc(v_userName_2339_);
lean_inc(v_fvarId_2338_);
lean_dec(v_val_2286_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2370_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; 
v___x_2347_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2340_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2349_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref(v___x_2347_);
v___x_2349_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2341_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2352_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref(v___x_2349_);
lean_inc(v_snd_2295_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 4, v_a_2350_);
lean_ctor_set(v___x_2345_, 3, v_a_2348_);
lean_ctor_set(v___x_2345_, 0, v_snd_2295_);
v___x_2352_ = v___x_2345_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_snd_2295_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_fvarId_2338_);
lean_ctor_set(v_reuseFailAlloc_2353_, 2, v_userName_2339_);
lean_ctor_set(v_reuseFailAlloc_2353_, 3, v_a_2348_);
lean_ctor_set(v_reuseFailAlloc_2353_, 4, v_a_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2353_, sizeof(void*)*5, v_nondep_2342_);
lean_ctor_set_uint8(v_reuseFailAlloc_2353_, sizeof(void*)*5 + 1, v_kind_2343_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
v_decl_2300_ = v___x_2352_;
goto v___jp_2299_;
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v_a_2348_);
lean_del_object(v___x_2345_);
lean_dec(v_userName_2339_);
lean_dec(v_fvarId_2338_);
lean_del_object(v___x_2297_);
lean_dec(v_snd_2295_);
lean_dec(v_fst_2294_);
lean_del_object(v___x_2292_);
lean_dec(v_fst_2290_);
lean_del_object(v___x_2288_);
lean_del_object(v___x_2273_);
v_a_2354_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2349_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2349_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_del_object(v___x_2345_);
lean_dec_ref(v_value_2341_);
lean_dec(v_userName_2339_);
lean_dec(v_fvarId_2338_);
lean_del_object(v___x_2297_);
lean_dec(v_snd_2295_);
lean_dec(v_fst_2294_);
lean_del_object(v___x_2292_);
lean_dec(v_fst_2290_);
lean_del_object(v___x_2288_);
lean_del_object(v___x_2273_);
v_a_2362_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2347_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2347_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
v___jp_2299_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2301_ = lean_unsigned_to_nat(1u);
v___x_2302_ = lean_nat_add(v_snd_2295_, v___x_2301_);
lean_dec(v_snd_2295_);
lean_inc_ref(v_decl_2300_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v_decl_2300_);
v___x_2304_ = v___x_2288_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_decl_2300_);
v___x_2304_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2305_ = l_Lean_PersistentArray_push___redArg(v_fst_2294_, v___x_2304_);
v___x_2306_ = l_Lean_LocalDecl_fvarId(v_decl_2300_);
v___x_2307_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2290_, v___x_2306_, v_decl_2300_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 1, v___x_2302_);
lean_ctor_set(v___x_2297_, 0, v___x_2305_);
v___x_2309_ = v___x_2297_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v___x_2302_);
v___x_2309_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2311_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 1, v___x_2309_);
lean_ctor_set(v___x_2292_, 0, v___x_2307_);
v___x_2311_ = v___x_2292_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
v_a_2277_ = v___x_2311_;
goto v___jp_2276_;
}
}
}
}
}
}
}
}
v___jp_2276_:
{
lean_object* v___x_2279_; 
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 1, v_a_2277_);
lean_ctor_set(v___x_2273_, 0, v___x_2275_);
v___x_2279_ = v___x_2273_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_a_2277_);
v___x_2279_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
size_t v___x_2280_; size_t v___x_2281_; 
v___x_2280_ = ((size_t)1ULL);
v___x_2281_ = lean_usize_add(v_i_2260_, v___x_2280_);
v_i_2260_ = v___x_2281_;
v_b_2261_ = v___x_2279_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8___boxed(lean_object* v_as_2378_, lean_object* v_sz_2379_, lean_object* v_i_2380_, lean_object* v_b_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
size_t v_sz_boxed_2389_; size_t v_i_boxed_2390_; lean_object* v_res_2391_; 
v_sz_boxed_2389_ = lean_unbox_usize(v_sz_2379_);
lean_dec(v_sz_2379_);
v_i_boxed_2390_ = lean_unbox_usize(v_i_2380_);
lean_dec(v_i_2380_);
v_res_2391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_2378_, v_sz_boxed_2389_, v_i_boxed_2390_, v_b_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec_ref(v_as_2378_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(lean_object* v_as_2392_, size_t v_sz_2393_, size_t v_i_2394_, lean_object* v_b_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
uint8_t v___x_2403_; 
v___x_2403_ = lean_usize_dec_lt(v_i_2394_, v_sz_2393_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2404_, 0, v_b_2395_);
return v___x_2404_;
}
else
{
lean_object* v_snd_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2510_; 
v_snd_2405_ = lean_ctor_get(v_b_2395_, 1);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_b_2395_);
if (v_isSharedCheck_2510_ == 0)
{
lean_object* v_unused_2511_; 
v_unused_2511_ = lean_ctor_get(v_b_2395_, 0);
lean_dec(v_unused_2511_);
v___x_2407_ = v_b_2395_;
v_isShared_2408_ = v_isSharedCheck_2510_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_snd_2405_);
lean_dec(v_b_2395_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2510_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2409_; lean_object* v_a_2411_; lean_object* v_a_2418_; 
v___x_2409_ = lean_box(0);
v_a_2418_ = lean_array_uget(v_as_2392_, v_i_2394_);
if (lean_obj_tag(v_a_2418_) == 0)
{
v_a_2411_ = v_snd_2405_;
goto v___jp_2410_;
}
else
{
lean_object* v_snd_2419_; lean_object* v_val_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2509_; 
v_snd_2419_ = lean_ctor_get(v_snd_2405_, 1);
lean_inc(v_snd_2419_);
v_val_2420_ = lean_ctor_get(v_a_2418_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v_a_2418_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2422_ = v_a_2418_;
v_isShared_2423_ = v_isSharedCheck_2509_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_val_2420_);
lean_dec(v_a_2418_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2509_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v_fst_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2507_; 
v_fst_2424_ = lean_ctor_get(v_snd_2405_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_snd_2405_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; 
v_unused_2508_ = lean_ctor_get(v_snd_2405_, 1);
lean_dec(v_unused_2508_);
v___x_2426_ = v_snd_2405_;
v_isShared_2427_ = v_isSharedCheck_2507_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_fst_2424_);
lean_dec(v_snd_2405_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2507_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_fst_2428_; lean_object* v_snd_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2506_; 
v_fst_2428_ = lean_ctor_get(v_snd_2419_, 0);
v_snd_2429_ = lean_ctor_get(v_snd_2419_, 1);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_snd_2419_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2431_ = v_snd_2419_;
v_isShared_2432_ = v_isSharedCheck_2506_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_snd_2429_);
lean_inc(v_fst_2428_);
lean_dec(v_snd_2419_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2506_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v_decl_2434_; 
if (lean_obj_tag(v_val_2420_) == 0)
{
lean_object* v_fvarId_2449_; lean_object* v_userName_2450_; lean_object* v_type_2451_; uint8_t v_bi_2452_; uint8_t v_kind_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2470_; 
v_fvarId_2449_ = lean_ctor_get(v_val_2420_, 1);
v_userName_2450_ = lean_ctor_get(v_val_2420_, 2);
v_type_2451_ = lean_ctor_get(v_val_2420_, 3);
v_bi_2452_ = lean_ctor_get_uint8(v_val_2420_, sizeof(void*)*4);
v_kind_2453_ = lean_ctor_get_uint8(v_val_2420_, sizeof(void*)*4 + 1);
v_isSharedCheck_2470_ = !lean_is_exclusive(v_val_2420_);
if (v_isSharedCheck_2470_ == 0)
{
lean_object* v_unused_2471_; 
v_unused_2471_ = lean_ctor_get(v_val_2420_, 0);
lean_dec(v_unused_2471_);
v___x_2455_ = v_val_2420_;
v_isShared_2456_ = v_isSharedCheck_2470_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_type_2451_);
lean_inc(v_userName_2450_);
lean_inc(v_fvarId_2449_);
lean_dec(v_val_2420_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2470_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; 
v___x_2457_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2451_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2460_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref(v___x_2457_);
lean_inc(v_snd_2429_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 3, v_a_2458_);
lean_ctor_set(v___x_2455_, 0, v_snd_2429_);
v___x_2460_ = v___x_2455_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_snd_2429_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_fvarId_2449_);
lean_ctor_set(v_reuseFailAlloc_2461_, 2, v_userName_2450_);
lean_ctor_set(v_reuseFailAlloc_2461_, 3, v_a_2458_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, sizeof(void*)*4, v_bi_2452_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, sizeof(void*)*4 + 1, v_kind_2453_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
v_decl_2434_ = v___x_2460_;
goto v___jp_2433_;
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_del_object(v___x_2455_);
lean_dec(v_userName_2450_);
lean_dec(v_fvarId_2449_);
lean_del_object(v___x_2431_);
lean_dec(v_snd_2429_);
lean_dec(v_fst_2428_);
lean_del_object(v___x_2426_);
lean_dec(v_fst_2424_);
lean_del_object(v___x_2422_);
lean_del_object(v___x_2407_);
v_a_2462_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2457_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2457_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2472_; lean_object* v_userName_2473_; lean_object* v_type_2474_; lean_object* v_value_2475_; uint8_t v_nondep_2476_; uint8_t v_kind_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2504_; 
v_fvarId_2472_ = lean_ctor_get(v_val_2420_, 1);
v_userName_2473_ = lean_ctor_get(v_val_2420_, 2);
v_type_2474_ = lean_ctor_get(v_val_2420_, 3);
v_value_2475_ = lean_ctor_get(v_val_2420_, 4);
v_nondep_2476_ = lean_ctor_get_uint8(v_val_2420_, sizeof(void*)*5);
v_kind_2477_ = lean_ctor_get_uint8(v_val_2420_, sizeof(void*)*5 + 1);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_val_2420_);
if (v_isSharedCheck_2504_ == 0)
{
lean_object* v_unused_2505_; 
v_unused_2505_ = lean_ctor_get(v_val_2420_, 0);
lean_dec(v_unused_2505_);
v___x_2479_ = v_val_2420_;
v_isShared_2480_ = v_isSharedCheck_2504_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_value_2475_);
lean_inc(v_type_2474_);
lean_inc(v_userName_2473_);
lean_inc(v_fvarId_2472_);
lean_dec(v_val_2420_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2504_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; 
v___x_2481_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2474_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2483_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref(v___x_2481_);
v___x_2483_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2475_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref(v___x_2483_);
lean_inc(v_snd_2429_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 4, v_a_2484_);
lean_ctor_set(v___x_2479_, 3, v_a_2482_);
lean_ctor_set(v___x_2479_, 0, v_snd_2429_);
v___x_2486_ = v___x_2479_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_snd_2429_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_fvarId_2472_);
lean_ctor_set(v_reuseFailAlloc_2487_, 2, v_userName_2473_);
lean_ctor_set(v_reuseFailAlloc_2487_, 3, v_a_2482_);
lean_ctor_set(v_reuseFailAlloc_2487_, 4, v_a_2484_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, sizeof(void*)*5, v_nondep_2476_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, sizeof(void*)*5 + 1, v_kind_2477_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
v_decl_2434_ = v___x_2486_;
goto v___jp_2433_;
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v_a_2482_);
lean_del_object(v___x_2479_);
lean_dec(v_userName_2473_);
lean_dec(v_fvarId_2472_);
lean_del_object(v___x_2431_);
lean_dec(v_snd_2429_);
lean_dec(v_fst_2428_);
lean_del_object(v___x_2426_);
lean_dec(v_fst_2424_);
lean_del_object(v___x_2422_);
lean_del_object(v___x_2407_);
v_a_2488_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2483_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2483_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_del_object(v___x_2479_);
lean_dec_ref(v_value_2475_);
lean_dec(v_userName_2473_);
lean_dec(v_fvarId_2472_);
lean_del_object(v___x_2431_);
lean_dec(v_snd_2429_);
lean_dec(v_fst_2428_);
lean_del_object(v___x_2426_);
lean_dec(v_fst_2424_);
lean_del_object(v___x_2422_);
lean_del_object(v___x_2407_);
v_a_2496_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2481_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2481_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
v___jp_2433_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2435_ = lean_unsigned_to_nat(1u);
v___x_2436_ = lean_nat_add(v_snd_2429_, v___x_2435_);
lean_dec(v_snd_2429_);
lean_inc_ref(v_decl_2434_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v_decl_2434_);
v___x_2438_ = v___x_2422_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_decl_2434_);
v___x_2438_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2439_ = l_Lean_PersistentArray_push___redArg(v_fst_2428_, v___x_2438_);
v___x_2440_ = l_Lean_LocalDecl_fvarId(v_decl_2434_);
v___x_2441_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2424_, v___x_2440_, v_decl_2434_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 1, v___x_2436_);
lean_ctor_set(v___x_2431_, 0, v___x_2439_);
v___x_2443_ = v___x_2431_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2447_, 1, v___x_2436_);
v___x_2443_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2445_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v___x_2443_);
lean_ctor_set(v___x_2426_, 0, v___x_2441_);
v___x_2445_ = v___x_2426_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
v_a_2411_ = v___x_2445_;
goto v___jp_2410_;
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
lean_object* v___x_2413_; 
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 1, v_a_2411_);
lean_ctor_set(v___x_2407_, 0, v___x_2409_);
v___x_2413_ = v___x_2407_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2409_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_a_2411_);
v___x_2413_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
size_t v___x_2414_; size_t v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = ((size_t)1ULL);
v___x_2415_ = lean_usize_add(v_i_2394_, v___x_2414_);
v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_2392_, v_sz_2393_, v___x_2415_, v___x_2413_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
return v___x_2416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3___boxed(lean_object* v_as_2512_, lean_object* v_sz_2513_, lean_object* v_i_2514_, lean_object* v_b_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
size_t v_sz_boxed_2523_; size_t v_i_boxed_2524_; lean_object* v_res_2525_; 
v_sz_boxed_2523_ = lean_unbox_usize(v_sz_2513_);
lean_dec(v_sz_2513_);
v_i_boxed_2524_ = lean_unbox_usize(v_i_2514_);
lean_dec(v_i_2514_);
v_res_2525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_as_2512_, v_sz_boxed_2523_, v_i_boxed_2524_, v_b_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec_ref(v_as_2512_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(lean_object* v_t_2526_, lean_object* v_init_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_root_2535_; lean_object* v_tail_2536_; lean_object* v___x_2537_; 
v_root_2535_ = lean_ctor_get(v_t_2526_, 0);
lean_inc_ref(v_root_2535_);
v_tail_2536_ = lean_ctor_get(v_t_2526_, 1);
lean_inc_ref(v_tail_2536_);
lean_dec_ref(v_t_2526_);
lean_inc_ref(v_init_2527_);
v___x_2537_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_2527_, v_root_2535_, v_init_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
lean_dec_ref(v_init_2527_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2574_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2574_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2574_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
if (lean_obj_tag(v_a_2538_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2544_; 
lean_dec_ref(v_tail_2536_);
v_a_2542_ = lean_ctor_get(v_a_2538_, 0);
lean_inc(v_a_2542_);
lean_dec_ref(v_a_2538_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v_a_2542_);
v___x_2544_ = v___x_2540_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2542_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; size_t v_sz_2549_; size_t v___x_2550_; lean_object* v___x_2551_; 
lean_del_object(v___x_2540_);
v_a_2546_ = lean_ctor_get(v_a_2538_, 0);
lean_inc(v_a_2546_);
lean_dec_ref(v_a_2538_);
v___x_2547_ = lean_box(0);
v___x_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
lean_ctor_set(v___x_2548_, 1, v_a_2546_);
v_sz_2549_ = lean_array_size(v_tail_2536_);
v___x_2550_ = ((size_t)0ULL);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_tail_2536_, v_sz_2549_, v___x_2550_, v___x_2548_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
lean_dec_ref(v_tail_2536_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2565_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2565_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2565_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v_fst_2556_; 
v_fst_2556_ = lean_ctor_get(v_a_2552_, 0);
if (lean_obj_tag(v_fst_2556_) == 0)
{
lean_object* v_snd_2557_; lean_object* v___x_2559_; 
v_snd_2557_ = lean_ctor_get(v_a_2552_, 1);
lean_inc(v_snd_2557_);
lean_dec(v_a_2552_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v_snd_2557_);
v___x_2559_ = v___x_2554_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_snd_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
else
{
lean_object* v_val_2561_; lean_object* v___x_2563_; 
lean_inc_ref(v_fst_2556_);
lean_dec(v_a_2552_);
v_val_2561_ = lean_ctor_get(v_fst_2556_, 0);
lean_inc(v_val_2561_);
lean_dec_ref(v_fst_2556_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v_val_2561_);
v___x_2563_ = v___x_2554_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_val_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
v_a_2566_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2551_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2551_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
lean_dec_ref(v_tail_2536_);
v_a_2575_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2537_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2537_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1___boxed(lean_object* v_t_2583_, lean_object* v_init_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_t_2583_, v_init_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
return v_res_2592_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_unsigned_to_nat(32u);
v___x_2594_ = lean_mk_empty_array_with_capacity(v___x_2593_);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1(void){
_start:
{
size_t v___x_2596_; lean_object* v_index_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v_decls_2601_; 
v___x_2596_ = ((size_t)5ULL);
v_index_2597_ = lean_unsigned_to_nat(0u);
v___x_2598_ = lean_unsigned_to_nat(32u);
v___x_2599_ = lean_mk_empty_array_with_capacity(v___x_2598_);
v___x_2600_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0);
v_decls_2601_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_decls_2601_, 0, v___x_2600_);
lean_ctor_set(v_decls_2601_, 1, v___x_2599_);
lean_ctor_set(v_decls_2601_, 2, v_index_2597_);
lean_ctor_set(v_decls_2601_, 3, v_index_2597_);
lean_ctor_set_usize(v_decls_2601_, 4, v___x_2596_);
return v_decls_2601_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2(void){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2602_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3(void){
_start:
{
lean_object* v___x_2603_; lean_object* v_fvarIdToDecl_2604_; 
v___x_2603_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2);
v_fvarIdToDecl_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fvarIdToDecl_2604_, 0, v___x_2603_);
return v_fvarIdToDecl_2604_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4(void){
_start:
{
lean_object* v_index_2605_; lean_object* v_decls_2606_; lean_object* v___x_2607_; 
v_index_2605_ = lean_unsigned_to_nat(0u);
v_decls_2606_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1);
v___x_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2607_, 0, v_decls_2606_);
lean_ctor_set(v___x_2607_, 1, v_index_2605_);
return v___x_2607_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5(void){
_start:
{
lean_object* v___x_2608_; lean_object* v_fvarIdToDecl_2609_; lean_object* v___x_2610_; 
v___x_2608_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4);
v_fvarIdToDecl_2609_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3);
v___x_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2610_, 0, v_fvarIdToDecl_2609_);
lean_ctor_set(v___x_2610_, 1, v___x_2608_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(lean_object* v_lctx_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_){
_start:
{
lean_object* v_decls_2619_; lean_object* v_auxDeclToFullName_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2648_; 
v_decls_2619_ = lean_ctor_get(v_lctx_2611_, 1);
v_auxDeclToFullName_2620_ = lean_ctor_get(v_lctx_2611_, 2);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_lctx_2611_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; 
v_unused_2649_ = lean_ctor_get(v_lctx_2611_, 0);
lean_dec(v_unused_2649_);
v___x_2622_ = v_lctx_2611_;
v_isShared_2623_ = v_isSharedCheck_2648_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_auxDeclToFullName_2620_);
lean_inc(v_decls_2619_);
lean_dec(v_lctx_2611_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2648_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5);
v___x_2625_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_decls_2619_, v___x_2624_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2639_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2639_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2639_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v_snd_2630_; lean_object* v_fst_2631_; lean_object* v_fst_2632_; lean_object* v___x_2634_; 
v_snd_2630_ = lean_ctor_get(v_a_2626_, 1);
lean_inc(v_snd_2630_);
v_fst_2631_ = lean_ctor_get(v_a_2626_, 0);
lean_inc(v_fst_2631_);
lean_dec(v_a_2626_);
v_fst_2632_ = lean_ctor_get(v_snd_2630_, 0);
lean_inc(v_fst_2632_);
lean_dec(v_snd_2630_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 1, v_fst_2632_);
lean_ctor_set(v___x_2622_, 0, v_fst_2631_);
v___x_2634_ = v___x_2622_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_fst_2631_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_fst_2632_);
lean_ctor_set(v_reuseFailAlloc_2638_, 2, v_auxDeclToFullName_2620_);
v___x_2634_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2636_; 
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v___x_2634_);
v___x_2636_ = v___x_2628_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_del_object(v___x_2622_);
lean_dec(v_auxDeclToFullName_2620_);
v_a_2640_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2625_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2625_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___boxed(lean_object* v_lctx_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0(lean_object* v_00_u03b2_2659_, lean_object* v_x_2660_, lean_object* v_x_2661_, lean_object* v_x_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_x_2660_, v_x_2661_, v_x_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(lean_object* v_00_u03b2_2664_, lean_object* v_x_2665_, size_t v_x_2666_, size_t v_x_2667_, lean_object* v_x_2668_, lean_object* v_x_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_2665_, v_x_2666_, v_x_2667_, v_x_2668_, v_x_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2671_, lean_object* v_x_2672_, lean_object* v_x_2673_, lean_object* v_x_2674_, lean_object* v_x_2675_, lean_object* v_x_2676_){
_start:
{
size_t v_x_10766__boxed_2677_; size_t v_x_10767__boxed_2678_; lean_object* v_res_2679_; 
v_x_10766__boxed_2677_ = lean_unbox_usize(v_x_2673_);
lean_dec(v_x_2673_);
v_x_10767__boxed_2678_ = lean_unbox_usize(v_x_2674_);
lean_dec(v_x_2674_);
v_res_2679_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(v_00_u03b2_2671_, v_x_2672_, v_x_10766__boxed_2677_, v_x_10767__boxed_2678_, v_x_2675_, v_x_2676_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2680_, lean_object* v_n_2681_, lean_object* v_k_2682_, lean_object* v_v_2683_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v_n_2681_, v_k_2682_, v_v_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2685_, size_t v_depth_2686_, lean_object* v_keys_2687_, lean_object* v_vals_2688_, lean_object* v_heq_2689_, lean_object* v_i_2690_, lean_object* v_entries_2691_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_2686_, v_keys_2687_, v_vals_2688_, v_i_2690_, v_entries_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2693_, lean_object* v_depth_2694_, lean_object* v_keys_2695_, lean_object* v_vals_2696_, lean_object* v_heq_2697_, lean_object* v_i_2698_, lean_object* v_entries_2699_){
_start:
{
size_t v_depth_boxed_2700_; lean_object* v_res_2701_; 
v_depth_boxed_2700_ = lean_unbox_usize(v_depth_2694_);
lean_dec(v_depth_2694_);
v_res_2701_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(v_00_u03b2_2693_, v_depth_boxed_2700_, v_keys_2695_, v_vals_2696_, v_heq_2697_, v_i_2698_, v_entries_2699_);
lean_dec_ref(v_vals_2696_);
lean_dec_ref(v_keys_2695_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2702_, lean_object* v_x_2703_, lean_object* v_x_2704_, lean_object* v_x_2705_, lean_object* v_x_2706_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2703_, v_x_2704_, v_x_2705_, v_x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2708_, lean_object* v_x_2709_, lean_object* v_x_2710_, lean_object* v_x_2711_){
_start:
{
lean_object* v_ks_2712_; lean_object* v_vs_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2737_; 
v_ks_2712_ = lean_ctor_get(v_x_2708_, 0);
v_vs_2713_ = lean_ctor_get(v_x_2708_, 1);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_x_2708_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2715_ = v_x_2708_;
v_isShared_2716_ = v_isSharedCheck_2737_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_vs_2713_);
lean_inc(v_ks_2712_);
lean_dec(v_x_2708_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2737_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2717_ = lean_array_get_size(v_ks_2712_);
v___x_2718_ = lean_nat_dec_lt(v_x_2709_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2722_; 
lean_dec(v_x_2709_);
v___x_2719_ = lean_array_push(v_ks_2712_, v_x_2710_);
v___x_2720_ = lean_array_push(v_vs_2713_, v_x_2711_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 1, v___x_2720_);
lean_ctor_set(v___x_2715_, 0, v___x_2719_);
v___x_2722_ = v___x_2715_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2719_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
else
{
lean_object* v_k_x27_2724_; uint8_t v___x_2725_; 
v_k_x27_2724_ = lean_array_fget_borrowed(v_ks_2712_, v_x_2709_);
v___x_2725_ = l_Lean_instBEqMVarId_beq(v_x_2710_, v_k_x27_2724_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2727_; 
if (v_isShared_2716_ == 0)
{
v___x_2727_ = v___x_2715_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_ks_2712_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_vs_2713_);
v___x_2727_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = lean_unsigned_to_nat(1u);
v___x_2729_ = lean_nat_add(v_x_2709_, v___x_2728_);
lean_dec(v_x_2709_);
v_x_2708_ = v___x_2727_;
v_x_2709_ = v___x_2729_;
goto _start;
}
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2732_ = lean_array_fset(v_ks_2712_, v_x_2709_, v_x_2710_);
v___x_2733_ = lean_array_fset(v_vs_2713_, v_x_2709_, v_x_2711_);
lean_dec(v_x_2709_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 1, v___x_2733_);
lean_ctor_set(v___x_2715_, 0, v___x_2732_);
v___x_2735_ = v___x_2715_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2732_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_2738_, lean_object* v_k_2739_, lean_object* v_v_2740_){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = lean_unsigned_to_nat(0u);
v___x_2742_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_2738_, v___x_2741_, v_k_2739_, v_v_2740_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2743_, size_t v_x_2744_, size_t v_x_2745_, lean_object* v_x_2746_, lean_object* v_x_2747_){
_start:
{
if (lean_obj_tag(v_x_2743_) == 0)
{
lean_object* v_es_2748_; size_t v___x_2749_; size_t v___x_2750_; size_t v___x_2751_; size_t v___x_2752_; lean_object* v_j_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
v_es_2748_ = lean_ctor_get(v_x_2743_, 0);
v___x_2749_ = ((size_t)5ULL);
v___x_2750_ = ((size_t)1ULL);
v___x_2751_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
v___x_2752_ = lean_usize_land(v_x_2744_, v___x_2751_);
v_j_2753_ = lean_usize_to_nat(v___x_2752_);
v___x_2754_ = lean_array_get_size(v_es_2748_);
v___x_2755_ = lean_nat_dec_lt(v_j_2753_, v___x_2754_);
if (v___x_2755_ == 0)
{
lean_dec(v_j_2753_);
lean_dec(v_x_2747_);
lean_dec(v_x_2746_);
return v_x_2743_;
}
else
{
lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2792_; 
lean_inc_ref(v_es_2748_);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_x_2743_);
if (v_isSharedCheck_2792_ == 0)
{
lean_object* v_unused_2793_; 
v_unused_2793_ = lean_ctor_get(v_x_2743_, 0);
lean_dec(v_unused_2793_);
v___x_2757_ = v_x_2743_;
v_isShared_2758_ = v_isSharedCheck_2792_;
goto v_resetjp_2756_;
}
else
{
lean_dec(v_x_2743_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2792_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v_v_2759_; lean_object* v___x_2760_; lean_object* v_xs_x27_2761_; lean_object* v___y_2763_; 
v_v_2759_ = lean_array_fget(v_es_2748_, v_j_2753_);
v___x_2760_ = lean_box(0);
v_xs_x27_2761_ = lean_array_fset(v_es_2748_, v_j_2753_, v___x_2760_);
switch(lean_obj_tag(v_v_2759_))
{
case 0:
{
lean_object* v_key_2768_; lean_object* v_val_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2779_; 
v_key_2768_ = lean_ctor_get(v_v_2759_, 0);
v_val_2769_ = lean_ctor_get(v_v_2759_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_v_2759_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2771_ = v_v_2759_;
v_isShared_2772_ = v_isSharedCheck_2779_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_val_2769_);
lean_inc(v_key_2768_);
lean_dec(v_v_2759_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2779_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
uint8_t v___x_2773_; 
v___x_2773_ = l_Lean_instBEqMVarId_beq(v_x_2746_, v_key_2768_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_del_object(v___x_2771_);
v___x_2774_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2768_, v_val_2769_, v_x_2746_, v_x_2747_);
v___x_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
v___y_2763_ = v___x_2775_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2777_; 
lean_dec(v_val_2769_);
lean_dec(v_key_2768_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 1, v_x_2747_);
lean_ctor_set(v___x_2771_, 0, v_x_2746_);
v___x_2777_ = v___x_2771_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_x_2746_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_x_2747_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
v___y_2763_ = v___x_2777_;
goto v___jp_2762_;
}
}
}
}
case 1:
{
lean_object* v_node_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2790_; 
v_node_2780_ = lean_ctor_get(v_v_2759_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_v_2759_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2782_ = v_v_2759_;
v_isShared_2783_ = v_isSharedCheck_2790_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_node_2780_);
lean_dec(v_v_2759_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2790_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
size_t v___x_2784_; size_t v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2784_ = lean_usize_shift_right(v_x_2744_, v___x_2749_);
v___x_2785_ = lean_usize_add(v_x_2745_, v___x_2750_);
v___x_2786_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_node_2780_, v___x_2784_, v___x_2785_, v_x_2746_, v_x_2747_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2786_);
v___x_2788_ = v___x_2782_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
v___y_2763_ = v___x_2788_;
goto v___jp_2762_;
}
}
}
default: 
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2791_, 0, v_x_2746_);
lean_ctor_set(v___x_2791_, 1, v_x_2747_);
v___y_2763_ = v___x_2791_;
goto v___jp_2762_;
}
}
v___jp_2762_:
{
lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2764_ = lean_array_fset(v_xs_x27_2761_, v_j_2753_, v___y_2763_);
lean_dec(v_j_2753_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v___x_2764_);
v___x_2766_ = v___x_2757_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
else
{
lean_object* v_ks_2794_; lean_object* v_vs_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2815_; 
v_ks_2794_ = lean_ctor_get(v_x_2743_, 0);
v_vs_2795_ = lean_ctor_get(v_x_2743_, 1);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_x_2743_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2797_ = v_x_2743_;
v_isShared_2798_ = v_isSharedCheck_2815_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_vs_2795_);
lean_inc(v_ks_2794_);
lean_dec(v_x_2743_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2815_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_ks_2794_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_vs_2795_);
v___x_2800_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
lean_object* v_newNode_2801_; uint8_t v___y_2803_; size_t v___x_2809_; uint8_t v___x_2810_; 
v_newNode_2801_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v___x_2800_, v_x_2746_, v_x_2747_);
v___x_2809_ = ((size_t)7ULL);
v___x_2810_ = lean_usize_dec_le(v___x_2809_, v_x_2745_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2811_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2801_);
v___x_2812_ = lean_unsigned_to_nat(4u);
v___x_2813_ = lean_nat_dec_lt(v___x_2811_, v___x_2812_);
lean_dec(v___x_2811_);
v___y_2803_ = v___x_2813_;
goto v___jp_2802_;
}
else
{
v___y_2803_ = v___x_2810_;
goto v___jp_2802_;
}
v___jp_2802_:
{
if (v___y_2803_ == 0)
{
lean_object* v_ks_2804_; lean_object* v_vs_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_ks_2804_ = lean_ctor_get(v_newNode_2801_, 0);
lean_inc_ref(v_ks_2804_);
v_vs_2805_ = lean_ctor_get(v_newNode_2801_, 1);
lean_inc_ref(v_vs_2805_);
lean_dec_ref(v_newNode_2801_);
v___x_2806_ = lean_unsigned_to_nat(0u);
v___x_2807_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2);
v___x_2808_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2745_, v_ks_2804_, v_vs_2805_, v___x_2806_, v___x_2807_);
lean_dec_ref(v_vs_2805_);
lean_dec_ref(v_ks_2804_);
return v___x_2808_;
}
else
{
return v_newNode_2801_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_2816_, lean_object* v_keys_2817_, lean_object* v_vals_2818_, lean_object* v_i_2819_, lean_object* v_entries_2820_){
_start:
{
lean_object* v___x_2821_; uint8_t v___x_2822_; 
v___x_2821_ = lean_array_get_size(v_keys_2817_);
v___x_2822_ = lean_nat_dec_lt(v_i_2819_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_dec(v_i_2819_);
return v_entries_2820_;
}
else
{
lean_object* v_k_2823_; lean_object* v_v_2824_; uint64_t v___x_2825_; size_t v_h_2826_; size_t v___x_2827_; lean_object* v___x_2828_; size_t v___x_2829_; size_t v___x_2830_; size_t v___x_2831_; size_t v_h_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v_k_2823_ = lean_array_fget_borrowed(v_keys_2817_, v_i_2819_);
v_v_2824_ = lean_array_fget_borrowed(v_vals_2818_, v_i_2819_);
v___x_2825_ = l_Lean_instHashableMVarId_hash(v_k_2823_);
v_h_2826_ = lean_uint64_to_usize(v___x_2825_);
v___x_2827_ = ((size_t)5ULL);
v___x_2828_ = lean_unsigned_to_nat(1u);
v___x_2829_ = ((size_t)1ULL);
v___x_2830_ = lean_usize_sub(v_depth_2816_, v___x_2829_);
v___x_2831_ = lean_usize_mul(v___x_2827_, v___x_2830_);
v_h_2832_ = lean_usize_shift_right(v_h_2826_, v___x_2831_);
v___x_2833_ = lean_nat_add(v_i_2819_, v___x_2828_);
lean_dec(v_i_2819_);
lean_inc(v_v_2824_);
lean_inc(v_k_2823_);
v___x_2834_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_entries_2820_, v_h_2832_, v_depth_2816_, v_k_2823_, v_v_2824_);
v_i_2819_ = v___x_2833_;
v_entries_2820_ = v___x_2834_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2836_, lean_object* v_keys_2837_, lean_object* v_vals_2838_, lean_object* v_i_2839_, lean_object* v_entries_2840_){
_start:
{
size_t v_depth_boxed_2841_; lean_object* v_res_2842_; 
v_depth_boxed_2841_ = lean_unbox_usize(v_depth_2836_);
lean_dec(v_depth_2836_);
v_res_2842_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_2841_, v_keys_2837_, v_vals_2838_, v_i_2839_, v_entries_2840_);
lean_dec_ref(v_vals_2838_);
lean_dec_ref(v_keys_2837_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2843_, lean_object* v_x_2844_, lean_object* v_x_2845_, lean_object* v_x_2846_, lean_object* v_x_2847_){
_start:
{
size_t v_x_2256__boxed_2848_; size_t v_x_2257__boxed_2849_; lean_object* v_res_2850_; 
v_x_2256__boxed_2848_ = lean_unbox_usize(v_x_2844_);
lean_dec(v_x_2844_);
v_x_2257__boxed_2849_ = lean_unbox_usize(v_x_2845_);
lean_dec(v_x_2845_);
v_res_2850_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_2843_, v_x_2256__boxed_2848_, v_x_2257__boxed_2849_, v_x_2846_, v_x_2847_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(lean_object* v_x_2851_, lean_object* v_x_2852_, lean_object* v_x_2853_){
_start:
{
uint64_t v___x_2854_; size_t v___x_2855_; size_t v___x_2856_; lean_object* v___x_2857_; 
v___x_2854_ = l_Lean_instHashableMVarId_hash(v_x_2852_);
v___x_2855_ = lean_uint64_to_usize(v___x_2854_);
v___x_2856_ = ((size_t)1ULL);
v___x_2857_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_2851_, v___x_2855_, v___x_2856_, v_x_2852_, v_x_2853_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(lean_object* v_mvarId_2858_, lean_object* v_val_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v___x_2862_; lean_object* v_mctx_2863_; lean_object* v_cache_2864_; lean_object* v_zetaDeltaFVarIds_2865_; lean_object* v_postponed_2866_; lean_object* v_diag_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2895_; 
v___x_2862_ = lean_st_ref_take(v___y_2860_);
v_mctx_2863_ = lean_ctor_get(v___x_2862_, 0);
v_cache_2864_ = lean_ctor_get(v___x_2862_, 1);
v_zetaDeltaFVarIds_2865_ = lean_ctor_get(v___x_2862_, 2);
v_postponed_2866_ = lean_ctor_get(v___x_2862_, 3);
v_diag_2867_ = lean_ctor_get(v___x_2862_, 4);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2869_ = v___x_2862_;
v_isShared_2870_ = v_isSharedCheck_2895_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_diag_2867_);
lean_inc(v_postponed_2866_);
lean_inc(v_zetaDeltaFVarIds_2865_);
lean_inc(v_cache_2864_);
lean_inc(v_mctx_2863_);
lean_dec(v___x_2862_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2895_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v_depth_2871_; lean_object* v_levelAssignDepth_2872_; lean_object* v_lmvarCounter_2873_; lean_object* v_mvarCounter_2874_; lean_object* v_lDecls_2875_; lean_object* v_decls_2876_; lean_object* v_userNames_2877_; lean_object* v_lAssignment_2878_; lean_object* v_eAssignment_2879_; lean_object* v_dAssignment_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2894_; 
v_depth_2871_ = lean_ctor_get(v_mctx_2863_, 0);
v_levelAssignDepth_2872_ = lean_ctor_get(v_mctx_2863_, 1);
v_lmvarCounter_2873_ = lean_ctor_get(v_mctx_2863_, 2);
v_mvarCounter_2874_ = lean_ctor_get(v_mctx_2863_, 3);
v_lDecls_2875_ = lean_ctor_get(v_mctx_2863_, 4);
v_decls_2876_ = lean_ctor_get(v_mctx_2863_, 5);
v_userNames_2877_ = lean_ctor_get(v_mctx_2863_, 6);
v_lAssignment_2878_ = lean_ctor_get(v_mctx_2863_, 7);
v_eAssignment_2879_ = lean_ctor_get(v_mctx_2863_, 8);
v_dAssignment_2880_ = lean_ctor_get(v_mctx_2863_, 9);
v_isSharedCheck_2894_ = !lean_is_exclusive(v_mctx_2863_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2882_ = v_mctx_2863_;
v_isShared_2883_ = v_isSharedCheck_2894_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_dAssignment_2880_);
lean_inc(v_eAssignment_2879_);
lean_inc(v_lAssignment_2878_);
lean_inc(v_userNames_2877_);
lean_inc(v_decls_2876_);
lean_inc(v_lDecls_2875_);
lean_inc(v_mvarCounter_2874_);
lean_inc(v_lmvarCounter_2873_);
lean_inc(v_levelAssignDepth_2872_);
lean_inc(v_depth_2871_);
lean_dec(v_mctx_2863_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2894_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2884_; lean_object* v___x_2886_; 
v___x_2884_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_eAssignment_2879_, v_mvarId_2858_, v_val_2859_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 8, v___x_2884_);
v___x_2886_ = v___x_2882_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_depth_2871_);
lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_levelAssignDepth_2872_);
lean_ctor_set(v_reuseFailAlloc_2893_, 2, v_lmvarCounter_2873_);
lean_ctor_set(v_reuseFailAlloc_2893_, 3, v_mvarCounter_2874_);
lean_ctor_set(v_reuseFailAlloc_2893_, 4, v_lDecls_2875_);
lean_ctor_set(v_reuseFailAlloc_2893_, 5, v_decls_2876_);
lean_ctor_set(v_reuseFailAlloc_2893_, 6, v_userNames_2877_);
lean_ctor_set(v_reuseFailAlloc_2893_, 7, v_lAssignment_2878_);
lean_ctor_set(v_reuseFailAlloc_2893_, 8, v___x_2884_);
lean_ctor_set(v_reuseFailAlloc_2893_, 9, v_dAssignment_2880_);
v___x_2886_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2888_; 
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2886_);
v___x_2888_ = v___x_2869_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_cache_2864_);
lean_ctor_set(v_reuseFailAlloc_2892_, 2, v_zetaDeltaFVarIds_2865_);
lean_ctor_set(v_reuseFailAlloc_2892_, 3, v_postponed_2866_);
lean_ctor_set(v_reuseFailAlloc_2892_, 4, v_diag_2867_);
v___x_2888_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2889_ = lean_st_ref_set(v___y_2860_, v___x_2888_);
v___x_2890_ = lean_box(0);
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
return v___x_2891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg___boxed(lean_object* v_mvarId_2896_, lean_object* v_val_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_2896_, v_val_2897_, v___y_2898_);
lean_dec(v___y_2898_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object* v_mvarId_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v___x_2909_; 
lean_inc(v_mvarId_2901_);
v___x_2909_ = l_Lean_MVarId_getDecl(v_mvarId_2901_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v_userName_2911_; lean_object* v_lctx_2912_; lean_object* v_type_2913_; lean_object* v_localInstances_2914_; lean_object* v___x_2915_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref(v___x_2909_);
v_userName_2911_ = lean_ctor_get(v_a_2910_, 0);
lean_inc(v_userName_2911_);
v_lctx_2912_ = lean_ctor_get(v_a_2910_, 1);
lean_inc_ref(v_lctx_2912_);
v_type_2913_ = lean_ctor_get(v_a_2910_, 2);
lean_inc_ref(v_type_2913_);
v_localInstances_2914_ = lean_ctor_get(v_a_2910_, 4);
lean_inc_ref(v_localInstances_2914_);
lean_dec(v_a_2910_);
v___x_2915_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_2912_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2917_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref(v___x_2915_);
v___x_2917_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2913_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; uint8_t v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref(v___x_2917_);
v___x_2919_ = 2;
v___x_2920_ = lean_unsigned_to_nat(0u);
v___x_2921_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_2916_, v_localInstances_2914_, v_a_2918_, v___x_2919_, v_userName_2911_, v___x_2920_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2931_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc_n(v_a_2922_, 2);
lean_dec_ref(v___x_2921_);
v___x_2923_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_2901_, v_a_2922_, v_a_2905_);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2931_ == 0)
{
lean_object* v_unused_2932_; 
v_unused_2932_ = lean_ctor_get(v___x_2923_, 0);
lean_dec(v_unused_2932_);
v___x_2925_ = v___x_2923_;
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
else
{
lean_dec(v___x_2923_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2927_ = l_Lean_Expr_mvarId_x21(v_a_2922_);
lean_dec(v_a_2922_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v___x_2927_);
v___x_2929_ = v___x_2925_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2927_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec(v_mvarId_2901_);
v_a_2933_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2921_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2921_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec(v_a_2916_);
lean_dec_ref(v_localInstances_2914_);
lean_dec(v_userName_2911_);
lean_dec(v_mvarId_2901_);
v_a_2941_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2917_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2917_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v_localInstances_2914_);
lean_dec_ref(v_type_2913_);
lean_dec(v_userName_2911_);
lean_dec(v_mvarId_2901_);
v_a_2949_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2915_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2915_);
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
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec(v_mvarId_2901_);
v_a_2957_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2909_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2909_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar___boxed(lean_object* v_mvarId_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_);
lean_dec(v_a_2971_);
lean_dec_ref(v_a_2970_);
lean_dec(v_a_2969_);
lean_dec_ref(v_a_2968_);
lean_dec(v_a_2967_);
lean_dec_ref(v_a_2966_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(lean_object* v_mvarId_2974_, lean_object* v_val_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_2974_, v_val_2975_, v___y_2979_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___boxed(lean_object* v_mvarId_2984_, lean_object* v_val_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(v_mvarId_2984_, v_val_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0(lean_object* v_00_u03b2_2994_, lean_object* v_x_2995_, lean_object* v_x_2996_, lean_object* v_x_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_x_2995_, v_x_2996_, v_x_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2999_, lean_object* v_x_3000_, size_t v_x_3001_, size_t v_x_3002_, lean_object* v_x_3003_, lean_object* v_x_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_3000_, v_x_3001_, v_x_3002_, v_x_3003_, v_x_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3006_, lean_object* v_x_3007_, lean_object* v_x_3008_, lean_object* v_x_3009_, lean_object* v_x_3010_, lean_object* v_x_3011_){
_start:
{
size_t v_x_2610__boxed_3012_; size_t v_x_2611__boxed_3013_; lean_object* v_res_3014_; 
v_x_2610__boxed_3012_ = lean_unbox_usize(v_x_3008_);
lean_dec(v_x_3008_);
v_x_2611__boxed_3013_ = lean_unbox_usize(v_x_3009_);
lean_dec(v_x_3009_);
v_res_3014_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(v_00_u03b2_3006_, v_x_3007_, v_x_2610__boxed_3012_, v_x_2611__boxed_3013_, v_x_3010_, v_x_3011_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3015_, lean_object* v_n_3016_, lean_object* v_k_3017_, lean_object* v_v_3018_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v_n_3016_, v_k_3017_, v_v_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3020_, size_t v_depth_3021_, lean_object* v_keys_3022_, lean_object* v_vals_3023_, lean_object* v_heq_3024_, lean_object* v_i_3025_, lean_object* v_entries_3026_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_3021_, v_keys_3022_, v_vals_3023_, v_i_3025_, v_entries_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3028_, lean_object* v_depth_3029_, lean_object* v_keys_3030_, lean_object* v_vals_3031_, lean_object* v_heq_3032_, lean_object* v_i_3033_, lean_object* v_entries_3034_){
_start:
{
size_t v_depth_boxed_3035_; lean_object* v_res_3036_; 
v_depth_boxed_3035_ = lean_unbox_usize(v_depth_3029_);
lean_dec(v_depth_3029_);
v_res_3036_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3028_, v_depth_boxed_3035_, v_keys_3030_, v_vals_3031_, v_heq_3032_, v_i_3033_, v_entries_3034_);
lean_dec_ref(v_vals_3031_);
lean_dec_ref(v_keys_3030_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3037_, lean_object* v_x_3038_, lean_object* v_x_3039_, lean_object* v_x_3040_, lean_object* v_x_3041_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_3038_, v_x_3039_, v_x_3040_, v_x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(lean_object* v_msgData_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v___x_3049_; lean_object* v_env_3050_; lean_object* v___x_3051_; lean_object* v_mctx_3052_; lean_object* v_lctx_3053_; lean_object* v_options_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3049_ = lean_st_ref_get(v___y_3047_);
v_env_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc_ref(v_env_3050_);
lean_dec(v___x_3049_);
v___x_3051_ = lean_st_ref_get(v___y_3045_);
v_mctx_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc_ref(v_mctx_3052_);
lean_dec(v___x_3051_);
v_lctx_3053_ = lean_ctor_get(v___y_3044_, 2);
v_options_3054_ = lean_ctor_get(v___y_3046_, 2);
lean_inc_ref(v_options_3054_);
lean_inc_ref(v_lctx_3053_);
v___x_3055_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3055_, 0, v_env_3050_);
lean_ctor_set(v___x_3055_, 1, v_mctx_3052_);
lean_ctor_set(v___x_3055_, 2, v_lctx_3053_);
lean_ctor_set(v___x_3055_, 3, v_options_3054_);
v___x_3056_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set(v___x_3056_, 1, v_msgData_3043_);
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0___boxed(lean_object* v_msgData_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msgData_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(lean_object* v_msg_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_ref_3071_; lean_object* v___x_3072_; lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3081_; 
v_ref_3071_ = lean_ctor_get(v___y_3068_, 5);
v___x_3072_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msg_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3075_ = v___x_3072_;
v_isShared_3076_ = v_isSharedCheck_3081_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3072_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3081_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3077_; lean_object* v___x_3079_; 
lean_inc(v_ref_3071_);
v___x_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3077_, 0, v_ref_3071_);
lean_ctor_set(v___x_3077_, 1, v_a_3073_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set_tag(v___x_3075_, 1);
lean_ctor_set(v___x_3075_, 0, v___x_3077_);
v___x_3079_ = v___x_3075_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3077_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg___boxed(lean_object* v_msg_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
return v_res_3088_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0));
v___x_3091_ = l_Lean_stringToMessageData(v___x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(lean_object* v_msg_3095_, lean_object* v_e_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v___y_3105_; lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2));
v___x_3113_ = lean_string_dec_eq(v_msg_3095_, v___x_3112_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3114_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3));
v___x_3115_ = lean_string_append(v___x_3114_, v_msg_3095_);
lean_dec_ref(v_msg_3095_);
v___x_3116_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__4));
v___x_3117_ = lean_string_append(v___x_3115_, v___x_3116_);
v___y_3105_ = v___x_3117_;
goto v___jp_3104_;
}
else
{
v___y_3105_ = v_msg_3095_;
goto v___jp_3104_;
}
v___jp_3104_:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3106_ = l_Lean_stringToMessageData(v___y_3105_);
v___x_3107_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1);
v___x_3108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3106_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = l_Lean_indentExpr(v_e_3096_);
v___x_3110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3108_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v___x_3110_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
return v___x_3111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___boxed(lean_object* v_msg_3118_, lean_object* v_e_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3118_, v_e_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec(v_a_3123_);
lean_dec_ref(v_a_3122_);
lean_dec(v_a_3121_);
lean_dec_ref(v_a_3120_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(lean_object* v_00_u03b1_3128_, lean_object* v_msg_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_3129_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___boxed(lean_object* v_00_u03b1_3138_, lean_object* v_msg_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(v_00_u03b1_3138_, v_msg_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3148_, lean_object* v_vals_3149_, lean_object* v_i_3150_, lean_object* v_k_3151_){
_start:
{
lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3152_ = lean_array_get_size(v_keys_3148_);
v___x_3153_ = lean_nat_dec_lt(v_i_3150_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; 
lean_dec_ref(v_k_3151_);
lean_dec(v_i_3150_);
v___x_3154_ = lean_box(0);
return v___x_3154_;
}
else
{
lean_object* v_k_x27_3155_; uint8_t v___x_3156_; 
v_k_x27_3155_ = lean_array_fget_borrowed(v_keys_3148_, v_i_3150_);
lean_inc(v_k_x27_3155_);
lean_inc_ref(v_k_3151_);
v___x_3156_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_3151_, v_k_x27_3155_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_unsigned_to_nat(1u);
v___x_3158_ = lean_nat_add(v_i_3150_, v___x_3157_);
lean_dec(v_i_3150_);
v_i_3150_ = v___x_3158_;
goto _start;
}
else
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
lean_dec_ref(v_k_3151_);
v___x_3160_ = lean_array_fget_borrowed(v_vals_3149_, v_i_3150_);
lean_dec(v_i_3150_);
lean_inc(v___x_3160_);
lean_inc(v_k_x27_3155_);
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v_k_x27_3155_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
return v___x_3162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3163_, lean_object* v_vals_3164_, lean_object* v_i_3165_, lean_object* v_k_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_3163_, v_vals_3164_, v_i_3165_, v_k_3166_);
lean_dec_ref(v_vals_3164_);
lean_dec_ref(v_keys_3163_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(lean_object* v_x_3168_, size_t v_x_3169_, lean_object* v_x_3170_){
_start:
{
if (lean_obj_tag(v_x_3168_) == 0)
{
lean_object* v_es_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3199_; 
v_es_3171_ = lean_ctor_get(v_x_3168_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_x_3168_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3173_ = v_x_3168_;
v_isShared_3174_ = v_isSharedCheck_3199_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_es_3171_);
lean_dec(v_x_3168_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3199_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3175_; size_t v___x_3176_; size_t v___x_3177_; size_t v___x_3178_; lean_object* v_j_3179_; lean_object* v___x_3180_; 
v___x_3175_ = lean_box(2);
v___x_3176_ = ((size_t)5ULL);
v___x_3177_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
v___x_3178_ = lean_usize_land(v_x_3169_, v___x_3177_);
v_j_3179_ = lean_usize_to_nat(v___x_3178_);
v___x_3180_ = lean_array_get(v___x_3175_, v_es_3171_, v_j_3179_);
lean_dec(v_j_3179_);
lean_dec_ref(v_es_3171_);
switch(lean_obj_tag(v___x_3180_))
{
case 0:
{
lean_object* v_key_3181_; lean_object* v_val_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3194_; 
v_key_3181_ = lean_ctor_get(v___x_3180_, 0);
v_val_3182_ = lean_ctor_get(v___x_3180_, 1);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3184_ = v___x_3180_;
v_isShared_3185_ = v_isSharedCheck_3194_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_val_3182_);
lean_inc(v_key_3181_);
lean_dec(v___x_3180_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3194_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
uint8_t v___x_3186_; 
lean_inc(v_key_3181_);
v___x_3186_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_3170_, v_key_3181_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; 
lean_del_object(v___x_3184_);
lean_dec(v_val_3182_);
lean_dec(v_key_3181_);
lean_del_object(v___x_3173_);
v___x_3187_ = lean_box(0);
return v___x_3187_;
}
else
{
lean_object* v___x_3189_; 
if (v_isShared_3185_ == 0)
{
v___x_3189_ = v___x_3184_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_key_3181_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_val_3182_);
v___x_3189_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3191_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set_tag(v___x_3173_, 1);
lean_ctor_set(v___x_3173_, 0, v___x_3189_);
v___x_3191_ = v___x_3173_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
}
case 1:
{
lean_object* v_node_3195_; size_t v___x_3196_; 
lean_del_object(v___x_3173_);
v_node_3195_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_node_3195_);
lean_dec_ref(v___x_3180_);
v___x_3196_ = lean_usize_shift_right(v_x_3169_, v___x_3176_);
v_x_3168_ = v_node_3195_;
v_x_3169_ = v___x_3196_;
goto _start;
}
default: 
{
lean_object* v___x_3198_; 
lean_del_object(v___x_3173_);
lean_dec_ref(v_x_3170_);
v___x_3198_ = lean_box(0);
return v___x_3198_;
}
}
}
}
else
{
lean_object* v_ks_3200_; lean_object* v_vs_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v_ks_3200_ = lean_ctor_get(v_x_3168_, 0);
lean_inc_ref(v_ks_3200_);
v_vs_3201_ = lean_ctor_get(v_x_3168_, 1);
lean_inc_ref(v_vs_3201_);
lean_dec_ref(v_x_3168_);
v___x_3202_ = lean_unsigned_to_nat(0u);
v___x_3203_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_ks_3200_, v_vs_3201_, v___x_3202_, v_x_3170_);
lean_dec_ref(v_vs_3201_);
lean_dec_ref(v_ks_3200_);
return v___x_3203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_3204_, lean_object* v_x_3205_, lean_object* v_x_3206_){
_start:
{
size_t v_x_7443__boxed_3207_; lean_object* v_res_3208_; 
v_x_7443__boxed_3207_ = lean_unbox_usize(v_x_3205_);
lean_dec(v_x_3205_);
v_res_3208_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3204_, v_x_7443__boxed_3207_, v_x_3206_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(lean_object* v_x_3209_, lean_object* v_x_3210_){
_start:
{
uint64_t v___x_3211_; size_t v___x_3212_; lean_object* v___x_3213_; 
v___x_3211_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3210_);
v___x_3212_ = lean_uint64_to_usize(v___x_3211_);
v___x_3213_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3209_, v___x_3212_, v_x_3210_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0(lean_object* v_msg_3214_, lean_object* v_e_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v___y_3228_; lean_object* v___x_3237_; lean_object* v_share_3238_; lean_object* v___x_3239_; 
v___x_3237_ = lean_st_ref_get(v___y_3217_);
v_share_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc_ref(v_share_3238_);
lean_dec(v___x_3237_);
lean_inc_ref(v_e_3215_);
v___x_3239_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_share_3238_, v_e_3215_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v___x_3240_; 
v___x_3240_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3214_, v_e_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
v___y_3228_ = v___x_3240_;
goto v___jp_3227_;
}
else
{
lean_object* v_val_3241_; lean_object* v_fst_3242_; uint8_t v___x_3243_; 
v_val_3241_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_val_3241_);
lean_dec_ref(v___x_3239_);
v_fst_3242_ = lean_ctor_get(v_val_3241_, 0);
lean_inc(v_fst_3242_);
lean_dec(v_val_3241_);
v___x_3243_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_3242_, v_e_3215_);
lean_dec(v_fst_3242_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; 
v___x_3244_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3214_, v_e_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
v___y_3228_ = v___x_3244_;
goto v___jp_3227_;
}
else
{
lean_dec_ref(v_e_3215_);
lean_dec_ref(v_msg_3214_);
goto v___jp_3223_;
}
}
v___jp_3223_:
{
uint8_t v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = 1;
v___x_3225_ = lean_box(v___x_3224_);
v___x_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
return v___x_3226_;
}
v___jp_3227_:
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
v_a_3229_ = lean_ctor_get(v___y_3228_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___y_3228_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___y_3228_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___y_3228_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0___boxed(lean_object* v_msg_3245_, lean_object* v_e_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_Expr_checkMaxShared___lam__0(v_msg_3245_, v_e_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
return v_res_3254_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(lean_object* v_a_3255_, lean_object* v_x_3256_){
_start:
{
if (lean_obj_tag(v_x_3256_) == 0)
{
uint8_t v___x_3257_; 
v___x_3257_ = 0;
return v___x_3257_;
}
else
{
lean_object* v_key_3258_; lean_object* v_tail_3259_; uint8_t v___x_3260_; 
v_key_3258_ = lean_ctor_get(v_x_3256_, 0);
v_tail_3259_ = lean_ctor_get(v_x_3256_, 2);
v___x_3260_ = lean_expr_eqv(v_key_3258_, v_a_3255_);
if (v___x_3260_ == 0)
{
v_x_3256_ = v_tail_3259_;
goto _start;
}
else
{
return v___x_3260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_a_3262_, lean_object* v_x_3263_){
_start:
{
uint8_t v_res_3264_; lean_object* v_r_3265_; 
v_res_3264_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3262_, v_x_3263_);
lean_dec(v_x_3263_);
lean_dec_ref(v_a_3262_);
v_r_3265_ = lean_box(v_res_3264_);
return v_r_3265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(lean_object* v_a_3266_, lean_object* v_b_3267_, lean_object* v_x_3268_){
_start:
{
if (lean_obj_tag(v_x_3268_) == 0)
{
lean_dec(v_b_3267_);
lean_dec_ref(v_a_3266_);
return v_x_3268_;
}
else
{
lean_object* v_key_3269_; lean_object* v_value_3270_; lean_object* v_tail_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3283_; 
v_key_3269_ = lean_ctor_get(v_x_3268_, 0);
v_value_3270_ = lean_ctor_get(v_x_3268_, 1);
v_tail_3271_ = lean_ctor_get(v_x_3268_, 2);
v_isSharedCheck_3283_ = !lean_is_exclusive(v_x_3268_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3273_ = v_x_3268_;
v_isShared_3274_ = v_isSharedCheck_3283_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_tail_3271_);
lean_inc(v_value_3270_);
lean_inc(v_key_3269_);
lean_dec(v_x_3268_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3283_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
uint8_t v___x_3275_; 
v___x_3275_ = lean_expr_eqv(v_key_3269_, v_a_3266_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3276_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3266_, v_b_3267_, v_tail_3271_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 2, v___x_3276_);
v___x_3278_ = v___x_3273_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_key_3269_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_value_3270_);
lean_ctor_set(v_reuseFailAlloc_3279_, 2, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
else
{
lean_object* v___x_3281_; 
lean_dec(v_value_3270_);
lean_dec(v_key_3269_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 1, v_b_3267_);
lean_ctor_set(v___x_3273_, 0, v_a_3266_);
v___x_3281_ = v___x_3273_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3266_);
lean_ctor_set(v_reuseFailAlloc_3282_, 1, v_b_3267_);
lean_ctor_set(v_reuseFailAlloc_3282_, 2, v_tail_3271_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(lean_object* v_x_3284_, lean_object* v_x_3285_){
_start:
{
if (lean_obj_tag(v_x_3285_) == 0)
{
return v_x_3284_;
}
else
{
lean_object* v_key_3286_; lean_object* v_value_3287_; lean_object* v_tail_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3311_; 
v_key_3286_ = lean_ctor_get(v_x_3285_, 0);
v_value_3287_ = lean_ctor_get(v_x_3285_, 1);
v_tail_3288_ = lean_ctor_get(v_x_3285_, 2);
v_isSharedCheck_3311_ = !lean_is_exclusive(v_x_3285_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3290_ = v_x_3285_;
v_isShared_3291_ = v_isSharedCheck_3311_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_tail_3288_);
lean_inc(v_value_3287_);
lean_inc(v_key_3286_);
lean_dec(v_x_3285_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3311_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3292_; uint64_t v___x_3293_; uint64_t v___x_3294_; uint64_t v___x_3295_; uint64_t v_fold_3296_; uint64_t v___x_3297_; uint64_t v___x_3298_; uint64_t v___x_3299_; size_t v___x_3300_; size_t v___x_3301_; size_t v___x_3302_; size_t v___x_3303_; size_t v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3307_; 
v___x_3292_ = lean_array_get_size(v_x_3284_);
v___x_3293_ = l_Lean_Expr_hash(v_key_3286_);
v___x_3294_ = 32ULL;
v___x_3295_ = lean_uint64_shift_right(v___x_3293_, v___x_3294_);
v_fold_3296_ = lean_uint64_xor(v___x_3293_, v___x_3295_);
v___x_3297_ = 16ULL;
v___x_3298_ = lean_uint64_shift_right(v_fold_3296_, v___x_3297_);
v___x_3299_ = lean_uint64_xor(v_fold_3296_, v___x_3298_);
v___x_3300_ = lean_uint64_to_usize(v___x_3299_);
v___x_3301_ = lean_usize_of_nat(v___x_3292_);
v___x_3302_ = ((size_t)1ULL);
v___x_3303_ = lean_usize_sub(v___x_3301_, v___x_3302_);
v___x_3304_ = lean_usize_land(v___x_3300_, v___x_3303_);
v___x_3305_ = lean_array_uget_borrowed(v_x_3284_, v___x_3304_);
lean_inc(v___x_3305_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 2, v___x_3305_);
v___x_3307_ = v___x_3290_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_key_3286_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_value_3287_);
lean_ctor_set(v_reuseFailAlloc_3310_, 2, v___x_3305_);
v___x_3307_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
lean_object* v___x_3308_; 
v___x_3308_ = lean_array_uset(v_x_3284_, v___x_3304_, v___x_3307_);
v_x_3284_ = v___x_3308_;
v_x_3285_ = v_tail_3288_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(lean_object* v_i_3312_, lean_object* v_source_3313_, lean_object* v_target_3314_){
_start:
{
lean_object* v___x_3315_; uint8_t v___x_3316_; 
v___x_3315_ = lean_array_get_size(v_source_3313_);
v___x_3316_ = lean_nat_dec_lt(v_i_3312_, v___x_3315_);
if (v___x_3316_ == 0)
{
lean_dec_ref(v_source_3313_);
lean_dec(v_i_3312_);
return v_target_3314_;
}
else
{
lean_object* v_es_3317_; lean_object* v___x_3318_; lean_object* v_source_3319_; lean_object* v_target_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v_es_3317_ = lean_array_fget(v_source_3313_, v_i_3312_);
v___x_3318_ = lean_box(0);
v_source_3319_ = lean_array_fset(v_source_3313_, v_i_3312_, v___x_3318_);
v_target_3320_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_target_3314_, v_es_3317_);
v___x_3321_ = lean_unsigned_to_nat(1u);
v___x_3322_ = lean_nat_add(v_i_3312_, v___x_3321_);
lean_dec(v_i_3312_);
v_i_3312_ = v___x_3322_;
v_source_3313_ = v_source_3319_;
v_target_3314_ = v_target_3320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(lean_object* v_data_3324_){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v_nbuckets_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3325_ = lean_array_get_size(v_data_3324_);
v___x_3326_ = lean_unsigned_to_nat(2u);
v_nbuckets_3327_ = lean_nat_mul(v___x_3325_, v___x_3326_);
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3329_ = lean_box(0);
v___x_3330_ = lean_mk_array(v_nbuckets_3327_, v___x_3329_);
v___x_3331_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v___x_3328_, v_data_3324_, v___x_3330_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(lean_object* v_m_3332_, lean_object* v_a_3333_, lean_object* v_b_3334_){
_start:
{
lean_object* v_size_3335_; lean_object* v_buckets_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3379_; 
v_size_3335_ = lean_ctor_get(v_m_3332_, 0);
v_buckets_3336_ = lean_ctor_get(v_m_3332_, 1);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_m_3332_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3338_ = v_m_3332_;
v_isShared_3339_ = v_isSharedCheck_3379_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_buckets_3336_);
lean_inc(v_size_3335_);
lean_dec(v_m_3332_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3379_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3340_; uint64_t v___x_3341_; uint64_t v___x_3342_; uint64_t v___x_3343_; uint64_t v_fold_3344_; uint64_t v___x_3345_; uint64_t v___x_3346_; uint64_t v___x_3347_; size_t v___x_3348_; size_t v___x_3349_; size_t v___x_3350_; size_t v___x_3351_; size_t v___x_3352_; lean_object* v_bkt_3353_; uint8_t v___x_3354_; 
v___x_3340_ = lean_array_get_size(v_buckets_3336_);
v___x_3341_ = l_Lean_Expr_hash(v_a_3333_);
v___x_3342_ = 32ULL;
v___x_3343_ = lean_uint64_shift_right(v___x_3341_, v___x_3342_);
v_fold_3344_ = lean_uint64_xor(v___x_3341_, v___x_3343_);
v___x_3345_ = 16ULL;
v___x_3346_ = lean_uint64_shift_right(v_fold_3344_, v___x_3345_);
v___x_3347_ = lean_uint64_xor(v_fold_3344_, v___x_3346_);
v___x_3348_ = lean_uint64_to_usize(v___x_3347_);
v___x_3349_ = lean_usize_of_nat(v___x_3340_);
v___x_3350_ = ((size_t)1ULL);
v___x_3351_ = lean_usize_sub(v___x_3349_, v___x_3350_);
v___x_3352_ = lean_usize_land(v___x_3348_, v___x_3351_);
v_bkt_3353_ = lean_array_uget_borrowed(v_buckets_3336_, v___x_3352_);
v___x_3354_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3333_, v_bkt_3353_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; lean_object* v_size_x27_3356_; lean_object* v___x_3357_; lean_object* v_buckets_x27_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; uint8_t v___x_3364_; 
v___x_3355_ = lean_unsigned_to_nat(1u);
v_size_x27_3356_ = lean_nat_add(v_size_3335_, v___x_3355_);
lean_dec(v_size_3335_);
lean_inc(v_bkt_3353_);
v___x_3357_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3357_, 0, v_a_3333_);
lean_ctor_set(v___x_3357_, 1, v_b_3334_);
lean_ctor_set(v___x_3357_, 2, v_bkt_3353_);
v_buckets_x27_3358_ = lean_array_uset(v_buckets_3336_, v___x_3352_, v___x_3357_);
v___x_3359_ = lean_unsigned_to_nat(4u);
v___x_3360_ = lean_nat_mul(v_size_x27_3356_, v___x_3359_);
v___x_3361_ = lean_unsigned_to_nat(3u);
v___x_3362_ = lean_nat_div(v___x_3360_, v___x_3361_);
lean_dec(v___x_3360_);
v___x_3363_ = lean_array_get_size(v_buckets_x27_3358_);
v___x_3364_ = lean_nat_dec_le(v___x_3362_, v___x_3363_);
lean_dec(v___x_3362_);
if (v___x_3364_ == 0)
{
lean_object* v_val_3365_; lean_object* v___x_3367_; 
v_val_3365_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_buckets_x27_3358_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 1, v_val_3365_);
lean_ctor_set(v___x_3338_, 0, v_size_x27_3356_);
v___x_3367_ = v___x_3338_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_size_x27_3356_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_val_3365_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
else
{
lean_object* v___x_3370_; 
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 1, v_buckets_x27_3358_);
lean_ctor_set(v___x_3338_, 0, v_size_x27_3356_);
v___x_3370_ = v___x_3338_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_size_x27_3356_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_buckets_x27_3358_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
else
{
lean_object* v___x_3372_; lean_object* v_buckets_x27_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
lean_inc(v_bkt_3353_);
v___x_3372_ = lean_box(0);
v_buckets_x27_3373_ = lean_array_uset(v_buckets_3336_, v___x_3352_, v___x_3372_);
v___x_3374_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3333_, v_b_3334_, v_bkt_3353_);
v___x_3375_ = lean_array_uset(v_buckets_x27_3373_, v___x_3352_, v___x_3374_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 1, v___x_3375_);
v___x_3377_ = v___x_3338_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_size_3335_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(lean_object* v_a_3380_, lean_object* v_x_3381_){
_start:
{
if (lean_obj_tag(v_x_3381_) == 0)
{
lean_object* v___x_3382_; 
v___x_3382_ = lean_box(0);
return v___x_3382_;
}
else
{
lean_object* v_key_3383_; lean_object* v_value_3384_; lean_object* v_tail_3385_; uint8_t v___x_3386_; 
v_key_3383_ = lean_ctor_get(v_x_3381_, 0);
v_value_3384_ = lean_ctor_get(v_x_3381_, 1);
v_tail_3385_ = lean_ctor_get(v_x_3381_, 2);
v___x_3386_ = lean_expr_eqv(v_key_3383_, v_a_3380_);
if (v___x_3386_ == 0)
{
v_x_3381_ = v_tail_3385_;
goto _start;
}
else
{
lean_object* v___x_3388_; 
lean_inc(v_value_3384_);
v___x_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3388_, 0, v_value_3384_);
return v___x_3388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_3389_, lean_object* v_x_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3389_, v_x_3390_);
lean_dec(v_x_3390_);
lean_dec_ref(v_a_3389_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(lean_object* v_m_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v_buckets_3394_; lean_object* v___x_3395_; uint64_t v___x_3396_; uint64_t v___x_3397_; uint64_t v___x_3398_; uint64_t v_fold_3399_; uint64_t v___x_3400_; uint64_t v___x_3401_; uint64_t v___x_3402_; size_t v___x_3403_; size_t v___x_3404_; size_t v___x_3405_; size_t v___x_3406_; size_t v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v_buckets_3394_ = lean_ctor_get(v_m_3392_, 1);
v___x_3395_ = lean_array_get_size(v_buckets_3394_);
v___x_3396_ = l_Lean_Expr_hash(v_a_3393_);
v___x_3397_ = 32ULL;
v___x_3398_ = lean_uint64_shift_right(v___x_3396_, v___x_3397_);
v_fold_3399_ = lean_uint64_xor(v___x_3396_, v___x_3398_);
v___x_3400_ = 16ULL;
v___x_3401_ = lean_uint64_shift_right(v_fold_3399_, v___x_3400_);
v___x_3402_ = lean_uint64_xor(v_fold_3399_, v___x_3401_);
v___x_3403_ = lean_uint64_to_usize(v___x_3402_);
v___x_3404_ = lean_usize_of_nat(v___x_3395_);
v___x_3405_ = ((size_t)1ULL);
v___x_3406_ = lean_usize_sub(v___x_3404_, v___x_3405_);
v___x_3407_ = lean_usize_land(v___x_3403_, v___x_3406_);
v___x_3408_ = lean_array_uget_borrowed(v_buckets_3394_, v___x_3407_);
v___x_3409_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3393_, v___x_3408_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg___boxed(lean_object* v_m_3410_, lean_object* v_a_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_3410_, v_a_3411_);
lean_dec_ref(v_a_3411_);
lean_dec_ref(v_m_3410_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(lean_object* v_g_3413_, lean_object* v_e_3414_, lean_object* v_a_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_a_3424_; lean_object* v___y_3430_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3432_ = lean_st_ref_get(v_a_3415_);
v___x_3433_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v___x_3432_, v_e_3414_);
lean_dec(v___x_3432_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v___x_3434_; 
lean_inc_ref(v_g_3413_);
lean_inc(v___y_3421_);
lean_inc_ref(v___y_3420_);
lean_inc(v___y_3419_);
lean_inc_ref(v___y_3418_);
lean_inc(v___y_3417_);
lean_inc_ref(v___y_3416_);
lean_inc_ref(v_e_3414_);
v___x_3434_ = lean_apply_8(v_g_3413_, v_e_3414_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, lean_box(0));
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v_d_3437_; lean_object* v_b_3438_; lean_object* v___y_3439_; uint8_t v___x_3442_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref(v___x_3434_);
v___x_3442_ = lean_unbox(v_a_3435_);
lean_dec(v_a_3435_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3443_; 
lean_dec_ref(v_g_3413_);
v___x_3443_ = lean_box(0);
v_a_3424_ = v___x_3443_;
goto v___jp_3423_;
}
else
{
switch(lean_obj_tag(v_e_3414_))
{
case 7:
{
lean_object* v_binderType_3444_; lean_object* v_body_3445_; 
v_binderType_3444_ = lean_ctor_get(v_e_3414_, 1);
v_body_3445_ = lean_ctor_get(v_e_3414_, 2);
lean_inc_ref(v_body_3445_);
lean_inc_ref(v_binderType_3444_);
v_d_3437_ = v_binderType_3444_;
v_b_3438_ = v_body_3445_;
v___y_3439_ = v_a_3415_;
goto v___jp_3436_;
}
case 6:
{
lean_object* v_binderType_3446_; lean_object* v_body_3447_; 
v_binderType_3446_ = lean_ctor_get(v_e_3414_, 1);
v_body_3447_ = lean_ctor_get(v_e_3414_, 2);
lean_inc_ref(v_body_3447_);
lean_inc_ref(v_binderType_3446_);
v_d_3437_ = v_binderType_3446_;
v_b_3438_ = v_body_3447_;
v___y_3439_ = v_a_3415_;
goto v___jp_3436_;
}
case 8:
{
lean_object* v_type_3448_; lean_object* v_value_3449_; lean_object* v_body_3450_; lean_object* v___x_3451_; 
v_type_3448_ = lean_ctor_get(v_e_3414_, 1);
v_value_3449_ = lean_ctor_get(v_e_3414_, 2);
v_body_3450_ = lean_ctor_get(v_e_3414_, 3);
lean_inc_ref(v_type_3448_);
lean_inc_ref(v_g_3413_);
v___x_3451_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3413_, v_type_3448_, v_a_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v___x_3452_; 
lean_dec_ref(v___x_3451_);
lean_inc_ref(v_value_3449_);
lean_inc_ref(v_g_3413_);
v___x_3452_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3413_, v_value_3449_, v_a_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v___x_3453_; 
lean_dec_ref(v___x_3452_);
lean_inc_ref(v_body_3450_);
v___x_3453_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3413_, v_body_3450_, v_a_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
v___y_3430_ = v___x_3453_;
goto v___jp_3429_;
}
else
{
lean_dec_ref(v_g_3413_);
v___y_3430_ = v___x_3452_;
goto v___jp_3429_;
}
}
else
{
lean_dec_ref(v_g_3413_);
v___y_3430_ = v___x_3451_;
goto v___jp_3429_;
}
}
case 5:
{
lean_object* v_fn_3454_; lean_object* v_arg_3455_; lean_object* v___x_3456_; 
v_fn_3454_ = lean_ctor_get(v_e_3414_, 0);
v_arg_3455_ = lean_ctor_get(v_e_3414_, 1);
lean_inc_ref(v_fn_3454_);
lean_inc_ref(v_g_3413_);
v___x_3456_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3413_, v_fn_3454_, v_a_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v___x_3457_; 
lean_dec_ref(v___x_3456_);
lean_inc_ref(v_arg_3455_);
v___x_3457_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3413_, v_arg_3455_, v_a_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
v___y_3430_ = v___x_3457_;
goto v___jp_3429_;
}
else
{
lean_dec_ref(v_g_3413_);
v___y_3430_ = v___x_3456_;
goto v___jp_3429_;
}
}
case 10:
{
lean_object* v_expr_3458_; lean_object* v___x_3459_; 
v_expr_3458_ = lean_ctor_get(v_e_3414_, 1);
lean_inc_ref(v_expr_3458_);
v___x_3459_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3413_, v_expr_3458_, v_a_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
v___y_3430_ = v___x_3459_;
goto v___jp_3429_;
}
case 11:
{
lean_object* v_struct_3460_; lean_object* v___x_3461_; 
v_struct_3460_ = lean_ctor_get(v_e_3414_, 2);
lean_inc_ref(v_struct_3460_);
v___x_3461_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3413_, v_struct_3460_, v_a_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
v___y_3430_ = v___x_3461_;
goto v___jp_3429_;
}
default: 
{
lean_object* v___x_3462_; 
lean_dec_ref(v_g_3413_);
v___x_3462_ = lean_box(0);
v_a_3424_ = v___x_3462_;
goto v___jp_3423_;
}
}
}
v___jp_3436_:
{
lean_object* v___x_3440_; 
lean_inc_ref(v_g_3413_);
v___x_3440_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3413_, v_d_3437_, v___y_3439_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v___x_3441_; 
lean_dec_ref(v___x_3440_);
v___x_3441_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3413_, v_b_3438_, v___y_3439_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
v___y_3430_ = v___x_3441_;
goto v___jp_3429_;
}
else
{
lean_dec_ref(v_b_3438_);
lean_dec_ref(v_g_3413_);
v___y_3430_ = v___x_3440_;
goto v___jp_3429_;
}
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec_ref(v_e_3414_);
lean_dec_ref(v_g_3413_);
v_a_3463_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3434_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3434_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
else
{
lean_object* v_val_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec_ref(v_e_3414_);
lean_dec_ref(v_g_3413_);
v_val_3471_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3433_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_val_3471_);
lean_dec(v___x_3433_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
lean_ctor_set_tag(v___x_3473_, 0);
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_val_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
v___jp_3423_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3425_ = lean_st_ref_take(v_a_3415_);
v___x_3426_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v___x_3425_, v_e_3414_, v_a_3424_);
v___x_3427_ = lean_st_ref_set(v_a_3415_, v___x_3426_);
v___x_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3428_, 0, v_a_3424_);
return v___x_3428_;
}
v___jp_3429_:
{
if (lean_obj_tag(v___y_3430_) == 0)
{
lean_object* v_a_3431_; 
v_a_3431_ = lean_ctor_get(v___y_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref(v___y_3430_);
v_a_3424_ = v_a_3431_;
goto v___jp_3423_;
}
else
{
lean_dec_ref(v_e_3414_);
return v___y_3430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1___boxed(lean_object* v_g_3479_, lean_object* v_e_3480_, lean_object* v_a_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3479_, v_e_3480_, v_a_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v_a_3481_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared(lean_object* v_e_3490_, lean_object* v_msg_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___f_3501_; lean_object* v___x_3502_; 
v___x_3499_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_3500_ = lean_st_mk_ref(v___x_3499_);
v___f_3501_ = lean_alloc_closure((void*)(l_Lean_Expr_checkMaxShared___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3501_, 0, v_msg_3491_);
v___x_3502_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v___f_3501_, v_e_3490_, v___x_3500_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3511_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3505_ = v___x_3502_;
v_isShared_3506_ = v_isSharedCheck_3511_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3502_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3511_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3507_; lean_object* v___x_3509_; 
v___x_3507_ = lean_st_ref_get(v___x_3500_);
lean_dec(v___x_3500_);
lean_dec(v___x_3507_);
if (v_isShared_3506_ == 0)
{
v___x_3509_ = v___x_3505_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3503_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
else
{
lean_dec(v___x_3500_);
return v___x_3502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___boxed(lean_object* v_e_3512_, lean_object* v_msg_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_Expr_checkMaxShared(v_e_3512_, v_msg_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec(v_a_3515_);
lean_dec_ref(v_a_3514_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(lean_object* v_00_u03b2_3522_, lean_object* v_x_3523_, lean_object* v_x_3524_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_3523_, v_x_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(lean_object* v_00_u03b2_3526_, lean_object* v_x_3527_, size_t v_x_3528_, lean_object* v_x_3529_){
_start:
{
lean_object* v___x_3530_; 
v___x_3530_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3527_, v_x_3528_, v_x_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3531_, lean_object* v_x_3532_, lean_object* v_x_3533_, lean_object* v_x_3534_){
_start:
{
size_t v_x_8038__boxed_3535_; lean_object* v_res_3536_; 
v_x_8038__boxed_3535_ = lean_unbox_usize(v_x_3533_);
lean_dec(v_x_3533_);
v_res_3536_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(v_00_u03b2_3531_, v_x_3532_, v_x_8038__boxed_3535_, v_x_3534_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(lean_object* v_00_u03b2_3537_, lean_object* v_m_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_3538_, v_a_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3541_, lean_object* v_m_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(v_00_u03b2_3541_, v_m_3542_, v_a_3543_);
lean_dec_ref(v_a_3543_);
lean_dec_ref(v_m_3542_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(lean_object* v_00_u03b2_3545_, lean_object* v_m_3546_, lean_object* v_a_3547_, lean_object* v_b_3548_){
_start:
{
lean_object* v___x_3549_; 
v___x_3549_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v_m_3546_, v_a_3547_, v_b_3548_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3550_, lean_object* v_keys_3551_, lean_object* v_vals_3552_, lean_object* v_heq_3553_, lean_object* v_i_3554_, lean_object* v_k_3555_){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_3551_, v_vals_3552_, v_i_3554_, v_k_3555_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3557_, lean_object* v_keys_3558_, lean_object* v_vals_3559_, lean_object* v_heq_3560_, lean_object* v_i_3561_, lean_object* v_k_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(v_00_u03b2_3557_, v_keys_3558_, v_vals_3559_, v_heq_3560_, v_i_3561_, v_k_3562_);
lean_dec_ref(v_vals_3559_);
lean_dec_ref(v_keys_3558_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3564_, lean_object* v_a_3565_, lean_object* v_x_3566_){
_start:
{
lean_object* v___x_3567_; 
v___x_3567_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3565_, v_x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_3568_, lean_object* v_a_3569_, lean_object* v_x_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(v_00_u03b2_3568_, v_a_3569_, v_x_3570_);
lean_dec(v_x_3570_);
lean_dec_ref(v_a_3569_);
return v_res_3571_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_3572_, lean_object* v_a_3573_, lean_object* v_x_3574_){
_start:
{
uint8_t v___x_3575_; 
v___x_3575_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3573_, v_x_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3576_, lean_object* v_a_3577_, lean_object* v_x_3578_){
_start:
{
uint8_t v_res_3579_; lean_object* v_r_3580_; 
v_res_3579_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(v_00_u03b2_3576_, v_a_3577_, v_x_3578_);
lean_dec(v_x_3578_);
lean_dec_ref(v_a_3577_);
v_r_3580_ = lean_box(v_res_3579_);
return v_r_3580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3581_, lean_object* v_data_3582_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_data_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_3584_, lean_object* v_a_3585_, lean_object* v_b_3586_, lean_object* v_x_3587_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3585_, v_b_3586_, v_x_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_3589_, lean_object* v_i_3590_, lean_object* v_source_3591_, lean_object* v_target_3592_){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v_i_3590_, v_source_3591_, v_target_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9(lean_object* v_00_u03b2_3594_, lean_object* v_x_3595_, lean_object* v_x_3596_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_x_3595_, v_x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared(lean_object* v_mvarId_3598_, lean_object* v_msg_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_Lean_MVarId_getDecl(v_mvarId_3598_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v_type_3609_; lean_object* v___x_3610_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref(v___x_3607_);
v_type_3609_ = lean_ctor_get(v_a_3608_, 2);
lean_inc_ref(v_type_3609_);
lean_dec(v_a_3608_);
v___x_3610_ = l_Lean_Expr_checkMaxShared(v_type_3609_, v_msg_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_);
return v___x_3610_;
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec_ref(v_msg_3599_);
v_a_3611_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3607_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3607_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared___boxed(lean_object* v_mvarId_3619_, lean_object* v_msg_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_MVarId_checkMaxShared(v_mvarId_3619_, v_msg_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3625_);
lean_dec(v_a_3624_);
lean_dec_ref(v_a_3623_);
lean_dec(v_a_3622_);
lean_dec_ref(v_a_3621_);
return v_res_3628_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(lean_object* v_x_3629_){
_start:
{
uint8_t v___x_3630_; 
v___x_3630_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_3629_);
if (v___x_3630_ == 0)
{
uint8_t v___x_3631_; 
v___x_3631_ = 1;
return v___x_3631_;
}
else
{
uint8_t v___x_3632_; 
v___x_3632_ = 0;
return v___x_3632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed(lean_object* v_x_3633_){
_start:
{
uint8_t v_res_3634_; lean_object* v_r_3635_; 
v_res_3634_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(v_x_3633_);
lean_dec(v_x_3633_);
v_r_3635_ = lean_box(v_res_3634_);
return v_r_3635_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__1(lean_object* v___f_3636_, lean_object* v_x_3637_){
_start:
{
switch(lean_obj_tag(v_x_3637_))
{
case 4:
{
lean_object* v_us_3638_; uint8_t v___x_3639_; 
v_us_3638_ = lean_ctor_get(v_x_3637_, 1);
lean_inc(v_us_3638_);
lean_dec_ref(v_x_3637_);
v___x_3639_ = l_List_any___redArg(v_us_3638_, v___f_3636_);
return v___x_3639_;
}
case 3:
{
lean_object* v_u_3640_; uint8_t v___x_3641_; 
lean_dec_ref(v___f_3636_);
v_u_3640_ = lean_ctor_get(v_x_3637_, 0);
lean_inc(v_u_3640_);
lean_dec_ref(v_x_3637_);
v___x_3641_ = l_Lean_Level_isAlreadyNormalizedCheap(v_u_3640_);
lean_dec(v_u_3640_);
if (v___x_3641_ == 0)
{
uint8_t v___x_3642_; 
v___x_3642_ = 1;
return v___x_3642_;
}
else
{
uint8_t v___x_3643_; 
v___x_3643_ = 0;
return v___x_3643_;
}
}
default: 
{
uint8_t v___x_3644_; 
lean_dec_ref(v_x_3637_);
lean_dec_ref(v___f_3636_);
v___x_3644_ = 0;
return v___x_3644_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__1___boxed(lean_object* v___f_3645_, lean_object* v_x_3646_){
_start:
{
uint8_t v_res_3647_; lean_object* v_r_3648_; 
v_res_3647_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__1(v___f_3645_, v_x_3646_);
v_r_3648_ = lean_box(v_res_3647_);
return v_r_3648_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(lean_object* v_e_3652_){
_start:
{
lean_object* v___f_3653_; lean_object* v___x_3654_; 
v___f_3653_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__1));
v___x_3654_ = lean_find_expr(v___f_3653_, v_e_3652_);
if (lean_obj_tag(v___x_3654_) == 0)
{
uint8_t v___x_3655_; 
v___x_3655_ = 1;
return v___x_3655_;
}
else
{
uint8_t v___x_3656_; 
lean_dec_ref(v___x_3654_);
v___x_3656_ = 0;
return v___x_3656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___boxed(lean_object* v_e_3657_){
_start:
{
uint8_t v_res_3658_; lean_object* v_r_3659_; 
v_res_3658_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_3657_);
lean_dec_ref(v_e_3657_);
v_r_3659_ = lean_box(v_res_3658_);
return v_r_3659_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(lean_object* v_a_3660_, lean_object* v_a_3661_){
_start:
{
if (lean_obj_tag(v_a_3660_) == 0)
{
lean_object* v___x_3662_; 
v___x_3662_ = l_List_reverse___redArg(v_a_3661_);
return v___x_3662_;
}
else
{
lean_object* v_head_3663_; lean_object* v_tail_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3673_; 
v_head_3663_ = lean_ctor_get(v_a_3660_, 0);
v_tail_3664_ = lean_ctor_get(v_a_3660_, 1);
v_isSharedCheck_3673_ = !lean_is_exclusive(v_a_3660_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3666_ = v_a_3660_;
v_isShared_3667_ = v_isSharedCheck_3673_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_tail_3664_);
lean_inc(v_head_3663_);
lean_dec(v_a_3660_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3673_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3668_; lean_object* v___x_3670_; 
v___x_3668_ = l_Lean_Level_normalize(v_head_3663_);
lean_dec(v_head_3663_);
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 1, v_a_3661_);
lean_ctor_set(v___x_3666_, 0, v___x_3668_);
v___x_3670_ = v___x_3666_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3668_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v_a_3661_);
v___x_3670_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
v_a_3660_ = v_tail_3664_;
v_a_3661_ = v___x_3670_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0(lean_object* v_e_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v___y_3679_; lean_object* v___y_3683_; 
switch(lean_obj_tag(v_e_3674_))
{
case 3:
{
lean_object* v_u_3686_; lean_object* v___x_3687_; size_t v___x_3688_; size_t v___x_3689_; uint8_t v___x_3690_; 
v_u_3686_ = lean_ctor_get(v_e_3674_, 0);
v___x_3687_ = l_Lean_Level_normalize(v_u_3686_);
v___x_3688_ = lean_ptr_addr(v_u_3686_);
v___x_3689_ = lean_ptr_addr(v___x_3687_);
v___x_3690_ = lean_usize_dec_eq(v___x_3688_, v___x_3689_);
if (v___x_3690_ == 0)
{
lean_object* v___x_3691_; 
lean_dec_ref(v_e_3674_);
v___x_3691_ = l_Lean_Expr_sort___override(v___x_3687_);
v___y_3679_ = v___x_3691_;
goto v___jp_3678_;
}
else
{
lean_dec(v___x_3687_);
v___y_3679_ = v_e_3674_;
goto v___jp_3678_;
}
}
case 4:
{
lean_object* v_declName_3692_; lean_object* v_us_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; 
v_declName_3692_ = lean_ctor_get(v_e_3674_, 0);
v_us_3693_ = lean_ctor_get(v_e_3674_, 1);
v___x_3694_ = lean_box(0);
lean_inc(v_us_3693_);
v___x_3695_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(v_us_3693_, v___x_3694_);
v___x_3696_ = l_ptrEqList___redArg(v_us_3693_, v___x_3695_);
if (v___x_3696_ == 0)
{
lean_object* v___x_3697_; 
lean_inc(v_declName_3692_);
lean_dec_ref(v_e_3674_);
v___x_3697_ = l_Lean_Expr_const___override(v_declName_3692_, v___x_3695_);
v___y_3683_ = v___x_3697_;
goto v___jp_3682_;
}
else
{
lean_dec(v___x_3695_);
v___y_3683_ = v_e_3674_;
goto v___jp_3682_;
}
}
default: 
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec_ref(v_e_3674_);
v___x_3698_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
return v___x_3699_;
}
}
v___jp_3678_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3680_, 0, v___y_3679_);
v___x_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
return v___x_3681_;
}
v___jp_3682_:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3684_, 0, v___y_3683_);
v___x_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
return v___x_3685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed(lean_object* v_e_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l_Lean_Meta_Sym_normalizeLevels___lam__0(v_e_3700_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1(lean_object* v_e_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3709_, 0, v_e_3705_);
v___x_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed(lean_object* v_e_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Lean_Meta_Sym_normalizeLevels___lam__1(v_e_3711_, v___y_3712_, v___y_3713_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_ref_3716_){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3718_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_3719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3719_, 0, v_ref_3716_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
v___x_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_ref_3721_, lean_object* v___y_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_3721_);
return v_res_3723_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3724_ = lean_box(0);
v___x_3725_ = l_Lean_interruptExceptionId;
v___x_3726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
lean_ctor_set(v___x_3726_, 1, v___x_3724_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg(){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0);
v___x_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v___y_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(lean_object* v_x_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v___y_3738_; lean_object* v___y_3748_; lean_object* v___y_3749_; uint8_t v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; uint8_t v___y_3763_; lean_object* v_fileName_3768_; lean_object* v_fileMap_3769_; lean_object* v_options_3770_; lean_object* v_currRecDepth_3771_; lean_object* v_maxRecDepth_3772_; lean_object* v_ref_3773_; lean_object* v_currNamespace_3774_; lean_object* v_openDecls_3775_; lean_object* v_initHeartbeats_3776_; lean_object* v_maxHeartbeats_3777_; lean_object* v_quotContext_3778_; lean_object* v_currMacroScope_3779_; uint8_t v_diag_3780_; lean_object* v_cancelTk_x3f_3781_; uint8_t v_suppressElabErrors_3782_; lean_object* v_inheritedTraceOptions_3783_; 
v_fileName_3768_ = lean_ctor_get(v___y_3734_, 0);
v_fileMap_3769_ = lean_ctor_get(v___y_3734_, 1);
v_options_3770_ = lean_ctor_get(v___y_3734_, 2);
v_currRecDepth_3771_ = lean_ctor_get(v___y_3734_, 3);
v_maxRecDepth_3772_ = lean_ctor_get(v___y_3734_, 4);
v_ref_3773_ = lean_ctor_get(v___y_3734_, 5);
v_currNamespace_3774_ = lean_ctor_get(v___y_3734_, 6);
v_openDecls_3775_ = lean_ctor_get(v___y_3734_, 7);
v_initHeartbeats_3776_ = lean_ctor_get(v___y_3734_, 8);
v_maxHeartbeats_3777_ = lean_ctor_get(v___y_3734_, 9);
v_quotContext_3778_ = lean_ctor_get(v___y_3734_, 10);
v_currMacroScope_3779_ = lean_ctor_get(v___y_3734_, 11);
v_diag_3780_ = lean_ctor_get_uint8(v___y_3734_, sizeof(void*)*14);
v_cancelTk_x3f_3781_ = lean_ctor_get(v___y_3734_, 12);
v_suppressElabErrors_3782_ = lean_ctor_get_uint8(v___y_3734_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3783_ = lean_ctor_get(v___y_3734_, 13);
if (lean_obj_tag(v_cancelTk_x3f_3781_) == 1)
{
lean_object* v_val_3789_; uint8_t v___x_3790_; 
v_val_3789_ = lean_ctor_get(v_cancelTk_x3f_3781_, 0);
v___x_3790_ = l_IO_CancelToken_isSet(v_val_3789_);
if (v___x_3790_ == 0)
{
goto v___jp_3784_;
}
else
{
lean_object* v___x_3791_; lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_dec_ref(v_x_3732_);
v___x_3791_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3791_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3791_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
else
{
goto v___jp_3784_;
}
v___jp_3737_:
{
if (lean_obj_tag(v___y_3738_) == 0)
{
return v___y_3738_;
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
v_a_3739_ = lean_ctor_get(v___y_3738_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___y_3738_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___y_3738_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___y_3738_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
v___jp_3747_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3764_ = lean_unsigned_to_nat(1u);
v___x_3765_ = lean_nat_add(v___y_3753_, v___x_3764_);
lean_inc_ref(v___y_3755_);
lean_inc(v___y_3749_);
lean_inc(v___y_3752_);
lean_inc(v___y_3762_);
lean_inc(v___y_3760_);
lean_inc(v___y_3748_);
lean_inc(v___y_3758_);
lean_inc(v___y_3757_);
lean_inc(v___y_3759_);
lean_inc_ref(v___y_3761_);
lean_inc_ref(v___y_3754_);
lean_inc_ref(v___y_3756_);
v___x_3766_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3766_, 0, v___y_3756_);
lean_ctor_set(v___x_3766_, 1, v___y_3754_);
lean_ctor_set(v___x_3766_, 2, v___y_3761_);
lean_ctor_set(v___x_3766_, 3, v___x_3765_);
lean_ctor_set(v___x_3766_, 4, v___y_3759_);
lean_ctor_set(v___x_3766_, 5, v___y_3751_);
lean_ctor_set(v___x_3766_, 6, v___y_3757_);
lean_ctor_set(v___x_3766_, 7, v___y_3758_);
lean_ctor_set(v___x_3766_, 8, v___y_3748_);
lean_ctor_set(v___x_3766_, 9, v___y_3760_);
lean_ctor_set(v___x_3766_, 10, v___y_3762_);
lean_ctor_set(v___x_3766_, 11, v___y_3752_);
lean_ctor_set(v___x_3766_, 12, v___y_3749_);
lean_ctor_set(v___x_3766_, 13, v___y_3755_);
lean_ctor_set_uint8(v___x_3766_, sizeof(void*)*14, v___y_3750_);
lean_ctor_set_uint8(v___x_3766_, sizeof(void*)*14 + 1, v___y_3763_);
lean_inc(v___y_3735_);
lean_inc(v___y_3733_);
v___x_3767_ = lean_apply_4(v_x_3732_, v___y_3733_, v___x_3766_, v___y_3735_, lean_box(0));
v___y_3738_ = v___x_3767_;
goto v___jp_3737_;
}
v___jp_3784_:
{
lean_object* v___x_3785_; uint8_t v___x_3786_; 
v___x_3785_ = lean_unsigned_to_nat(0u);
v___x_3786_ = lean_nat_dec_eq(v_maxRecDepth_3772_, v___x_3785_);
if (v___x_3786_ == 0)
{
uint8_t v___x_3787_; 
v___x_3787_ = lean_nat_dec_eq(v_currRecDepth_3771_, v_maxRecDepth_3772_);
if (v___x_3787_ == 0)
{
lean_inc(v_ref_3773_);
v___y_3748_ = v_initHeartbeats_3776_;
v___y_3749_ = v_cancelTk_x3f_3781_;
v___y_3750_ = v_diag_3780_;
v___y_3751_ = v_ref_3773_;
v___y_3752_ = v_currMacroScope_3779_;
v___y_3753_ = v_currRecDepth_3771_;
v___y_3754_ = v_fileMap_3769_;
v___y_3755_ = v_inheritedTraceOptions_3783_;
v___y_3756_ = v_fileName_3768_;
v___y_3757_ = v_currNamespace_3774_;
v___y_3758_ = v_openDecls_3775_;
v___y_3759_ = v_maxRecDepth_3772_;
v___y_3760_ = v_maxHeartbeats_3777_;
v___y_3761_ = v_options_3770_;
v___y_3762_ = v_quotContext_3778_;
v___y_3763_ = v_suppressElabErrors_3782_;
goto v___jp_3747_;
}
else
{
lean_object* v___x_3788_; 
lean_dec_ref(v_x_3732_);
lean_inc(v_ref_3773_);
v___x_3788_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_3773_);
v___y_3738_ = v___x_3788_;
goto v___jp_3737_;
}
}
else
{
lean_inc(v_ref_3773_);
v___y_3748_ = v_initHeartbeats_3776_;
v___y_3749_ = v_cancelTk_x3f_3781_;
v___y_3750_ = v_diag_3780_;
v___y_3751_ = v_ref_3773_;
v___y_3752_ = v_currMacroScope_3779_;
v___y_3753_ = v_currRecDepth_3771_;
v___y_3754_ = v_fileMap_3769_;
v___y_3755_ = v_inheritedTraceOptions_3783_;
v___y_3756_ = v_fileName_3768_;
v___y_3757_ = v_currNamespace_3774_;
v___y_3758_ = v_openDecls_3775_;
v___y_3759_ = v_maxRecDepth_3772_;
v___y_3760_ = v_maxHeartbeats_3777_;
v___y_3761_ = v_options_3770_;
v___y_3762_ = v_quotContext_3778_;
v___y_3763_ = v_suppressElabErrors_3782_;
goto v___jp_3747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_x_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v_x_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3801_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3806_, lean_object* v_x_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3811_ = lean_apply_1(v_x_3807_, lean_box(0));
v___x_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3813_, lean_object* v_x_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(v_00_u03b1_3813_, v_x_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(lean_object* v_pre_3819_, lean_object* v_post_3820_, size_t v_sz_3821_, size_t v_i_3822_, lean_object* v_bs_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
uint8_t v___x_3828_; 
v___x_3828_ = lean_usize_dec_lt(v_i_3822_, v_sz_3821_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3829_; 
lean_dec_ref(v_post_3820_);
lean_dec_ref(v_pre_3819_);
v___x_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3829_, 0, v_bs_3823_);
return v___x_3829_;
}
else
{
lean_object* v_v_3830_; lean_object* v___x_3831_; 
v_v_3830_ = lean_array_uget_borrowed(v_bs_3823_, v_i_3822_);
lean_inc(v_v_3830_);
lean_inc_ref(v_post_3820_);
lean_inc_ref(v_pre_3819_);
v___x_3831_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3819_, v_post_3820_, v_v_3830_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3833_; lean_object* v_bs_x27_3834_; size_t v___x_3835_; size_t v___x_3836_; lean_object* v___x_3837_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3832_);
lean_dec_ref(v___x_3831_);
v___x_3833_ = lean_unsigned_to_nat(0u);
v_bs_x27_3834_ = lean_array_uset(v_bs_3823_, v_i_3822_, v___x_3833_);
v___x_3835_ = ((size_t)1ULL);
v___x_3836_ = lean_usize_add(v_i_3822_, v___x_3835_);
v___x_3837_ = lean_array_uset(v_bs_x27_3834_, v_i_3822_, v_a_3832_);
v_i_3822_ = v___x_3836_;
v_bs_3823_ = v___x_3837_;
goto _start;
}
else
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3846_; 
lean_dec_ref(v_bs_3823_);
lean_dec_ref(v_post_3820_);
lean_dec_ref(v_pre_3819_);
v_a_3839_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3841_ = v___x_3831_;
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3831_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3844_; 
if (v_isShared_3842_ == 0)
{
v___x_3844_ = v___x_3841_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_a_3839_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(lean_object* v_pre_3847_, lean_object* v_post_3848_, lean_object* v_x_3849_, lean_object* v_x_3850_, lean_object* v_x_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
if (lean_obj_tag(v_x_3849_) == 5)
{
lean_object* v_fn_3856_; lean_object* v_arg_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v_fn_3856_ = lean_ctor_get(v_x_3849_, 0);
lean_inc_ref(v_fn_3856_);
v_arg_3857_ = lean_ctor_get(v_x_3849_, 1);
lean_inc_ref(v_arg_3857_);
lean_dec_ref(v_x_3849_);
v___x_3858_ = lean_array_set(v_x_3850_, v_x_3851_, v_arg_3857_);
v___x_3859_ = lean_unsigned_to_nat(1u);
v___x_3860_ = lean_nat_sub(v_x_3851_, v___x_3859_);
lean_dec(v_x_3851_);
v_x_3849_ = v_fn_3856_;
v_x_3850_ = v___x_3858_;
v_x_3851_ = v___x_3860_;
goto _start;
}
else
{
lean_object* v___x_3862_; 
lean_dec(v_x_3851_);
lean_inc_ref(v_post_3848_);
lean_inc_ref(v_pre_3847_);
v___x_3862_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3847_, v_post_3848_, v_x_3849_, v___y_3852_, v___y_3853_, v___y_3854_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v_a_3863_; size_t v_sz_3864_; size_t v___x_3865_; lean_object* v___x_3866_; 
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref(v___x_3862_);
v_sz_3864_ = lean_array_size(v_x_3850_);
v___x_3865_ = ((size_t)0ULL);
lean_inc_ref(v_post_3848_);
lean_inc_ref(v_pre_3847_);
v___x_3866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_3847_, v_post_3848_, v_sz_3864_, v___x_3865_, v_x_3850_, v___y_3852_, v___y_3853_, v___y_3854_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref(v___x_3866_);
v___x_3868_ = l_Lean_mkAppN(v_a_3863_, v_a_3867_);
lean_dec(v_a_3867_);
v___x_3869_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3847_, v_post_3848_, v___x_3868_, v___y_3852_, v___y_3853_, v___y_3854_);
return v___x_3869_;
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_dec(v_a_3863_);
lean_dec_ref(v_post_3848_);
lean_dec_ref(v_pre_3847_);
v_a_3870_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3866_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3866_);
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
lean_dec_ref(v_x_3850_);
lean_dec_ref(v_post_3848_);
lean_dec_ref(v_pre_3847_);
return v___x_3862_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(lean_object* v___x_3878_, lean_object* v_pre_3879_, lean_object* v_e_3880_, lean_object* v_post_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; uint8_t v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; uint8_t v___y_3894_; lean_object* v___y_3904_; lean_object* v___y_3905_; uint8_t v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; uint8_t v___y_3909_; lean_object* v___y_3917_; uint8_t v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; uint8_t v___y_3922_; lean_object* v___x_3929_; 
v___x_3929_ = l_Lean_Core_checkSystem(v___x_3878_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v___x_3930_; 
lean_dec_ref(v___x_3929_);
lean_inc_ref(v_pre_3879_);
lean_inc(v___y_3884_);
lean_inc_ref(v___y_3883_);
lean_inc_ref(v_e_3880_);
v___x_3930_ = lean_apply_4(v_pre_3879_, v_e_3880_, v___y_3883_, v___y_3884_, lean_box(0));
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_4020_; 
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_3933_ = v___x_3930_;
v_isShared_3934_ = v_isSharedCheck_4020_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3930_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_4020_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___y_3936_; 
switch(lean_obj_tag(v_a_3931_))
{
case 0:
{
lean_object* v_e_4010_; lean_object* v___x_4012_; 
lean_dec_ref(v_post_3881_);
lean_dec_ref(v_e_3880_);
lean_dec_ref(v_pre_3879_);
v_e_4010_ = lean_ctor_get(v_a_3931_, 0);
lean_inc_ref(v_e_4010_);
lean_dec_ref(v_a_3931_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v_e_4010_);
v___x_4012_ = v___x_3933_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_e_4010_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
case 1:
{
lean_object* v_e_4014_; lean_object* v___x_4015_; 
lean_del_object(v___x_3933_);
lean_dec_ref(v_e_3880_);
v_e_4014_ = lean_ctor_get(v_a_3931_, 0);
lean_inc_ref(v_e_4014_);
lean_dec_ref(v_a_3931_);
lean_inc_ref(v_post_3881_);
lean_inc_ref(v_pre_3879_);
v___x_4015_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3879_, v_post_3881_, v_e_4014_, v___y_3882_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___x_4017_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref(v___x_4015_);
v___x_4017_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v_a_4016_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_4017_;
}
else
{
lean_dec_ref(v_post_3881_);
lean_dec_ref(v_pre_3879_);
return v___x_4015_;
}
}
default: 
{
lean_object* v_e_x3f_4018_; 
lean_del_object(v___x_3933_);
v_e_x3f_4018_ = lean_ctor_get(v_a_3931_, 0);
lean_inc(v_e_x3f_4018_);
lean_dec_ref(v_a_3931_);
if (lean_obj_tag(v_e_x3f_4018_) == 0)
{
v___y_3936_ = v_e_3880_;
goto v___jp_3935_;
}
else
{
lean_object* v_val_4019_; 
lean_dec_ref(v_e_3880_);
v_val_4019_ = lean_ctor_get(v_e_x3f_4018_, 0);
lean_inc(v_val_4019_);
lean_dec_ref(v_e_x3f_4018_);
v___y_3936_ = v_val_4019_;
goto v___jp_3935_;
}
}
}
v___jp_3935_:
{
switch(lean_obj_tag(v___y_3936_))
{
case 7:
{
lean_object* v_binderName_3937_; lean_object* v_binderType_3938_; lean_object* v_body_3939_; uint8_t v_binderInfo_3940_; lean_object* v___x_3941_; 
v_binderName_3937_ = lean_ctor_get(v___y_3936_, 0);
lean_inc(v_binderName_3937_);
v_binderType_3938_ = lean_ctor_get(v___y_3936_, 1);
v_body_3939_ = lean_ctor_get(v___y_3936_, 2);
v_binderInfo_3940_ = lean_ctor_get_uint8(v___y_3936_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3938_);
lean_inc_ref(v_post_3881_);
lean_inc_ref(v_pre_3879_);
v___x_3941_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3879_, v_post_3881_, v_binderType_3938_, v___y_3882_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; lean_object* v___x_3943_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3942_);
lean_dec_ref(v___x_3941_);
lean_inc_ref(v_body_3939_);
lean_inc_ref(v_post_3881_);
lean_inc_ref(v_pre_3879_);
v___x_3943_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3879_, v_post_3881_, v_body_3939_, v___y_3882_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; size_t v___x_3945_; size_t v___x_3946_; uint8_t v___x_3947_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref(v___x_3943_);
v___x_3945_ = lean_ptr_addr(v_binderType_3938_);
v___x_3946_ = lean_ptr_addr(v_a_3942_);
v___x_3947_ = lean_usize_dec_eq(v___x_3945_, v___x_3946_);
if (v___x_3947_ == 0)
{
v___y_3917_ = v_binderName_3937_;
v___y_3918_ = v_binderInfo_3940_;
v___y_3919_ = v_a_3944_;
v___y_3920_ = v_a_3942_;
v___y_3921_ = v___y_3936_;
v___y_3922_ = v___x_3947_;
goto v___jp_3916_;
}
else
{
size_t v___x_3948_; size_t v___x_3949_; uint8_t v___x_3950_; 
v___x_3948_ = lean_ptr_addr(v_body_3939_);
v___x_3949_ = lean_ptr_addr(v_a_3944_);
v___x_3950_ = lean_usize_dec_eq(v___x_3948_, v___x_3949_);
v___y_3917_ = v_binderName_3937_;
v___y_3918_ = v_binderInfo_3940_;
v___y_3919_ = v_a_3944_;
v___y_3920_ = v_a_3942_;
v___y_3921_ = v___y_3936_;
v___y_3922_ = v___x_3950_;
goto v___jp_3916_;
}
}
else
{
lean_dec(v_a_3942_);
lean_dec_ref(v___y_3936_);
lean_dec(v_binderName_3937_);
lean_dec_ref(v_post_3881_);
lean_dec_ref(v_pre_3879_);
return v___x_3943_;
}
}
else
{
lean_dec_ref(v___y_3936_);
lean_dec(v_binderName_3937_);
lean_dec_ref(v_post_3881_);
lean_dec_ref(v_pre_3879_);
return v___x_3941_;
}
}
case 6:
{
lean_object* v_binderName_3951_; lean_object* v_binderType_3952_; lean_object* v_body_3953_; uint8_t v_binderInfo_3954_; lean_object* v___x_3955_; 
v_binderName_3951_ = lean_ctor_get(v___y_3936_, 0);
lean_inc(v_binderName_3951_);
v_binderType_3952_ = lean_ctor_get(v___y_3936_, 1);
v_body_3953_ = lean_ctor_get(v___y_3936_, 2);
v_binderInfo_3954_ = lean_ctor_get_uint8(v___y_3936_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3952_);
lean_inc_ref(v_post_3881_);
lean_inc_ref(v_pre_3879_);
v___x_3955_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3879_, v_post_3881_, v_binderType_3952_, v___y_3882_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3957_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3956_);
lean_dec_ref(v___x_3955_);
lean_inc_ref(v_body_3953_);
lean_inc_ref(v_post_3881_);
lean_inc_ref(v_pre_3879_);
v___x_3957_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3879_, v_post_3881_, v_body_3953_, v___y_3882_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; size_t v___x_3959_; size_t v___x_3960_; uint8_t v___x_3961_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref(v___x_3957_);
v___x_3959_ = lean_ptr_addr(v_binderType_3952_);
v___x_3960_ = lean_ptr_addr(v_a_3956_);
v___x_3961_ = lean_usize_dec_eq(v___x_3959_, v___x_3960_);
if (v___x_3961_ == 0)
{
v___y_3904_ = v_a_3956_;
v___y_3905_ = v_binderName_3951_;
v___y_3906_ = v_binderInfo_3954_;
v___y_3907_ = v_a_3958_;
v___y_3908_ = v___y_3936_;
v___y_3909_ = v___x_3961_;
goto v___jp_3903_;
}
else
{
size_t v___x_3962_; size_t v___x_3963_; uint8_t v___x_3964_; 
v___x_3962_ = lean_ptr_addr(v_body_3953_);
v___x_3963_ = lean_ptr_addr(v_a_3958_);
v___x_3964_ = lean_usize_dec_eq(v___x_3962_, v___x_3963_);
v___y_3904_ = v_a_3956_;
v___y_3905_ = v_binderName_3951_;
v___y_3906_ = v_binderInfo_3954_;
v___y_3907_ = v_a_3958_;
v___y_3908_ = v___y_3936_;
v___y_3909_ = v___x_3964_;
goto v___jp_3903_;
}
}
else
{
lean_dec(v_a_3956_);
lean_dec(v_binderName_3951_);
lean_dec_ref(v___y_3936_);
lean_dec_ref(v_post_3881_);
lean_dec_ref(v_pre_3879_);
return v___x_3957_;
}
}
else
{
lean_dec(v_binderName_3951_);
lean_dec_ref(v___y_3936_);
lean_dec_ref(v_post_3881_);
lean_dec_ref(v_pre_3879_);
return v___x_3955_;
}
}
case 8:
{
lean_object* v_declName_3965_; lean_object* v_type_3966_; lean_object* v_value_3967_; lean_object* v_body_3968_; uint8_t v_nondep_3969_; lean_object* v___x_3970_; 
v_declName_3965_ = lean_ctor_get(v___y_3936_, 0);
lean_inc(v_declName_3965_);
v_type_3966_ = lean_ctor_get(v___y_3936_, 1);
v_value_3967_ = lean_ctor_get(v___y_3936_, 2);
v_body_3968_ = lean_ctor_get(v___y_3936_, 3);
lean_inc_ref(v_body_3968_);
v_nondep_3969_ = lean_ctor_get_uint8(v___y_3936_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_3966_);
lean_inc_ref(v_post_3881_);
lean_inc_ref(v_pre_3879_);
v___x_3970_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3879_, v_post_3881_, v_type_3966_, v___y_3882_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3972_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_a_3971_);
lean_dec_ref(v___x_3970_);
lean_inc_ref(v_value_3967_);
lean_inc_ref(v_post_3881_);
lean_inc_ref(v_pre_3879_);
v___x_3972_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3879_, v_post_3881_, v_value_3967_, v___y_3882_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3974_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref(v___x_3972_);
lean_inc_ref(v_body_3968_);
lean_inc_ref(v_post_3881_);
lean_inc_ref(v_pre_3879_);
v___x_3974_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3879_, v_post_3881_, v_body_3968_, v___y_3882_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; size_t v___x_3976_; size_t v___x_3977_; uint8_t v___x_3978_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_a_3975_);
lean_dec_ref(v___x_3974_);
v___x_3976_ = lean_ptr_addr(v_type_3966_);
v___x_3977_ = lean_ptr_addr(v_a_3971_);
v___x_3978_ = lean_usize_dec_eq(v___x_3976_, v___x_3977_);
if (v___x_3978_ == 0)
{
v___y_3887_ = v_body_3968_;
v___y_3888_ = v_a_3971_;
v___y_3889_ = v_declName_3965_;
v___y_3890_ = v_a_3973_;
v___y_3891_ = v_nondep_3969_;
v___y_3892_ = v_a_3975_;
v___y_3893_ = v___y_3936_;
v___y_3894_ = v___x_3978_;
goto v___jp_3886_;
}
else
{
size_t v___x_3979_; size_t v___x_3980_; uint8_t v___x_3981_; 
v___x_3979_ = lean_ptr_addr(v_value_3967_);
v___x_3980_ = lean_ptr_addr(v_a_3973_);
v___x_3981_ = lean_usize_dec_eq(v___x_3979_, v___x_3980_);
v___y_3887_ = v_body_3968_;
v___y_3888_ = v_a_3971_;
v___y_3889_ = v_declName_3965_;
v___y_3890_ = v_a_3973_;
v___y_3891_ = v_nondep_3969_;
v___y_3892_ = v_a_3975_;
v___y_3893_ = v___y_3936_;
v___y_3894_ = v___x_3981_;
goto v___jp_3886_;
}
}
else
{
lean_dec(v_a_3973_);
lean_dec(v_a_3971_);
lean_dec_ref(v_body_3968_);
lean_dec_ref(v___y_3936_);
lean_dec(v_declName_3965_);
lean_dec_ref(v_post_3881_);
lean_dec_ref(v_pre_3879_);
return v___x_3974_;
}
}
else
{
lean_dec(v_a_3971_);
lean_dec_ref(v_body_3968_);
lean_dec_ref(v___y_3936_);
lean_dec(v_declName_3965_);
lean_dec_ref(v_post_3881_);
lean_dec_ref(v_pre_3879_);
return v___x_3972_;
}
}
else
{
lean_dec_ref(v_body_3968_);
lean_dec(v_declName_3965_);
lean_dec_ref(v___y_3936_);
lean_dec_ref(v_post_3881_);
lean_dec_ref(v_pre_3879_);
return v___x_3970_;
}
}
case 5:
{
lean_object* v_dummy_3982_; lean_object* v_nargs_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v_dummy_3982_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_3983_ = l_Lean_Expr_getAppNumArgs(v___y_3936_);
lean_inc(v_nargs_3983_);
v___x_3984_ = lean_mk_array(v_nargs_3983_, v_dummy_3982_);
v___x_3985_ = lean_unsigned_to_nat(1u);
v___x_3986_ = lean_nat_sub(v_nargs_3983_, v___x_3985_);
lean_dec(v_nargs_3983_);
v___x_3987_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_3879_, v_post_3881_, v___y_3936_, v___x_3984_, v___x_3986_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3987_;
}
case 10:
{
lean_object* v_data_3988_; lean_object* v_expr_3989_; lean_object* v___x_3990_; 
v_data_3988_ = lean_ctor_get(v___y_3936_, 0);
v_expr_3989_ = lean_ctor_get(v___y_3936_, 1);
lean_inc_ref(v_expr_3989_);
lean_inc_ref(v_post_3881_);
lean_inc_ref(v_pre_3879_);
v___x_3990_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3879_, v_post_3881_, v_expr_3989_, v___y_3882_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; size_t v___x_3992_; size_t v___x_3993_; uint8_t v___x_3994_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_a_3991_);
lean_dec_ref(v___x_3990_);
v___x_3992_ = lean_ptr_addr(v_expr_3989_);
v___x_3993_ = lean_ptr_addr(v_a_3991_);
v___x_3994_ = lean_usize_dec_eq(v___x_3992_, v___x_3993_);
if (v___x_3994_ == 0)
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
lean_inc(v_data_3988_);
lean_dec_ref(v___y_3936_);
v___x_3995_ = l_Lean_Expr_mdata___override(v_data_3988_, v_a_3991_);
v___x_3996_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v___x_3995_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3996_;
}
else
{
lean_object* v___x_3997_; 
lean_dec(v_a_3991_);
v___x_3997_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v___y_3936_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3997_;
}
}
else
{
lean_dec_ref(v___y_3936_);
lean_dec_ref(v_post_3881_);
lean_dec_ref(v_pre_3879_);
return v___x_3990_;
}
}
case 11:
{
lean_object* v_typeName_3998_; lean_object* v_idx_3999_; lean_object* v_struct_4000_; lean_object* v___x_4001_; 
v_typeName_3998_ = lean_ctor_get(v___y_3936_, 0);
v_idx_3999_ = lean_ctor_get(v___y_3936_, 1);
v_struct_4000_ = lean_ctor_get(v___y_3936_, 2);
lean_inc_ref(v_struct_4000_);
lean_inc_ref(v_post_3881_);
lean_inc_ref(v_pre_3879_);
v___x_4001_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3879_, v_post_3881_, v_struct_4000_, v___y_3882_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; size_t v___x_4003_; size_t v___x_4004_; uint8_t v___x_4005_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref(v___x_4001_);
v___x_4003_ = lean_ptr_addr(v_struct_4000_);
v___x_4004_ = lean_ptr_addr(v_a_4002_);
v___x_4005_ = lean_usize_dec_eq(v___x_4003_, v___x_4004_);
if (v___x_4005_ == 0)
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
lean_inc(v_idx_3999_);
lean_inc(v_typeName_3998_);
lean_dec_ref(v___y_3936_);
v___x_4006_ = l_Lean_Expr_proj___override(v_typeName_3998_, v_idx_3999_, v_a_4002_);
v___x_4007_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v___x_4006_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_4007_;
}
else
{
lean_object* v___x_4008_; 
lean_dec(v_a_4002_);
v___x_4008_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v___y_3936_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_4008_;
}
}
else
{
lean_dec_ref(v___y_3936_);
lean_dec_ref(v_post_3881_);
lean_dec_ref(v_pre_3879_);
return v___x_4001_;
}
}
default: 
{
lean_object* v___x_4009_; 
v___x_4009_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v___y_3936_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_4009_;
}
}
}
}
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_dec_ref(v_post_3881_);
lean_dec_ref(v_e_3880_);
lean_dec_ref(v_pre_3879_);
v_a_4021_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_3930_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_3930_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_dec_ref(v_post_3881_);
lean_dec_ref(v_e_3880_);
lean_dec_ref(v_pre_3879_);
v_a_4029_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_3929_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_3929_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
v___jp_3886_:
{
if (v___y_3894_ == 0)
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
lean_dec_ref(v___y_3893_);
lean_dec_ref(v___y_3887_);
v___x_3895_ = l_Lean_Expr_letE___override(v___y_3889_, v___y_3888_, v___y_3890_, v___y_3892_, v___y_3891_);
v___x_3896_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v___x_3895_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3896_;
}
else
{
size_t v___x_3897_; size_t v___x_3898_; uint8_t v___x_3899_; 
v___x_3897_ = lean_ptr_addr(v___y_3887_);
lean_dec_ref(v___y_3887_);
v___x_3898_ = lean_ptr_addr(v___y_3892_);
v___x_3899_ = lean_usize_dec_eq(v___x_3897_, v___x_3898_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
lean_dec_ref(v___y_3893_);
v___x_3900_ = l_Lean_Expr_letE___override(v___y_3889_, v___y_3888_, v___y_3890_, v___y_3892_, v___y_3891_);
v___x_3901_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v___x_3900_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3901_;
}
else
{
lean_object* v___x_3902_; 
lean_dec_ref(v___y_3892_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
v___x_3902_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v___y_3893_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3902_;
}
}
}
v___jp_3903_:
{
if (v___y_3909_ == 0)
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
lean_dec_ref(v___y_3908_);
v___x_3910_ = l_Lean_Expr_lam___override(v___y_3905_, v___y_3904_, v___y_3907_, v___y_3906_);
v___x_3911_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v___x_3910_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3911_;
}
else
{
uint8_t v___x_3912_; 
v___x_3912_ = l_Lean_instBEqBinderInfo_beq(v___y_3906_, v___y_3906_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
lean_dec_ref(v___y_3908_);
v___x_3913_ = l_Lean_Expr_lam___override(v___y_3905_, v___y_3904_, v___y_3907_, v___y_3906_);
v___x_3914_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v___x_3913_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3914_;
}
else
{
lean_object* v___x_3915_; 
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
v___x_3915_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v___y_3908_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3915_;
}
}
}
v___jp_3916_:
{
if (v___y_3922_ == 0)
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
lean_dec_ref(v___y_3921_);
v___x_3923_ = l_Lean_Expr_forallE___override(v___y_3917_, v___y_3920_, v___y_3919_, v___y_3918_);
v___x_3924_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v___x_3923_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3924_;
}
else
{
uint8_t v___x_3925_; 
v___x_3925_ = l_Lean_instBEqBinderInfo_beq(v___y_3918_, v___y_3918_);
if (v___x_3925_ == 0)
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
lean_dec_ref(v___y_3921_);
v___x_3926_ = l_Lean_Expr_forallE___override(v___y_3917_, v___y_3920_, v___y_3919_, v___y_3918_);
v___x_3927_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v___x_3926_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3927_;
}
else
{
lean_object* v___x_3928_; 
lean_dec_ref(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3917_);
v___x_3928_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3879_, v_post_3881_, v___y_3921_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4037_, lean_object* v_pre_4038_, lean_object* v_e_4039_, lean_object* v_post_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(v___x_4037_, v_pre_4038_, v_e_4039_, v_post_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(lean_object* v_pre_4046_, lean_object* v_post_4047_, lean_object* v_e_4048_, lean_object* v_a_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; 
lean_inc(v_a_4049_);
v___x_4053_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4053_, 0, lean_box(0));
lean_closure_set(v___x_4053_, 1, lean_box(0));
lean_closure_set(v___x_4053_, 2, v_a_4049_);
v___x_4054_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___x_4053_, v___y_4050_, v___y_4051_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4086_; 
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4057_ = v___x_4054_;
v_isShared_4058_ = v_isSharedCheck_4086_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4054_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4086_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4059_; 
v___x_4059_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_4055_, v_e_4048_);
lean_dec(v_a_4055_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v___x_4060_; lean_object* v___f_4061_; lean_object* v___x_4062_; 
lean_del_object(v___x_4057_);
v___x_4060_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_4048_);
v___f_4061_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed), 8, 4);
lean_closure_set(v___f_4061_, 0, v___x_4060_);
lean_closure_set(v___f_4061_, 1, v_pre_4046_);
lean_closure_set(v___f_4061_, 2, v_e_4048_);
lean_closure_set(v___f_4061_, 3, v_post_4047_);
v___x_4062_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v___f_4061_, v_a_4049_, v___y_4050_, v___y_4051_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v___f_4064_; lean_object* v___x_4065_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc_n(v_a_4063_, 2);
lean_dec_ref(v___x_4062_);
lean_inc(v_a_4049_);
v___f_4064_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4064_, 0, v_a_4049_);
lean_closure_set(v___f_4064_, 1, v_e_4048_);
lean_closure_set(v___f_4064_, 2, v_a_4063_);
v___x_4065_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___f_4064_, v___y_4050_, v___y_4051_);
if (lean_obj_tag(v___x_4065_) == 0)
{
lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4072_ == 0)
{
lean_object* v_unused_4073_; 
v_unused_4073_ = lean_ctor_get(v___x_4065_, 0);
lean_dec(v_unused_4073_);
v___x_4067_ = v___x_4065_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_dec(v___x_4065_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 0, v_a_4063_);
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4063_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_dec(v_a_4063_);
v_a_4074_ = lean_ctor_get(v___x_4065_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4065_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4065_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
else
{
lean_dec_ref(v_e_4048_);
return v___x_4062_;
}
}
else
{
lean_object* v_val_4082_; lean_object* v___x_4084_; 
lean_dec_ref(v_e_4048_);
lean_dec_ref(v_post_4047_);
lean_dec_ref(v_pre_4046_);
v_val_4082_ = lean_ctor_get(v___x_4059_, 0);
lean_inc(v_val_4082_);
lean_dec_ref(v___x_4059_);
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 0, v_val_4082_);
v___x_4084_ = v___x_4057_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_val_4082_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
lean_dec_ref(v_e_4048_);
lean_dec_ref(v_post_4047_);
lean_dec_ref(v_pre_4046_);
v_a_4087_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4054_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4054_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(lean_object* v_pre_4095_, lean_object* v_post_4096_, lean_object* v_e_4097_, lean_object* v_a_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
lean_inc_ref(v_post_4096_);
lean_inc(v___y_4100_);
lean_inc_ref(v___y_4099_);
lean_inc_ref(v_e_4097_);
v___x_4102_ = lean_apply_4(v_post_4096_, v_e_4097_, v___y_4099_, v___y_4100_, lean_box(0));
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4121_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4105_ = v___x_4102_;
v_isShared_4106_ = v_isSharedCheck_4121_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4102_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4121_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
switch(lean_obj_tag(v_a_4103_))
{
case 0:
{
lean_object* v_e_4107_; lean_object* v___x_4109_; 
lean_dec_ref(v_e_4097_);
lean_dec_ref(v_post_4096_);
lean_dec_ref(v_pre_4095_);
v_e_4107_ = lean_ctor_get(v_a_4103_, 0);
lean_inc_ref(v_e_4107_);
lean_dec_ref(v_a_4103_);
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 0, v_e_4107_);
v___x_4109_ = v___x_4105_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_e_4107_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
case 1:
{
lean_object* v_e_4111_; lean_object* v___x_4112_; 
lean_del_object(v___x_4105_);
lean_dec_ref(v_e_4097_);
v_e_4111_ = lean_ctor_get(v_a_4103_, 0);
lean_inc_ref(v_e_4111_);
lean_dec_ref(v_a_4103_);
v___x_4112_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4095_, v_post_4096_, v_e_4111_, v_a_4098_, v___y_4099_, v___y_4100_);
return v___x_4112_;
}
default: 
{
lean_object* v_e_x3f_4113_; 
lean_dec_ref(v_post_4096_);
lean_dec_ref(v_pre_4095_);
v_e_x3f_4113_ = lean_ctor_get(v_a_4103_, 0);
lean_inc(v_e_x3f_4113_);
lean_dec_ref(v_a_4103_);
if (lean_obj_tag(v_e_x3f_4113_) == 0)
{
lean_object* v___x_4115_; 
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 0, v_e_4097_);
v___x_4115_ = v___x_4105_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_e_4097_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
else
{
lean_object* v_val_4117_; lean_object* v___x_4119_; 
lean_dec_ref(v_e_4097_);
v_val_4117_ = lean_ctor_get(v_e_x3f_4113_, 0);
lean_inc(v_val_4117_);
lean_dec_ref(v_e_x3f_4113_);
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 0, v_val_4117_);
v___x_4119_ = v___x_4105_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_val_4117_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
}
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
lean_dec_ref(v_e_4097_);
lean_dec_ref(v_post_4096_);
lean_dec_ref(v_pre_4095_);
v_a_4122_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4102_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4102_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4130_, lean_object* v_post_4131_, lean_object* v_e_4132_, lean_object* v_a_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4130_, v_post_4131_, v_e_4132_, v_a_4133_, v___y_4134_, v___y_4135_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v_a_4133_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4138_, lean_object* v_post_4139_, lean_object* v_sz_4140_, lean_object* v_i_4141_, lean_object* v_bs_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
size_t v_sz_boxed_4147_; size_t v_i_boxed_4148_; lean_object* v_res_4149_; 
v_sz_boxed_4147_ = lean_unbox_usize(v_sz_4140_);
lean_dec(v_sz_4140_);
v_i_boxed_4148_ = lean_unbox_usize(v_i_4141_);
lean_dec(v_i_4141_);
v_res_4149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_4138_, v_post_4139_, v_sz_boxed_4147_, v_i_boxed_4148_, v_bs_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___boxed(lean_object* v_pre_4150_, lean_object* v_post_4151_, lean_object* v_x_4152_, lean_object* v_x_4153_, lean_object* v_x_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_4150_, v_post_4151_, v_x_4152_, v_x_4153_, v_x_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___boxed(lean_object* v_pre_4160_, lean_object* v_post_4161_, lean_object* v_e_4162_, lean_object* v_a_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4160_, v_post_4161_, v_e_4162_, v_a_4163_, v___y_4164_, v___y_4165_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v_a_4163_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_object* v_00_u03b1_4168_, lean_object* v_x_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = lean_apply_1(v_x_4169_, lean_box(0));
v___x_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0___boxed(lean_object* v_00_u03b1_4175_, lean_object* v_x_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(v_00_u03b1_4175_, v_x_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(lean_object* v_input_4181_, lean_object* v_pre_4182_, lean_object* v_post_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v_a_4189_; lean_object* v___x_4190_; 
v___x_4187_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_4188_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_4187_, v___y_4184_, v___y_4185_);
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_a_4189_);
lean_dec_ref(v___x_4188_);
v___x_4190_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4182_, v_post_4183_, v_input_4181_, v_a_4189_, v___y_4184_, v___y_4185_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v_a_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_a_4191_);
lean_dec_ref(v___x_4190_);
v___x_4192_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4192_, 0, lean_box(0));
lean_closure_set(v___x_4192_, 1, lean_box(0));
lean_closure_set(v___x_4192_, 2, v_a_4189_);
v___x_4193_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_4192_, v___y_4184_, v___y_4185_);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4200_ == 0)
{
lean_object* v_unused_4201_; 
v_unused_4201_ = lean_ctor_get(v___x_4193_, 0);
lean_dec(v_unused_4201_);
v___x_4195_ = v___x_4193_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_dec(v___x_4193_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 0, v_a_4191_);
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_a_4191_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
else
{
lean_dec(v_a_4189_);
return v___x_4190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___boxed(lean_object* v_input_4202_, lean_object* v_pre_4203_, lean_object* v_post_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_input_4202_, v_pre_4203_, v_post_4204_, v___y_4205_, v___y_4206_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object* v_e_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_){
_start:
{
uint8_t v___x_4215_; 
v___x_4215_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_4211_);
if (v___x_4215_ == 0)
{
lean_object* v_pre_4216_; lean_object* v___f_4217_; lean_object* v___x_4218_; 
v_pre_4216_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__0));
v___f_4217_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__1));
v___x_4218_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_e_4211_, v_pre_4216_, v___f_4217_, v_a_4212_, v_a_4213_);
return v___x_4218_;
}
else
{
lean_object* v___x_4219_; 
v___x_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4219_, 0, v_e_4211_);
return v___x_4219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___boxed(lean_object* v_e_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l_Lean_Meta_Sym_normalizeLevels(v_e_4220_, v_a_4221_, v_a_4222_);
lean_dec(v_a_4222_);
lean_dec_ref(v_a_4221_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4225_, lean_object* v_ref_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v___x_4230_; 
v___x_4230_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_4226_);
return v___x_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4231_, lean_object* v_ref_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_){
_start:
{
lean_object* v_res_4236_; 
v_res_4236_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4231_, v_ref_4232_, v___y_4233_, v___y_4234_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
return v_res_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v___x_4241_; 
v___x_4241_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
return v___x_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7(v_00_u03b1_4242_, v___y_4243_, v___y_4244_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(lean_object* v_00_u03b1_4247_, lean_object* v_x_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v_x_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b1_4254_, lean_object* v_x_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_00_u03b1_4254_, v_x_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
return v_res_4260_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
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
