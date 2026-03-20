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
uint8_t l_Lean_Meta_Sym_instBEqAlphaKey___private__1(lean_object*, lean_object*);
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
uint64_t l_Lean_Meta_Sym_instHashableAlphaKey___private__1(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_declName_65_);
lean_dec_ref(v___x_64_);
lean_inc(v_declName_65_);
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
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
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
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
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
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
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
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
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
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
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
lean_inc(v_declName_151_);
lean_dec_ref(v_e_150_);
lean_inc(v_declName_151_);
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
lean_object* v___y_395_; lean_object* v_fileName_404_; lean_object* v_fileMap_405_; lean_object* v_options_406_; lean_object* v_currRecDepth_407_; lean_object* v_maxRecDepth_408_; lean_object* v_ref_409_; lean_object* v_currNamespace_410_; lean_object* v_openDecls_411_; lean_object* v_initHeartbeats_412_; lean_object* v_maxHeartbeats_413_; lean_object* v_quotContext_414_; lean_object* v_currMacroScope_415_; uint8_t v_diag_416_; lean_object* v_cancelTk_x3f_417_; uint8_t v_suppressElabErrors_418_; lean_object* v_inheritedTraceOptions_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_431_; 
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
v_isSharedCheck_431_ = !lean_is_exclusive(v___y_391_);
if (v_isSharedCheck_431_ == 0)
{
v___x_421_ = v___y_391_;
v_isShared_422_ = v_isSharedCheck_431_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_inheritedTraceOptions_419_);
lean_inc(v_cancelTk_x3f_417_);
lean_inc(v_currMacroScope_415_);
lean_inc(v_quotContext_414_);
lean_inc(v_maxHeartbeats_413_);
lean_inc(v_initHeartbeats_412_);
lean_inc(v_openDecls_411_);
lean_inc(v_currNamespace_410_);
lean_inc(v_ref_409_);
lean_inc(v_maxRecDepth_408_);
lean_inc(v_currRecDepth_407_);
lean_inc(v_options_406_);
lean_inc(v_fileMap_405_);
lean_inc(v_fileName_404_);
lean_dec(v___y_391_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_431_;
goto v_resetjp_420_;
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
v_resetjp_420_:
{
uint8_t v___x_423_; 
v___x_423_ = lean_nat_dec_eq(v_currRecDepth_407_, v_maxRecDepth_408_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = lean_nat_add(v_currRecDepth_407_, v___x_424_);
lean_dec(v_currRecDepth_407_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 3, v___x_425_);
v___x_427_ = v___x_421_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_fileName_404_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_fileMap_405_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v_options_406_);
lean_ctor_set(v_reuseFailAlloc_429_, 3, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_429_, 4, v_maxRecDepth_408_);
lean_ctor_set(v_reuseFailAlloc_429_, 5, v_ref_409_);
lean_ctor_set(v_reuseFailAlloc_429_, 6, v_currNamespace_410_);
lean_ctor_set(v_reuseFailAlloc_429_, 7, v_openDecls_411_);
lean_ctor_set(v_reuseFailAlloc_429_, 8, v_initHeartbeats_412_);
lean_ctor_set(v_reuseFailAlloc_429_, 9, v_maxHeartbeats_413_);
lean_ctor_set(v_reuseFailAlloc_429_, 10, v_quotContext_414_);
lean_ctor_set(v_reuseFailAlloc_429_, 11, v_currMacroScope_415_);
lean_ctor_set(v_reuseFailAlloc_429_, 12, v_cancelTk_x3f_417_);
lean_ctor_set(v_reuseFailAlloc_429_, 13, v_inheritedTraceOptions_419_);
lean_ctor_set_uint8(v_reuseFailAlloc_429_, sizeof(void*)*14, v_diag_416_);
lean_ctor_set_uint8(v_reuseFailAlloc_429_, sizeof(void*)*14 + 1, v_suppressElabErrors_418_);
v___x_427_ = v_reuseFailAlloc_429_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; 
v___x_428_ = lean_apply_6(v_x_387_, v___y_388_, v___y_389_, v___y_390_, v___x_427_, v___y_392_, lean_box(0));
v___y_395_ = v___x_428_;
goto v___jp_394_;
}
}
else
{
lean_object* v___x_430_; 
lean_del_object(v___x_421_);
lean_dec_ref(v_inheritedTraceOptions_419_);
lean_dec(v_cancelTk_x3f_417_);
lean_dec(v_currMacroScope_415_);
lean_dec(v_quotContext_414_);
lean_dec(v_maxHeartbeats_413_);
lean_dec(v_initHeartbeats_412_);
lean_dec(v_openDecls_411_);
lean_dec(v_currNamespace_410_);
lean_dec(v_maxRecDepth_408_);
lean_dec(v_currRecDepth_407_);
lean_dec_ref(v_options_406_);
lean_dec_ref(v_fileMap_405_);
lean_dec_ref(v_fileName_404_);
lean_dec(v___y_392_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v_x_387_);
v___x_430_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_409_);
v___y_395_ = v___x_430_;
goto v___jp_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_440_, lean_object* v_x_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_apply_1(v_x_441_, lean_box(0));
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_449_, lean_object* v_x_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(v_00_u03b1_449_, v_x_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_457_, lean_object* v_x_458_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
lean_object* v___x_459_; 
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
lean_object* v_key_460_; lean_object* v_value_461_; lean_object* v_tail_462_; uint8_t v___x_463_; 
v_key_460_ = lean_ctor_get(v_x_458_, 0);
v_value_461_ = lean_ctor_get(v_x_458_, 1);
v_tail_462_ = lean_ctor_get(v_x_458_, 2);
v___x_463_ = l_Lean_ExprStructEq_beq(v_key_460_, v_a_457_);
if (v___x_463_ == 0)
{
v_x_458_ = v_tail_462_;
goto _start;
}
else
{
lean_object* v___x_465_; 
lean_inc(v_value_461_);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v_value_461_);
return v___x_465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_466_, lean_object* v_x_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_466_, v_x_467_);
lean_dec(v_x_467_);
lean_dec_ref(v_a_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object* v_m_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_buckets_471_; lean_object* v___x_472_; uint64_t v___x_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v_fold_476_; uint64_t v___x_477_; uint64_t v___x_478_; uint64_t v___x_479_; size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_buckets_471_ = lean_ctor_get(v_m_469_, 1);
v___x_472_ = lean_array_get_size(v_buckets_471_);
v___x_473_ = l_Lean_ExprStructEq_hash(v_a_470_);
v___x_474_ = 32ULL;
v___x_475_ = lean_uint64_shift_right(v___x_473_, v___x_474_);
v_fold_476_ = lean_uint64_xor(v___x_473_, v___x_475_);
v___x_477_ = 16ULL;
v___x_478_ = lean_uint64_shift_right(v_fold_476_, v___x_477_);
v___x_479_ = lean_uint64_xor(v_fold_476_, v___x_478_);
v___x_480_ = lean_uint64_to_usize(v___x_479_);
v___x_481_ = lean_usize_of_nat(v___x_472_);
v___x_482_ = ((size_t)1ULL);
v___x_483_ = lean_usize_sub(v___x_481_, v___x_482_);
v___x_484_ = lean_usize_land(v___x_480_, v___x_483_);
v___x_485_ = lean_array_uget_borrowed(v_buckets_471_, v___x_484_);
v___x_486_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_470_, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_487_, v_a_488_);
lean_dec_ref(v_a_488_);
lean_dec_ref(v_m_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_490_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(v___x_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_504_, lean_object* v___y_505_, lean_object* v_b_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = lean_apply_7(v_k_504_, v_b_506_, v___y_505_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, lean_box(0));
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_513_, lean_object* v___y_514_, lean_object* v_b_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_513_, v___y_514_, v_b_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_522_, uint8_t v_bi_523_, lean_object* v_type_524_, lean_object* v_k_525_, uint8_t v_kind_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___f_533_; lean_object* v___x_534_; 
v___f_533_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_533_, 0, v_k_525_);
lean_closure_set(v___f_533_, 1, v___y_527_);
v___x_534_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_522_, v_bi_523_, v_type_524_, v___f_533_, v_kind_526_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_534_) == 0)
{
return v___x_534_;
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_543_, lean_object* v_bi_544_, lean_object* v_type_545_, lean_object* v_k_546_, lean_object* v_kind_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
uint8_t v_bi_boxed_554_; uint8_t v_kind_boxed_555_; lean_object* v_res_556_; 
v_bi_boxed_554_ = lean_unbox(v_bi_544_);
v_kind_boxed_555_ = lean_unbox(v_kind_547_);
v_res_556_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_543_, v_bi_boxed_554_, v_type_545_, v_k_546_, v_kind_boxed_555_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_557_, lean_object* v_type_558_, lean_object* v_val_559_, lean_object* v_k_560_, uint8_t v_nondep_561_, uint8_t v_kind_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___f_569_; lean_object* v___x_570_; 
v___f_569_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_569_, 0, v_k_560_);
lean_closure_set(v___f_569_, 1, v___y_563_);
v___x_570_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_557_, v_type_558_, v_val_559_, v___f_569_, v_nondep_561_, v_kind_562_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_570_) == 0)
{
return v___x_570_;
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_579_, lean_object* v_type_580_, lean_object* v_val_581_, lean_object* v_k_582_, lean_object* v_nondep_583_, lean_object* v_kind_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
uint8_t v_nondep_boxed_591_; uint8_t v_kind_boxed_592_; lean_object* v_res_593_; 
v_nondep_boxed_591_ = lean_unbox(v_nondep_583_);
v_kind_boxed_592_ = lean_unbox(v_kind_584_);
v_res_593_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_579_, v_type_580_, v_val_581_, v_k_582_, v_nondep_boxed_591_, v_kind_boxed_592_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_596_, lean_object* v_pre_597_, lean_object* v_post_598_, uint8_t v_usedLetOnly_599_, uint8_t v_skipConstInApp_600_, uint8_t v_skipInstances_601_, lean_object* v_body_602_, lean_object* v_x_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_array_push(v_fvars_596_, v_x_603_);
v___x_611_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_597_, v_post_598_, v_usedLetOnly_599_, v_skipConstInApp_600_, v_skipInstances_601_, v___x_610_, v_body_602_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_612_, lean_object* v_pre_613_, lean_object* v_post_614_, lean_object* v_usedLetOnly_615_, lean_object* v_skipConstInApp_616_, lean_object* v_skipInstances_617_, lean_object* v_body_618_, lean_object* v_x_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
uint8_t v_usedLetOnly_boxed_626_; uint8_t v_skipConstInApp_boxed_627_; uint8_t v_skipInstances_boxed_628_; lean_object* v_res_629_; 
v_usedLetOnly_boxed_626_ = lean_unbox(v_usedLetOnly_615_);
v_skipConstInApp_boxed_627_ = lean_unbox(v_skipConstInApp_616_);
v_skipInstances_boxed_628_ = lean_unbox(v_skipInstances_617_);
v_res_629_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(v_fvars_612_, v_pre_613_, v_post_614_, v_usedLetOnly_boxed_626_, v_skipConstInApp_boxed_627_, v_skipInstances_boxed_628_, v_body_618_, v_x_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object* v_pre_630_, lean_object* v_post_631_, uint8_t v_usedLetOnly_632_, uint8_t v_skipConstInApp_633_, uint8_t v_skipInstances_634_, lean_object* v_e_635_, lean_object* v_a_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; 
lean_inc_ref(v_post_631_);
lean_inc(v___y_640_);
lean_inc_ref(v___y_639_);
lean_inc(v___y_638_);
lean_inc_ref(v___y_637_);
lean_inc_ref(v_e_635_);
v___x_642_ = lean_apply_6(v_post_631_, v_e_635_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, lean_box(0));
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_661_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_661_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_661_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_661_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
switch(lean_obj_tag(v_a_643_))
{
case 0:
{
lean_object* v_e_647_; lean_object* v___x_649_; 
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_e_635_);
lean_dec_ref(v_post_631_);
lean_dec_ref(v_pre_630_);
v_e_647_ = lean_ctor_get(v_a_643_, 0);
lean_inc_ref(v_e_647_);
lean_dec_ref(v_a_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v_e_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_e_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
case 1:
{
lean_object* v_e_651_; lean_object* v___x_652_; 
lean_del_object(v___x_645_);
lean_dec_ref(v_e_635_);
v_e_651_ = lean_ctor_get(v_a_643_, 0);
lean_inc_ref(v_e_651_);
lean_dec_ref(v_a_643_);
v___x_652_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_630_, v_post_631_, v_usedLetOnly_632_, v_skipConstInApp_633_, v_skipInstances_634_, v_e_651_, v_a_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
return v___x_652_;
}
default: 
{
lean_object* v_e_x3f_653_; 
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_post_631_);
lean_dec_ref(v_pre_630_);
v_e_x3f_653_ = lean_ctor_get(v_a_643_, 0);
lean_inc(v_e_x3f_653_);
lean_dec_ref(v_a_643_);
if (lean_obj_tag(v_e_x3f_653_) == 0)
{
lean_object* v___x_655_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v_e_635_);
v___x_655_ = v___x_645_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_e_635_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
else
{
lean_object* v_val_657_; lean_object* v___x_659_; 
lean_dec_ref(v_e_635_);
v_val_657_ = lean_ctor_get(v_e_x3f_653_, 0);
lean_inc(v_val_657_);
lean_dec_ref(v_e_x3f_653_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v_val_657_);
v___x_659_ = v___x_645_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_val_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_e_635_);
lean_dec_ref(v_post_631_);
lean_dec_ref(v_pre_630_);
v_a_662_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_642_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_642_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object* v_pre_670_, lean_object* v_post_671_, uint8_t v_usedLetOnly_672_, uint8_t v_skipConstInApp_673_, uint8_t v_skipInstances_674_, lean_object* v_fvars_675_, lean_object* v_e_676_, lean_object* v_a_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
if (lean_obj_tag(v_e_676_) == 6)
{
lean_object* v_binderName_683_; lean_object* v_binderType_684_; lean_object* v_body_685_; uint8_t v_binderInfo_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_binderName_683_ = lean_ctor_get(v_e_676_, 0);
lean_inc(v_binderName_683_);
v_binderType_684_ = lean_ctor_get(v_e_676_, 1);
lean_inc_ref(v_binderType_684_);
v_body_685_ = lean_ctor_get(v_e_676_, 2);
lean_inc_ref(v_body_685_);
v_binderInfo_686_ = lean_ctor_get_uint8(v_e_676_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_676_);
v___x_687_ = lean_expr_instantiate_rev(v_binderType_684_, v_fvars_675_);
lean_dec_ref(v_binderType_684_);
lean_inc(v___y_681_);
lean_inc_ref(v___y_680_);
lean_inc(v___y_679_);
lean_inc_ref(v___y_678_);
lean_inc(v_a_677_);
lean_inc_ref(v_post_671_);
lean_inc_ref(v_pre_670_);
v___x_688_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_670_, v_post_671_, v_usedLetOnly_672_, v_skipConstInApp_673_, v_skipInstances_674_, v___x_687_, v_a_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___f_693_; uint8_t v___x_694_; lean_object* v___x_695_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref(v___x_688_);
v___x_690_ = lean_box(v_usedLetOnly_672_);
v___x_691_ = lean_box(v_skipConstInApp_673_);
v___x_692_ = lean_box(v_skipInstances_674_);
v___f_693_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_693_, 0, v_fvars_675_);
lean_closure_set(v___f_693_, 1, v_pre_670_);
lean_closure_set(v___f_693_, 2, v_post_671_);
lean_closure_set(v___f_693_, 3, v___x_690_);
lean_closure_set(v___f_693_, 4, v___x_691_);
lean_closure_set(v___f_693_, 5, v___x_692_);
lean_closure_set(v___f_693_, 6, v_body_685_);
v___x_694_ = 0;
v___x_695_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_683_, v_binderInfo_686_, v_a_689_, v___f_693_, v___x_694_, v_a_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
return v___x_695_;
}
else
{
lean_dec_ref(v_body_685_);
lean_dec(v_binderName_683_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_fvars_675_);
lean_dec_ref(v_post_671_);
lean_dec_ref(v_pre_670_);
return v___x_688_;
}
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_expr_instantiate_rev(v_e_676_, v_fvars_675_);
lean_dec_ref(v_e_676_);
lean_inc(v___y_681_);
lean_inc_ref(v___y_680_);
lean_inc(v___y_679_);
lean_inc_ref(v___y_678_);
lean_inc(v_a_677_);
lean_inc_ref(v_post_671_);
lean_inc_ref(v_pre_670_);
v___x_697_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_670_, v_post_671_, v_usedLetOnly_672_, v_skipConstInApp_673_, v_skipInstances_674_, v___x_696_, v_a_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; uint8_t v___x_699_; uint8_t v___x_700_; uint8_t v___x_701_; lean_object* v___x_702_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref(v___x_697_);
v___x_699_ = 0;
v___x_700_ = 1;
v___x_701_ = 1;
v___x_702_ = l_Lean_Meta_mkLambdaFVars(v_fvars_675_, v_a_698_, v___x_699_, v_usedLetOnly_672_, v___x_699_, v___x_700_, v___x_701_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec_ref(v_fvars_675_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref(v___x_702_);
v___x_704_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_670_, v_post_671_, v_usedLetOnly_672_, v_skipConstInApp_673_, v_skipInstances_674_, v_a_703_, v_a_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
return v___x_704_;
}
else
{
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_post_671_);
lean_dec_ref(v_pre_670_);
return v___x_702_;
}
}
else
{
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_fvars_675_);
lean_dec_ref(v_post_671_);
lean_dec_ref(v_pre_670_);
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_705_, lean_object* v_pre_706_, lean_object* v_post_707_, uint8_t v_usedLetOnly_708_, uint8_t v_skipConstInApp_709_, uint8_t v_skipInstances_710_, lean_object* v_body_711_, lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_array_push(v_fvars_705_, v_x_712_);
v___x_720_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_706_, v_post_707_, v_usedLetOnly_708_, v_skipConstInApp_709_, v_skipInstances_710_, v___x_719_, v_body_711_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_721_, lean_object* v_pre_722_, lean_object* v_post_723_, lean_object* v_usedLetOnly_724_, lean_object* v_skipConstInApp_725_, lean_object* v_skipInstances_726_, lean_object* v_body_727_, lean_object* v_x_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
uint8_t v_usedLetOnly_boxed_735_; uint8_t v_skipConstInApp_boxed_736_; uint8_t v_skipInstances_boxed_737_; lean_object* v_res_738_; 
v_usedLetOnly_boxed_735_ = lean_unbox(v_usedLetOnly_724_);
v_skipConstInApp_boxed_736_ = lean_unbox(v_skipConstInApp_725_);
v_skipInstances_boxed_737_ = lean_unbox(v_skipInstances_726_);
v_res_738_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(v_fvars_721_, v_pre_722_, v_post_723_, v_usedLetOnly_boxed_735_, v_skipConstInApp_boxed_736_, v_skipInstances_boxed_737_, v_body_727_, v_x_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object* v_pre_739_, lean_object* v_post_740_, uint8_t v_usedLetOnly_741_, uint8_t v_skipConstInApp_742_, uint8_t v_skipInstances_743_, lean_object* v_fvars_744_, lean_object* v_e_745_, lean_object* v_a_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
if (lean_obj_tag(v_e_745_) == 8)
{
lean_object* v_declName_752_; lean_object* v_type_753_; lean_object* v_value_754_; lean_object* v_body_755_; uint8_t v_nondep_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_declName_752_ = lean_ctor_get(v_e_745_, 0);
lean_inc(v_declName_752_);
v_type_753_ = lean_ctor_get(v_e_745_, 1);
lean_inc_ref(v_type_753_);
v_value_754_ = lean_ctor_get(v_e_745_, 2);
lean_inc_ref(v_value_754_);
v_body_755_ = lean_ctor_get(v_e_745_, 3);
lean_inc_ref(v_body_755_);
v_nondep_756_ = lean_ctor_get_uint8(v_e_745_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_745_);
v___x_757_ = lean_expr_instantiate_rev(v_type_753_, v_fvars_744_);
lean_dec_ref(v_type_753_);
lean_inc(v___y_750_);
lean_inc_ref(v___y_749_);
lean_inc(v___y_748_);
lean_inc_ref(v___y_747_);
lean_inc(v_a_746_);
lean_inc_ref(v_post_740_);
lean_inc_ref(v_pre_739_);
v___x_758_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_739_, v_post_740_, v_usedLetOnly_741_, v_skipConstInApp_742_, v_skipInstances_743_, v___x_757_, v_a_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref(v___x_758_);
v___x_760_ = lean_expr_instantiate_rev(v_value_754_, v_fvars_744_);
lean_dec_ref(v_value_754_);
lean_inc(v___y_750_);
lean_inc_ref(v___y_749_);
lean_inc(v___y_748_);
lean_inc_ref(v___y_747_);
lean_inc(v_a_746_);
lean_inc_ref(v_post_740_);
lean_inc_ref(v_pre_739_);
v___x_761_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_739_, v_post_740_, v_usedLetOnly_741_, v_skipConstInApp_742_, v_skipInstances_743_, v___x_760_, v_a_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___f_766_; uint8_t v___x_767_; lean_object* v___x_768_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref(v___x_761_);
v___x_763_ = lean_box(v_usedLetOnly_741_);
v___x_764_ = lean_box(v_skipConstInApp_742_);
v___x_765_ = lean_box(v_skipInstances_743_);
v___f_766_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_766_, 0, v_fvars_744_);
lean_closure_set(v___f_766_, 1, v_pre_739_);
lean_closure_set(v___f_766_, 2, v_post_740_);
lean_closure_set(v___f_766_, 3, v___x_763_);
lean_closure_set(v___f_766_, 4, v___x_764_);
lean_closure_set(v___f_766_, 5, v___x_765_);
lean_closure_set(v___f_766_, 6, v_body_755_);
v___x_767_ = 0;
v___x_768_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_752_, v_a_759_, v_a_762_, v___f_766_, v_nondep_756_, v___x_767_, v_a_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
return v___x_768_;
}
else
{
lean_dec(v_a_759_);
lean_dec_ref(v_body_755_);
lean_dec(v_declName_752_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_fvars_744_);
lean_dec_ref(v_post_740_);
lean_dec_ref(v_pre_739_);
return v___x_761_;
}
}
else
{
lean_dec_ref(v_body_755_);
lean_dec_ref(v_value_754_);
lean_dec(v_declName_752_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_fvars_744_);
lean_dec_ref(v_post_740_);
lean_dec_ref(v_pre_739_);
return v___x_758_;
}
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_expr_instantiate_rev(v_e_745_, v_fvars_744_);
lean_dec_ref(v_e_745_);
lean_inc(v___y_750_);
lean_inc_ref(v___y_749_);
lean_inc(v___y_748_);
lean_inc_ref(v___y_747_);
lean_inc(v_a_746_);
lean_inc_ref(v_post_740_);
lean_inc_ref(v_pre_739_);
v___x_770_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_739_, v_post_740_, v_usedLetOnly_741_, v_skipConstInApp_742_, v_skipInstances_743_, v___x_769_, v_a_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; uint8_t v___x_772_; uint8_t v___x_773_; lean_object* v___x_774_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref(v___x_770_);
v___x_772_ = 0;
v___x_773_ = 1;
v___x_774_ = l_Lean_Meta_mkLetFVars(v_fvars_744_, v_a_771_, v_usedLetOnly_741_, v___x_772_, v___x_773_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec_ref(v_fvars_744_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_776_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref(v___x_774_);
v___x_776_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_739_, v_post_740_, v_usedLetOnly_741_, v_skipConstInApp_742_, v_skipInstances_743_, v_a_775_, v_a_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
return v___x_776_;
}
else
{
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_post_740_);
lean_dec_ref(v_pre_739_);
return v___x_774_;
}
}
else
{
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_fvars_744_);
lean_dec_ref(v_post_740_);
lean_dec_ref(v_pre_739_);
return v___x_770_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_777_; lean_object* v_dummy_778_; 
v___x_777_ = lean_box(0);
v_dummy_778_ = l_Lean_Expr_sort___override(v___x_777_);
return v_dummy_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object* v_pre_779_, lean_object* v_post_780_, uint8_t v_usedLetOnly_781_, uint8_t v_skipConstInApp_782_, uint8_t v_skipInstances_783_, size_t v_sz_784_, size_t v_i_785_, lean_object* v_bs_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
uint8_t v___x_793_; 
v___x_793_ = lean_usize_dec_lt(v_i_785_, v_sz_784_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v_post_780_);
lean_dec_ref(v_pre_779_);
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v_bs_786_);
return v___x_794_;
}
else
{
lean_object* v_v_795_; lean_object* v___x_796_; 
v_v_795_ = lean_array_uget_borrowed(v_bs_786_, v_i_785_);
lean_inc(v___y_791_);
lean_inc_ref(v___y_790_);
lean_inc(v___y_789_);
lean_inc_ref(v___y_788_);
lean_inc(v___y_787_);
lean_inc(v_v_795_);
lean_inc_ref(v_post_780_);
lean_inc_ref(v_pre_779_);
v___x_796_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_779_, v_post_780_, v_usedLetOnly_781_, v_skipConstInApp_782_, v_skipInstances_783_, v_v_795_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_798_; lean_object* v_bs_x27_799_; size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref(v___x_796_);
v___x_798_ = lean_unsigned_to_nat(0u);
v_bs_x27_799_ = lean_array_uset(v_bs_786_, v_i_785_, v___x_798_);
v___x_800_ = ((size_t)1ULL);
v___x_801_ = lean_usize_add(v_i_785_, v___x_800_);
v___x_802_ = lean_array_uset(v_bs_x27_799_, v_i_785_, v_a_797_);
v_i_785_ = v___x_801_;
v_bs_786_ = v___x_802_;
goto _start;
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v_bs_786_);
lean_dec_ref(v_post_780_);
lean_dec_ref(v_pre_779_);
v_a_804_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_796_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_796_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_812_, lean_object* v_post_813_, uint8_t v_usedLetOnly_814_, uint8_t v_skipConstInApp_815_, uint8_t v_skipInstances_816_, lean_object* v___x_817_, lean_object* v___y_818_, lean_object* v_b_819_, lean_object* v_a_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_812_, v_post_813_, v_usedLetOnly_814_, v_skipConstInApp_815_, v_skipInstances_816_, v___x_817_, v___y_818_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_836_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_836_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_836_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_836_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_831_ = lean_array_fset(v_b_819_, v_a_820_, v_a_827_);
v___x_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_832_);
v___x_834_ = v___x_829_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref(v_b_819_);
v_a_837_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_826_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_826_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_845_, lean_object* v_post_846_, lean_object* v_usedLetOnly_847_, lean_object* v_skipConstInApp_848_, lean_object* v_skipInstances_849_, lean_object* v___x_850_, lean_object* v___y_851_, lean_object* v_b_852_, lean_object* v_a_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
uint8_t v_usedLetOnly_boxed_859_; uint8_t v_skipConstInApp_boxed_860_; uint8_t v_skipInstances_boxed_861_; lean_object* v_res_862_; 
v_usedLetOnly_boxed_859_ = lean_unbox(v_usedLetOnly_847_);
v_skipConstInApp_boxed_860_ = lean_unbox(v_skipConstInApp_848_);
v_skipInstances_boxed_861_ = lean_unbox(v_skipInstances_849_);
v_res_862_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_845_, v_post_846_, v_usedLetOnly_boxed_859_, v_skipConstInApp_boxed_860_, v_skipInstances_boxed_861_, v___x_850_, v___y_851_, v_b_852_, v_a_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v_a_853_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_863_, lean_object* v___x_864_, lean_object* v_pre_865_, lean_object* v_post_866_, uint8_t v_usedLetOnly_867_, uint8_t v_skipConstInApp_868_, uint8_t v_skipInstances_869_, lean_object* v_a_870_, lean_object* v_b_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___y_879_; uint8_t v___x_902_; 
v___x_902_ = lean_nat_dec_lt(v_a_870_, v_upperBound_863_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec(v_a_870_);
lean_dec_ref(v_post_866_);
lean_dec_ref(v_pre_865_);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v_b_871_);
return v___x_903_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_904_ = lean_array_fget_borrowed(v_b_871_, v_a_870_);
v___x_905_ = lean_array_get_size(v___x_864_);
v___x_906_ = lean_nat_dec_lt(v_a_870_, v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___f_910_; 
lean_inc(v___x_904_);
v___x_907_ = lean_box(v_usedLetOnly_867_);
v___x_908_ = lean_box(v_skipConstInApp_868_);
v___x_909_ = lean_box(v_skipInstances_869_);
lean_inc(v_a_870_);
lean_inc(v___y_872_);
lean_inc_ref(v_post_866_);
lean_inc_ref(v_pre_865_);
v___f_910_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_910_, 0, v_pre_865_);
lean_closure_set(v___f_910_, 1, v_post_866_);
lean_closure_set(v___f_910_, 2, v___x_907_);
lean_closure_set(v___f_910_, 3, v___x_908_);
lean_closure_set(v___f_910_, 4, v___x_909_);
lean_closure_set(v___f_910_, 5, v___x_904_);
lean_closure_set(v___f_910_, 6, v___y_872_);
lean_closure_set(v___f_910_, 7, v_b_871_);
lean_closure_set(v___f_910_, 8, v_a_870_);
v___y_879_ = v___f_910_;
goto v___jp_878_;
}
else
{
lean_object* v___x_911_; uint8_t v_isInstance_912_; 
v___x_911_ = lean_array_fget_borrowed(v___x_864_, v_a_870_);
v_isInstance_912_ = lean_ctor_get_uint8(v___x_911_, sizeof(void*)*1 + 4);
if (v_isInstance_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___f_916_; 
lean_inc(v___x_904_);
v___x_913_ = lean_box(v_usedLetOnly_867_);
v___x_914_ = lean_box(v_skipConstInApp_868_);
v___x_915_ = lean_box(v_skipInstances_869_);
lean_inc(v_a_870_);
lean_inc(v___y_872_);
lean_inc_ref(v_post_866_);
lean_inc_ref(v_pre_865_);
v___f_916_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_916_, 0, v_pre_865_);
lean_closure_set(v___f_916_, 1, v_post_866_);
lean_closure_set(v___f_916_, 2, v___x_913_);
lean_closure_set(v___f_916_, 3, v___x_914_);
lean_closure_set(v___f_916_, 4, v___x_915_);
lean_closure_set(v___f_916_, 5, v___x_904_);
lean_closure_set(v___f_916_, 6, v___y_872_);
lean_closure_set(v___f_916_, 7, v_b_871_);
lean_closure_set(v___f_916_, 8, v_a_870_);
v___y_879_ = v___f_916_;
goto v___jp_878_;
}
else
{
lean_object* v___x_917_; lean_object* v___f_918_; 
v___x_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_917_, 0, v_b_871_);
v___f_918_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_918_, 0, v___x_917_);
v___y_879_ = v___f_918_;
goto v___jp_878_;
}
}
}
v___jp_878_:
{
lean_object* v___x_880_; 
lean_inc(v___y_876_);
lean_inc_ref(v___y_875_);
lean_inc(v___y_874_);
lean_inc_ref(v___y_873_);
v___x_880_ = lean_apply_5(v___y_879_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, lean_box(0));
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_893_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_893_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_893_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_893_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
if (lean_obj_tag(v_a_881_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_887_; 
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec(v_a_870_);
lean_dec_ref(v_post_866_);
lean_dec_ref(v_pre_865_);
v_a_885_ = lean_ctor_get(v_a_881_, 0);
lean_inc(v_a_885_);
lean_dec_ref(v_a_881_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v_a_885_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
lean_del_object(v___x_883_);
v_a_889_ = lean_ctor_get(v_a_881_, 0);
lean_inc(v_a_889_);
lean_dec_ref(v_a_881_);
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_891_ = lean_nat_add(v_a_870_, v___x_890_);
lean_dec(v_a_870_);
v_a_870_ = v___x_891_;
v_b_871_ = v_a_889_;
goto _start;
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec(v_a_870_);
lean_dec_ref(v_post_866_);
lean_dec_ref(v_pre_865_);
v_a_894_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_880_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_880_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t v_skipInstances_919_, lean_object* v_pre_920_, lean_object* v_post_921_, uint8_t v_usedLetOnly_922_, uint8_t v_skipConstInApp_923_, lean_object* v_x_924_, lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_f_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; 
if (lean_obj_tag(v_x_924_) == 5)
{
lean_object* v_fn_982_; lean_object* v_arg_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_fn_982_ = lean_ctor_get(v_x_924_, 0);
lean_inc_ref(v_fn_982_);
v_arg_983_ = lean_ctor_get(v_x_924_, 1);
lean_inc_ref(v_arg_983_);
lean_dec_ref(v_x_924_);
v___x_984_ = lean_array_set(v_x_925_, v_x_926_, v_arg_983_);
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = lean_nat_sub(v_x_926_, v___x_985_);
lean_dec(v_x_926_);
v_x_924_ = v_fn_982_;
v_x_925_ = v___x_984_;
v_x_926_ = v___x_986_;
goto _start;
}
else
{
lean_dec(v_x_926_);
if (v_skipConstInApp_923_ == 0)
{
goto v___jp_979_;
}
else
{
uint8_t v___x_988_; 
v___x_988_ = l_Lean_Expr_isConst(v_x_924_);
if (v___x_988_ == 0)
{
goto v___jp_979_;
}
else
{
v_f_934_ = v_x_924_;
v___y_935_ = v___y_927_;
v___y_936_ = v___y_928_;
v___y_937_ = v___y_929_;
v___y_938_ = v___y_930_;
v___y_939_ = v___y_931_;
goto v___jp_933_;
}
}
}
v___jp_933_:
{
if (v_skipInstances_919_ == 0)
{
size_t v_sz_940_; size_t v___x_941_; lean_object* v___x_942_; 
v_sz_940_ = lean_array_size(v_x_925_);
v___x_941_ = ((size_t)0ULL);
lean_inc(v___y_939_);
lean_inc_ref(v___y_938_);
lean_inc(v___y_937_);
lean_inc_ref(v___y_936_);
lean_inc(v___y_935_);
lean_inc_ref(v_post_921_);
lean_inc_ref(v_pre_920_);
v___x_942_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_920_, v_post_921_, v_usedLetOnly_922_, v_skipConstInApp_923_, v_skipInstances_919_, v_sz_940_, v___x_941_, v_x_925_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref(v___x_942_);
v___x_944_ = l_Lean_mkAppN(v_f_934_, v_a_943_);
lean_dec(v_a_943_);
v___x_945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_920_, v_post_921_, v_usedLetOnly_922_, v_skipConstInApp_923_, v_skipInstances_919_, v___x_944_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
return v___x_945_;
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v_f_934_);
lean_dec_ref(v_post_921_);
lean_dec_ref(v_pre_920_);
v_a_946_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_942_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_942_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_array_get_size(v_x_925_);
lean_inc(v___y_939_);
lean_inc_ref(v___y_938_);
lean_inc(v___y_937_);
lean_inc_ref(v___y_936_);
lean_inc_ref(v_f_934_);
v___x_955_ = l_Lean_Meta_getFunInfoNArgs(v_f_934_, v___x_954_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v_paramInfo_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref(v___x_955_);
v_paramInfo_957_ = lean_ctor_get(v_a_956_, 0);
lean_inc_ref(v_paramInfo_957_);
lean_dec(v_a_956_);
v___x_958_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_939_);
lean_inc_ref(v___y_938_);
lean_inc(v___y_937_);
lean_inc_ref(v___y_936_);
lean_inc(v___y_935_);
lean_inc_ref(v_post_921_);
lean_inc_ref(v_pre_920_);
v___x_959_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v___x_954_, v_paramInfo_957_, v_pre_920_, v_post_921_, v_usedLetOnly_922_, v_skipConstInApp_923_, v_skipInstances_919_, v___x_958_, v_x_925_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec_ref(v_paramInfo_957_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref(v___x_959_);
v___x_961_ = l_Lean_mkAppN(v_f_934_, v_a_960_);
lean_dec(v_a_960_);
v___x_962_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_920_, v_post_921_, v_usedLetOnly_922_, v_skipConstInApp_923_, v_skipInstances_919_, v___x_961_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
return v___x_962_;
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v_f_934_);
lean_dec_ref(v_post_921_);
lean_dec_ref(v_pre_920_);
v_a_963_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_959_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_959_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v_f_934_);
lean_dec_ref(v_x_925_);
lean_dec_ref(v_post_921_);
lean_dec_ref(v_pre_920_);
v_a_971_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_955_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_955_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
v___jp_979_:
{
lean_object* v___x_980_; 
lean_inc(v___y_931_);
lean_inc_ref(v___y_930_);
lean_inc(v___y_929_);
lean_inc_ref(v___y_928_);
lean_inc(v___y_927_);
lean_inc_ref(v_post_921_);
lean_inc_ref(v_pre_920_);
v___x_980_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_920_, v_post_921_, v_usedLetOnly_922_, v_skipConstInApp_923_, v_skipInstances_919_, v_x_924_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref(v___x_980_);
v_f_934_ = v_a_981_;
v___y_935_ = v___y_927_;
v___y_936_ = v___y_928_;
v___y_937_ = v___y_929_;
v___y_938_ = v___y_930_;
v___y_939_ = v___y_931_;
goto v___jp_933_;
}
else
{
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v_x_925_);
lean_dec_ref(v_post_921_);
lean_dec_ref(v_pre_920_);
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object* v_pre_989_, lean_object* v_e_990_, lean_object* v_post_991_, uint8_t v_usedLetOnly_992_, uint8_t v_skipConstInApp_993_, uint8_t v_skipInstances_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; 
lean_inc_ref(v_pre_989_);
lean_inc(v___y_999_);
lean_inc_ref(v___y_998_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc_ref(v_e_990_);
v___x_1001_ = lean_apply_6(v_pre_989_, v_e_990_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, lean_box(0));
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
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v_post_991_);
lean_dec_ref(v_e_990_);
lean_dec_ref(v_pre_989_);
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
lean_dec_ref(v_e_990_);
v_e_1046_ = lean_ctor_get(v_a_1002_, 0);
lean_inc_ref(v_e_1046_);
lean_dec_ref(v_a_1002_);
v___x_1047_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_989_, v_post_991_, v_usedLetOnly_992_, v_skipConstInApp_993_, v_skipInstances_994_, v_e_1046_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
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
v___y_1007_ = v_e_990_;
goto v___jp_1006_;
}
else
{
lean_object* v_val_1049_; 
lean_dec_ref(v_e_990_);
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
v___x_1009_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_989_, v_post_991_, v_usedLetOnly_992_, v_skipConstInApp_993_, v_skipInstances_994_, v___x_1008_, v___y_1007_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1009_;
}
case 6:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1011_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_989_, v_post_991_, v_usedLetOnly_992_, v_skipConstInApp_993_, v_skipInstances_994_, v___x_1010_, v___y_1007_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1011_;
}
case 8:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1013_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_989_, v_post_991_, v_usedLetOnly_992_, v_skipConstInApp_993_, v_skipInstances_994_, v___x_1012_, v___y_1007_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
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
v___x_1019_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_994_, v_pre_989_, v_post_991_, v_usedLetOnly_992_, v_skipConstInApp_993_, v___y_1007_, v___x_1016_, v___x_1018_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1019_;
}
case 10:
{
lean_object* v_data_1020_; lean_object* v_expr_1021_; lean_object* v___x_1022_; 
v_data_1020_ = lean_ctor_get(v___y_1007_, 0);
v_expr_1021_ = lean_ctor_get(v___y_1007_, 1);
lean_inc(v___y_999_);
lean_inc_ref(v___y_998_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v___y_995_);
lean_inc_ref(v_expr_1021_);
lean_inc_ref(v_post_991_);
lean_inc_ref(v_pre_989_);
v___x_1022_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_989_, v_post_991_, v_usedLetOnly_992_, v_skipConstInApp_993_, v_skipInstances_994_, v_expr_1021_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
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
v___x_1028_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_989_, v_post_991_, v_usedLetOnly_992_, v_skipConstInApp_993_, v_skipInstances_994_, v___x_1027_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1028_;
}
else
{
lean_object* v___x_1029_; 
lean_dec(v_a_1023_);
v___x_1029_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_989_, v_post_991_, v_usedLetOnly_992_, v_skipConstInApp_993_, v_skipInstances_994_, v___y_1007_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1029_;
}
}
else
{
lean_dec_ref(v___y_1007_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v_post_991_);
lean_dec_ref(v_pre_989_);
return v___x_1022_;
}
}
case 11:
{
lean_object* v_typeName_1030_; lean_object* v_idx_1031_; lean_object* v_struct_1032_; lean_object* v___x_1033_; 
v_typeName_1030_ = lean_ctor_get(v___y_1007_, 0);
v_idx_1031_ = lean_ctor_get(v___y_1007_, 1);
v_struct_1032_ = lean_ctor_get(v___y_1007_, 2);
lean_inc(v___y_999_);
lean_inc_ref(v___y_998_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v___y_995_);
lean_inc_ref(v_struct_1032_);
lean_inc_ref(v_post_991_);
lean_inc_ref(v_pre_989_);
v___x_1033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_989_, v_post_991_, v_usedLetOnly_992_, v_skipConstInApp_993_, v_skipInstances_994_, v_struct_1032_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
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
v___x_1039_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_989_, v_post_991_, v_usedLetOnly_992_, v_skipConstInApp_993_, v_skipInstances_994_, v___x_1038_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1039_;
}
else
{
lean_object* v___x_1040_; 
lean_dec(v_a_1034_);
v___x_1040_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_989_, v_post_991_, v_usedLetOnly_992_, v_skipConstInApp_993_, v_skipInstances_994_, v___y_1007_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1040_;
}
}
else
{
lean_dec_ref(v___y_1007_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v_post_991_);
lean_dec_ref(v_pre_989_);
return v___x_1033_;
}
}
default: 
{
lean_object* v___x_1041_; 
v___x_1041_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_989_, v_post_991_, v_usedLetOnly_992_, v_skipConstInApp_993_, v_skipInstances_994_, v___y_1007_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1041_;
}
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v_post_991_);
lean_dec_ref(v_e_990_);
lean_dec_ref(v_pre_989_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_1059_, lean_object* v_e_1060_, lean_object* v_post_1061_, lean_object* v_usedLetOnly_1062_, lean_object* v_skipConstInApp_1063_, lean_object* v_skipInstances_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
uint8_t v_usedLetOnly_boxed_1071_; uint8_t v_skipConstInApp_boxed_1072_; uint8_t v_skipInstances_boxed_1073_; lean_object* v_res_1074_; 
v_usedLetOnly_boxed_1071_ = lean_unbox(v_usedLetOnly_1062_);
v_skipConstInApp_boxed_1072_ = lean_unbox(v_skipConstInApp_1063_);
v_skipInstances_boxed_1073_ = lean_unbox(v_skipInstances_1064_);
v_res_1074_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(v_pre_1059_, v_e_1060_, v_post_1061_, v_usedLetOnly_boxed_1071_, v_skipConstInApp_boxed_1072_, v_skipInstances_boxed_1073_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object* v_pre_1075_, lean_object* v_post_1076_, uint8_t v_usedLetOnly_1077_, uint8_t v_skipConstInApp_1078_, uint8_t v_skipInstances_1079_, lean_object* v_e_1080_, lean_object* v_a_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_inc(v_a_1081_);
v___x_1087_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1087_, 0, lean_box(0));
lean_closure_set(v___x_1087_, 1, lean_box(0));
lean_closure_set(v___x_1087_, 2, v_a_1081_);
v___x_1088_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___x_1087_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1122_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1122_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1122_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_1089_, v_e_1080_);
lean_dec(v_a_1089_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___f_1097_; lean_object* v___x_1098_; 
lean_del_object(v___x_1091_);
v___x_1094_ = lean_box(v_usedLetOnly_1077_);
v___x_1095_ = lean_box(v_skipConstInApp_1078_);
v___x_1096_ = lean_box(v_skipInstances_1079_);
lean_inc_ref(v_e_1080_);
v___f_1097_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1097_, 0, v_pre_1075_);
lean_closure_set(v___f_1097_, 1, v_e_1080_);
lean_closure_set(v___f_1097_, 2, v_post_1076_);
lean_closure_set(v___f_1097_, 3, v___x_1094_);
lean_closure_set(v___f_1097_, 4, v___x_1095_);
lean_closure_set(v___f_1097_, 5, v___x_1096_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc(v_a_1081_);
v___x_1098_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v___f_1097_, v_a_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref(v___x_1098_);
lean_inc(v_a_1099_);
v___f_1100_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1100_, 0, v_a_1081_);
lean_closure_set(v___f_1100_, 1, v_e_1080_);
lean_closure_set(v___f_1100_, 2, v_a_1099_);
v___x_1101_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___f_1100_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1108_ == 0)
{
lean_object* v_unused_1109_; 
v_unused_1109_ = lean_ctor_get(v___x_1101_, 0);
lean_dec(v_unused_1109_);
v___x_1103_ = v___x_1101_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_dec(v___x_1101_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v_a_1099_);
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1099_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec(v_a_1099_);
v_a_1110_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1101_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1101_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_e_1080_);
return v___x_1098_;
}
}
else
{
lean_object* v_val_1118_; lean_object* v___x_1120_; 
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_e_1080_);
lean_dec_ref(v_post_1076_);
lean_dec_ref(v_pre_1075_);
v_val_1118_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_val_1118_);
lean_dec_ref(v___x_1093_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v_val_1118_);
v___x_1120_ = v___x_1091_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_val_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_e_1080_);
lean_dec_ref(v_post_1076_);
lean_dec_ref(v_pre_1075_);
v_a_1123_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1088_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1088_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_1131_, lean_object* v_pre_1132_, lean_object* v_post_1133_, lean_object* v_usedLetOnly_1134_, lean_object* v_skipConstInApp_1135_, lean_object* v_skipInstances_1136_, lean_object* v_body_1137_, lean_object* v_x_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
uint8_t v_usedLetOnly_boxed_1145_; uint8_t v_skipConstInApp_boxed_1146_; uint8_t v_skipInstances_boxed_1147_; lean_object* v_res_1148_; 
v_usedLetOnly_boxed_1145_ = lean_unbox(v_usedLetOnly_1134_);
v_skipConstInApp_boxed_1146_ = lean_unbox(v_skipConstInApp_1135_);
v_skipInstances_boxed_1147_ = lean_unbox(v_skipInstances_1136_);
v_res_1148_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(v_fvars_1131_, v_pre_1132_, v_post_1133_, v_usedLetOnly_boxed_1145_, v_skipConstInApp_boxed_1146_, v_skipInstances_boxed_1147_, v_body_1137_, v_x_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object* v_pre_1149_, lean_object* v_post_1150_, uint8_t v_usedLetOnly_1151_, uint8_t v_skipConstInApp_1152_, uint8_t v_skipInstances_1153_, lean_object* v_fvars_1154_, lean_object* v_e_1155_, lean_object* v_a_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
if (lean_obj_tag(v_e_1155_) == 7)
{
lean_object* v_binderName_1162_; lean_object* v_binderType_1163_; lean_object* v_body_1164_; uint8_t v_binderInfo_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_binderName_1162_ = lean_ctor_get(v_e_1155_, 0);
lean_inc(v_binderName_1162_);
v_binderType_1163_ = lean_ctor_get(v_e_1155_, 1);
lean_inc_ref(v_binderType_1163_);
v_body_1164_ = lean_ctor_get(v_e_1155_, 2);
lean_inc_ref(v_body_1164_);
v_binderInfo_1165_ = lean_ctor_get_uint8(v_e_1155_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1155_);
v___x_1166_ = lean_expr_instantiate_rev(v_binderType_1163_, v_fvars_1154_);
lean_dec_ref(v_binderType_1163_);
lean_inc(v___y_1160_);
lean_inc_ref(v___y_1159_);
lean_inc(v___y_1158_);
lean_inc_ref(v___y_1157_);
lean_inc(v_a_1156_);
lean_inc_ref(v_post_1150_);
lean_inc_ref(v_pre_1149_);
v___x_1167_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1149_, v_post_1150_, v_usedLetOnly_1151_, v_skipConstInApp_1152_, v_skipInstances_1153_, v___x_1166_, v_a_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___f_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref(v___x_1167_);
v___x_1169_ = lean_box(v_usedLetOnly_1151_);
v___x_1170_ = lean_box(v_skipConstInApp_1152_);
v___x_1171_ = lean_box(v_skipInstances_1153_);
v___f_1172_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1172_, 0, v_fvars_1154_);
lean_closure_set(v___f_1172_, 1, v_pre_1149_);
lean_closure_set(v___f_1172_, 2, v_post_1150_);
lean_closure_set(v___f_1172_, 3, v___x_1169_);
lean_closure_set(v___f_1172_, 4, v___x_1170_);
lean_closure_set(v___f_1172_, 5, v___x_1171_);
lean_closure_set(v___f_1172_, 6, v_body_1164_);
v___x_1173_ = 0;
v___x_1174_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_1162_, v_binderInfo_1165_, v_a_1168_, v___f_1172_, v___x_1173_, v_a_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
return v___x_1174_;
}
else
{
lean_dec_ref(v_body_1164_);
lean_dec(v_binderName_1162_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_fvars_1154_);
lean_dec_ref(v_post_1150_);
lean_dec_ref(v_pre_1149_);
return v___x_1167_;
}
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_expr_instantiate_rev(v_e_1155_, v_fvars_1154_);
lean_dec_ref(v_e_1155_);
lean_inc(v___y_1160_);
lean_inc_ref(v___y_1159_);
lean_inc(v___y_1158_);
lean_inc_ref(v___y_1157_);
lean_inc(v_a_1156_);
lean_inc_ref(v_post_1150_);
lean_inc_ref(v_pre_1149_);
v___x_1176_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1149_, v_post_1150_, v_usedLetOnly_1151_, v_skipConstInApp_1152_, v_skipInstances_1153_, v___x_1175_, v_a_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; uint8_t v___x_1178_; uint8_t v___x_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref(v___x_1176_);
v___x_1178_ = 0;
v___x_1179_ = 1;
v___x_1180_ = 1;
v___x_1181_ = l_Lean_Meta_mkForallFVars(v_fvars_1154_, v_a_1177_, v___x_1178_, v_usedLetOnly_1151_, v___x_1179_, v___x_1180_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
lean_dec_ref(v_fvars_1154_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref(v___x_1181_);
v___x_1183_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1149_, v_post_1150_, v_usedLetOnly_1151_, v_skipConstInApp_1152_, v_skipInstances_1153_, v_a_1182_, v_a_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
return v___x_1183_;
}
else
{
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_post_1150_);
lean_dec_ref(v_pre_1149_);
return v___x_1181_;
}
}
else
{
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_fvars_1154_);
lean_dec_ref(v_post_1150_);
lean_dec_ref(v_pre_1149_);
return v___x_1176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_1184_, lean_object* v_pre_1185_, lean_object* v_post_1186_, uint8_t v_usedLetOnly_1187_, uint8_t v_skipConstInApp_1188_, uint8_t v_skipInstances_1189_, lean_object* v_body_1190_, lean_object* v_x_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_array_push(v_fvars_1184_, v_x_1191_);
v___x_1199_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1185_, v_post_1186_, v_usedLetOnly_1187_, v_skipConstInApp_1188_, v_skipInstances_1189_, v___x_1198_, v_body_1190_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1200_, lean_object* v_post_1201_, lean_object* v_usedLetOnly_1202_, lean_object* v_skipConstInApp_1203_, lean_object* v_skipInstances_1204_, lean_object* v_e_1205_, lean_object* v_a_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
uint8_t v_usedLetOnly_boxed_1212_; uint8_t v_skipConstInApp_boxed_1213_; uint8_t v_skipInstances_boxed_1214_; lean_object* v_res_1215_; 
v_usedLetOnly_boxed_1212_ = lean_unbox(v_usedLetOnly_1202_);
v_skipConstInApp_boxed_1213_ = lean_unbox(v_skipConstInApp_1203_);
v_skipInstances_boxed_1214_ = lean_unbox(v_skipInstances_1204_);
v_res_1215_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1200_, v_post_1201_, v_usedLetOnly_boxed_1212_, v_skipConstInApp_boxed_1213_, v_skipInstances_boxed_1214_, v_e_1205_, v_a_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1216_, lean_object* v_post_1217_, lean_object* v_usedLetOnly_1218_, lean_object* v_skipConstInApp_1219_, lean_object* v_skipInstances_1220_, lean_object* v_sz_1221_, lean_object* v_i_1222_, lean_object* v_bs_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
uint8_t v_usedLetOnly_boxed_1230_; uint8_t v_skipConstInApp_boxed_1231_; uint8_t v_skipInstances_boxed_1232_; size_t v_sz_boxed_1233_; size_t v_i_boxed_1234_; lean_object* v_res_1235_; 
v_usedLetOnly_boxed_1230_ = lean_unbox(v_usedLetOnly_1218_);
v_skipConstInApp_boxed_1231_ = lean_unbox(v_skipConstInApp_1219_);
v_skipInstances_boxed_1232_ = lean_unbox(v_skipInstances_1220_);
v_sz_boxed_1233_ = lean_unbox_usize(v_sz_1221_);
lean_dec(v_sz_1221_);
v_i_boxed_1234_ = lean_unbox_usize(v_i_1222_);
lean_dec(v_i_1222_);
v_res_1235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1216_, v_post_1217_, v_usedLetOnly_boxed_1230_, v_skipConstInApp_boxed_1231_, v_skipInstances_boxed_1232_, v_sz_boxed_1233_, v_i_boxed_1234_, v_bs_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object* v_pre_1236_, lean_object* v_post_1237_, lean_object* v_usedLetOnly_1238_, lean_object* v_skipConstInApp_1239_, lean_object* v_skipInstances_1240_, lean_object* v_e_1241_, lean_object* v_a_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
uint8_t v_usedLetOnly_boxed_1248_; uint8_t v_skipConstInApp_boxed_1249_; uint8_t v_skipInstances_boxed_1250_; lean_object* v_res_1251_; 
v_usedLetOnly_boxed_1248_ = lean_unbox(v_usedLetOnly_1238_);
v_skipConstInApp_boxed_1249_ = lean_unbox(v_skipConstInApp_1239_);
v_skipInstances_boxed_1250_ = lean_unbox(v_skipInstances_1240_);
v_res_1251_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1236_, v_post_1237_, v_usedLetOnly_boxed_1248_, v_skipConstInApp_boxed_1249_, v_skipInstances_boxed_1250_, v_e_1241_, v_a_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_1252_, lean_object* v_post_1253_, lean_object* v_usedLetOnly_1254_, lean_object* v_skipConstInApp_1255_, lean_object* v_skipInstances_1256_, lean_object* v_fvars_1257_, lean_object* v_e_1258_, lean_object* v_a_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v_usedLetOnly_boxed_1265_; uint8_t v_skipConstInApp_boxed_1266_; uint8_t v_skipInstances_boxed_1267_; lean_object* v_res_1268_; 
v_usedLetOnly_boxed_1265_ = lean_unbox(v_usedLetOnly_1254_);
v_skipConstInApp_boxed_1266_ = lean_unbox(v_skipConstInApp_1255_);
v_skipInstances_boxed_1267_ = lean_unbox(v_skipInstances_1256_);
v_res_1268_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1252_, v_post_1253_, v_usedLetOnly_boxed_1265_, v_skipConstInApp_boxed_1266_, v_skipInstances_boxed_1267_, v_fvars_1257_, v_e_1258_, v_a_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_1269_, lean_object* v_post_1270_, lean_object* v_usedLetOnly_1271_, lean_object* v_skipConstInApp_1272_, lean_object* v_skipInstances_1273_, lean_object* v_fvars_1274_, lean_object* v_e_1275_, lean_object* v_a_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
uint8_t v_usedLetOnly_boxed_1282_; uint8_t v_skipConstInApp_boxed_1283_; uint8_t v_skipInstances_boxed_1284_; lean_object* v_res_1285_; 
v_usedLetOnly_boxed_1282_ = lean_unbox(v_usedLetOnly_1271_);
v_skipConstInApp_boxed_1283_ = lean_unbox(v_skipConstInApp_1272_);
v_skipInstances_boxed_1284_ = lean_unbox(v_skipInstances_1273_);
v_res_1285_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1269_, v_post_1270_, v_usedLetOnly_boxed_1282_, v_skipConstInApp_boxed_1283_, v_skipInstances_boxed_1284_, v_fvars_1274_, v_e_1275_, v_a_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_1286_, lean_object* v_post_1287_, lean_object* v_usedLetOnly_1288_, lean_object* v_skipConstInApp_1289_, lean_object* v_skipInstances_1290_, lean_object* v_fvars_1291_, lean_object* v_e_1292_, lean_object* v_a_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
uint8_t v_usedLetOnly_boxed_1299_; uint8_t v_skipConstInApp_boxed_1300_; uint8_t v_skipInstances_boxed_1301_; lean_object* v_res_1302_; 
v_usedLetOnly_boxed_1299_ = lean_unbox(v_usedLetOnly_1288_);
v_skipConstInApp_boxed_1300_ = lean_unbox(v_skipConstInApp_1289_);
v_skipInstances_boxed_1301_ = lean_unbox(v_skipInstances_1290_);
v_res_1302_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1286_, v_post_1287_, v_usedLetOnly_boxed_1299_, v_skipConstInApp_boxed_1300_, v_skipInstances_boxed_1301_, v_fvars_1291_, v_e_1292_, v_a_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_1303_, lean_object* v___x_1304_, lean_object* v_pre_1305_, lean_object* v_post_1306_, lean_object* v_usedLetOnly_1307_, lean_object* v_skipConstInApp_1308_, lean_object* v_skipInstances_1309_, lean_object* v_a_1310_, lean_object* v_b_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v_usedLetOnly_boxed_1318_; uint8_t v_skipConstInApp_boxed_1319_; uint8_t v_skipInstances_boxed_1320_; lean_object* v_res_1321_; 
v_usedLetOnly_boxed_1318_ = lean_unbox(v_usedLetOnly_1307_);
v_skipConstInApp_boxed_1319_ = lean_unbox(v_skipConstInApp_1308_);
v_skipInstances_boxed_1320_ = lean_unbox(v_skipInstances_1309_);
v_res_1321_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1303_, v___x_1304_, v_pre_1305_, v_post_1306_, v_usedLetOnly_boxed_1318_, v_skipConstInApp_boxed_1319_, v_skipInstances_boxed_1320_, v_a_1310_, v_b_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec_ref(v___x_1304_);
lean_dec(v_upperBound_1303_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_1322_, lean_object* v_pre_1323_, lean_object* v_post_1324_, lean_object* v_usedLetOnly_1325_, lean_object* v_skipConstInApp_1326_, lean_object* v_x_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
uint8_t v_skipInstances_boxed_1336_; uint8_t v_usedLetOnly_boxed_1337_; uint8_t v_skipConstInApp_boxed_1338_; lean_object* v_res_1339_; 
v_skipInstances_boxed_1336_ = lean_unbox(v_skipInstances_1322_);
v_usedLetOnly_boxed_1337_ = lean_unbox(v_usedLetOnly_1325_);
v_skipConstInApp_boxed_1338_ = lean_unbox(v_skipConstInApp_1326_);
v_res_1339_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_boxed_1336_, v_pre_1323_, v_post_1324_, v_usedLetOnly_boxed_1337_, v_skipConstInApp_boxed_1338_, v_x_1327_, v_x_1328_, v_x_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
return v_res_1339_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_unsigned_to_nat(16u);
v___x_1342_ = lean_mk_array(v___x_1341_, v___x_1340_);
return v___x_1342_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1343_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0);
v___x_1344_ = lean_unsigned_to_nat(0u);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
lean_ctor_set(v___x_1345_, 1, v___x_1343_);
return v___x_1345_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_1347_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1347_, 0, lean_box(0));
lean_closure_set(v___x_1347_, 1, lean_box(0));
lean_closure_set(v___x_1347_, 2, v___x_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object* v_input_1348_, lean_object* v_pre_1349_, lean_object* v_post_1350_, uint8_t v_usedLetOnly_1351_, uint8_t v_skipConstInApp_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v_a_1360_; uint8_t v___x_1361_; lean_object* v___x_1362_; 
v___x_1358_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_1359_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1358_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = 0;
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc_ref(v___y_1353_);
lean_inc(v_a_1360_);
v___x_1362_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1349_, v_post_1350_, v_usedLetOnly_1351_, v_skipConstInApp_1352_, v___x_1361_, v_input_1348_, v_a_1360_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1364_, 0, lean_box(0));
lean_closure_set(v___x_1364_, 1, lean_box(0));
lean_closure_set(v___x_1364_, 2, v_a_1360_);
v___x_1365_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1364_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v___x_1365_, 0);
lean_dec(v_unused_1373_);
v___x_1367_ = v___x_1365_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_dec(v___x_1365_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v_a_1363_);
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1363_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
else
{
lean_dec(v_a_1360_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object* v_input_1374_, lean_object* v_pre_1375_, lean_object* v_post_1376_, lean_object* v_usedLetOnly_1377_, lean_object* v_skipConstInApp_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v_usedLetOnly_boxed_1384_; uint8_t v_skipConstInApp_boxed_1385_; lean_object* v_res_1386_; 
v_usedLetOnly_boxed_1384_ = lean_unbox(v_usedLetOnly_1377_);
v_skipConstInApp_boxed_1385_ = lean_unbox(v_skipConstInApp_1378_);
v_res_1386_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_input_1374_, v_pre_1375_, v_post_1376_, v_usedLetOnly_boxed_1384_, v_skipConstInApp_boxed_1385_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object* v_e_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v___x_1395_; lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1408_; 
v___x_1395_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_1389_, v_a_1393_);
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1408_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1408_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
uint8_t v___x_1400_; 
v___x_1400_ = lean_unbox(v_a_1396_);
lean_dec(v_a_1396_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1402_; 
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v_e_1389_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_e_1389_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
else
{
lean_object* v___f_1404_; uint8_t v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_del_object(v___x_1398_);
v___f_1404_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__0));
v___x_1405_ = 0;
v___x_1406_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__1));
v___x_1407_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_1389_, v___x_1406_, v___f_1404_, v___x_1405_, v___x_1405_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
return v___x_1407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object* v_e_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_Meta_Sym_unfoldReducible(v_e_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object* v_upperBound_1416_, lean_object* v___x_1417_, lean_object* v_pre_1418_, lean_object* v_post_1419_, uint8_t v_usedLetOnly_1420_, uint8_t v_skipConstInApp_1421_, uint8_t v_skipInstances_1422_, lean_object* v___x_1423_, lean_object* v_inst_1424_, lean_object* v_R_1425_, lean_object* v_a_1426_, lean_object* v_b_1427_, lean_object* v_c_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1416_, v___x_1417_, v_pre_1418_, v_post_1419_, v_usedLetOnly_1420_, v_skipConstInApp_1421_, v_skipInstances_1422_, v_a_1426_, v_b_1427_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1436_ = _args[0];
lean_object* v___x_1437_ = _args[1];
lean_object* v_pre_1438_ = _args[2];
lean_object* v_post_1439_ = _args[3];
lean_object* v_usedLetOnly_1440_ = _args[4];
lean_object* v_skipConstInApp_1441_ = _args[5];
lean_object* v_skipInstances_1442_ = _args[6];
lean_object* v___x_1443_ = _args[7];
lean_object* v_inst_1444_ = _args[8];
lean_object* v_R_1445_ = _args[9];
lean_object* v_a_1446_ = _args[10];
lean_object* v_b_1447_ = _args[11];
lean_object* v_c_1448_ = _args[12];
lean_object* v___y_1449_ = _args[13];
lean_object* v___y_1450_ = _args[14];
lean_object* v___y_1451_ = _args[15];
lean_object* v___y_1452_ = _args[16];
lean_object* v___y_1453_ = _args[17];
lean_object* v___y_1454_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1455_; uint8_t v_skipConstInApp_boxed_1456_; uint8_t v_skipInstances_boxed_1457_; lean_object* v_res_1458_; 
v_usedLetOnly_boxed_1455_ = lean_unbox(v_usedLetOnly_1440_);
v_skipConstInApp_boxed_1456_ = lean_unbox(v_skipConstInApp_1441_);
v_skipInstances_boxed_1457_ = lean_unbox(v_skipInstances_1442_);
v_res_1458_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_upperBound_1436_, v___x_1437_, v_pre_1438_, v_post_1439_, v_usedLetOnly_boxed_1455_, v_skipConstInApp_boxed_1456_, v_skipInstances_boxed_1457_, v___x_1443_, v_inst_1444_, v_R_1445_, v_a_1446_, v_b_1447_, v_c_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___x_1443_);
lean_dec_ref(v___x_1437_);
lean_dec(v_upperBound_1436_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1459_, lean_object* v_m_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_1460_, v_a_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1463_, lean_object* v_m_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(v_00_u03b2_1463_, v_m_1464_, v_a_1465_);
lean_dec_ref(v_a_1465_);
lean_dec_ref(v_m_1464_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1467_, lean_object* v_name_1468_, uint8_t v_bi_1469_, lean_object* v_type_1470_, lean_object* v_k_1471_, uint8_t v_kind_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_1468_, v_bi_1469_, v_type_1470_, v_k_1471_, v_kind_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1480_, lean_object* v_name_1481_, lean_object* v_bi_1482_, lean_object* v_type_1483_, lean_object* v_k_1484_, lean_object* v_kind_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
uint8_t v_bi_boxed_1492_; uint8_t v_kind_boxed_1493_; lean_object* v_res_1494_; 
v_bi_boxed_1492_ = lean_unbox(v_bi_1482_);
v_kind_boxed_1493_ = lean_unbox(v_kind_1485_);
v_res_1494_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1480_, v_name_1481_, v_bi_boxed_1492_, v_type_1483_, v_k_1484_, v_kind_boxed_1493_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_1495_, lean_object* v_name_1496_, lean_object* v_type_1497_, lean_object* v_val_1498_, lean_object* v_k_1499_, uint8_t v_nondep_1500_, uint8_t v_kind_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1496_, v_type_1497_, v_val_1498_, v_k_1499_, v_nondep_1500_, v_kind_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1509_, lean_object* v_name_1510_, lean_object* v_type_1511_, lean_object* v_val_1512_, lean_object* v_k_1513_, lean_object* v_nondep_1514_, lean_object* v_kind_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
uint8_t v_nondep_boxed_1522_; uint8_t v_kind_boxed_1523_; lean_object* v_res_1524_; 
v_nondep_boxed_1522_ = lean_unbox(v_nondep_1514_);
v_kind_boxed_1523_ = lean_unbox(v_kind_1515_);
v_res_1524_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_1509_, v_name_1510_, v_type_1511_, v_val_1512_, v_k_1513_, v_nondep_boxed_1522_, v_kind_boxed_1523_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_1525_, lean_object* v_ref_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1526_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1533_, lean_object* v_ref_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_1533_, v_ref_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_1541_, lean_object* v_x_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_1550_, lean_object* v_x_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(v_00_u03b1_1550_, v_x_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_1559_, lean_object* v_m_1560_, lean_object* v_a_1561_, lean_object* v_b_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_1560_, v_a_1561_, v_b_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_1564_, lean_object* v_a_1565_, lean_object* v_x_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1565_, v_x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1568_, lean_object* v_a_1569_, lean_object* v_x_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_1568_, v_a_1569_, v_x_1570_);
lean_dec(v_x_1570_);
lean_dec_ref(v_a_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_1572_, lean_object* v_a_1573_, lean_object* v_x_1574_){
_start:
{
uint8_t v___x_1575_; 
v___x_1575_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_1573_, v_x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_1576_, lean_object* v_a_1577_, lean_object* v_x_1578_){
_start:
{
uint8_t v_res_1579_; lean_object* v_r_1580_; 
v_res_1579_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_1576_, v_a_1577_, v_x_1578_);
lean_dec(v_x_1578_);
lean_dec_ref(v_a_1577_);
v_r_1580_ = lean_box(v_res_1579_);
return v_r_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_1581_, lean_object* v_data_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_data_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_1584_, lean_object* v_a_1585_, lean_object* v_b_1586_, lean_object* v_x_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_1585_, v_b_1586_, v_x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_1589_, lean_object* v_i_1590_, lean_object* v_source_1591_, lean_object* v_target_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_1590_, v_source_1591_, v_target_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_1595_, v_x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(lean_object* v_e_1598_, lean_object* v___y_1599_){
_start:
{
uint8_t v___x_1601_; 
v___x_1601_ = l_Lean_Expr_hasMVar(v_e_1598_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_e_1598_);
return v___x_1602_;
}
else
{
lean_object* v___x_1603_; lean_object* v_mctx_1604_; lean_object* v___x_1605_; lean_object* v_fst_1606_; lean_object* v_snd_1607_; lean_object* v___x_1608_; lean_object* v_cache_1609_; lean_object* v_zetaDeltaFVarIds_1610_; lean_object* v_postponed_1611_; lean_object* v_diag_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1621_; 
v___x_1603_ = lean_st_ref_get(v___y_1599_);
v_mctx_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc_ref(v_mctx_1604_);
lean_dec(v___x_1603_);
v___x_1605_ = l_Lean_instantiateMVarsCore(v_mctx_1604_, v_e_1598_);
v_fst_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_fst_1606_);
v_snd_1607_ = lean_ctor_get(v___x_1605_, 1);
lean_inc(v_snd_1607_);
lean_dec_ref(v___x_1605_);
v___x_1608_ = lean_st_ref_take(v___y_1599_);
v_cache_1609_ = lean_ctor_get(v___x_1608_, 1);
v_zetaDeltaFVarIds_1610_ = lean_ctor_get(v___x_1608_, 2);
v_postponed_1611_ = lean_ctor_get(v___x_1608_, 3);
v_diag_1612_ = lean_ctor_get(v___x_1608_, 4);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; 
v_unused_1622_ = lean_ctor_get(v___x_1608_, 0);
lean_dec(v_unused_1622_);
v___x_1614_ = v___x_1608_;
v_isShared_1615_ = v_isSharedCheck_1621_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_diag_1612_);
lean_inc(v_postponed_1611_);
lean_inc(v_zetaDeltaFVarIds_1610_);
lean_inc(v_cache_1609_);
lean_dec(v___x_1608_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1621_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v_snd_1607_);
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_snd_1607_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_cache_1609_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_zetaDeltaFVarIds_1610_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v_postponed_1611_);
lean_ctor_set(v_reuseFailAlloc_1620_, 4, v_diag_1612_);
v___x_1617_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = lean_st_ref_set(v___y_1599_, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v_fst_1606_);
return v___x_1619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg___boxed(lean_object* v_e_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_1623_, v___y_1624_);
lean_dec(v___y_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0(lean_object* v_e_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_1627_, v___y_1631_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___boxed(lean_object* v_e_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0(v_e_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(lean_object* v_e_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v___x_1653_; lean_object* v_a_1654_; lean_object* v___x_1655_; 
v___x_1653_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_1645_, v_a_1649_);
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref(v___x_1653_);
v___x_1655_ = l_Lean_Meta_Sym_unfoldReducible(v_a_1654_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1657_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref(v___x_1655_);
v___x_1657_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1656_, v_a_1647_);
return v___x_1657_;
}
else
{
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr___boxed(lean_object* v_e_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_e_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_, lean_object* v_x_1670_){
_start:
{
lean_object* v_ks_1671_; lean_object* v_vs_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1696_; 
v_ks_1671_ = lean_ctor_get(v_x_1667_, 0);
v_vs_1672_ = lean_ctor_get(v_x_1667_, 1);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_x_1667_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1674_ = v_x_1667_;
v_isShared_1675_ = v_isSharedCheck_1696_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_vs_1672_);
lean_inc(v_ks_1671_);
lean_dec(v_x_1667_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1696_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1676_ = lean_array_get_size(v_ks_1671_);
v___x_1677_ = lean_nat_dec_lt(v_x_1668_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
lean_dec(v_x_1668_);
v___x_1678_ = lean_array_push(v_ks_1671_, v_x_1669_);
v___x_1679_ = lean_array_push(v_vs_1672_, v_x_1670_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v___x_1679_);
lean_ctor_set(v___x_1674_, 0, v___x_1678_);
v___x_1681_ = v___x_1674_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
else
{
lean_object* v_k_x27_1683_; uint8_t v___x_1684_; 
v_k_x27_1683_ = lean_array_fget_borrowed(v_ks_1671_, v_x_1668_);
v___x_1684_ = l_Lean_instBEqFVarId_beq(v_x_1669_, v_k_x27_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1686_; 
if (v_isShared_1675_ == 0)
{
v___x_1686_ = v___x_1674_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_ks_1671_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_vs_1672_);
v___x_1686_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_unsigned_to_nat(1u);
v___x_1688_ = lean_nat_add(v_x_1668_, v___x_1687_);
lean_dec(v_x_1668_);
v_x_1667_ = v___x_1686_;
v_x_1668_ = v___x_1688_;
goto _start;
}
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1691_ = lean_array_fset(v_ks_1671_, v_x_1668_, v_x_1669_);
v___x_1692_ = lean_array_fset(v_vs_1672_, v_x_1668_, v_x_1670_);
lean_dec(v_x_1668_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v___x_1692_);
lean_ctor_set(v___x_1674_, 0, v___x_1691_);
v___x_1694_ = v___x_1674_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1697_, lean_object* v_k_1698_, lean_object* v_v_1699_){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = lean_unsigned_to_nat(0u);
v___x_1701_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1697_, v___x_1700_, v_k_1698_, v_v_1699_);
return v___x_1701_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1702_; size_t v___x_1703_; size_t v___x_1704_; 
v___x_1702_ = ((size_t)5ULL);
v___x_1703_ = ((size_t)1ULL);
v___x_1704_ = lean_usize_shift_left(v___x_1703_, v___x_1702_);
return v___x_1704_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1705_; size_t v___x_1706_; size_t v___x_1707_; 
v___x_1705_ = ((size_t)1ULL);
v___x_1706_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0);
v___x_1707_ = lean_usize_sub(v___x_1706_, v___x_1705_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(lean_object* v_x_1709_, size_t v_x_1710_, size_t v_x_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_){
_start:
{
if (lean_obj_tag(v_x_1709_) == 0)
{
lean_object* v_es_1714_; size_t v___x_1715_; size_t v___x_1716_; size_t v___x_1717_; size_t v___x_1718_; lean_object* v_j_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v_es_1714_ = lean_ctor_get(v_x_1709_, 0);
v___x_1715_ = ((size_t)5ULL);
v___x_1716_ = ((size_t)1ULL);
v___x_1717_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
v___x_1718_ = lean_usize_land(v_x_1710_, v___x_1717_);
v_j_1719_ = lean_usize_to_nat(v___x_1718_);
v___x_1720_ = lean_array_get_size(v_es_1714_);
v___x_1721_ = lean_nat_dec_lt(v_j_1719_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_dec(v_j_1719_);
lean_dec(v_x_1713_);
lean_dec(v_x_1712_);
return v_x_1709_;
}
else
{
lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1758_; 
lean_inc_ref(v_es_1714_);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_x_1709_);
if (v_isSharedCheck_1758_ == 0)
{
lean_object* v_unused_1759_; 
v_unused_1759_ = lean_ctor_get(v_x_1709_, 0);
lean_dec(v_unused_1759_);
v___x_1723_ = v_x_1709_;
v_isShared_1724_ = v_isSharedCheck_1758_;
goto v_resetjp_1722_;
}
else
{
lean_dec(v_x_1709_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1758_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_v_1725_; lean_object* v___x_1726_; lean_object* v_xs_x27_1727_; lean_object* v___y_1729_; 
v_v_1725_ = lean_array_fget(v_es_1714_, v_j_1719_);
v___x_1726_ = lean_box(0);
v_xs_x27_1727_ = lean_array_fset(v_es_1714_, v_j_1719_, v___x_1726_);
switch(lean_obj_tag(v_v_1725_))
{
case 0:
{
lean_object* v_key_1734_; lean_object* v_val_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1745_; 
v_key_1734_ = lean_ctor_get(v_v_1725_, 0);
v_val_1735_ = lean_ctor_get(v_v_1725_, 1);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_v_1725_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1737_ = v_v_1725_;
v_isShared_1738_ = v_isSharedCheck_1745_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_val_1735_);
lean_inc(v_key_1734_);
lean_dec(v_v_1725_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1745_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
uint8_t v___x_1739_; 
v___x_1739_ = l_Lean_instBEqFVarId_beq(v_x_1712_, v_key_1734_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_del_object(v___x_1737_);
v___x_1740_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1734_, v_val_1735_, v_x_1712_, v_x_1713_);
v___x_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
v___y_1729_ = v___x_1741_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1743_; 
lean_dec(v_val_1735_);
lean_dec(v_key_1734_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 1, v_x_1713_);
lean_ctor_set(v___x_1737_, 0, v_x_1712_);
v___x_1743_ = v___x_1737_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_x_1712_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_x_1713_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
v___y_1729_ = v___x_1743_;
goto v___jp_1728_;
}
}
}
}
case 1:
{
lean_object* v_node_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1756_; 
v_node_1746_ = lean_ctor_get(v_v_1725_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_v_1725_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1748_ = v_v_1725_;
v_isShared_1749_ = v_isSharedCheck_1756_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_node_1746_);
lean_dec(v_v_1725_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1756_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1750_ = lean_usize_shift_right(v_x_1710_, v___x_1715_);
v___x_1751_ = lean_usize_add(v_x_1711_, v___x_1716_);
v___x_1752_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_node_1746_, v___x_1750_, v___x_1751_, v_x_1712_, v_x_1713_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1752_);
v___x_1754_ = v___x_1748_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
v___y_1729_ = v___x_1754_;
goto v___jp_1728_;
}
}
}
default: 
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v_x_1712_);
lean_ctor_set(v___x_1757_, 1, v_x_1713_);
v___y_1729_ = v___x_1757_;
goto v___jp_1728_;
}
}
v___jp_1728_:
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1730_ = lean_array_fset(v_xs_x27_1727_, v_j_1719_, v___y_1729_);
lean_dec(v_j_1719_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1730_);
v___x_1732_ = v___x_1723_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
else
{
lean_object* v_ks_1760_; lean_object* v_vs_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1781_; 
v_ks_1760_ = lean_ctor_get(v_x_1709_, 0);
v_vs_1761_ = lean_ctor_get(v_x_1709_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_x_1709_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1763_ = v_x_1709_;
v_isShared_1764_ = v_isSharedCheck_1781_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_vs_1761_);
lean_inc(v_ks_1760_);
lean_dec(v_x_1709_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1781_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_ks_1760_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_vs_1761_);
v___x_1766_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v_newNode_1767_; uint8_t v___y_1769_; size_t v___x_1775_; uint8_t v___x_1776_; 
v_newNode_1767_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v___x_1766_, v_x_1712_, v_x_1713_);
v___x_1775_ = ((size_t)7ULL);
v___x_1776_ = lean_usize_dec_le(v___x_1775_, v_x_1711_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1777_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1767_);
v___x_1778_ = lean_unsigned_to_nat(4u);
v___x_1779_ = lean_nat_dec_lt(v___x_1777_, v___x_1778_);
lean_dec(v___x_1777_);
v___y_1769_ = v___x_1779_;
goto v___jp_1768_;
}
else
{
v___y_1769_ = v___x_1776_;
goto v___jp_1768_;
}
v___jp_1768_:
{
if (v___y_1769_ == 0)
{
lean_object* v_ks_1770_; lean_object* v_vs_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v_ks_1770_ = lean_ctor_get(v_newNode_1767_, 0);
lean_inc_ref(v_ks_1770_);
v_vs_1771_ = lean_ctor_get(v_newNode_1767_, 1);
lean_inc_ref(v_vs_1771_);
lean_dec_ref(v_newNode_1767_);
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2);
v___x_1774_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_x_1711_, v_ks_1770_, v_vs_1771_, v___x_1772_, v___x_1773_);
lean_dec_ref(v_vs_1771_);
lean_dec_ref(v_ks_1770_);
return v___x_1774_;
}
else
{
return v_newNode_1767_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(size_t v_depth_1782_, lean_object* v_keys_1783_, lean_object* v_vals_1784_, lean_object* v_i_1785_, lean_object* v_entries_1786_){
_start:
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = lean_array_get_size(v_keys_1783_);
v___x_1788_ = lean_nat_dec_lt(v_i_1785_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_dec(v_i_1785_);
return v_entries_1786_;
}
else
{
lean_object* v_k_1789_; lean_object* v_v_1790_; uint64_t v___x_1791_; size_t v_h_1792_; size_t v___x_1793_; lean_object* v___x_1794_; size_t v___x_1795_; size_t v___x_1796_; size_t v___x_1797_; size_t v_h_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_k_1789_ = lean_array_fget_borrowed(v_keys_1783_, v_i_1785_);
v_v_1790_ = lean_array_fget_borrowed(v_vals_1784_, v_i_1785_);
v___x_1791_ = l_Lean_instHashableFVarId_hash(v_k_1789_);
v_h_1792_ = lean_uint64_to_usize(v___x_1791_);
v___x_1793_ = ((size_t)5ULL);
v___x_1794_ = lean_unsigned_to_nat(1u);
v___x_1795_ = ((size_t)1ULL);
v___x_1796_ = lean_usize_sub(v_depth_1782_, v___x_1795_);
v___x_1797_ = lean_usize_mul(v___x_1793_, v___x_1796_);
v_h_1798_ = lean_usize_shift_right(v_h_1792_, v___x_1797_);
v___x_1799_ = lean_nat_add(v_i_1785_, v___x_1794_);
lean_dec(v_i_1785_);
lean_inc(v_v_1790_);
lean_inc(v_k_1789_);
v___x_1800_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_entries_1786_, v_h_1798_, v_depth_1782_, v_k_1789_, v_v_1790_);
v_i_1785_ = v___x_1799_;
v_entries_1786_ = v___x_1800_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1802_, lean_object* v_keys_1803_, lean_object* v_vals_1804_, lean_object* v_i_1805_, lean_object* v_entries_1806_){
_start:
{
size_t v_depth_boxed_1807_; lean_object* v_res_1808_; 
v_depth_boxed_1807_ = lean_unbox_usize(v_depth_1802_);
lean_dec(v_depth_1802_);
v_res_1808_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1807_, v_keys_1803_, v_vals_1804_, v_i_1805_, v_entries_1806_);
lean_dec_ref(v_vals_1804_);
lean_dec_ref(v_keys_1803_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___boxed(lean_object* v_x_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_, lean_object* v_x_1812_, lean_object* v_x_1813_){
_start:
{
size_t v_x_9894__boxed_1814_; size_t v_x_9895__boxed_1815_; lean_object* v_res_1816_; 
v_x_9894__boxed_1814_ = lean_unbox_usize(v_x_1810_);
lean_dec(v_x_1810_);
v_x_9895__boxed_1815_ = lean_unbox_usize(v_x_1811_);
lean_dec(v_x_1811_);
v_res_1816_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_1809_, v_x_9894__boxed_1814_, v_x_9895__boxed_1815_, v_x_1812_, v_x_1813_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(lean_object* v_x_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_){
_start:
{
uint64_t v___x_1820_; size_t v___x_1821_; size_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1820_ = l_Lean_instHashableFVarId_hash(v_x_1818_);
v___x_1821_ = lean_uint64_to_usize(v___x_1820_);
v___x_1822_ = ((size_t)1ULL);
v___x_1823_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_1817_, v___x_1821_, v___x_1822_, v_x_1818_, v_x_1819_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(lean_object* v_as_1824_, size_t v_sz_1825_, size_t v_i_1826_, lean_object* v_b_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
uint8_t v___x_1835_; 
v___x_1835_ = lean_usize_dec_lt(v_i_1826_, v_sz_1825_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; 
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v_b_1827_);
return v___x_1836_;
}
else
{
lean_object* v_snd_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1942_; 
v_snd_1837_ = lean_ctor_get(v_b_1827_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_b_1827_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; 
v_unused_1943_ = lean_ctor_get(v_b_1827_, 0);
lean_dec(v_unused_1943_);
v___x_1839_ = v_b_1827_;
v_isShared_1840_ = v_isSharedCheck_1942_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_snd_1837_);
lean_dec(v_b_1827_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1942_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v_a_1843_; lean_object* v_a_1850_; 
v___x_1841_ = lean_box(0);
v_a_1850_ = lean_array_uget(v_as_1824_, v_i_1826_);
if (lean_obj_tag(v_a_1850_) == 0)
{
v_a_1843_ = v_snd_1837_;
goto v___jp_1842_;
}
else
{
lean_object* v_snd_1851_; lean_object* v_val_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1941_; 
v_snd_1851_ = lean_ctor_get(v_snd_1837_, 1);
lean_inc(v_snd_1851_);
v_val_1852_ = lean_ctor_get(v_a_1850_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_a_1850_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1854_ = v_a_1850_;
v_isShared_1855_ = v_isSharedCheck_1941_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_val_1852_);
lean_dec(v_a_1850_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1941_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v_fst_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1939_; 
v_fst_1856_ = lean_ctor_get(v_snd_1837_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_snd_1837_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v_snd_1837_, 1);
lean_dec(v_unused_1940_);
v___x_1858_ = v_snd_1837_;
v_isShared_1859_ = v_isSharedCheck_1939_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_fst_1856_);
lean_dec(v_snd_1837_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1939_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v_fst_1860_; lean_object* v_snd_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1938_; 
v_fst_1860_ = lean_ctor_get(v_snd_1851_, 0);
v_snd_1861_ = lean_ctor_get(v_snd_1851_, 1);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_snd_1851_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1863_ = v_snd_1851_;
v_isShared_1864_ = v_isSharedCheck_1938_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_snd_1861_);
lean_inc(v_fst_1860_);
lean_dec(v_snd_1851_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1938_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v_decl_1866_; 
if (lean_obj_tag(v_val_1852_) == 0)
{
lean_object* v_fvarId_1881_; lean_object* v_userName_1882_; lean_object* v_type_1883_; uint8_t v_bi_1884_; uint8_t v_kind_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1902_; 
v_fvarId_1881_ = lean_ctor_get(v_val_1852_, 1);
v_userName_1882_ = lean_ctor_get(v_val_1852_, 2);
v_type_1883_ = lean_ctor_get(v_val_1852_, 3);
v_bi_1884_ = lean_ctor_get_uint8(v_val_1852_, sizeof(void*)*4);
v_kind_1885_ = lean_ctor_get_uint8(v_val_1852_, sizeof(void*)*4 + 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_val_1852_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v_val_1852_, 0);
lean_dec(v_unused_1903_);
v___x_1887_ = v_val_1852_;
v_isShared_1888_ = v_isSharedCheck_1902_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_type_1883_);
lean_inc(v_userName_1882_);
lean_inc(v_fvarId_1881_);
lean_dec(v_val_1852_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1902_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; 
lean_inc(v___y_1833_);
lean_inc_ref(v___y_1832_);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
v___x_1889_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_1883_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref(v___x_1889_);
lean_inc(v_snd_1861_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 3, v_a_1890_);
lean_ctor_set(v___x_1887_, 0, v_snd_1861_);
v___x_1892_ = v___x_1887_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_snd_1861_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_fvarId_1881_);
lean_ctor_set(v_reuseFailAlloc_1893_, 2, v_userName_1882_);
lean_ctor_set(v_reuseFailAlloc_1893_, 3, v_a_1890_);
lean_ctor_set_uint8(v_reuseFailAlloc_1893_, sizeof(void*)*4, v_bi_1884_);
lean_ctor_set_uint8(v_reuseFailAlloc_1893_, sizeof(void*)*4 + 1, v_kind_1885_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
v_decl_1866_ = v___x_1892_;
goto v___jp_1865_;
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_del_object(v___x_1887_);
lean_dec(v_userName_1882_);
lean_dec(v_fvarId_1881_);
lean_del_object(v___x_1863_);
lean_dec(v_snd_1861_);
lean_dec(v_fst_1860_);
lean_del_object(v___x_1858_);
lean_dec(v_fst_1856_);
lean_del_object(v___x_1854_);
lean_del_object(v___x_1839_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
v_a_1894_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1889_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1889_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
else
{
lean_object* v_fvarId_1904_; lean_object* v_userName_1905_; lean_object* v_type_1906_; lean_object* v_value_1907_; uint8_t v_nondep_1908_; uint8_t v_kind_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1936_; 
v_fvarId_1904_ = lean_ctor_get(v_val_1852_, 1);
v_userName_1905_ = lean_ctor_get(v_val_1852_, 2);
v_type_1906_ = lean_ctor_get(v_val_1852_, 3);
v_value_1907_ = lean_ctor_get(v_val_1852_, 4);
v_nondep_1908_ = lean_ctor_get_uint8(v_val_1852_, sizeof(void*)*5);
v_kind_1909_ = lean_ctor_get_uint8(v_val_1852_, sizeof(void*)*5 + 1);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_val_1852_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v_val_1852_, 0);
lean_dec(v_unused_1937_);
v___x_1911_ = v_val_1852_;
v_isShared_1912_ = v_isSharedCheck_1936_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_value_1907_);
lean_inc(v_type_1906_);
lean_inc(v_userName_1905_);
lean_inc(v_fvarId_1904_);
lean_dec(v_val_1852_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1936_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; 
lean_inc(v___y_1833_);
lean_inc_ref(v___y_1832_);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
v___x_1913_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_1906_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref(v___x_1913_);
lean_inc(v___y_1833_);
lean_inc_ref(v___y_1832_);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
v___x_1915_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_1907_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
lean_inc(v_snd_1861_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 4, v_a_1916_);
lean_ctor_set(v___x_1911_, 3, v_a_1914_);
lean_ctor_set(v___x_1911_, 0, v_snd_1861_);
v___x_1918_ = v___x_1911_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_snd_1861_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_fvarId_1904_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_userName_1905_);
lean_ctor_set(v_reuseFailAlloc_1919_, 3, v_a_1914_);
lean_ctor_set(v_reuseFailAlloc_1919_, 4, v_a_1916_);
lean_ctor_set_uint8(v_reuseFailAlloc_1919_, sizeof(void*)*5, v_nondep_1908_);
lean_ctor_set_uint8(v_reuseFailAlloc_1919_, sizeof(void*)*5 + 1, v_kind_1909_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
v_decl_1866_ = v___x_1918_;
goto v___jp_1865_;
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec(v_a_1914_);
lean_del_object(v___x_1911_);
lean_dec(v_userName_1905_);
lean_dec(v_fvarId_1904_);
lean_del_object(v___x_1863_);
lean_dec(v_snd_1861_);
lean_dec(v_fst_1860_);
lean_del_object(v___x_1858_);
lean_dec(v_fst_1856_);
lean_del_object(v___x_1854_);
lean_del_object(v___x_1839_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
v_a_1920_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1915_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1915_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_del_object(v___x_1911_);
lean_dec_ref(v_value_1907_);
lean_dec(v_userName_1905_);
lean_dec(v_fvarId_1904_);
lean_del_object(v___x_1863_);
lean_dec(v_snd_1861_);
lean_dec(v_fst_1860_);
lean_del_object(v___x_1858_);
lean_dec(v_fst_1856_);
lean_del_object(v___x_1854_);
lean_del_object(v___x_1839_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
v_a_1928_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1913_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1913_);
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
}
v___jp_1865_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1867_ = lean_unsigned_to_nat(1u);
v___x_1868_ = lean_nat_add(v_snd_1861_, v___x_1867_);
lean_dec(v_snd_1861_);
lean_inc_ref(v_decl_1866_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_decl_1866_);
v___x_1870_ = v___x_1854_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_decl_1866_);
v___x_1870_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1871_ = l_Lean_PersistentArray_push___redArg(v_fst_1860_, v___x_1870_);
v___x_1872_ = l_Lean_LocalDecl_fvarId(v_decl_1866_);
v___x_1873_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_1856_, v___x_1872_, v_decl_1866_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 1, v___x_1868_);
lean_ctor_set(v___x_1863_, 0, v___x_1871_);
v___x_1875_ = v___x_1863_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1871_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v___x_1868_);
v___x_1875_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1877_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v___x_1875_);
lean_ctor_set(v___x_1858_, 0, v___x_1873_);
v___x_1877_ = v___x_1858_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
v_a_1843_ = v___x_1877_;
goto v___jp_1842_;
}
}
}
}
}
}
}
}
v___jp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 1, v_a_1843_);
lean_ctor_set(v___x_1839_, 0, v___x_1841_);
v___x_1845_ = v___x_1839_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1841_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_a_1843_);
v___x_1845_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
size_t v___x_1846_; size_t v___x_1847_; 
v___x_1846_ = ((size_t)1ULL);
v___x_1847_ = lean_usize_add(v_i_1826_, v___x_1846_);
v_i_1826_ = v___x_1847_;
v_b_1827_ = v___x_1845_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_as_1944_, lean_object* v_sz_1945_, lean_object* v_i_1946_, lean_object* v_b_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
size_t v_sz_boxed_1955_; size_t v_i_boxed_1956_; lean_object* v_res_1957_; 
v_sz_boxed_1955_ = lean_unbox_usize(v_sz_1945_);
lean_dec(v_sz_1945_);
v_i_boxed_1956_ = lean_unbox_usize(v_i_1946_);
lean_dec(v_i_1946_);
v_res_1957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_1944_, v_sz_boxed_1955_, v_i_boxed_1956_, v_b_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec_ref(v_as_1944_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(lean_object* v_as_1958_, size_t v_sz_1959_, size_t v_i_1960_, lean_object* v_b_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
uint8_t v___x_1969_; 
v___x_1969_ = lean_usize_dec_lt(v_i_1960_, v_sz_1959_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v_b_1961_);
return v___x_1970_;
}
else
{
lean_object* v_snd_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2076_; 
v_snd_1971_ = lean_ctor_get(v_b_1961_, 1);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_b_1961_);
if (v_isSharedCheck_2076_ == 0)
{
lean_object* v_unused_2077_; 
v_unused_2077_ = lean_ctor_get(v_b_1961_, 0);
lean_dec(v_unused_2077_);
v___x_1973_ = v_b_1961_;
v_isShared_1974_ = v_isSharedCheck_2076_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_snd_1971_);
lean_dec(v_b_1961_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2076_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v_a_1977_; lean_object* v_a_1984_; 
v___x_1975_ = lean_box(0);
v_a_1984_ = lean_array_uget(v_as_1958_, v_i_1960_);
if (lean_obj_tag(v_a_1984_) == 0)
{
v_a_1977_ = v_snd_1971_;
goto v___jp_1976_;
}
else
{
lean_object* v_snd_1985_; lean_object* v_val_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2075_; 
v_snd_1985_ = lean_ctor_get(v_snd_1971_, 1);
lean_inc(v_snd_1985_);
v_val_1986_ = lean_ctor_get(v_a_1984_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_a_1984_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_1988_ = v_a_1984_;
v_isShared_1989_ = v_isSharedCheck_2075_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_val_1986_);
lean_dec(v_a_1984_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2075_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v_fst_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2073_; 
v_fst_1990_ = lean_ctor_get(v_snd_1971_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_snd_1971_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v_snd_1971_, 1);
lean_dec(v_unused_2074_);
v___x_1992_ = v_snd_1971_;
v_isShared_1993_ = v_isSharedCheck_2073_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_fst_1990_);
lean_dec(v_snd_1971_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2073_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v_fst_1994_; lean_object* v_snd_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2072_; 
v_fst_1994_ = lean_ctor_get(v_snd_1985_, 0);
v_snd_1995_ = lean_ctor_get(v_snd_1985_, 1);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_snd_1985_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_1997_ = v_snd_1985_;
v_isShared_1998_ = v_isSharedCheck_2072_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_snd_1995_);
lean_inc(v_fst_1994_);
lean_dec(v_snd_1985_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2072_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_decl_2000_; 
if (lean_obj_tag(v_val_1986_) == 0)
{
lean_object* v_fvarId_2015_; lean_object* v_userName_2016_; lean_object* v_type_2017_; uint8_t v_bi_2018_; uint8_t v_kind_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2036_; 
v_fvarId_2015_ = lean_ctor_get(v_val_1986_, 1);
v_userName_2016_ = lean_ctor_get(v_val_1986_, 2);
v_type_2017_ = lean_ctor_get(v_val_1986_, 3);
v_bi_2018_ = lean_ctor_get_uint8(v_val_1986_, sizeof(void*)*4);
v_kind_2019_ = lean_ctor_get_uint8(v_val_1986_, sizeof(void*)*4 + 1);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_val_1986_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v_val_1986_, 0);
lean_dec(v_unused_2037_);
v___x_2021_ = v_val_1986_;
v_isShared_2022_ = v_isSharedCheck_2036_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_type_2017_);
lean_inc(v_userName_2016_);
lean_inc(v_fvarId_2015_);
lean_dec(v_val_1986_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2036_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; 
lean_inc(v___y_1967_);
lean_inc_ref(v___y_1966_);
lean_inc(v___y_1965_);
lean_inc_ref(v___y_1964_);
v___x_2023_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2017_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref(v___x_2023_);
lean_inc(v_snd_1995_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 3, v_a_2024_);
lean_ctor_set(v___x_2021_, 0, v_snd_1995_);
v___x_2026_ = v___x_2021_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_snd_1995_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_fvarId_2015_);
lean_ctor_set(v_reuseFailAlloc_2027_, 2, v_userName_2016_);
lean_ctor_set(v_reuseFailAlloc_2027_, 3, v_a_2024_);
lean_ctor_set_uint8(v_reuseFailAlloc_2027_, sizeof(void*)*4, v_bi_2018_);
lean_ctor_set_uint8(v_reuseFailAlloc_2027_, sizeof(void*)*4 + 1, v_kind_2019_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
v_decl_2000_ = v___x_2026_;
goto v___jp_1999_;
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_del_object(v___x_2021_);
lean_dec(v_userName_2016_);
lean_dec(v_fvarId_2015_);
lean_del_object(v___x_1997_);
lean_dec(v_snd_1995_);
lean_dec(v_fst_1994_);
lean_del_object(v___x_1992_);
lean_dec(v_fst_1990_);
lean_del_object(v___x_1988_);
lean_del_object(v___x_1973_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
v_a_2028_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2023_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2023_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2038_; lean_object* v_userName_2039_; lean_object* v_type_2040_; lean_object* v_value_2041_; uint8_t v_nondep_2042_; uint8_t v_kind_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2070_; 
v_fvarId_2038_ = lean_ctor_get(v_val_1986_, 1);
v_userName_2039_ = lean_ctor_get(v_val_1986_, 2);
v_type_2040_ = lean_ctor_get(v_val_1986_, 3);
v_value_2041_ = lean_ctor_get(v_val_1986_, 4);
v_nondep_2042_ = lean_ctor_get_uint8(v_val_1986_, sizeof(void*)*5);
v_kind_2043_ = lean_ctor_get_uint8(v_val_1986_, sizeof(void*)*5 + 1);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_val_1986_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; 
v_unused_2071_ = lean_ctor_get(v_val_1986_, 0);
lean_dec(v_unused_2071_);
v___x_2045_ = v_val_1986_;
v_isShared_2046_ = v_isSharedCheck_2070_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_value_2041_);
lean_inc(v_type_2040_);
lean_inc(v_userName_2039_);
lean_inc(v_fvarId_2038_);
lean_dec(v_val_1986_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2070_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; 
lean_inc(v___y_1967_);
lean_inc_ref(v___y_1966_);
lean_inc(v___y_1965_);
lean_inc_ref(v___y_1964_);
v___x_2047_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2040_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref(v___x_2047_);
lean_inc(v___y_1967_);
lean_inc_ref(v___y_1966_);
lean_inc(v___y_1965_);
lean_inc_ref(v___y_1964_);
v___x_2049_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2041_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
lean_inc(v_snd_1995_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 4, v_a_2050_);
lean_ctor_set(v___x_2045_, 3, v_a_2048_);
lean_ctor_set(v___x_2045_, 0, v_snd_1995_);
v___x_2052_ = v___x_2045_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_snd_1995_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_fvarId_2038_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_userName_2039_);
lean_ctor_set(v_reuseFailAlloc_2053_, 3, v_a_2048_);
lean_ctor_set(v_reuseFailAlloc_2053_, 4, v_a_2050_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*5, v_nondep_2042_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*5 + 1, v_kind_2043_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
v_decl_2000_ = v___x_2052_;
goto v___jp_1999_;
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec(v_a_2048_);
lean_del_object(v___x_2045_);
lean_dec(v_userName_2039_);
lean_dec(v_fvarId_2038_);
lean_del_object(v___x_1997_);
lean_dec(v_snd_1995_);
lean_dec(v_fst_1994_);
lean_del_object(v___x_1992_);
lean_dec(v_fst_1990_);
lean_del_object(v___x_1988_);
lean_del_object(v___x_1973_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
v_a_2054_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2049_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2049_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_del_object(v___x_2045_);
lean_dec_ref(v_value_2041_);
lean_dec(v_userName_2039_);
lean_dec(v_fvarId_2038_);
lean_del_object(v___x_1997_);
lean_dec(v_snd_1995_);
lean_dec(v_fst_1994_);
lean_del_object(v___x_1992_);
lean_dec(v_fst_1990_);
lean_del_object(v___x_1988_);
lean_del_object(v___x_1973_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
v_a_2062_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2047_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2047_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
v___jp_1999_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2001_ = lean_unsigned_to_nat(1u);
v___x_2002_ = lean_nat_add(v_snd_1995_, v___x_2001_);
lean_dec(v_snd_1995_);
lean_inc_ref(v_decl_2000_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v_decl_2000_);
v___x_2004_ = v___x_1988_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_decl_2000_);
v___x_2004_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2005_ = l_Lean_PersistentArray_push___redArg(v_fst_1994_, v___x_2004_);
v___x_2006_ = l_Lean_LocalDecl_fvarId(v_decl_2000_);
v___x_2007_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_1990_, v___x_2006_, v_decl_2000_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 1, v___x_2002_);
lean_ctor_set(v___x_1997_, 0, v___x_2005_);
v___x_2009_ = v___x_1997_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v___x_2002_);
v___x_2009_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2011_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 1, v___x_2009_);
lean_ctor_set(v___x_1992_, 0, v___x_2007_);
v___x_2011_ = v___x_1992_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
v_a_1977_ = v___x_2011_;
goto v___jp_1976_;
}
}
}
}
}
}
}
}
v___jp_1976_:
{
lean_object* v___x_1979_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 1, v_a_1977_);
lean_ctor_set(v___x_1973_, 0, v___x_1975_);
v___x_1979_ = v___x_1973_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_a_1977_);
v___x_1979_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
size_t v___x_1980_; size_t v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = ((size_t)1ULL);
v___x_1981_ = lean_usize_add(v_i_1960_, v___x_1980_);
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_1958_, v_sz_1959_, v___x_1981_, v___x_1979_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
return v___x_1982_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6___boxed(lean_object* v_as_2078_, lean_object* v_sz_2079_, lean_object* v_i_2080_, lean_object* v_b_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
size_t v_sz_boxed_2089_; size_t v_i_boxed_2090_; lean_object* v_res_2091_; 
v_sz_boxed_2089_ = lean_unbox_usize(v_sz_2079_);
lean_dec(v_sz_2079_);
v_i_boxed_2090_ = lean_unbox_usize(v_i_2080_);
lean_dec(v_i_2080_);
v_res_2091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_as_2078_, v_sz_boxed_2089_, v_i_boxed_2090_, v_b_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec_ref(v_as_2078_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(lean_object* v_inh_2092_, lean_object* v_n_2093_, lean_object* v_b_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
if (lean_obj_tag(v_n_2093_) == 0)
{
lean_object* v_cs_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2136_; 
v_cs_2102_ = lean_ctor_get(v_n_2093_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_n_2093_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2104_ = v_n_2093_;
v_isShared_2105_ = v_isSharedCheck_2136_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_cs_2102_);
lean_dec(v_n_2093_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2136_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; size_t v_sz_2108_; size_t v___x_2109_; lean_object* v___x_2110_; 
v___x_2106_ = lean_box(0);
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v_b_2094_);
v_sz_2108_ = lean_array_size(v_cs_2102_);
v___x_2109_ = ((size_t)0ULL);
v___x_2110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_inh_2092_, v_cs_2102_, v_sz_2108_, v___x_2109_, v___x_2107_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
lean_dec_ref(v_cs_2102_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2127_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2127_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2127_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v_fst_2115_; 
v_fst_2115_ = lean_ctor_get(v_a_2111_, 0);
if (lean_obj_tag(v_fst_2115_) == 0)
{
lean_object* v_snd_2116_; lean_object* v___x_2118_; 
v_snd_2116_ = lean_ctor_get(v_a_2111_, 1);
lean_inc(v_snd_2116_);
lean_dec(v_a_2111_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set_tag(v___x_2104_, 1);
lean_ctor_set(v___x_2104_, 0, v_snd_2116_);
v___x_2118_ = v___x_2104_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_snd_2116_);
v___x_2118_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2120_; 
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2118_);
v___x_2120_ = v___x_2113_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
else
{
lean_object* v_val_2123_; lean_object* v___x_2125_; 
lean_inc_ref(v_fst_2115_);
lean_dec(v_a_2111_);
lean_del_object(v___x_2104_);
v_val_2123_ = lean_ctor_get(v_fst_2115_, 0);
lean_inc(v_val_2123_);
lean_dec_ref(v_fst_2115_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v_val_2123_);
v___x_2125_ = v___x_2113_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_val_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_del_object(v___x_2104_);
v_a_2128_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2110_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2110_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
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
}
else
{
lean_object* v_vs_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2171_; 
v_vs_2137_ = lean_ctor_get(v_n_2093_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_n_2093_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2139_ = v_n_2093_;
v_isShared_2140_ = v_isSharedCheck_2171_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_vs_2137_);
lean_dec(v_n_2093_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2171_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; size_t v_sz_2143_; size_t v___x_2144_; lean_object* v___x_2145_; 
v___x_2141_ = lean_box(0);
v___x_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
lean_ctor_set(v___x_2142_, 1, v_b_2094_);
v_sz_2143_ = lean_array_size(v_vs_2137_);
v___x_2144_ = ((size_t)0ULL);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_vs_2137_, v_sz_2143_, v___x_2144_, v___x_2142_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
lean_dec_ref(v_vs_2137_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2162_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2162_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2162_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_fst_2150_; 
v_fst_2150_ = lean_ctor_get(v_a_2146_, 0);
if (lean_obj_tag(v_fst_2150_) == 0)
{
lean_object* v_snd_2151_; lean_object* v___x_2153_; 
v_snd_2151_ = lean_ctor_get(v_a_2146_, 1);
lean_inc(v_snd_2151_);
lean_dec(v_a_2146_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v_snd_2151_);
v___x_2153_ = v___x_2139_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_snd_2151_);
v___x_2153_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2155_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2153_);
v___x_2155_ = v___x_2148_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
else
{
lean_object* v_val_2158_; lean_object* v___x_2160_; 
lean_inc_ref(v_fst_2150_);
lean_dec(v_a_2146_);
lean_del_object(v___x_2139_);
v_val_2158_ = lean_ctor_get(v_fst_2150_, 0);
lean_inc(v_val_2158_);
lean_dec_ref(v_fst_2150_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v_val_2158_);
v___x_2160_ = v___x_2148_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_val_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_del_object(v___x_2139_);
v_a_2163_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2145_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2145_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(lean_object* v_inh_2172_, lean_object* v_as_2173_, size_t v_sz_2174_, size_t v_i_2175_, lean_object* v_b_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
uint8_t v___x_2184_; 
v___x_2184_ = lean_usize_dec_lt(v_i_2175_, v_sz_2174_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; 
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v_b_2176_);
return v___x_2185_;
}
else
{
lean_object* v_snd_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2220_; 
v_snd_2186_ = lean_ctor_get(v_b_2176_, 1);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_b_2176_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; 
v_unused_2221_ = lean_ctor_get(v_b_2176_, 0);
lean_dec(v_unused_2221_);
v___x_2188_ = v_b_2176_;
v_isShared_2189_ = v_isSharedCheck_2220_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_snd_2186_);
lean_dec(v_b_2176_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2220_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v_a_2190_; lean_object* v___x_2191_; 
v_a_2190_ = lean_array_uget_borrowed(v_as_2173_, v_i_2175_);
lean_inc(v___y_2182_);
lean_inc_ref(v___y_2181_);
lean_inc(v___y_2180_);
lean_inc_ref(v___y_2179_);
lean_inc(v_snd_2186_);
lean_inc(v_a_2190_);
v___x_2191_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_inh_2172_, v_a_2190_, v_snd_2186_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2211_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2194_ = v___x_2191_;
v_isShared_2195_ = v_isSharedCheck_2211_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2211_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
if (lean_obj_tag(v_a_2192_) == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
v___x_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2196_, 0, v_a_2192_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2196_);
v___x_2198_ = v___x_2188_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_snd_2186_);
v___x_2198_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2200_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2198_);
v___x_2200_ = v___x_2194_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
lean_del_object(v___x_2194_);
lean_dec(v_snd_2186_);
v_a_2203_ = lean_ctor_get(v_a_2192_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v_a_2192_);
v___x_2204_ = lean_box(0);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 1, v_a_2203_);
lean_ctor_set(v___x_2188_, 0, v___x_2204_);
v___x_2206_ = v___x_2188_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_a_2203_);
v___x_2206_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
size_t v___x_2207_; size_t v___x_2208_; 
v___x_2207_ = ((size_t)1ULL);
v___x_2208_ = lean_usize_add(v_i_2175_, v___x_2207_);
v_i_2175_ = v___x_2208_;
v_b_2176_ = v___x_2206_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_del_object(v___x_2188_);
lean_dec(v_snd_2186_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
v_a_2212_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2191_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2191_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_inh_2222_, lean_object* v_as_2223_, lean_object* v_sz_2224_, lean_object* v_i_2225_, lean_object* v_b_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
size_t v_sz_boxed_2234_; size_t v_i_boxed_2235_; lean_object* v_res_2236_; 
v_sz_boxed_2234_ = lean_unbox_usize(v_sz_2224_);
lean_dec(v_sz_2224_);
v_i_boxed_2235_ = lean_unbox_usize(v_i_2225_);
lean_dec(v_i_2225_);
v_res_2236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_inh_2222_, v_as_2223_, v_sz_boxed_2234_, v_i_boxed_2235_, v_b_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec_ref(v_as_2223_);
lean_dec_ref(v_inh_2222_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2___boxed(lean_object* v_inh_2237_, lean_object* v_n_2238_, lean_object* v_b_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_inh_2237_, v_n_2238_, v_b_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec_ref(v_inh_2237_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(lean_object* v_as_2248_, size_t v_sz_2249_, size_t v_i_2250_, lean_object* v_b_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_usize_dec_lt(v_i_2250_, v_sz_2249_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; 
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v_b_2251_);
return v___x_2260_;
}
else
{
lean_object* v_snd_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2366_; 
v_snd_2261_ = lean_ctor_get(v_b_2251_, 1);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_b_2251_);
if (v_isSharedCheck_2366_ == 0)
{
lean_object* v_unused_2367_; 
v_unused_2367_ = lean_ctor_get(v_b_2251_, 0);
lean_dec(v_unused_2367_);
v___x_2263_ = v_b_2251_;
v_isShared_2264_ = v_isSharedCheck_2366_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_snd_2261_);
lean_dec(v_b_2251_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2366_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v_a_2267_; lean_object* v_a_2274_; 
v___x_2265_ = lean_box(0);
v_a_2274_ = lean_array_uget(v_as_2248_, v_i_2250_);
if (lean_obj_tag(v_a_2274_) == 0)
{
v_a_2267_ = v_snd_2261_;
goto v___jp_2266_;
}
else
{
lean_object* v_snd_2275_; lean_object* v_val_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2365_; 
v_snd_2275_ = lean_ctor_get(v_snd_2261_, 1);
lean_inc(v_snd_2275_);
v_val_2276_ = lean_ctor_get(v_a_2274_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_a_2274_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2278_ = v_a_2274_;
v_isShared_2279_ = v_isSharedCheck_2365_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_val_2276_);
lean_dec(v_a_2274_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2365_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v_fst_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2363_; 
v_fst_2280_ = lean_ctor_get(v_snd_2261_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_snd_2261_);
if (v_isSharedCheck_2363_ == 0)
{
lean_object* v_unused_2364_; 
v_unused_2364_ = lean_ctor_get(v_snd_2261_, 1);
lean_dec(v_unused_2364_);
v___x_2282_ = v_snd_2261_;
v_isShared_2283_ = v_isSharedCheck_2363_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_fst_2280_);
lean_dec(v_snd_2261_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2363_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v_fst_2284_; lean_object* v_snd_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2362_; 
v_fst_2284_ = lean_ctor_get(v_snd_2275_, 0);
v_snd_2285_ = lean_ctor_get(v_snd_2275_, 1);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_snd_2275_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2287_ = v_snd_2275_;
v_isShared_2288_ = v_isSharedCheck_2362_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_snd_2285_);
lean_inc(v_fst_2284_);
lean_dec(v_snd_2275_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2362_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v_decl_2290_; 
if (lean_obj_tag(v_val_2276_) == 0)
{
lean_object* v_fvarId_2305_; lean_object* v_userName_2306_; lean_object* v_type_2307_; uint8_t v_bi_2308_; uint8_t v_kind_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2326_; 
v_fvarId_2305_ = lean_ctor_get(v_val_2276_, 1);
v_userName_2306_ = lean_ctor_get(v_val_2276_, 2);
v_type_2307_ = lean_ctor_get(v_val_2276_, 3);
v_bi_2308_ = lean_ctor_get_uint8(v_val_2276_, sizeof(void*)*4);
v_kind_2309_ = lean_ctor_get_uint8(v_val_2276_, sizeof(void*)*4 + 1);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_val_2276_);
if (v_isSharedCheck_2326_ == 0)
{
lean_object* v_unused_2327_; 
v_unused_2327_ = lean_ctor_get(v_val_2276_, 0);
lean_dec(v_unused_2327_);
v___x_2311_ = v_val_2276_;
v_isShared_2312_ = v_isSharedCheck_2326_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_type_2307_);
lean_inc(v_userName_2306_);
lean_inc(v_fvarId_2305_);
lean_dec(v_val_2276_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2326_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; 
lean_inc(v___y_2257_);
lean_inc_ref(v___y_2256_);
lean_inc(v___y_2255_);
lean_inc_ref(v___y_2254_);
v___x_2313_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2307_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref(v___x_2313_);
lean_inc(v_snd_2285_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 3, v_a_2314_);
lean_ctor_set(v___x_2311_, 0, v_snd_2285_);
v___x_2316_ = v___x_2311_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_snd_2285_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_fvarId_2305_);
lean_ctor_set(v_reuseFailAlloc_2317_, 2, v_userName_2306_);
lean_ctor_set(v_reuseFailAlloc_2317_, 3, v_a_2314_);
lean_ctor_set_uint8(v_reuseFailAlloc_2317_, sizeof(void*)*4, v_bi_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2317_, sizeof(void*)*4 + 1, v_kind_2309_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
v_decl_2290_ = v___x_2316_;
goto v___jp_2289_;
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_del_object(v___x_2311_);
lean_dec(v_userName_2306_);
lean_dec(v_fvarId_2305_);
lean_del_object(v___x_2287_);
lean_dec(v_snd_2285_);
lean_dec(v_fst_2284_);
lean_del_object(v___x_2282_);
lean_dec(v_fst_2280_);
lean_del_object(v___x_2278_);
lean_del_object(v___x_2263_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
v_a_2318_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2313_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2313_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2328_; lean_object* v_userName_2329_; lean_object* v_type_2330_; lean_object* v_value_2331_; uint8_t v_nondep_2332_; uint8_t v_kind_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2360_; 
v_fvarId_2328_ = lean_ctor_get(v_val_2276_, 1);
v_userName_2329_ = lean_ctor_get(v_val_2276_, 2);
v_type_2330_ = lean_ctor_get(v_val_2276_, 3);
v_value_2331_ = lean_ctor_get(v_val_2276_, 4);
v_nondep_2332_ = lean_ctor_get_uint8(v_val_2276_, sizeof(void*)*5);
v_kind_2333_ = lean_ctor_get_uint8(v_val_2276_, sizeof(void*)*5 + 1);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_val_2276_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; 
v_unused_2361_ = lean_ctor_get(v_val_2276_, 0);
lean_dec(v_unused_2361_);
v___x_2335_ = v_val_2276_;
v_isShared_2336_ = v_isSharedCheck_2360_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_value_2331_);
lean_inc(v_type_2330_);
lean_inc(v_userName_2329_);
lean_inc(v_fvarId_2328_);
lean_dec(v_val_2276_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2360_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; 
lean_inc(v___y_2257_);
lean_inc_ref(v___y_2256_);
lean_inc(v___y_2255_);
lean_inc_ref(v___y_2254_);
v___x_2337_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2330_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref(v___x_2337_);
lean_inc(v___y_2257_);
lean_inc_ref(v___y_2256_);
lean_inc(v___y_2255_);
lean_inc_ref(v___y_2254_);
v___x_2339_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2331_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref(v___x_2339_);
lean_inc(v_snd_2285_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 4, v_a_2340_);
lean_ctor_set(v___x_2335_, 3, v_a_2338_);
lean_ctor_set(v___x_2335_, 0, v_snd_2285_);
v___x_2342_ = v___x_2335_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_snd_2285_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_fvarId_2328_);
lean_ctor_set(v_reuseFailAlloc_2343_, 2, v_userName_2329_);
lean_ctor_set(v_reuseFailAlloc_2343_, 3, v_a_2338_);
lean_ctor_set(v_reuseFailAlloc_2343_, 4, v_a_2340_);
lean_ctor_set_uint8(v_reuseFailAlloc_2343_, sizeof(void*)*5, v_nondep_2332_);
lean_ctor_set_uint8(v_reuseFailAlloc_2343_, sizeof(void*)*5 + 1, v_kind_2333_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
v_decl_2290_ = v___x_2342_;
goto v___jp_2289_;
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v_a_2338_);
lean_del_object(v___x_2335_);
lean_dec(v_userName_2329_);
lean_dec(v_fvarId_2328_);
lean_del_object(v___x_2287_);
lean_dec(v_snd_2285_);
lean_dec(v_fst_2284_);
lean_del_object(v___x_2282_);
lean_dec(v_fst_2280_);
lean_del_object(v___x_2278_);
lean_del_object(v___x_2263_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
v_a_2344_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2339_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2339_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_del_object(v___x_2335_);
lean_dec_ref(v_value_2331_);
lean_dec(v_userName_2329_);
lean_dec(v_fvarId_2328_);
lean_del_object(v___x_2287_);
lean_dec(v_snd_2285_);
lean_dec(v_fst_2284_);
lean_del_object(v___x_2282_);
lean_dec(v_fst_2280_);
lean_del_object(v___x_2278_);
lean_del_object(v___x_2263_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
v_a_2352_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2337_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2337_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
}
v___jp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2291_ = lean_unsigned_to_nat(1u);
v___x_2292_ = lean_nat_add(v_snd_2285_, v___x_2291_);
lean_dec(v_snd_2285_);
lean_inc_ref(v_decl_2290_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 0, v_decl_2290_);
v___x_2294_ = v___x_2278_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_decl_2290_);
v___x_2294_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2295_ = l_Lean_PersistentArray_push___redArg(v_fst_2284_, v___x_2294_);
v___x_2296_ = l_Lean_LocalDecl_fvarId(v_decl_2290_);
v___x_2297_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2280_, v___x_2296_, v_decl_2290_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 1, v___x_2292_);
lean_ctor_set(v___x_2287_, 0, v___x_2295_);
v___x_2299_ = v___x_2287_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2303_, 1, v___x_2292_);
v___x_2299_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v___x_2301_; 
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 1, v___x_2299_);
lean_ctor_set(v___x_2282_, 0, v___x_2297_);
v___x_2301_ = v___x_2282_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2297_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
v_a_2267_ = v___x_2301_;
goto v___jp_2266_;
}
}
}
}
}
}
}
}
v___jp_2266_:
{
lean_object* v___x_2269_; 
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 1, v_a_2267_);
lean_ctor_set(v___x_2263_, 0, v___x_2265_);
v___x_2269_ = v___x_2263_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_a_2267_);
v___x_2269_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
size_t v___x_2270_; size_t v___x_2271_; 
v___x_2270_ = ((size_t)1ULL);
v___x_2271_ = lean_usize_add(v_i_2250_, v___x_2270_);
v_i_2250_ = v___x_2271_;
v_b_2251_ = v___x_2269_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8___boxed(lean_object* v_as_2368_, lean_object* v_sz_2369_, lean_object* v_i_2370_, lean_object* v_b_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
size_t v_sz_boxed_2379_; size_t v_i_boxed_2380_; lean_object* v_res_2381_; 
v_sz_boxed_2379_ = lean_unbox_usize(v_sz_2369_);
lean_dec(v_sz_2369_);
v_i_boxed_2380_ = lean_unbox_usize(v_i_2370_);
lean_dec(v_i_2370_);
v_res_2381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_2368_, v_sz_boxed_2379_, v_i_boxed_2380_, v_b_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec_ref(v_as_2368_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(lean_object* v_as_2382_, size_t v_sz_2383_, size_t v_i_2384_, lean_object* v_b_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
uint8_t v___x_2393_; 
v___x_2393_ = lean_usize_dec_lt(v_i_2384_, v_sz_2383_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; 
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v_b_2385_);
return v___x_2394_;
}
else
{
lean_object* v_snd_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2500_; 
v_snd_2395_ = lean_ctor_get(v_b_2385_, 1);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_b_2385_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; 
v_unused_2501_ = lean_ctor_get(v_b_2385_, 0);
lean_dec(v_unused_2501_);
v___x_2397_ = v_b_2385_;
v_isShared_2398_ = v_isSharedCheck_2500_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_snd_2395_);
lean_dec(v_b_2385_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2500_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v_a_2401_; lean_object* v_a_2408_; 
v___x_2399_ = lean_box(0);
v_a_2408_ = lean_array_uget(v_as_2382_, v_i_2384_);
if (lean_obj_tag(v_a_2408_) == 0)
{
v_a_2401_ = v_snd_2395_;
goto v___jp_2400_;
}
else
{
lean_object* v_snd_2409_; lean_object* v_val_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2499_; 
v_snd_2409_ = lean_ctor_get(v_snd_2395_, 1);
lean_inc(v_snd_2409_);
v_val_2410_ = lean_ctor_get(v_a_2408_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_a_2408_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2412_ = v_a_2408_;
v_isShared_2413_ = v_isSharedCheck_2499_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_val_2410_);
lean_dec(v_a_2408_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2499_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v_fst_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2497_; 
v_fst_2414_ = lean_ctor_get(v_snd_2395_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_snd_2395_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; 
v_unused_2498_ = lean_ctor_get(v_snd_2395_, 1);
lean_dec(v_unused_2498_);
v___x_2416_ = v_snd_2395_;
v_isShared_2417_ = v_isSharedCheck_2497_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_fst_2414_);
lean_dec(v_snd_2395_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2497_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v_fst_2418_; lean_object* v_snd_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2496_; 
v_fst_2418_ = lean_ctor_get(v_snd_2409_, 0);
v_snd_2419_ = lean_ctor_get(v_snd_2409_, 1);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_snd_2409_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2421_ = v_snd_2409_;
v_isShared_2422_ = v_isSharedCheck_2496_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_snd_2419_);
lean_inc(v_fst_2418_);
lean_dec(v_snd_2409_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2496_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v_decl_2424_; 
if (lean_obj_tag(v_val_2410_) == 0)
{
lean_object* v_fvarId_2439_; lean_object* v_userName_2440_; lean_object* v_type_2441_; uint8_t v_bi_2442_; uint8_t v_kind_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2460_; 
v_fvarId_2439_ = lean_ctor_get(v_val_2410_, 1);
v_userName_2440_ = lean_ctor_get(v_val_2410_, 2);
v_type_2441_ = lean_ctor_get(v_val_2410_, 3);
v_bi_2442_ = lean_ctor_get_uint8(v_val_2410_, sizeof(void*)*4);
v_kind_2443_ = lean_ctor_get_uint8(v_val_2410_, sizeof(void*)*4 + 1);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_val_2410_);
if (v_isSharedCheck_2460_ == 0)
{
lean_object* v_unused_2461_; 
v_unused_2461_ = lean_ctor_get(v_val_2410_, 0);
lean_dec(v_unused_2461_);
v___x_2445_ = v_val_2410_;
v_isShared_2446_ = v_isSharedCheck_2460_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_type_2441_);
lean_inc(v_userName_2440_);
lean_inc(v_fvarId_2439_);
lean_dec(v_val_2410_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2460_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; 
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v___y_2388_);
v___x_2447_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2441_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2450_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2448_);
lean_dec_ref(v___x_2447_);
lean_inc(v_snd_2419_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 3, v_a_2448_);
lean_ctor_set(v___x_2445_, 0, v_snd_2419_);
v___x_2450_ = v___x_2445_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_snd_2419_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_fvarId_2439_);
lean_ctor_set(v_reuseFailAlloc_2451_, 2, v_userName_2440_);
lean_ctor_set(v_reuseFailAlloc_2451_, 3, v_a_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*4, v_bi_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*4 + 1, v_kind_2443_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
v_decl_2424_ = v___x_2450_;
goto v___jp_2423_;
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_del_object(v___x_2445_);
lean_dec(v_userName_2440_);
lean_dec(v_fvarId_2439_);
lean_del_object(v___x_2421_);
lean_dec(v_snd_2419_);
lean_dec(v_fst_2418_);
lean_del_object(v___x_2416_);
lean_dec(v_fst_2414_);
lean_del_object(v___x_2412_);
lean_del_object(v___x_2397_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
v_a_2452_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2447_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2447_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2462_; lean_object* v_userName_2463_; lean_object* v_type_2464_; lean_object* v_value_2465_; uint8_t v_nondep_2466_; uint8_t v_kind_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2494_; 
v_fvarId_2462_ = lean_ctor_get(v_val_2410_, 1);
v_userName_2463_ = lean_ctor_get(v_val_2410_, 2);
v_type_2464_ = lean_ctor_get(v_val_2410_, 3);
v_value_2465_ = lean_ctor_get(v_val_2410_, 4);
v_nondep_2466_ = lean_ctor_get_uint8(v_val_2410_, sizeof(void*)*5);
v_kind_2467_ = lean_ctor_get_uint8(v_val_2410_, sizeof(void*)*5 + 1);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_val_2410_);
if (v_isSharedCheck_2494_ == 0)
{
lean_object* v_unused_2495_; 
v_unused_2495_ = lean_ctor_get(v_val_2410_, 0);
lean_dec(v_unused_2495_);
v___x_2469_ = v_val_2410_;
v_isShared_2470_ = v_isSharedCheck_2494_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_value_2465_);
lean_inc(v_type_2464_);
lean_inc(v_userName_2463_);
lean_inc(v_fvarId_2462_);
lean_dec(v_val_2410_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2494_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; 
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v___y_2388_);
v___x_2471_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2464_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2473_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref(v___x_2471_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v___y_2388_);
v___x_2473_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2465_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2476_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref(v___x_2473_);
lean_inc(v_snd_2419_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 4, v_a_2474_);
lean_ctor_set(v___x_2469_, 3, v_a_2472_);
lean_ctor_set(v___x_2469_, 0, v_snd_2419_);
v___x_2476_ = v___x_2469_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_snd_2419_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_fvarId_2462_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_userName_2463_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_a_2472_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_a_2474_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, sizeof(void*)*5, v_nondep_2466_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, sizeof(void*)*5 + 1, v_kind_2467_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
v_decl_2424_ = v___x_2476_;
goto v___jp_2423_;
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_a_2472_);
lean_del_object(v___x_2469_);
lean_dec(v_userName_2463_);
lean_dec(v_fvarId_2462_);
lean_del_object(v___x_2421_);
lean_dec(v_snd_2419_);
lean_dec(v_fst_2418_);
lean_del_object(v___x_2416_);
lean_dec(v_fst_2414_);
lean_del_object(v___x_2412_);
lean_del_object(v___x_2397_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
v_a_2478_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2473_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2473_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_del_object(v___x_2469_);
lean_dec_ref(v_value_2465_);
lean_dec(v_userName_2463_);
lean_dec(v_fvarId_2462_);
lean_del_object(v___x_2421_);
lean_dec(v_snd_2419_);
lean_dec(v_fst_2418_);
lean_del_object(v___x_2416_);
lean_dec(v_fst_2414_);
lean_del_object(v___x_2412_);
lean_del_object(v___x_2397_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
v_a_2486_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2471_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2471_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
v___jp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2428_; 
v___x_2425_ = lean_unsigned_to_nat(1u);
v___x_2426_ = lean_nat_add(v_snd_2419_, v___x_2425_);
lean_dec(v_snd_2419_);
lean_inc_ref(v_decl_2424_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v_decl_2424_);
v___x_2428_ = v___x_2412_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_decl_2424_);
v___x_2428_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2429_ = l_Lean_PersistentArray_push___redArg(v_fst_2418_, v___x_2428_);
v___x_2430_ = l_Lean_LocalDecl_fvarId(v_decl_2424_);
v___x_2431_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2414_, v___x_2430_, v_decl_2424_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 1, v___x_2426_);
lean_ctor_set(v___x_2421_, 0, v___x_2429_);
v___x_2433_ = v___x_2421_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v___x_2426_);
v___x_2433_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2435_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v___x_2433_);
lean_ctor_set(v___x_2416_, 0, v___x_2431_);
v___x_2435_ = v___x_2416_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
v_a_2401_ = v___x_2435_;
goto v___jp_2400_;
}
}
}
}
}
}
}
}
v___jp_2400_:
{
lean_object* v___x_2403_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 1, v_a_2401_);
lean_ctor_set(v___x_2397_, 0, v___x_2399_);
v___x_2403_ = v___x_2397_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_a_2401_);
v___x_2403_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
size_t v___x_2404_; size_t v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = ((size_t)1ULL);
v___x_2405_ = lean_usize_add(v_i_2384_, v___x_2404_);
v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_2382_, v_sz_2383_, v___x_2405_, v___x_2403_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3___boxed(lean_object* v_as_2502_, lean_object* v_sz_2503_, lean_object* v_i_2504_, lean_object* v_b_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
size_t v_sz_boxed_2513_; size_t v_i_boxed_2514_; lean_object* v_res_2515_; 
v_sz_boxed_2513_ = lean_unbox_usize(v_sz_2503_);
lean_dec(v_sz_2503_);
v_i_boxed_2514_ = lean_unbox_usize(v_i_2504_);
lean_dec(v_i_2504_);
v_res_2515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_as_2502_, v_sz_boxed_2513_, v_i_boxed_2514_, v_b_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec_ref(v_as_2502_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(lean_object* v_t_2516_, lean_object* v_init_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_root_2525_; lean_object* v_tail_2526_; lean_object* v___x_2527_; 
v_root_2525_ = lean_ctor_get(v_t_2516_, 0);
lean_inc_ref(v_root_2525_);
v_tail_2526_ = lean_ctor_get(v_t_2516_, 1);
lean_inc_ref(v_tail_2526_);
lean_dec_ref(v_t_2516_);
lean_inc(v___y_2523_);
lean_inc_ref(v___y_2522_);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc_ref(v_init_2517_);
v___x_2527_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_2517_, v_root_2525_, v_init_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec_ref(v_init_2517_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2564_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2530_ = v___x_2527_;
v_isShared_2531_ = v_isSharedCheck_2564_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2527_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2564_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
if (lean_obj_tag(v_a_2528_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; 
lean_dec_ref(v_tail_2526_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
v_a_2532_ = lean_ctor_get(v_a_2528_, 0);
lean_inc(v_a_2532_);
lean_dec_ref(v_a_2528_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v_a_2532_);
v___x_2534_ = v___x_2530_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; size_t v_sz_2539_; size_t v___x_2540_; lean_object* v___x_2541_; 
lean_del_object(v___x_2530_);
v_a_2536_ = lean_ctor_get(v_a_2528_, 0);
lean_inc(v_a_2536_);
lean_dec_ref(v_a_2528_);
v___x_2537_ = lean_box(0);
v___x_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
lean_ctor_set(v___x_2538_, 1, v_a_2536_);
v_sz_2539_ = lean_array_size(v_tail_2526_);
v___x_2540_ = ((size_t)0ULL);
v___x_2541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_tail_2526_, v_sz_2539_, v___x_2540_, v___x_2538_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec_ref(v_tail_2526_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2555_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2555_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2555_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v_fst_2546_; 
v_fst_2546_ = lean_ctor_get(v_a_2542_, 0);
if (lean_obj_tag(v_fst_2546_) == 0)
{
lean_object* v_snd_2547_; lean_object* v___x_2549_; 
v_snd_2547_ = lean_ctor_get(v_a_2542_, 1);
lean_inc(v_snd_2547_);
lean_dec(v_a_2542_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v_snd_2547_);
v___x_2549_ = v___x_2544_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_snd_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
else
{
lean_object* v_val_2551_; lean_object* v___x_2553_; 
lean_inc_ref(v_fst_2546_);
lean_dec(v_a_2542_);
v_val_2551_ = lean_ctor_get(v_fst_2546_, 0);
lean_inc(v_val_2551_);
lean_dec_ref(v_fst_2546_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v_val_2551_);
v___x_2553_ = v___x_2544_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_val_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
v_a_2556_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2541_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2541_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref(v_tail_2526_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
v_a_2565_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2527_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2527_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1___boxed(lean_object* v_t_2573_, lean_object* v_init_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_t_2573_, v_init_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
return v_res_2582_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = lean_unsigned_to_nat(32u);
v___x_2584_ = lean_mk_empty_array_with_capacity(v___x_2583_);
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
return v___x_2585_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1(void){
_start:
{
size_t v___x_2586_; lean_object* v_index_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v_decls_2591_; 
v___x_2586_ = ((size_t)5ULL);
v_index_2587_ = lean_unsigned_to_nat(0u);
v___x_2588_ = lean_unsigned_to_nat(32u);
v___x_2589_ = lean_mk_empty_array_with_capacity(v___x_2588_);
v___x_2590_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0);
v_decls_2591_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_decls_2591_, 0, v___x_2590_);
lean_ctor_set(v_decls_2591_, 1, v___x_2589_);
lean_ctor_set(v_decls_2591_, 2, v_index_2587_);
lean_ctor_set(v_decls_2591_, 3, v_index_2587_);
lean_ctor_set_usize(v_decls_2591_, 4, v___x_2586_);
return v_decls_2591_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2(void){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2592_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3(void){
_start:
{
lean_object* v___x_2593_; lean_object* v_fvarIdToDecl_2594_; 
v___x_2593_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2);
v_fvarIdToDecl_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fvarIdToDecl_2594_, 0, v___x_2593_);
return v_fvarIdToDecl_2594_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4(void){
_start:
{
lean_object* v_index_2595_; lean_object* v_decls_2596_; lean_object* v___x_2597_; 
v_index_2595_ = lean_unsigned_to_nat(0u);
v_decls_2596_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1);
v___x_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2597_, 0, v_decls_2596_);
lean_ctor_set(v___x_2597_, 1, v_index_2595_);
return v___x_2597_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5(void){
_start:
{
lean_object* v___x_2598_; lean_object* v_fvarIdToDecl_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4);
v_fvarIdToDecl_2599_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3);
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v_fvarIdToDecl_2599_);
lean_ctor_set(v___x_2600_, 1, v___x_2598_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(lean_object* v_lctx_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v_decls_2609_; lean_object* v_auxDeclToFullName_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2638_; 
v_decls_2609_ = lean_ctor_get(v_lctx_2601_, 1);
v_auxDeclToFullName_2610_ = lean_ctor_get(v_lctx_2601_, 2);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_lctx_2601_);
if (v_isSharedCheck_2638_ == 0)
{
lean_object* v_unused_2639_; 
v_unused_2639_ = lean_ctor_get(v_lctx_2601_, 0);
lean_dec(v_unused_2639_);
v___x_2612_ = v_lctx_2601_;
v_isShared_2613_ = v_isSharedCheck_2638_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_auxDeclToFullName_2610_);
lean_inc(v_decls_2609_);
lean_dec(v_lctx_2601_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2638_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5);
v___x_2615_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_decls_2609_, v___x_2614_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2629_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2618_ = v___x_2615_;
v_isShared_2619_ = v_isSharedCheck_2629_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2615_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2629_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v_snd_2620_; lean_object* v_fst_2621_; lean_object* v_fst_2622_; lean_object* v___x_2624_; 
v_snd_2620_ = lean_ctor_get(v_a_2616_, 1);
lean_inc(v_snd_2620_);
v_fst_2621_ = lean_ctor_get(v_a_2616_, 0);
lean_inc(v_fst_2621_);
lean_dec(v_a_2616_);
v_fst_2622_ = lean_ctor_get(v_snd_2620_, 0);
lean_inc(v_fst_2622_);
lean_dec(v_snd_2620_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 1, v_fst_2622_);
lean_ctor_set(v___x_2612_, 0, v_fst_2621_);
v___x_2624_ = v___x_2612_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_fst_2621_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_fst_2622_);
lean_ctor_set(v_reuseFailAlloc_2628_, 2, v_auxDeclToFullName_2610_);
v___x_2624_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2626_; 
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v___x_2624_);
v___x_2626_ = v___x_2618_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_del_object(v___x_2612_);
lean_dec(v_auxDeclToFullName_2610_);
v_a_2630_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2615_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2615_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___boxed(lean_object* v_lctx_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0(lean_object* v_00_u03b2_2649_, lean_object* v_x_2650_, lean_object* v_x_2651_, lean_object* v_x_2652_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_x_2650_, v_x_2651_, v_x_2652_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(lean_object* v_00_u03b2_2654_, lean_object* v_x_2655_, size_t v_x_2656_, size_t v_x_2657_, lean_object* v_x_2658_, lean_object* v_x_2659_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_2655_, v_x_2656_, v_x_2657_, v_x_2658_, v_x_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_, lean_object* v_x_2664_, lean_object* v_x_2665_, lean_object* v_x_2666_){
_start:
{
size_t v_x_11445__boxed_2667_; size_t v_x_11446__boxed_2668_; lean_object* v_res_2669_; 
v_x_11445__boxed_2667_ = lean_unbox_usize(v_x_2663_);
lean_dec(v_x_2663_);
v_x_11446__boxed_2668_ = lean_unbox_usize(v_x_2664_);
lean_dec(v_x_2664_);
v_res_2669_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(v_00_u03b2_2661_, v_x_2662_, v_x_11445__boxed_2667_, v_x_11446__boxed_2668_, v_x_2665_, v_x_2666_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2670_, lean_object* v_n_2671_, lean_object* v_k_2672_, lean_object* v_v_2673_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v_n_2671_, v_k_2672_, v_v_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2675_, size_t v_depth_2676_, lean_object* v_keys_2677_, lean_object* v_vals_2678_, lean_object* v_heq_2679_, lean_object* v_i_2680_, lean_object* v_entries_2681_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_2676_, v_keys_2677_, v_vals_2678_, v_i_2680_, v_entries_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2683_, lean_object* v_depth_2684_, lean_object* v_keys_2685_, lean_object* v_vals_2686_, lean_object* v_heq_2687_, lean_object* v_i_2688_, lean_object* v_entries_2689_){
_start:
{
size_t v_depth_boxed_2690_; lean_object* v_res_2691_; 
v_depth_boxed_2690_ = lean_unbox_usize(v_depth_2684_);
lean_dec(v_depth_2684_);
v_res_2691_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(v_00_u03b2_2683_, v_depth_boxed_2690_, v_keys_2685_, v_vals_2686_, v_heq_2687_, v_i_2688_, v_entries_2689_);
lean_dec_ref(v_vals_2686_);
lean_dec_ref(v_keys_2685_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2692_, lean_object* v_x_2693_, lean_object* v_x_2694_, lean_object* v_x_2695_, lean_object* v_x_2696_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2693_, v_x_2694_, v_x_2695_, v_x_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2698_, lean_object* v_x_2699_, lean_object* v_x_2700_, lean_object* v_x_2701_){
_start:
{
lean_object* v_ks_2702_; lean_object* v_vs_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2727_; 
v_ks_2702_ = lean_ctor_get(v_x_2698_, 0);
v_vs_2703_ = lean_ctor_get(v_x_2698_, 1);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_x_2698_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2705_ = v_x_2698_;
v_isShared_2706_ = v_isSharedCheck_2727_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_vs_2703_);
lean_inc(v_ks_2702_);
lean_dec(v_x_2698_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2727_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2707_ = lean_array_get_size(v_ks_2702_);
v___x_2708_ = lean_nat_dec_lt(v_x_2699_, v___x_2707_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
lean_dec(v_x_2699_);
v___x_2709_ = lean_array_push(v_ks_2702_, v_x_2700_);
v___x_2710_ = lean_array_push(v_vs_2703_, v_x_2701_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 1, v___x_2710_);
lean_ctor_set(v___x_2705_, 0, v___x_2709_);
v___x_2712_ = v___x_2705_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2709_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
else
{
lean_object* v_k_x27_2714_; uint8_t v___x_2715_; 
v_k_x27_2714_ = lean_array_fget_borrowed(v_ks_2702_, v_x_2699_);
v___x_2715_ = l_Lean_instBEqMVarId_beq(v_x_2700_, v_k_x27_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2717_; 
if (v_isShared_2706_ == 0)
{
v___x_2717_ = v___x_2705_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_ks_2702_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_vs_2703_);
v___x_2717_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = lean_unsigned_to_nat(1u);
v___x_2719_ = lean_nat_add(v_x_2699_, v___x_2718_);
lean_dec(v_x_2699_);
v_x_2698_ = v___x_2717_;
v_x_2699_ = v___x_2719_;
goto _start;
}
}
else
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2722_ = lean_array_fset(v_ks_2702_, v_x_2699_, v_x_2700_);
v___x_2723_ = lean_array_fset(v_vs_2703_, v_x_2699_, v_x_2701_);
lean_dec(v_x_2699_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 1, v___x_2723_);
lean_ctor_set(v___x_2705_, 0, v___x_2722_);
v___x_2725_ = v___x_2705_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_2728_, lean_object* v_k_2729_, lean_object* v_v_2730_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_2728_, v___x_2731_, v_k_2729_, v_v_2730_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2733_, size_t v_x_2734_, size_t v_x_2735_, lean_object* v_x_2736_, lean_object* v_x_2737_){
_start:
{
if (lean_obj_tag(v_x_2733_) == 0)
{
lean_object* v_es_2738_; size_t v___x_2739_; size_t v___x_2740_; size_t v___x_2741_; size_t v___x_2742_; lean_object* v_j_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
v_es_2738_ = lean_ctor_get(v_x_2733_, 0);
v___x_2739_ = ((size_t)5ULL);
v___x_2740_ = ((size_t)1ULL);
v___x_2741_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
v___x_2742_ = lean_usize_land(v_x_2734_, v___x_2741_);
v_j_2743_ = lean_usize_to_nat(v___x_2742_);
v___x_2744_ = lean_array_get_size(v_es_2738_);
v___x_2745_ = lean_nat_dec_lt(v_j_2743_, v___x_2744_);
if (v___x_2745_ == 0)
{
lean_dec(v_j_2743_);
lean_dec(v_x_2737_);
lean_dec(v_x_2736_);
return v_x_2733_;
}
else
{
lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2782_; 
lean_inc_ref(v_es_2738_);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_x_2733_);
if (v_isSharedCheck_2782_ == 0)
{
lean_object* v_unused_2783_; 
v_unused_2783_ = lean_ctor_get(v_x_2733_, 0);
lean_dec(v_unused_2783_);
v___x_2747_ = v_x_2733_;
v_isShared_2748_ = v_isSharedCheck_2782_;
goto v_resetjp_2746_;
}
else
{
lean_dec(v_x_2733_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2782_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v_v_2749_; lean_object* v___x_2750_; lean_object* v_xs_x27_2751_; lean_object* v___y_2753_; 
v_v_2749_ = lean_array_fget(v_es_2738_, v_j_2743_);
v___x_2750_ = lean_box(0);
v_xs_x27_2751_ = lean_array_fset(v_es_2738_, v_j_2743_, v___x_2750_);
switch(lean_obj_tag(v_v_2749_))
{
case 0:
{
lean_object* v_key_2758_; lean_object* v_val_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2769_; 
v_key_2758_ = lean_ctor_get(v_v_2749_, 0);
v_val_2759_ = lean_ctor_get(v_v_2749_, 1);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_v_2749_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2761_ = v_v_2749_;
v_isShared_2762_ = v_isSharedCheck_2769_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_val_2759_);
lean_inc(v_key_2758_);
lean_dec(v_v_2749_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2769_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
uint8_t v___x_2763_; 
v___x_2763_ = l_Lean_instBEqMVarId_beq(v_x_2736_, v_key_2758_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
lean_del_object(v___x_2761_);
v___x_2764_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2758_, v_val_2759_, v_x_2736_, v_x_2737_);
v___x_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2764_);
v___y_2753_ = v___x_2765_;
goto v___jp_2752_;
}
else
{
lean_object* v___x_2767_; 
lean_dec(v_val_2759_);
lean_dec(v_key_2758_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 1, v_x_2737_);
lean_ctor_set(v___x_2761_, 0, v_x_2736_);
v___x_2767_ = v___x_2761_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_x_2736_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_x_2737_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
v___y_2753_ = v___x_2767_;
goto v___jp_2752_;
}
}
}
}
case 1:
{
lean_object* v_node_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2780_; 
v_node_2770_ = lean_ctor_get(v_v_2749_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_v_2749_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2772_ = v_v_2749_;
v_isShared_2773_ = v_isSharedCheck_2780_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_node_2770_);
lean_dec(v_v_2749_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2780_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
size_t v___x_2774_; size_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2774_ = lean_usize_shift_right(v_x_2734_, v___x_2739_);
v___x_2775_ = lean_usize_add(v_x_2735_, v___x_2740_);
v___x_2776_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_node_2770_, v___x_2774_, v___x_2775_, v_x_2736_, v_x_2737_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v___x_2776_);
v___x_2778_ = v___x_2772_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
v___y_2753_ = v___x_2778_;
goto v___jp_2752_;
}
}
}
default: 
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2781_, 0, v_x_2736_);
lean_ctor_set(v___x_2781_, 1, v_x_2737_);
v___y_2753_ = v___x_2781_;
goto v___jp_2752_;
}
}
v___jp_2752_:
{
lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2754_ = lean_array_fset(v_xs_x27_2751_, v_j_2743_, v___y_2753_);
lean_dec(v_j_2743_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v___x_2754_);
v___x_2756_ = v___x_2747_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2754_);
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
lean_object* v_ks_2784_; lean_object* v_vs_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2805_; 
v_ks_2784_ = lean_ctor_get(v_x_2733_, 0);
v_vs_2785_ = lean_ctor_get(v_x_2733_, 1);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_x_2733_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2787_ = v_x_2733_;
v_isShared_2788_ = v_isSharedCheck_2805_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_vs_2785_);
lean_inc(v_ks_2784_);
lean_dec(v_x_2733_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2805_;
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
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_ks_2784_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_vs_2785_);
v___x_2790_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v_newNode_2791_; uint8_t v___y_2793_; size_t v___x_2799_; uint8_t v___x_2800_; 
v_newNode_2791_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v___x_2790_, v_x_2736_, v_x_2737_);
v___x_2799_ = ((size_t)7ULL);
v___x_2800_ = lean_usize_dec_le(v___x_2799_, v_x_2735_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v___x_2801_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2791_);
v___x_2802_ = lean_unsigned_to_nat(4u);
v___x_2803_ = lean_nat_dec_lt(v___x_2801_, v___x_2802_);
lean_dec(v___x_2801_);
v___y_2793_ = v___x_2803_;
goto v___jp_2792_;
}
else
{
v___y_2793_ = v___x_2800_;
goto v___jp_2792_;
}
v___jp_2792_:
{
if (v___y_2793_ == 0)
{
lean_object* v_ks_2794_; lean_object* v_vs_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_ks_2794_ = lean_ctor_get(v_newNode_2791_, 0);
lean_inc_ref(v_ks_2794_);
v_vs_2795_ = lean_ctor_get(v_newNode_2791_, 1);
lean_inc_ref(v_vs_2795_);
lean_dec_ref(v_newNode_2791_);
v___x_2796_ = lean_unsigned_to_nat(0u);
v___x_2797_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2);
v___x_2798_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2735_, v_ks_2794_, v_vs_2795_, v___x_2796_, v___x_2797_);
lean_dec_ref(v_vs_2795_);
lean_dec_ref(v_ks_2794_);
return v___x_2798_;
}
else
{
return v_newNode_2791_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_2806_, lean_object* v_keys_2807_, lean_object* v_vals_2808_, lean_object* v_i_2809_, lean_object* v_entries_2810_){
_start:
{
lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2811_ = lean_array_get_size(v_keys_2807_);
v___x_2812_ = lean_nat_dec_lt(v_i_2809_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_dec(v_i_2809_);
return v_entries_2810_;
}
else
{
lean_object* v_k_2813_; lean_object* v_v_2814_; uint64_t v___x_2815_; size_t v_h_2816_; size_t v___x_2817_; lean_object* v___x_2818_; size_t v___x_2819_; size_t v___x_2820_; size_t v___x_2821_; size_t v_h_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v_k_2813_ = lean_array_fget_borrowed(v_keys_2807_, v_i_2809_);
v_v_2814_ = lean_array_fget_borrowed(v_vals_2808_, v_i_2809_);
v___x_2815_ = l_Lean_instHashableMVarId_hash(v_k_2813_);
v_h_2816_ = lean_uint64_to_usize(v___x_2815_);
v___x_2817_ = ((size_t)5ULL);
v___x_2818_ = lean_unsigned_to_nat(1u);
v___x_2819_ = ((size_t)1ULL);
v___x_2820_ = lean_usize_sub(v_depth_2806_, v___x_2819_);
v___x_2821_ = lean_usize_mul(v___x_2817_, v___x_2820_);
v_h_2822_ = lean_usize_shift_right(v_h_2816_, v___x_2821_);
v___x_2823_ = lean_nat_add(v_i_2809_, v___x_2818_);
lean_dec(v_i_2809_);
lean_inc(v_v_2814_);
lean_inc(v_k_2813_);
v___x_2824_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_entries_2810_, v_h_2822_, v_depth_2806_, v_k_2813_, v_v_2814_);
v_i_2809_ = v___x_2823_;
v_entries_2810_ = v___x_2824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2826_, lean_object* v_keys_2827_, lean_object* v_vals_2828_, lean_object* v_i_2829_, lean_object* v_entries_2830_){
_start:
{
size_t v_depth_boxed_2831_; lean_object* v_res_2832_; 
v_depth_boxed_2831_ = lean_unbox_usize(v_depth_2826_);
lean_dec(v_depth_2826_);
v_res_2832_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_2831_, v_keys_2827_, v_vals_2828_, v_i_2829_, v_entries_2830_);
lean_dec_ref(v_vals_2828_);
lean_dec_ref(v_keys_2827_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2833_, lean_object* v_x_2834_, lean_object* v_x_2835_, lean_object* v_x_2836_, lean_object* v_x_2837_){
_start:
{
size_t v_x_2239__boxed_2838_; size_t v_x_2240__boxed_2839_; lean_object* v_res_2840_; 
v_x_2239__boxed_2838_ = lean_unbox_usize(v_x_2834_);
lean_dec(v_x_2834_);
v_x_2240__boxed_2839_ = lean_unbox_usize(v_x_2835_);
lean_dec(v_x_2835_);
v_res_2840_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_2833_, v_x_2239__boxed_2838_, v_x_2240__boxed_2839_, v_x_2836_, v_x_2837_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(lean_object* v_x_2841_, lean_object* v_x_2842_, lean_object* v_x_2843_){
_start:
{
uint64_t v___x_2844_; size_t v___x_2845_; size_t v___x_2846_; lean_object* v___x_2847_; 
v___x_2844_ = l_Lean_instHashableMVarId_hash(v_x_2842_);
v___x_2845_ = lean_uint64_to_usize(v___x_2844_);
v___x_2846_ = ((size_t)1ULL);
v___x_2847_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_2841_, v___x_2845_, v___x_2846_, v_x_2842_, v_x_2843_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(lean_object* v_mvarId_2848_, lean_object* v_val_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v___x_2852_; lean_object* v_mctx_2853_; lean_object* v_cache_2854_; lean_object* v_zetaDeltaFVarIds_2855_; lean_object* v_postponed_2856_; lean_object* v_diag_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2884_; 
v___x_2852_ = lean_st_ref_take(v___y_2850_);
v_mctx_2853_ = lean_ctor_get(v___x_2852_, 0);
v_cache_2854_ = lean_ctor_get(v___x_2852_, 1);
v_zetaDeltaFVarIds_2855_ = lean_ctor_get(v___x_2852_, 2);
v_postponed_2856_ = lean_ctor_get(v___x_2852_, 3);
v_diag_2857_ = lean_ctor_get(v___x_2852_, 4);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2859_ = v___x_2852_;
v_isShared_2860_ = v_isSharedCheck_2884_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_diag_2857_);
lean_inc(v_postponed_2856_);
lean_inc(v_zetaDeltaFVarIds_2855_);
lean_inc(v_cache_2854_);
lean_inc(v_mctx_2853_);
lean_dec(v___x_2852_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2884_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v_depth_2861_; lean_object* v_levelAssignDepth_2862_; lean_object* v_mvarCounter_2863_; lean_object* v_lDepth_2864_; lean_object* v_decls_2865_; lean_object* v_userNames_2866_; lean_object* v_lAssignment_2867_; lean_object* v_eAssignment_2868_; lean_object* v_dAssignment_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2883_; 
v_depth_2861_ = lean_ctor_get(v_mctx_2853_, 0);
v_levelAssignDepth_2862_ = lean_ctor_get(v_mctx_2853_, 1);
v_mvarCounter_2863_ = lean_ctor_get(v_mctx_2853_, 2);
v_lDepth_2864_ = lean_ctor_get(v_mctx_2853_, 3);
v_decls_2865_ = lean_ctor_get(v_mctx_2853_, 4);
v_userNames_2866_ = lean_ctor_get(v_mctx_2853_, 5);
v_lAssignment_2867_ = lean_ctor_get(v_mctx_2853_, 6);
v_eAssignment_2868_ = lean_ctor_get(v_mctx_2853_, 7);
v_dAssignment_2869_ = lean_ctor_get(v_mctx_2853_, 8);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_mctx_2853_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2871_ = v_mctx_2853_;
v_isShared_2872_ = v_isSharedCheck_2883_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_dAssignment_2869_);
lean_inc(v_eAssignment_2868_);
lean_inc(v_lAssignment_2867_);
lean_inc(v_userNames_2866_);
lean_inc(v_decls_2865_);
lean_inc(v_lDepth_2864_);
lean_inc(v_mvarCounter_2863_);
lean_inc(v_levelAssignDepth_2862_);
lean_inc(v_depth_2861_);
lean_dec(v_mctx_2853_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2883_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2873_; lean_object* v___x_2875_; 
v___x_2873_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_eAssignment_2868_, v_mvarId_2848_, v_val_2849_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 7, v___x_2873_);
v___x_2875_ = v___x_2871_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_depth_2861_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_levelAssignDepth_2862_);
lean_ctor_set(v_reuseFailAlloc_2882_, 2, v_mvarCounter_2863_);
lean_ctor_set(v_reuseFailAlloc_2882_, 3, v_lDepth_2864_);
lean_ctor_set(v_reuseFailAlloc_2882_, 4, v_decls_2865_);
lean_ctor_set(v_reuseFailAlloc_2882_, 5, v_userNames_2866_);
lean_ctor_set(v_reuseFailAlloc_2882_, 6, v_lAssignment_2867_);
lean_ctor_set(v_reuseFailAlloc_2882_, 7, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2882_, 8, v_dAssignment_2869_);
v___x_2875_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2877_; 
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2875_);
v___x_2877_ = v___x_2859_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2875_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_cache_2854_);
lean_ctor_set(v_reuseFailAlloc_2881_, 2, v_zetaDeltaFVarIds_2855_);
lean_ctor_set(v_reuseFailAlloc_2881_, 3, v_postponed_2856_);
lean_ctor_set(v_reuseFailAlloc_2881_, 4, v_diag_2857_);
v___x_2877_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = lean_st_ref_set(v___y_2850_, v___x_2877_);
v___x_2879_ = lean_box(0);
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
return v___x_2880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg___boxed(lean_object* v_mvarId_2885_, lean_object* v_val_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_2885_, v_val_2886_, v___y_2887_);
lean_dec(v___y_2887_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object* v_mvarId_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v___x_2898_; 
lean_inc(v_mvarId_2890_);
v___x_2898_ = l_Lean_MVarId_getDecl(v_mvarId_2890_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v_userName_2900_; lean_object* v_lctx_2901_; lean_object* v_type_2902_; lean_object* v_localInstances_2903_; lean_object* v___x_2904_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref(v___x_2898_);
v_userName_2900_ = lean_ctor_get(v_a_2899_, 0);
lean_inc(v_userName_2900_);
v_lctx_2901_ = lean_ctor_get(v_a_2899_, 1);
lean_inc_ref(v_lctx_2901_);
v_type_2902_ = lean_ctor_get(v_a_2899_, 2);
lean_inc_ref(v_type_2902_);
v_localInstances_2903_ = lean_ctor_get(v_a_2899_, 4);
lean_inc_ref(v_localInstances_2903_);
lean_dec(v_a_2899_);
lean_inc(v_a_2896_);
lean_inc_ref(v_a_2895_);
lean_inc(v_a_2894_);
lean_inc_ref(v_a_2893_);
v___x_2904_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_2901_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2906_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
lean_dec_ref(v___x_2904_);
lean_inc(v_a_2896_);
lean_inc_ref(v_a_2895_);
lean_inc(v_a_2894_);
lean_inc_ref(v_a_2893_);
v___x_2906_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2902_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; uint8_t v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
lean_dec_ref(v___x_2906_);
v___x_2908_ = 2;
v___x_2909_ = lean_unsigned_to_nat(0u);
v___x_2910_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_2905_, v_localInstances_2903_, v_a_2907_, v___x_2908_, v_userName_2900_, v___x_2909_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec_ref(v_a_2893_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2920_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref(v___x_2910_);
lean_inc(v_a_2911_);
v___x_2912_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_2890_, v_a_2911_, v_a_2894_);
lean_dec(v_a_2894_);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; 
v_unused_2921_ = lean_ctor_get(v___x_2912_, 0);
lean_dec(v_unused_2921_);
v___x_2914_ = v___x_2912_;
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
else
{
lean_dec(v___x_2912_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2916_ = l_Lean_Expr_mvarId_x21(v_a_2911_);
lean_dec(v_a_2911_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2916_);
v___x_2918_ = v___x_2914_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v_a_2894_);
lean_dec(v_mvarId_2890_);
v_a_2922_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2910_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2910_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v_a_2905_);
lean_dec_ref(v_localInstances_2903_);
lean_dec(v_userName_2900_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_mvarId_2890_);
v_a_2930_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2906_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2906_);
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
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec_ref(v_localInstances_2903_);
lean_dec_ref(v_type_2902_);
lean_dec(v_userName_2900_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_mvarId_2890_);
v_a_2938_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2904_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2904_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_mvarId_2890_);
v_a_2946_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2898_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2898_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar___boxed(lean_object* v_mvarId_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(lean_object* v_mvarId_2963_, lean_object* v_val_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_2963_, v_val_2964_, v___y_2968_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___boxed(lean_object* v_mvarId_2973_, lean_object* v_val_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(v_mvarId_2973_, v_val_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0(lean_object* v_00_u03b2_2983_, lean_object* v_x_2984_, lean_object* v_x_2985_, lean_object* v_x_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_x_2984_, v_x_2985_, v_x_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2988_, lean_object* v_x_2989_, size_t v_x_2990_, size_t v_x_2991_, lean_object* v_x_2992_, lean_object* v_x_2993_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_2989_, v_x_2990_, v_x_2991_, v_x_2992_, v_x_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2995_, lean_object* v_x_2996_, lean_object* v_x_2997_, lean_object* v_x_2998_, lean_object* v_x_2999_, lean_object* v_x_3000_){
_start:
{
size_t v_x_2611__boxed_3001_; size_t v_x_2612__boxed_3002_; lean_object* v_res_3003_; 
v_x_2611__boxed_3001_ = lean_unbox_usize(v_x_2997_);
lean_dec(v_x_2997_);
v_x_2612__boxed_3002_ = lean_unbox_usize(v_x_2998_);
lean_dec(v_x_2998_);
v_res_3003_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(v_00_u03b2_2995_, v_x_2996_, v_x_2611__boxed_3001_, v_x_2612__boxed_3002_, v_x_2999_, v_x_3000_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3004_, lean_object* v_n_3005_, lean_object* v_k_3006_, lean_object* v_v_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v_n_3005_, v_k_3006_, v_v_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3009_, size_t v_depth_3010_, lean_object* v_keys_3011_, lean_object* v_vals_3012_, lean_object* v_heq_3013_, lean_object* v_i_3014_, lean_object* v_entries_3015_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_3010_, v_keys_3011_, v_vals_3012_, v_i_3014_, v_entries_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3017_, lean_object* v_depth_3018_, lean_object* v_keys_3019_, lean_object* v_vals_3020_, lean_object* v_heq_3021_, lean_object* v_i_3022_, lean_object* v_entries_3023_){
_start:
{
size_t v_depth_boxed_3024_; lean_object* v_res_3025_; 
v_depth_boxed_3024_ = lean_unbox_usize(v_depth_3018_);
lean_dec(v_depth_3018_);
v_res_3025_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3017_, v_depth_boxed_3024_, v_keys_3019_, v_vals_3020_, v_heq_3021_, v_i_3022_, v_entries_3023_);
lean_dec_ref(v_vals_3020_);
lean_dec_ref(v_keys_3019_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3026_, lean_object* v_x_3027_, lean_object* v_x_3028_, lean_object* v_x_3029_, lean_object* v_x_3030_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_3027_, v_x_3028_, v_x_3029_, v_x_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(lean_object* v_msgData_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v___x_3038_; lean_object* v_env_3039_; lean_object* v___x_3040_; lean_object* v_mctx_3041_; lean_object* v_lctx_3042_; lean_object* v_options_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3038_ = lean_st_ref_get(v___y_3036_);
v_env_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc_ref(v_env_3039_);
lean_dec(v___x_3038_);
v___x_3040_ = lean_st_ref_get(v___y_3034_);
v_mctx_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc_ref(v_mctx_3041_);
lean_dec(v___x_3040_);
v_lctx_3042_ = lean_ctor_get(v___y_3033_, 2);
v_options_3043_ = lean_ctor_get(v___y_3035_, 2);
lean_inc_ref(v_options_3043_);
lean_inc_ref(v_lctx_3042_);
v___x_3044_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3044_, 0, v_env_3039_);
lean_ctor_set(v___x_3044_, 1, v_mctx_3041_);
lean_ctor_set(v___x_3044_, 2, v_lctx_3042_);
lean_ctor_set(v___x_3044_, 3, v_options_3043_);
v___x_3045_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set(v___x_3045_, 1, v_msgData_3032_);
v___x_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0___boxed(lean_object* v_msgData_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msgData_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(lean_object* v_msg_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_ref_3060_; lean_object* v___x_3061_; lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3070_; 
v_ref_3060_ = lean_ctor_get(v___y_3057_, 5);
v___x_3061_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msg_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3064_ = v___x_3061_;
v_isShared_3065_ = v_isSharedCheck_3070_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3061_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3070_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3066_; lean_object* v___x_3068_; 
lean_inc(v_ref_3060_);
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v_ref_3060_);
lean_ctor_set(v___x_3066_, 1, v_a_3062_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set_tag(v___x_3064_, 1);
lean_ctor_set(v___x_3064_, 0, v___x_3066_);
v___x_3068_ = v___x_3064_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg___boxed(lean_object* v_msg_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
return v_res_3077_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0));
v___x_3080_ = l_Lean_stringToMessageData(v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(lean_object* v_msg_3084_, lean_object* v_e_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v___y_3094_; lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3101_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2));
v___x_3102_ = lean_string_dec_eq(v_msg_3084_, v___x_3101_);
if (v___x_3102_ == 0)
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3103_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3));
v___x_3104_ = lean_string_append(v___x_3103_, v_msg_3084_);
lean_dec_ref(v_msg_3084_);
v___x_3105_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__4));
v___x_3106_ = lean_string_append(v___x_3104_, v___x_3105_);
v___y_3094_ = v___x_3106_;
goto v___jp_3093_;
}
else
{
v___y_3094_ = v_msg_3084_;
goto v___jp_3093_;
}
v___jp_3093_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3095_ = l_Lean_stringToMessageData(v___y_3094_);
v___x_3096_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1);
v___x_3097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3095_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
v___x_3098_ = l_Lean_indentExpr(v_e_3085_);
v___x_3099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3097_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v___x_3099_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
return v___x_3100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___boxed(lean_object* v_msg_3107_, lean_object* v_e_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3107_, v_e_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
lean_dec(v_a_3114_);
lean_dec_ref(v_a_3113_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(lean_object* v_00_u03b1_3117_, lean_object* v_msg_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_3118_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___boxed(lean_object* v_00_u03b1_3127_, lean_object* v_msg_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(v_00_u03b1_3127_, v_msg_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3137_, lean_object* v_vals_3138_, lean_object* v_i_3139_, lean_object* v_k_3140_){
_start:
{
lean_object* v___x_3141_; uint8_t v___x_3142_; 
v___x_3141_ = lean_array_get_size(v_keys_3137_);
v___x_3142_ = lean_nat_dec_lt(v_i_3139_, v___x_3141_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; 
lean_dec_ref(v_k_3140_);
lean_dec(v_i_3139_);
v___x_3143_ = lean_box(0);
return v___x_3143_;
}
else
{
lean_object* v_k_x27_3144_; uint8_t v___x_3145_; 
v_k_x27_3144_ = lean_array_fget_borrowed(v_keys_3137_, v_i_3139_);
lean_inc(v_k_x27_3144_);
lean_inc_ref(v_k_3140_);
v___x_3145_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_k_3140_, v_k_x27_3144_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = lean_unsigned_to_nat(1u);
v___x_3147_ = lean_nat_add(v_i_3139_, v___x_3146_);
lean_dec(v_i_3139_);
v_i_3139_ = v___x_3147_;
goto _start;
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
lean_dec_ref(v_k_3140_);
v___x_3149_ = lean_array_fget_borrowed(v_vals_3138_, v_i_3139_);
lean_dec(v_i_3139_);
lean_inc(v___x_3149_);
lean_inc(v_k_x27_3144_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_k_x27_3144_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
return v___x_3151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3152_, lean_object* v_vals_3153_, lean_object* v_i_3154_, lean_object* v_k_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_3152_, v_vals_3153_, v_i_3154_, v_k_3155_);
lean_dec_ref(v_vals_3153_);
lean_dec_ref(v_keys_3152_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(lean_object* v_x_3157_, size_t v_x_3158_, lean_object* v_x_3159_){
_start:
{
if (lean_obj_tag(v_x_3157_) == 0)
{
lean_object* v_es_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3188_; 
v_es_3160_ = lean_ctor_get(v_x_3157_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v_x_3157_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3162_ = v_x_3157_;
v_isShared_3163_ = v_isSharedCheck_3188_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_es_3160_);
lean_dec(v_x_3157_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3188_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; size_t v___x_3165_; size_t v___x_3166_; size_t v___x_3167_; lean_object* v_j_3168_; lean_object* v___x_3169_; 
v___x_3164_ = lean_box(2);
v___x_3165_ = ((size_t)5ULL);
v___x_3166_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
v___x_3167_ = lean_usize_land(v_x_3158_, v___x_3166_);
v_j_3168_ = lean_usize_to_nat(v___x_3167_);
v___x_3169_ = lean_array_get(v___x_3164_, v_es_3160_, v_j_3168_);
lean_dec(v_j_3168_);
lean_dec_ref(v_es_3160_);
switch(lean_obj_tag(v___x_3169_))
{
case 0:
{
lean_object* v_key_3170_; lean_object* v_val_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3183_; 
v_key_3170_ = lean_ctor_get(v___x_3169_, 0);
v_val_3171_ = lean_ctor_get(v___x_3169_, 1);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3173_ = v___x_3169_;
v_isShared_3174_ = v_isSharedCheck_3183_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_val_3171_);
lean_inc(v_key_3170_);
lean_dec(v___x_3169_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3183_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
uint8_t v___x_3175_; 
lean_inc(v_key_3170_);
v___x_3175_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_x_3159_, v_key_3170_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; 
lean_del_object(v___x_3173_);
lean_dec(v_val_3171_);
lean_dec(v_key_3170_);
lean_del_object(v___x_3162_);
v___x_3176_ = lean_box(0);
return v___x_3176_;
}
else
{
lean_object* v___x_3178_; 
if (v_isShared_3174_ == 0)
{
v___x_3178_ = v___x_3173_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_key_3170_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_val_3171_);
v___x_3178_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3180_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set_tag(v___x_3162_, 1);
lean_ctor_set(v___x_3162_, 0, v___x_3178_);
v___x_3180_ = v___x_3162_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
}
case 1:
{
lean_object* v_node_3184_; size_t v___x_3185_; 
lean_del_object(v___x_3162_);
v_node_3184_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_node_3184_);
lean_dec_ref(v___x_3169_);
v___x_3185_ = lean_usize_shift_right(v_x_3158_, v___x_3165_);
v_x_3157_ = v_node_3184_;
v_x_3158_ = v___x_3185_;
goto _start;
}
default: 
{
lean_object* v___x_3187_; 
lean_del_object(v___x_3162_);
lean_dec_ref(v_x_3159_);
v___x_3187_ = lean_box(0);
return v___x_3187_;
}
}
}
}
else
{
lean_object* v_ks_3189_; lean_object* v_vs_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v_ks_3189_ = lean_ctor_get(v_x_3157_, 0);
lean_inc_ref(v_ks_3189_);
v_vs_3190_ = lean_ctor_get(v_x_3157_, 1);
lean_inc_ref(v_vs_3190_);
lean_dec_ref(v_x_3157_);
v___x_3191_ = lean_unsigned_to_nat(0u);
v___x_3192_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_ks_3189_, v_vs_3190_, v___x_3191_, v_x_3159_);
lean_dec_ref(v_vs_3190_);
lean_dec_ref(v_ks_3189_);
return v___x_3192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_3193_, lean_object* v_x_3194_, lean_object* v_x_3195_){
_start:
{
size_t v_x_7570__boxed_3196_; lean_object* v_res_3197_; 
v_x_7570__boxed_3196_ = lean_unbox_usize(v_x_3194_);
lean_dec(v_x_3194_);
v_res_3197_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3193_, v_x_7570__boxed_3196_, v_x_3195_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(lean_object* v_x_3198_, lean_object* v_x_3199_){
_start:
{
uint64_t v___x_3200_; size_t v___x_3201_; lean_object* v___x_3202_; 
v___x_3200_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_x_3199_);
v___x_3201_ = lean_uint64_to_usize(v___x_3200_);
v___x_3202_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3198_, v___x_3201_, v_x_3199_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0(lean_object* v_msg_3203_, lean_object* v_e_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v___y_3217_; lean_object* v___x_3226_; lean_object* v_share_3227_; lean_object* v___x_3228_; 
v___x_3226_ = lean_st_ref_get(v___y_3206_);
v_share_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc_ref(v_share_3227_);
lean_dec(v___x_3226_);
lean_inc_ref(v_e_3204_);
v___x_3228_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_share_3227_, v_e_3204_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v___x_3229_; 
v___x_3229_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3203_, v_e_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
v___y_3217_ = v___x_3229_;
goto v___jp_3216_;
}
else
{
lean_object* v_val_3230_; lean_object* v_fst_3231_; uint8_t v___x_3232_; 
v_val_3230_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_val_3230_);
lean_dec_ref(v___x_3228_);
v_fst_3231_ = lean_ctor_get(v_val_3230_, 0);
lean_inc(v_fst_3231_);
lean_dec(v_val_3230_);
v___x_3232_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_3231_, v_e_3204_);
lean_dec(v_fst_3231_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; 
v___x_3233_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3203_, v_e_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
v___y_3217_ = v___x_3233_;
goto v___jp_3216_;
}
else
{
lean_dec_ref(v_e_3204_);
lean_dec_ref(v_msg_3203_);
goto v___jp_3212_;
}
}
v___jp_3212_:
{
uint8_t v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3213_ = 1;
v___x_3214_ = lean_box(v___x_3213_);
v___x_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
return v___x_3215_;
}
v___jp_3216_:
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
v_a_3218_ = lean_ctor_get(v___y_3217_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___y_3217_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___y_3217_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___y_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0___boxed(lean_object* v_msg_3234_, lean_object* v_e_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Lean_Expr_checkMaxShared___lam__0(v_msg_3234_, v_e_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
return v_res_3243_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(lean_object* v_a_3244_, lean_object* v_x_3245_){
_start:
{
if (lean_obj_tag(v_x_3245_) == 0)
{
uint8_t v___x_3246_; 
v___x_3246_ = 0;
return v___x_3246_;
}
else
{
lean_object* v_key_3247_; lean_object* v_tail_3248_; uint8_t v___x_3249_; 
v_key_3247_ = lean_ctor_get(v_x_3245_, 0);
v_tail_3248_ = lean_ctor_get(v_x_3245_, 2);
v___x_3249_ = lean_expr_eqv(v_key_3247_, v_a_3244_);
if (v___x_3249_ == 0)
{
v_x_3245_ = v_tail_3248_;
goto _start;
}
else
{
return v___x_3249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_a_3251_, lean_object* v_x_3252_){
_start:
{
uint8_t v_res_3253_; lean_object* v_r_3254_; 
v_res_3253_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3251_, v_x_3252_);
lean_dec(v_x_3252_);
lean_dec_ref(v_a_3251_);
v_r_3254_ = lean_box(v_res_3253_);
return v_r_3254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(lean_object* v_a_3255_, lean_object* v_b_3256_, lean_object* v_x_3257_){
_start:
{
if (lean_obj_tag(v_x_3257_) == 0)
{
lean_dec(v_b_3256_);
lean_dec_ref(v_a_3255_);
return v_x_3257_;
}
else
{
lean_object* v_key_3258_; lean_object* v_value_3259_; lean_object* v_tail_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3272_; 
v_key_3258_ = lean_ctor_get(v_x_3257_, 0);
v_value_3259_ = lean_ctor_get(v_x_3257_, 1);
v_tail_3260_ = lean_ctor_get(v_x_3257_, 2);
v_isSharedCheck_3272_ = !lean_is_exclusive(v_x_3257_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3262_ = v_x_3257_;
v_isShared_3263_ = v_isSharedCheck_3272_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_tail_3260_);
lean_inc(v_value_3259_);
lean_inc(v_key_3258_);
lean_dec(v_x_3257_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3272_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
uint8_t v___x_3264_; 
v___x_3264_ = lean_expr_eqv(v_key_3258_, v_a_3255_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3267_; 
v___x_3265_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3255_, v_b_3256_, v_tail_3260_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 2, v___x_3265_);
v___x_3267_ = v___x_3262_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_key_3258_);
lean_ctor_set(v_reuseFailAlloc_3268_, 1, v_value_3259_);
lean_ctor_set(v_reuseFailAlloc_3268_, 2, v___x_3265_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
else
{
lean_object* v___x_3270_; 
lean_dec(v_value_3259_);
lean_dec(v_key_3258_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 1, v_b_3256_);
lean_ctor_set(v___x_3262_, 0, v_a_3255_);
v___x_3270_ = v___x_3262_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3255_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_b_3256_);
lean_ctor_set(v_reuseFailAlloc_3271_, 2, v_tail_3260_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(lean_object* v_x_3273_, lean_object* v_x_3274_){
_start:
{
if (lean_obj_tag(v_x_3274_) == 0)
{
return v_x_3273_;
}
else
{
lean_object* v_key_3275_; lean_object* v_value_3276_; lean_object* v_tail_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3300_; 
v_key_3275_ = lean_ctor_get(v_x_3274_, 0);
v_value_3276_ = lean_ctor_get(v_x_3274_, 1);
v_tail_3277_ = lean_ctor_get(v_x_3274_, 2);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_x_3274_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3279_ = v_x_3274_;
v_isShared_3280_ = v_isSharedCheck_3300_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_tail_3277_);
lean_inc(v_value_3276_);
lean_inc(v_key_3275_);
lean_dec(v_x_3274_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3300_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3281_; uint64_t v___x_3282_; uint64_t v___x_3283_; uint64_t v___x_3284_; uint64_t v_fold_3285_; uint64_t v___x_3286_; uint64_t v___x_3287_; uint64_t v___x_3288_; size_t v___x_3289_; size_t v___x_3290_; size_t v___x_3291_; size_t v___x_3292_; size_t v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3281_ = lean_array_get_size(v_x_3273_);
v___x_3282_ = l_Lean_Expr_hash(v_key_3275_);
v___x_3283_ = 32ULL;
v___x_3284_ = lean_uint64_shift_right(v___x_3282_, v___x_3283_);
v_fold_3285_ = lean_uint64_xor(v___x_3282_, v___x_3284_);
v___x_3286_ = 16ULL;
v___x_3287_ = lean_uint64_shift_right(v_fold_3285_, v___x_3286_);
v___x_3288_ = lean_uint64_xor(v_fold_3285_, v___x_3287_);
v___x_3289_ = lean_uint64_to_usize(v___x_3288_);
v___x_3290_ = lean_usize_of_nat(v___x_3281_);
v___x_3291_ = ((size_t)1ULL);
v___x_3292_ = lean_usize_sub(v___x_3290_, v___x_3291_);
v___x_3293_ = lean_usize_land(v___x_3289_, v___x_3292_);
v___x_3294_ = lean_array_uget_borrowed(v_x_3273_, v___x_3293_);
lean_inc(v___x_3294_);
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 2, v___x_3294_);
v___x_3296_ = v___x_3279_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_key_3275_);
lean_ctor_set(v_reuseFailAlloc_3299_, 1, v_value_3276_);
lean_ctor_set(v_reuseFailAlloc_3299_, 2, v___x_3294_);
v___x_3296_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3297_; 
v___x_3297_ = lean_array_uset(v_x_3273_, v___x_3293_, v___x_3296_);
v_x_3273_ = v___x_3297_;
v_x_3274_ = v_tail_3277_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(lean_object* v_i_3301_, lean_object* v_source_3302_, lean_object* v_target_3303_){
_start:
{
lean_object* v___x_3304_; uint8_t v___x_3305_; 
v___x_3304_ = lean_array_get_size(v_source_3302_);
v___x_3305_ = lean_nat_dec_lt(v_i_3301_, v___x_3304_);
if (v___x_3305_ == 0)
{
lean_dec_ref(v_source_3302_);
lean_dec(v_i_3301_);
return v_target_3303_;
}
else
{
lean_object* v_es_3306_; lean_object* v___x_3307_; lean_object* v_source_3308_; lean_object* v_target_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v_es_3306_ = lean_array_fget(v_source_3302_, v_i_3301_);
v___x_3307_ = lean_box(0);
v_source_3308_ = lean_array_fset(v_source_3302_, v_i_3301_, v___x_3307_);
v_target_3309_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_target_3303_, v_es_3306_);
v___x_3310_ = lean_unsigned_to_nat(1u);
v___x_3311_ = lean_nat_add(v_i_3301_, v___x_3310_);
lean_dec(v_i_3301_);
v_i_3301_ = v___x_3311_;
v_source_3302_ = v_source_3308_;
v_target_3303_ = v_target_3309_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(lean_object* v_data_3313_){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v_nbuckets_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3314_ = lean_array_get_size(v_data_3313_);
v___x_3315_ = lean_unsigned_to_nat(2u);
v_nbuckets_3316_ = lean_nat_mul(v___x_3314_, v___x_3315_);
v___x_3317_ = lean_unsigned_to_nat(0u);
v___x_3318_ = lean_box(0);
v___x_3319_ = lean_mk_array(v_nbuckets_3316_, v___x_3318_);
v___x_3320_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v___x_3317_, v_data_3313_, v___x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(lean_object* v_m_3321_, lean_object* v_a_3322_, lean_object* v_b_3323_){
_start:
{
lean_object* v_size_3324_; lean_object* v_buckets_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3368_; 
v_size_3324_ = lean_ctor_get(v_m_3321_, 0);
v_buckets_3325_ = lean_ctor_get(v_m_3321_, 1);
v_isSharedCheck_3368_ = !lean_is_exclusive(v_m_3321_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3327_ = v_m_3321_;
v_isShared_3328_ = v_isSharedCheck_3368_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_buckets_3325_);
lean_inc(v_size_3324_);
lean_dec(v_m_3321_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3368_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3329_; uint64_t v___x_3330_; uint64_t v___x_3331_; uint64_t v___x_3332_; uint64_t v_fold_3333_; uint64_t v___x_3334_; uint64_t v___x_3335_; uint64_t v___x_3336_; size_t v___x_3337_; size_t v___x_3338_; size_t v___x_3339_; size_t v___x_3340_; size_t v___x_3341_; lean_object* v_bkt_3342_; uint8_t v___x_3343_; 
v___x_3329_ = lean_array_get_size(v_buckets_3325_);
v___x_3330_ = l_Lean_Expr_hash(v_a_3322_);
v___x_3331_ = 32ULL;
v___x_3332_ = lean_uint64_shift_right(v___x_3330_, v___x_3331_);
v_fold_3333_ = lean_uint64_xor(v___x_3330_, v___x_3332_);
v___x_3334_ = 16ULL;
v___x_3335_ = lean_uint64_shift_right(v_fold_3333_, v___x_3334_);
v___x_3336_ = lean_uint64_xor(v_fold_3333_, v___x_3335_);
v___x_3337_ = lean_uint64_to_usize(v___x_3336_);
v___x_3338_ = lean_usize_of_nat(v___x_3329_);
v___x_3339_ = ((size_t)1ULL);
v___x_3340_ = lean_usize_sub(v___x_3338_, v___x_3339_);
v___x_3341_ = lean_usize_land(v___x_3337_, v___x_3340_);
v_bkt_3342_ = lean_array_uget_borrowed(v_buckets_3325_, v___x_3341_);
v___x_3343_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3322_, v_bkt_3342_);
if (v___x_3343_ == 0)
{
lean_object* v___x_3344_; lean_object* v_size_x27_3345_; lean_object* v___x_3346_; lean_object* v_buckets_x27_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; uint8_t v___x_3353_; 
v___x_3344_ = lean_unsigned_to_nat(1u);
v_size_x27_3345_ = lean_nat_add(v_size_3324_, v___x_3344_);
lean_dec(v_size_3324_);
lean_inc(v_bkt_3342_);
v___x_3346_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3346_, 0, v_a_3322_);
lean_ctor_set(v___x_3346_, 1, v_b_3323_);
lean_ctor_set(v___x_3346_, 2, v_bkt_3342_);
v_buckets_x27_3347_ = lean_array_uset(v_buckets_3325_, v___x_3341_, v___x_3346_);
v___x_3348_ = lean_unsigned_to_nat(4u);
v___x_3349_ = lean_nat_mul(v_size_x27_3345_, v___x_3348_);
v___x_3350_ = lean_unsigned_to_nat(3u);
v___x_3351_ = lean_nat_div(v___x_3349_, v___x_3350_);
lean_dec(v___x_3349_);
v___x_3352_ = lean_array_get_size(v_buckets_x27_3347_);
v___x_3353_ = lean_nat_dec_le(v___x_3351_, v___x_3352_);
lean_dec(v___x_3351_);
if (v___x_3353_ == 0)
{
lean_object* v_val_3354_; lean_object* v___x_3356_; 
v_val_3354_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_buckets_x27_3347_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 1, v_val_3354_);
lean_ctor_set(v___x_3327_, 0, v_size_x27_3345_);
v___x_3356_ = v___x_3327_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_size_x27_3345_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v_val_3354_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
else
{
lean_object* v___x_3359_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 1, v_buckets_x27_3347_);
lean_ctor_set(v___x_3327_, 0, v_size_x27_3345_);
v___x_3359_ = v___x_3327_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_size_x27_3345_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_buckets_x27_3347_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
else
{
lean_object* v___x_3361_; lean_object* v_buckets_x27_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3366_; 
lean_inc(v_bkt_3342_);
v___x_3361_ = lean_box(0);
v_buckets_x27_3362_ = lean_array_uset(v_buckets_3325_, v___x_3341_, v___x_3361_);
v___x_3363_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3322_, v_b_3323_, v_bkt_3342_);
v___x_3364_ = lean_array_uset(v_buckets_x27_3362_, v___x_3341_, v___x_3363_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 1, v___x_3364_);
v___x_3366_ = v___x_3327_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_size_3324_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(lean_object* v_a_3369_, lean_object* v_x_3370_){
_start:
{
if (lean_obj_tag(v_x_3370_) == 0)
{
lean_object* v___x_3371_; 
v___x_3371_ = lean_box(0);
return v___x_3371_;
}
else
{
lean_object* v_key_3372_; lean_object* v_value_3373_; lean_object* v_tail_3374_; uint8_t v___x_3375_; 
v_key_3372_ = lean_ctor_get(v_x_3370_, 0);
v_value_3373_ = lean_ctor_get(v_x_3370_, 1);
v_tail_3374_ = lean_ctor_get(v_x_3370_, 2);
v___x_3375_ = lean_expr_eqv(v_key_3372_, v_a_3369_);
if (v___x_3375_ == 0)
{
v_x_3370_ = v_tail_3374_;
goto _start;
}
else
{
lean_object* v___x_3377_; 
lean_inc(v_value_3373_);
v___x_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3377_, 0, v_value_3373_);
return v___x_3377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_3378_, lean_object* v_x_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3378_, v_x_3379_);
lean_dec(v_x_3379_);
lean_dec_ref(v_a_3378_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(lean_object* v_m_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v_buckets_3383_; lean_object* v___x_3384_; uint64_t v___x_3385_; uint64_t v___x_3386_; uint64_t v___x_3387_; uint64_t v_fold_3388_; uint64_t v___x_3389_; uint64_t v___x_3390_; uint64_t v___x_3391_; size_t v___x_3392_; size_t v___x_3393_; size_t v___x_3394_; size_t v___x_3395_; size_t v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v_buckets_3383_ = lean_ctor_get(v_m_3381_, 1);
v___x_3384_ = lean_array_get_size(v_buckets_3383_);
v___x_3385_ = l_Lean_Expr_hash(v_a_3382_);
v___x_3386_ = 32ULL;
v___x_3387_ = lean_uint64_shift_right(v___x_3385_, v___x_3386_);
v_fold_3388_ = lean_uint64_xor(v___x_3385_, v___x_3387_);
v___x_3389_ = 16ULL;
v___x_3390_ = lean_uint64_shift_right(v_fold_3388_, v___x_3389_);
v___x_3391_ = lean_uint64_xor(v_fold_3388_, v___x_3390_);
v___x_3392_ = lean_uint64_to_usize(v___x_3391_);
v___x_3393_ = lean_usize_of_nat(v___x_3384_);
v___x_3394_ = ((size_t)1ULL);
v___x_3395_ = lean_usize_sub(v___x_3393_, v___x_3394_);
v___x_3396_ = lean_usize_land(v___x_3392_, v___x_3395_);
v___x_3397_ = lean_array_uget_borrowed(v_buckets_3383_, v___x_3396_);
v___x_3398_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3382_, v___x_3397_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg___boxed(lean_object* v_m_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_3399_, v_a_3400_);
lean_dec_ref(v_a_3400_);
lean_dec_ref(v_m_3399_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(lean_object* v_g_3402_, lean_object* v_e_3403_, lean_object* v_a_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_a_3413_; lean_object* v___y_3419_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = lean_st_ref_get(v_a_3404_);
v___x_3422_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v___x_3421_, v_e_3403_);
lean_dec(v___x_3421_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v___x_3423_; 
lean_inc_ref(v_g_3402_);
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
lean_inc(v___y_3408_);
lean_inc_ref(v___y_3407_);
lean_inc(v___y_3406_);
lean_inc_ref(v___y_3405_);
lean_inc_ref(v_e_3403_);
v___x_3423_ = lean_apply_8(v_g_3402_, v_e_3403_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, lean_box(0));
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v_d_3426_; lean_object* v_b_3427_; lean_object* v___y_3428_; uint8_t v___x_3431_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref(v___x_3423_);
v___x_3431_ = lean_unbox(v_a_3424_);
lean_dec(v_a_3424_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3432_; 
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec_ref(v_g_3402_);
v___x_3432_ = lean_box(0);
v_a_3413_ = v___x_3432_;
goto v___jp_3412_;
}
else
{
switch(lean_obj_tag(v_e_3403_))
{
case 7:
{
lean_object* v_binderType_3433_; lean_object* v_body_3434_; 
v_binderType_3433_ = lean_ctor_get(v_e_3403_, 1);
v_body_3434_ = lean_ctor_get(v_e_3403_, 2);
lean_inc_ref(v_body_3434_);
lean_inc_ref(v_binderType_3433_);
v_d_3426_ = v_binderType_3433_;
v_b_3427_ = v_body_3434_;
v___y_3428_ = v_a_3404_;
goto v___jp_3425_;
}
case 6:
{
lean_object* v_binderType_3435_; lean_object* v_body_3436_; 
v_binderType_3435_ = lean_ctor_get(v_e_3403_, 1);
v_body_3436_ = lean_ctor_get(v_e_3403_, 2);
lean_inc_ref(v_body_3436_);
lean_inc_ref(v_binderType_3435_);
v_d_3426_ = v_binderType_3435_;
v_b_3427_ = v_body_3436_;
v___y_3428_ = v_a_3404_;
goto v___jp_3425_;
}
case 8:
{
lean_object* v_type_3437_; lean_object* v_value_3438_; lean_object* v_body_3439_; lean_object* v___x_3440_; 
v_type_3437_ = lean_ctor_get(v_e_3403_, 1);
v_value_3438_ = lean_ctor_get(v_e_3403_, 2);
v_body_3439_ = lean_ctor_get(v_e_3403_, 3);
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
lean_inc(v___y_3408_);
lean_inc_ref(v___y_3407_);
lean_inc(v___y_3406_);
lean_inc_ref(v___y_3405_);
lean_inc_ref(v_type_3437_);
lean_inc_ref(v_g_3402_);
v___x_3440_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3402_, v_type_3437_, v_a_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v___x_3441_; 
lean_dec_ref(v___x_3440_);
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
lean_inc(v___y_3408_);
lean_inc_ref(v___y_3407_);
lean_inc(v___y_3406_);
lean_inc_ref(v___y_3405_);
lean_inc_ref(v_value_3438_);
lean_inc_ref(v_g_3402_);
v___x_3441_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3402_, v_value_3438_, v_a_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v___x_3442_; 
lean_dec_ref(v___x_3441_);
lean_inc_ref(v_body_3439_);
v___x_3442_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3402_, v_body_3439_, v_a_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
v___y_3419_ = v___x_3442_;
goto v___jp_3418_;
}
else
{
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec_ref(v_g_3402_);
v___y_3419_ = v___x_3441_;
goto v___jp_3418_;
}
}
else
{
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec_ref(v_g_3402_);
v___y_3419_ = v___x_3440_;
goto v___jp_3418_;
}
}
case 5:
{
lean_object* v_fn_3443_; lean_object* v_arg_3444_; lean_object* v___x_3445_; 
v_fn_3443_ = lean_ctor_get(v_e_3403_, 0);
v_arg_3444_ = lean_ctor_get(v_e_3403_, 1);
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
lean_inc(v___y_3408_);
lean_inc_ref(v___y_3407_);
lean_inc(v___y_3406_);
lean_inc_ref(v___y_3405_);
lean_inc_ref(v_fn_3443_);
lean_inc_ref(v_g_3402_);
v___x_3445_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3402_, v_fn_3443_, v_a_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v___x_3446_; 
lean_dec_ref(v___x_3445_);
lean_inc_ref(v_arg_3444_);
v___x_3446_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3402_, v_arg_3444_, v_a_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
v___y_3419_ = v___x_3446_;
goto v___jp_3418_;
}
else
{
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec_ref(v_g_3402_);
v___y_3419_ = v___x_3445_;
goto v___jp_3418_;
}
}
case 10:
{
lean_object* v_expr_3447_; lean_object* v___x_3448_; 
v_expr_3447_ = lean_ctor_get(v_e_3403_, 1);
lean_inc_ref(v_expr_3447_);
v___x_3448_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3402_, v_expr_3447_, v_a_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
v___y_3419_ = v___x_3448_;
goto v___jp_3418_;
}
case 11:
{
lean_object* v_struct_3449_; lean_object* v___x_3450_; 
v_struct_3449_ = lean_ctor_get(v_e_3403_, 2);
lean_inc_ref(v_struct_3449_);
v___x_3450_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3402_, v_struct_3449_, v_a_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
v___y_3419_ = v___x_3450_;
goto v___jp_3418_;
}
default: 
{
lean_object* v___x_3451_; 
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec_ref(v_g_3402_);
v___x_3451_ = lean_box(0);
v_a_3413_ = v___x_3451_;
goto v___jp_3412_;
}
}
}
v___jp_3425_:
{
lean_object* v___x_3429_; 
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
lean_inc(v___y_3408_);
lean_inc_ref(v___y_3407_);
lean_inc(v___y_3406_);
lean_inc_ref(v___y_3405_);
lean_inc_ref(v_g_3402_);
v___x_3429_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3402_, v_d_3426_, v___y_3428_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v___x_3430_; 
lean_dec_ref(v___x_3429_);
v___x_3430_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3402_, v_b_3427_, v___y_3428_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
v___y_3419_ = v___x_3430_;
goto v___jp_3418_;
}
else
{
lean_dec_ref(v_b_3427_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec_ref(v_g_3402_);
v___y_3419_ = v___x_3429_;
goto v___jp_3418_;
}
}
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec_ref(v_e_3403_);
lean_dec_ref(v_g_3402_);
v_a_3452_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3423_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3423_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
else
{
lean_object* v_val_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec_ref(v_e_3403_);
lean_dec_ref(v_g_3402_);
v_val_3460_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3422_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_val_3460_);
lean_dec(v___x_3422_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
lean_ctor_set_tag(v___x_3462_, 0);
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_val_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
v___jp_3412_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3414_ = lean_st_ref_take(v_a_3404_);
v___x_3415_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v___x_3414_, v_e_3403_, v_a_3413_);
v___x_3416_ = lean_st_ref_set(v_a_3404_, v___x_3415_);
v___x_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3417_, 0, v_a_3413_);
return v___x_3417_;
}
v___jp_3418_:
{
if (lean_obj_tag(v___y_3419_) == 0)
{
lean_object* v_a_3420_; 
v_a_3420_ = lean_ctor_get(v___y_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref(v___y_3419_);
v_a_3413_ = v_a_3420_;
goto v___jp_3412_;
}
else
{
lean_dec_ref(v_e_3403_);
return v___y_3419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1___boxed(lean_object* v_g_3468_, lean_object* v_e_3469_, lean_object* v_a_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3468_, v_e_3469_, v_a_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v_a_3470_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared(lean_object* v_e_3479_, lean_object* v_msg_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___f_3490_; lean_object* v___x_3491_; 
v___x_3488_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_3489_ = lean_st_mk_ref(v___x_3488_);
v___f_3490_ = lean_alloc_closure((void*)(l_Lean_Expr_checkMaxShared___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3490_, 0, v_msg_3480_);
v___x_3491_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v___f_3490_, v_e_3479_, v___x_3489_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3500_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3494_ = v___x_3491_;
v_isShared_3495_ = v_isSharedCheck_3500_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3491_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3500_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3496_; lean_object* v___x_3498_; 
v___x_3496_ = lean_st_ref_get(v___x_3489_);
lean_dec(v___x_3489_);
lean_dec(v___x_3496_);
if (v_isShared_3495_ == 0)
{
v___x_3498_ = v___x_3494_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3492_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
else
{
lean_dec(v___x_3489_);
return v___x_3491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___boxed(lean_object* v_e_3501_, lean_object* v_msg_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_Expr_checkMaxShared(v_e_3501_, v_msg_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(lean_object* v_00_u03b2_3511_, lean_object* v_x_3512_, lean_object* v_x_3513_){
_start:
{
lean_object* v___x_3514_; 
v___x_3514_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_3512_, v_x_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(lean_object* v_00_u03b2_3515_, lean_object* v_x_3516_, size_t v_x_3517_, lean_object* v_x_3518_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3516_, v_x_3517_, v_x_3518_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3520_, lean_object* v_x_3521_, lean_object* v_x_3522_, lean_object* v_x_3523_){
_start:
{
size_t v_x_8186__boxed_3524_; lean_object* v_res_3525_; 
v_x_8186__boxed_3524_ = lean_unbox_usize(v_x_3522_);
lean_dec(v_x_3522_);
v_res_3525_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(v_00_u03b2_3520_, v_x_3521_, v_x_8186__boxed_3524_, v_x_3523_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(lean_object* v_00_u03b2_3526_, lean_object* v_m_3527_, lean_object* v_a_3528_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_3527_, v_a_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3530_, lean_object* v_m_3531_, lean_object* v_a_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(v_00_u03b2_3530_, v_m_3531_, v_a_3532_);
lean_dec_ref(v_a_3532_);
lean_dec_ref(v_m_3531_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(lean_object* v_00_u03b2_3534_, lean_object* v_m_3535_, lean_object* v_a_3536_, lean_object* v_b_3537_){
_start:
{
lean_object* v___x_3538_; 
v___x_3538_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v_m_3535_, v_a_3536_, v_b_3537_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3539_, lean_object* v_keys_3540_, lean_object* v_vals_3541_, lean_object* v_heq_3542_, lean_object* v_i_3543_, lean_object* v_k_3544_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_3540_, v_vals_3541_, v_i_3543_, v_k_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3546_, lean_object* v_keys_3547_, lean_object* v_vals_3548_, lean_object* v_heq_3549_, lean_object* v_i_3550_, lean_object* v_k_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(v_00_u03b2_3546_, v_keys_3547_, v_vals_3548_, v_heq_3549_, v_i_3550_, v_k_3551_);
lean_dec_ref(v_vals_3548_);
lean_dec_ref(v_keys_3547_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3553_, lean_object* v_a_3554_, lean_object* v_x_3555_){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3554_, v_x_3555_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_3557_, lean_object* v_a_3558_, lean_object* v_x_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(v_00_u03b2_3557_, v_a_3558_, v_x_3559_);
lean_dec(v_x_3559_);
lean_dec_ref(v_a_3558_);
return v_res_3560_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_3561_, lean_object* v_a_3562_, lean_object* v_x_3563_){
_start:
{
uint8_t v___x_3564_; 
v___x_3564_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3562_, v_x_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3565_, lean_object* v_a_3566_, lean_object* v_x_3567_){
_start:
{
uint8_t v_res_3568_; lean_object* v_r_3569_; 
v_res_3568_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(v_00_u03b2_3565_, v_a_3566_, v_x_3567_);
lean_dec(v_x_3567_);
lean_dec_ref(v_a_3566_);
v_r_3569_ = lean_box(v_res_3568_);
return v_r_3569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3570_, lean_object* v_data_3571_){
_start:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_data_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_3573_, lean_object* v_a_3574_, lean_object* v_b_3575_, lean_object* v_x_3576_){
_start:
{
lean_object* v___x_3577_; 
v___x_3577_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3574_, v_b_3575_, v_x_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_3578_, lean_object* v_i_3579_, lean_object* v_source_3580_, lean_object* v_target_3581_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v_i_3579_, v_source_3580_, v_target_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9(lean_object* v_00_u03b2_3583_, lean_object* v_x_3584_, lean_object* v_x_3585_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_x_3584_, v_x_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared(lean_object* v_mvarId_3587_, lean_object* v_msg_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l_Lean_MVarId_getDecl(v_mvarId_3587_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v_type_3598_; lean_object* v___x_3599_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref(v___x_3596_);
v_type_3598_ = lean_ctor_get(v_a_3597_, 2);
lean_inc_ref(v_type_3598_);
lean_dec(v_a_3597_);
v___x_3599_ = l_Lean_Expr_checkMaxShared(v_type_3598_, v_msg_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_);
return v___x_3599_;
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_dec(v_a_3594_);
lean_dec_ref(v_a_3593_);
lean_dec(v_a_3592_);
lean_dec_ref(v_a_3591_);
lean_dec(v_a_3590_);
lean_dec_ref(v_a_3589_);
lean_dec_ref(v_msg_3588_);
v_a_3600_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3596_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3596_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared___boxed(lean_object* v_mvarId_3608_, lean_object* v_msg_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l_Lean_MVarId_checkMaxShared(v_mvarId_3608_, v_msg_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_);
return v_res_3617_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(lean_object* v_x_3618_){
_start:
{
uint8_t v___x_3619_; 
v___x_3619_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_3618_);
if (v___x_3619_ == 0)
{
uint8_t v___x_3620_; 
v___x_3620_ = 1;
return v___x_3620_;
}
else
{
uint8_t v___x_3621_; 
v___x_3621_ = 0;
return v___x_3621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed(lean_object* v_x_3622_){
_start:
{
uint8_t v_res_3623_; lean_object* v_r_3624_; 
v_res_3623_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(v_x_3622_);
lean_dec(v_x_3622_);
v_r_3624_ = lean_box(v_res_3623_);
return v_r_3624_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__1(lean_object* v___f_3625_, lean_object* v_x_3626_){
_start:
{
switch(lean_obj_tag(v_x_3626_))
{
case 4:
{
lean_object* v_us_3627_; uint8_t v___x_3628_; 
v_us_3627_ = lean_ctor_get(v_x_3626_, 1);
lean_inc(v_us_3627_);
lean_dec_ref(v_x_3626_);
v___x_3628_ = l_List_any___redArg(v_us_3627_, v___f_3625_);
return v___x_3628_;
}
case 3:
{
lean_object* v_u_3629_; uint8_t v___x_3630_; 
lean_dec_ref(v___f_3625_);
v_u_3629_ = lean_ctor_get(v_x_3626_, 0);
lean_inc(v_u_3629_);
lean_dec_ref(v_x_3626_);
v___x_3630_ = l_Lean_Level_isAlreadyNormalizedCheap(v_u_3629_);
lean_dec(v_u_3629_);
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
default: 
{
uint8_t v___x_3633_; 
lean_dec_ref(v_x_3626_);
lean_dec_ref(v___f_3625_);
v___x_3633_ = 0;
return v___x_3633_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__1___boxed(lean_object* v___f_3634_, lean_object* v_x_3635_){
_start:
{
uint8_t v_res_3636_; lean_object* v_r_3637_; 
v_res_3636_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__1(v___f_3634_, v_x_3635_);
v_r_3637_ = lean_box(v_res_3636_);
return v_r_3637_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(lean_object* v_e_3641_){
_start:
{
lean_object* v___f_3642_; lean_object* v___x_3643_; 
v___f_3642_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__1));
v___x_3643_ = lean_find_expr(v___f_3642_, v_e_3641_);
if (lean_obj_tag(v___x_3643_) == 0)
{
uint8_t v___x_3644_; 
v___x_3644_ = 1;
return v___x_3644_;
}
else
{
uint8_t v___x_3645_; 
lean_dec_ref(v___x_3643_);
v___x_3645_ = 0;
return v___x_3645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___boxed(lean_object* v_e_3646_){
_start:
{
uint8_t v_res_3647_; lean_object* v_r_3648_; 
v_res_3647_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_3646_);
lean_dec_ref(v_e_3646_);
v_r_3648_ = lean_box(v_res_3647_);
return v_r_3648_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(lean_object* v_a_3649_, lean_object* v_a_3650_){
_start:
{
if (lean_obj_tag(v_a_3649_) == 0)
{
lean_object* v___x_3651_; 
v___x_3651_ = l_List_reverse___redArg(v_a_3650_);
return v___x_3651_;
}
else
{
lean_object* v_head_3652_; lean_object* v_tail_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3662_; 
v_head_3652_ = lean_ctor_get(v_a_3649_, 0);
v_tail_3653_ = lean_ctor_get(v_a_3649_, 1);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_a_3649_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3655_ = v_a_3649_;
v_isShared_3656_ = v_isSharedCheck_3662_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_tail_3653_);
lean_inc(v_head_3652_);
lean_dec(v_a_3649_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3662_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; lean_object* v___x_3659_; 
v___x_3657_ = l_Lean_Level_normalize(v_head_3652_);
lean_dec(v_head_3652_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 1, v_a_3650_);
lean_ctor_set(v___x_3655_, 0, v___x_3657_);
v___x_3659_ = v___x_3655_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3657_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_a_3650_);
v___x_3659_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
v_a_3649_ = v_tail_3653_;
v_a_3650_ = v___x_3659_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0(lean_object* v_e_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v___y_3668_; lean_object* v___y_3672_; 
switch(lean_obj_tag(v_e_3663_))
{
case 3:
{
lean_object* v_u_3675_; lean_object* v___x_3676_; size_t v___x_3677_; size_t v___x_3678_; uint8_t v___x_3679_; 
v_u_3675_ = lean_ctor_get(v_e_3663_, 0);
v___x_3676_ = l_Lean_Level_normalize(v_u_3675_);
v___x_3677_ = lean_ptr_addr(v_u_3675_);
v___x_3678_ = lean_ptr_addr(v___x_3676_);
v___x_3679_ = lean_usize_dec_eq(v___x_3677_, v___x_3678_);
if (v___x_3679_ == 0)
{
lean_object* v___x_3680_; 
lean_dec_ref(v_e_3663_);
v___x_3680_ = l_Lean_Expr_sort___override(v___x_3676_);
v___y_3668_ = v___x_3680_;
goto v___jp_3667_;
}
else
{
lean_dec(v___x_3676_);
v___y_3668_ = v_e_3663_;
goto v___jp_3667_;
}
}
case 4:
{
lean_object* v_declName_3681_; lean_object* v_us_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; 
v_declName_3681_ = lean_ctor_get(v_e_3663_, 0);
v_us_3682_ = lean_ctor_get(v_e_3663_, 1);
v___x_3683_ = lean_box(0);
lean_inc(v_us_3682_);
v___x_3684_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(v_us_3682_, v___x_3683_);
v___x_3685_ = l_ptrEqList___redArg(v_us_3682_, v___x_3684_);
if (v___x_3685_ == 0)
{
lean_object* v___x_3686_; 
lean_inc(v_declName_3681_);
lean_dec_ref(v_e_3663_);
v___x_3686_ = l_Lean_Expr_const___override(v_declName_3681_, v___x_3684_);
v___y_3672_ = v___x_3686_;
goto v___jp_3671_;
}
else
{
lean_dec(v___x_3684_);
v___y_3672_ = v_e_3663_;
goto v___jp_3671_;
}
}
default: 
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
lean_dec_ref(v_e_3663_);
v___x_3687_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
return v___x_3688_;
}
}
v___jp_3667_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3669_, 0, v___y_3668_);
v___x_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
return v___x_3670_;
}
v___jp_3671_:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3673_, 0, v___y_3672_);
v___x_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
return v___x_3674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed(lean_object* v_e_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_Meta_Sym_normalizeLevels___lam__0(v_e_3689_, v___y_3690_, v___y_3691_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1(lean_object* v_e_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3698_, 0, v_e_3694_);
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed(lean_object* v_e_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l_Lean_Meta_Sym_normalizeLevels___lam__1(v_e_3700_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_ref_3705_){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3707_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3708_, 0, v_ref_3705_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
v___x_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_ref_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_3710_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(lean_object* v_x_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v___y_3719_; lean_object* v_fileName_3728_; lean_object* v_fileMap_3729_; lean_object* v_options_3730_; lean_object* v_currRecDepth_3731_; lean_object* v_maxRecDepth_3732_; lean_object* v_ref_3733_; lean_object* v_currNamespace_3734_; lean_object* v_openDecls_3735_; lean_object* v_initHeartbeats_3736_; lean_object* v_maxHeartbeats_3737_; lean_object* v_quotContext_3738_; lean_object* v_currMacroScope_3739_; uint8_t v_diag_3740_; lean_object* v_cancelTk_x3f_3741_; uint8_t v_suppressElabErrors_3742_; lean_object* v_inheritedTraceOptions_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3755_; 
v_fileName_3728_ = lean_ctor_get(v___y_3715_, 0);
v_fileMap_3729_ = lean_ctor_get(v___y_3715_, 1);
v_options_3730_ = lean_ctor_get(v___y_3715_, 2);
v_currRecDepth_3731_ = lean_ctor_get(v___y_3715_, 3);
v_maxRecDepth_3732_ = lean_ctor_get(v___y_3715_, 4);
v_ref_3733_ = lean_ctor_get(v___y_3715_, 5);
v_currNamespace_3734_ = lean_ctor_get(v___y_3715_, 6);
v_openDecls_3735_ = lean_ctor_get(v___y_3715_, 7);
v_initHeartbeats_3736_ = lean_ctor_get(v___y_3715_, 8);
v_maxHeartbeats_3737_ = lean_ctor_get(v___y_3715_, 9);
v_quotContext_3738_ = lean_ctor_get(v___y_3715_, 10);
v_currMacroScope_3739_ = lean_ctor_get(v___y_3715_, 11);
v_diag_3740_ = lean_ctor_get_uint8(v___y_3715_, sizeof(void*)*14);
v_cancelTk_x3f_3741_ = lean_ctor_get(v___y_3715_, 12);
v_suppressElabErrors_3742_ = lean_ctor_get_uint8(v___y_3715_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3743_ = lean_ctor_get(v___y_3715_, 13);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___y_3715_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3745_ = v___y_3715_;
v_isShared_3746_ = v_isSharedCheck_3755_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_inheritedTraceOptions_3743_);
lean_inc(v_cancelTk_x3f_3741_);
lean_inc(v_currMacroScope_3739_);
lean_inc(v_quotContext_3738_);
lean_inc(v_maxHeartbeats_3737_);
lean_inc(v_initHeartbeats_3736_);
lean_inc(v_openDecls_3735_);
lean_inc(v_currNamespace_3734_);
lean_inc(v_ref_3733_);
lean_inc(v_maxRecDepth_3732_);
lean_inc(v_currRecDepth_3731_);
lean_inc(v_options_3730_);
lean_inc(v_fileMap_3729_);
lean_inc(v_fileName_3728_);
lean_dec(v___y_3715_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3755_;
goto v_resetjp_3744_;
}
v___jp_3718_:
{
if (lean_obj_tag(v___y_3719_) == 0)
{
return v___y_3719_;
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
v_a_3720_ = lean_ctor_get(v___y_3719_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___y_3719_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___y_3719_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___y_3719_);
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
v_resetjp_3744_:
{
uint8_t v___x_3747_; 
v___x_3747_ = lean_nat_dec_eq(v_currRecDepth_3731_, v_maxRecDepth_3732_);
if (v___x_3747_ == 0)
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3751_; 
v___x_3748_ = lean_unsigned_to_nat(1u);
v___x_3749_ = lean_nat_add(v_currRecDepth_3731_, v___x_3748_);
lean_dec(v_currRecDepth_3731_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 3, v___x_3749_);
v___x_3751_ = v___x_3745_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_fileName_3728_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_fileMap_3729_);
lean_ctor_set(v_reuseFailAlloc_3753_, 2, v_options_3730_);
lean_ctor_set(v_reuseFailAlloc_3753_, 3, v___x_3749_);
lean_ctor_set(v_reuseFailAlloc_3753_, 4, v_maxRecDepth_3732_);
lean_ctor_set(v_reuseFailAlloc_3753_, 5, v_ref_3733_);
lean_ctor_set(v_reuseFailAlloc_3753_, 6, v_currNamespace_3734_);
lean_ctor_set(v_reuseFailAlloc_3753_, 7, v_openDecls_3735_);
lean_ctor_set(v_reuseFailAlloc_3753_, 8, v_initHeartbeats_3736_);
lean_ctor_set(v_reuseFailAlloc_3753_, 9, v_maxHeartbeats_3737_);
lean_ctor_set(v_reuseFailAlloc_3753_, 10, v_quotContext_3738_);
lean_ctor_set(v_reuseFailAlloc_3753_, 11, v_currMacroScope_3739_);
lean_ctor_set(v_reuseFailAlloc_3753_, 12, v_cancelTk_x3f_3741_);
lean_ctor_set(v_reuseFailAlloc_3753_, 13, v_inheritedTraceOptions_3743_);
lean_ctor_set_uint8(v_reuseFailAlloc_3753_, sizeof(void*)*14, v_diag_3740_);
lean_ctor_set_uint8(v_reuseFailAlloc_3753_, sizeof(void*)*14 + 1, v_suppressElabErrors_3742_);
v___x_3751_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
lean_object* v___x_3752_; 
v___x_3752_ = lean_apply_4(v_x_3713_, v___y_3714_, v___x_3751_, v___y_3716_, lean_box(0));
v___y_3719_ = v___x_3752_;
goto v___jp_3718_;
}
}
else
{
lean_object* v___x_3754_; 
lean_del_object(v___x_3745_);
lean_dec_ref(v_inheritedTraceOptions_3743_);
lean_dec(v_cancelTk_x3f_3741_);
lean_dec(v_currMacroScope_3739_);
lean_dec(v_quotContext_3738_);
lean_dec(v_maxHeartbeats_3737_);
lean_dec(v_initHeartbeats_3736_);
lean_dec(v_openDecls_3735_);
lean_dec(v_currNamespace_3734_);
lean_dec(v_maxRecDepth_3732_);
lean_dec(v_currRecDepth_3731_);
lean_dec_ref(v_options_3730_);
lean_dec_ref(v_fileMap_3729_);
lean_dec_ref(v_fileName_3728_);
lean_dec(v___y_3716_);
lean_dec(v___y_3714_);
lean_dec_ref(v_x_3713_);
v___x_3754_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_3733_);
v___y_3719_ = v___x_3754_;
goto v___jp_3718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_x_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v_x_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3762_, lean_object* v_x_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3767_ = lean_apply_1(v_x_3763_, lean_box(0));
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3769_, lean_object* v_x_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(v_00_u03b1_3769_, v_x_3770_, v___y_3771_, v___y_3772_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(lean_object* v_pre_3775_, lean_object* v_post_3776_, size_t v_sz_3777_, size_t v_i_3778_, lean_object* v_bs_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
uint8_t v___x_3784_; 
v___x_3784_ = lean_usize_dec_lt(v_i_3778_, v_sz_3777_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; 
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v_post_3776_);
lean_dec_ref(v_pre_3775_);
v___x_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3785_, 0, v_bs_3779_);
return v___x_3785_;
}
else
{
lean_object* v_v_3786_; lean_object* v___x_3787_; 
v_v_3786_ = lean_array_uget_borrowed(v_bs_3779_, v_i_3778_);
lean_inc(v___y_3782_);
lean_inc_ref(v___y_3781_);
lean_inc(v___y_3780_);
lean_inc(v_v_3786_);
lean_inc_ref(v_post_3776_);
lean_inc_ref(v_pre_3775_);
v___x_3787_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3775_, v_post_3776_, v_v_3786_, v___y_3780_, v___y_3781_, v___y_3782_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3789_; lean_object* v_bs_x27_3790_; size_t v___x_3791_; size_t v___x_3792_; lean_object* v___x_3793_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3788_);
lean_dec_ref(v___x_3787_);
v___x_3789_ = lean_unsigned_to_nat(0u);
v_bs_x27_3790_ = lean_array_uset(v_bs_3779_, v_i_3778_, v___x_3789_);
v___x_3791_ = ((size_t)1ULL);
v___x_3792_ = lean_usize_add(v_i_3778_, v___x_3791_);
v___x_3793_ = lean_array_uset(v_bs_x27_3790_, v_i_3778_, v_a_3788_);
v_i_3778_ = v___x_3792_;
v_bs_3779_ = v___x_3793_;
goto _start;
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v_bs_3779_);
lean_dec_ref(v_post_3776_);
lean_dec_ref(v_pre_3775_);
v_a_3795_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3787_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3787_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(lean_object* v_pre_3803_, lean_object* v_post_3804_, lean_object* v_x_3805_, lean_object* v_x_3806_, lean_object* v_x_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
if (lean_obj_tag(v_x_3805_) == 5)
{
lean_object* v_fn_3812_; lean_object* v_arg_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v_fn_3812_ = lean_ctor_get(v_x_3805_, 0);
lean_inc_ref(v_fn_3812_);
v_arg_3813_ = lean_ctor_get(v_x_3805_, 1);
lean_inc_ref(v_arg_3813_);
lean_dec_ref(v_x_3805_);
v___x_3814_ = lean_array_set(v_x_3806_, v_x_3807_, v_arg_3813_);
v___x_3815_ = lean_unsigned_to_nat(1u);
v___x_3816_ = lean_nat_sub(v_x_3807_, v___x_3815_);
lean_dec(v_x_3807_);
v_x_3805_ = v_fn_3812_;
v_x_3806_ = v___x_3814_;
v_x_3807_ = v___x_3816_;
goto _start;
}
else
{
lean_object* v___x_3818_; 
lean_dec(v_x_3807_);
lean_inc(v___y_3810_);
lean_inc_ref(v___y_3809_);
lean_inc(v___y_3808_);
lean_inc_ref(v_post_3804_);
lean_inc_ref(v_pre_3803_);
v___x_3818_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3803_, v_post_3804_, v_x_3805_, v___y_3808_, v___y_3809_, v___y_3810_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; size_t v_sz_3820_; size_t v___x_3821_; lean_object* v___x_3822_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_a_3819_);
lean_dec_ref(v___x_3818_);
v_sz_3820_ = lean_array_size(v_x_3806_);
v___x_3821_ = ((size_t)0ULL);
lean_inc(v___y_3810_);
lean_inc_ref(v___y_3809_);
lean_inc(v___y_3808_);
lean_inc_ref(v_post_3804_);
lean_inc_ref(v_pre_3803_);
v___x_3822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_3803_, v_post_3804_, v_sz_3820_, v___x_3821_, v_x_3806_, v___y_3808_, v___y_3809_, v___y_3810_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_a_3823_);
lean_dec_ref(v___x_3822_);
v___x_3824_ = l_Lean_mkAppN(v_a_3819_, v_a_3823_);
lean_dec(v_a_3823_);
v___x_3825_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3803_, v_post_3804_, v___x_3824_, v___y_3808_, v___y_3809_, v___y_3810_);
return v___x_3825_;
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec(v_a_3819_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v___y_3808_);
lean_dec_ref(v_post_3804_);
lean_dec_ref(v_pre_3803_);
v_a_3826_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3822_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3822_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
else
{
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v___y_3808_);
lean_dec_ref(v_x_3806_);
lean_dec_ref(v_post_3804_);
lean_dec_ref(v_pre_3803_);
return v___x_3818_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(lean_object* v_pre_3834_, lean_object* v_e_3835_, lean_object* v_post_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; uint8_t v___y_3847_; lean_object* v___y_3848_; uint8_t v___y_3849_; lean_object* v___y_3859_; uint8_t v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; uint8_t v___y_3864_; uint8_t v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; uint8_t v___y_3877_; lean_object* v___x_3884_; 
lean_inc_ref(v_pre_3834_);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc_ref(v_e_3835_);
v___x_3884_ = lean_apply_4(v_pre_3834_, v_e_3835_, v___y_3838_, v___y_3839_, lean_box(0));
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3974_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3887_ = v___x_3884_;
v_isShared_3888_ = v_isSharedCheck_3974_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3884_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3974_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___y_3890_; 
switch(lean_obj_tag(v_a_3885_))
{
case 0:
{
lean_object* v_e_3964_; lean_object* v___x_3966_; 
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v_post_3836_);
lean_dec_ref(v_e_3835_);
lean_dec_ref(v_pre_3834_);
v_e_3964_ = lean_ctor_get(v_a_3885_, 0);
lean_inc_ref(v_e_3964_);
lean_dec_ref(v_a_3885_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 0, v_e_3964_);
v___x_3966_ = v___x_3887_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_e_3964_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
case 1:
{
lean_object* v_e_3968_; lean_object* v___x_3969_; 
lean_del_object(v___x_3887_);
lean_dec_ref(v_e_3835_);
v_e_3968_ = lean_ctor_get(v_a_3885_, 0);
lean_inc_ref(v_e_3968_);
lean_dec_ref(v_a_3885_);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc(v___y_3837_);
lean_inc_ref(v_post_3836_);
lean_inc_ref(v_pre_3834_);
v___x_3969_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3834_, v_post_3836_, v_e_3968_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3971_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref(v___x_3969_);
v___x_3971_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v_a_3970_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3971_;
}
else
{
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v_post_3836_);
lean_dec_ref(v_pre_3834_);
return v___x_3969_;
}
}
default: 
{
lean_object* v_e_x3f_3972_; 
lean_del_object(v___x_3887_);
v_e_x3f_3972_ = lean_ctor_get(v_a_3885_, 0);
lean_inc(v_e_x3f_3972_);
lean_dec_ref(v_a_3885_);
if (lean_obj_tag(v_e_x3f_3972_) == 0)
{
v___y_3890_ = v_e_3835_;
goto v___jp_3889_;
}
else
{
lean_object* v_val_3973_; 
lean_dec_ref(v_e_3835_);
v_val_3973_ = lean_ctor_get(v_e_x3f_3972_, 0);
lean_inc(v_val_3973_);
lean_dec_ref(v_e_x3f_3972_);
v___y_3890_ = v_val_3973_;
goto v___jp_3889_;
}
}
}
v___jp_3889_:
{
switch(lean_obj_tag(v___y_3890_))
{
case 7:
{
lean_object* v_binderName_3891_; lean_object* v_binderType_3892_; lean_object* v_body_3893_; uint8_t v_binderInfo_3894_; lean_object* v___x_3895_; 
v_binderName_3891_ = lean_ctor_get(v___y_3890_, 0);
lean_inc(v_binderName_3891_);
v_binderType_3892_ = lean_ctor_get(v___y_3890_, 1);
v_body_3893_ = lean_ctor_get(v___y_3890_, 2);
v_binderInfo_3894_ = lean_ctor_get_uint8(v___y_3890_, sizeof(void*)*3 + 8);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc(v___y_3837_);
lean_inc_ref(v_binderType_3892_);
lean_inc_ref(v_post_3836_);
lean_inc_ref(v_pre_3834_);
v___x_3895_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3834_, v_post_3836_, v_binderType_3892_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3897_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
lean_dec_ref(v___x_3895_);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc(v___y_3837_);
lean_inc_ref(v_body_3893_);
lean_inc_ref(v_post_3836_);
lean_inc_ref(v_pre_3834_);
v___x_3897_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3834_, v_post_3836_, v_body_3893_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; size_t v___x_3899_; size_t v___x_3900_; uint8_t v___x_3901_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref(v___x_3897_);
v___x_3899_ = lean_ptr_addr(v_binderType_3892_);
v___x_3900_ = lean_ptr_addr(v_a_3896_);
v___x_3901_ = lean_usize_dec_eq(v___x_3899_, v___x_3900_);
if (v___x_3901_ == 0)
{
v___y_3872_ = v_binderInfo_3894_;
v___y_3873_ = v_a_3896_;
v___y_3874_ = v___y_3890_;
v___y_3875_ = v_a_3898_;
v___y_3876_ = v_binderName_3891_;
v___y_3877_ = v___x_3901_;
goto v___jp_3871_;
}
else
{
size_t v___x_3902_; size_t v___x_3903_; uint8_t v___x_3904_; 
v___x_3902_ = lean_ptr_addr(v_body_3893_);
v___x_3903_ = lean_ptr_addr(v_a_3898_);
v___x_3904_ = lean_usize_dec_eq(v___x_3902_, v___x_3903_);
v___y_3872_ = v_binderInfo_3894_;
v___y_3873_ = v_a_3896_;
v___y_3874_ = v___y_3890_;
v___y_3875_ = v_a_3898_;
v___y_3876_ = v_binderName_3891_;
v___y_3877_ = v___x_3904_;
goto v___jp_3871_;
}
}
else
{
lean_dec(v_a_3896_);
lean_dec_ref(v___y_3890_);
lean_dec(v_binderName_3891_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v_post_3836_);
lean_dec_ref(v_pre_3834_);
return v___x_3897_;
}
}
else
{
lean_dec_ref(v___y_3890_);
lean_dec(v_binderName_3891_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v_post_3836_);
lean_dec_ref(v_pre_3834_);
return v___x_3895_;
}
}
case 6:
{
lean_object* v_binderName_3905_; lean_object* v_binderType_3906_; lean_object* v_body_3907_; uint8_t v_binderInfo_3908_; lean_object* v___x_3909_; 
v_binderName_3905_ = lean_ctor_get(v___y_3890_, 0);
lean_inc(v_binderName_3905_);
v_binderType_3906_ = lean_ctor_get(v___y_3890_, 1);
v_body_3907_ = lean_ctor_get(v___y_3890_, 2);
v_binderInfo_3908_ = lean_ctor_get_uint8(v___y_3890_, sizeof(void*)*3 + 8);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc(v___y_3837_);
lean_inc_ref(v_binderType_3906_);
lean_inc_ref(v_post_3836_);
lean_inc_ref(v_pre_3834_);
v___x_3909_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3834_, v_post_3836_, v_binderType_3906_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3911_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref(v___x_3909_);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc(v___y_3837_);
lean_inc_ref(v_body_3907_);
lean_inc_ref(v_post_3836_);
lean_inc_ref(v_pre_3834_);
v___x_3911_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3834_, v_post_3836_, v_body_3907_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; size_t v___x_3913_; size_t v___x_3914_; uint8_t v___x_3915_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref(v___x_3911_);
v___x_3913_ = lean_ptr_addr(v_binderType_3906_);
v___x_3914_ = lean_ptr_addr(v_a_3910_);
v___x_3915_ = lean_usize_dec_eq(v___x_3913_, v___x_3914_);
if (v___x_3915_ == 0)
{
v___y_3859_ = v_binderName_3905_;
v___y_3860_ = v_binderInfo_3908_;
v___y_3861_ = v_a_3912_;
v___y_3862_ = v___y_3890_;
v___y_3863_ = v_a_3910_;
v___y_3864_ = v___x_3915_;
goto v___jp_3858_;
}
else
{
size_t v___x_3916_; size_t v___x_3917_; uint8_t v___x_3918_; 
v___x_3916_ = lean_ptr_addr(v_body_3907_);
v___x_3917_ = lean_ptr_addr(v_a_3912_);
v___x_3918_ = lean_usize_dec_eq(v___x_3916_, v___x_3917_);
v___y_3859_ = v_binderName_3905_;
v___y_3860_ = v_binderInfo_3908_;
v___y_3861_ = v_a_3912_;
v___y_3862_ = v___y_3890_;
v___y_3863_ = v_a_3910_;
v___y_3864_ = v___x_3918_;
goto v___jp_3858_;
}
}
else
{
lean_dec(v_a_3910_);
lean_dec_ref(v___y_3890_);
lean_dec(v_binderName_3905_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v_post_3836_);
lean_dec_ref(v_pre_3834_);
return v___x_3911_;
}
}
else
{
lean_dec_ref(v___y_3890_);
lean_dec(v_binderName_3905_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v_post_3836_);
lean_dec_ref(v_pre_3834_);
return v___x_3909_;
}
}
case 8:
{
lean_object* v_declName_3919_; lean_object* v_type_3920_; lean_object* v_value_3921_; lean_object* v_body_3922_; uint8_t v_nondep_3923_; lean_object* v___x_3924_; 
v_declName_3919_ = lean_ctor_get(v___y_3890_, 0);
lean_inc(v_declName_3919_);
v_type_3920_ = lean_ctor_get(v___y_3890_, 1);
v_value_3921_ = lean_ctor_get(v___y_3890_, 2);
v_body_3922_ = lean_ctor_get(v___y_3890_, 3);
lean_inc_ref(v_body_3922_);
v_nondep_3923_ = lean_ctor_get_uint8(v___y_3890_, sizeof(void*)*4 + 8);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc(v___y_3837_);
lean_inc_ref(v_type_3920_);
lean_inc_ref(v_post_3836_);
lean_inc_ref(v_pre_3834_);
v___x_3924_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3834_, v_post_3836_, v_type_3920_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3926_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref(v___x_3924_);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc(v___y_3837_);
lean_inc_ref(v_value_3921_);
lean_inc_ref(v_post_3836_);
lean_inc_ref(v_pre_3834_);
v___x_3926_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3834_, v_post_3836_, v_value_3921_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_a_3927_; lean_object* v___x_3928_; 
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
lean_inc(v_a_3927_);
lean_dec_ref(v___x_3926_);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc(v___y_3837_);
lean_inc_ref(v_body_3922_);
lean_inc_ref(v_post_3836_);
lean_inc_ref(v_pre_3834_);
v___x_3928_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3834_, v_post_3836_, v_body_3922_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; size_t v___x_3930_; size_t v___x_3931_; uint8_t v___x_3932_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
lean_dec_ref(v___x_3928_);
v___x_3930_ = lean_ptr_addr(v_type_3920_);
v___x_3931_ = lean_ptr_addr(v_a_3925_);
v___x_3932_ = lean_usize_dec_eq(v___x_3930_, v___x_3931_);
if (v___x_3932_ == 0)
{
v___y_3842_ = v_body_3922_;
v___y_3843_ = v_a_3929_;
v___y_3844_ = v_a_3927_;
v___y_3845_ = v___y_3890_;
v___y_3846_ = v_declName_3919_;
v___y_3847_ = v_nondep_3923_;
v___y_3848_ = v_a_3925_;
v___y_3849_ = v___x_3932_;
goto v___jp_3841_;
}
else
{
size_t v___x_3933_; size_t v___x_3934_; uint8_t v___x_3935_; 
v___x_3933_ = lean_ptr_addr(v_value_3921_);
v___x_3934_ = lean_ptr_addr(v_a_3927_);
v___x_3935_ = lean_usize_dec_eq(v___x_3933_, v___x_3934_);
v___y_3842_ = v_body_3922_;
v___y_3843_ = v_a_3929_;
v___y_3844_ = v_a_3927_;
v___y_3845_ = v___y_3890_;
v___y_3846_ = v_declName_3919_;
v___y_3847_ = v_nondep_3923_;
v___y_3848_ = v_a_3925_;
v___y_3849_ = v___x_3935_;
goto v___jp_3841_;
}
}
else
{
lean_dec(v_a_3927_);
lean_dec(v_a_3925_);
lean_dec_ref(v_body_3922_);
lean_dec(v_declName_3919_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v_post_3836_);
lean_dec_ref(v_pre_3834_);
return v___x_3928_;
}
}
else
{
lean_dec(v_a_3925_);
lean_dec_ref(v_body_3922_);
lean_dec_ref(v___y_3890_);
lean_dec(v_declName_3919_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v_post_3836_);
lean_dec_ref(v_pre_3834_);
return v___x_3926_;
}
}
else
{
lean_dec_ref(v_body_3922_);
lean_dec_ref(v___y_3890_);
lean_dec(v_declName_3919_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v_post_3836_);
lean_dec_ref(v_pre_3834_);
return v___x_3924_;
}
}
case 5:
{
lean_object* v_dummy_3936_; lean_object* v_nargs_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v_dummy_3936_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_3937_ = l_Lean_Expr_getAppNumArgs(v___y_3890_);
lean_inc(v_nargs_3937_);
v___x_3938_ = lean_mk_array(v_nargs_3937_, v_dummy_3936_);
v___x_3939_ = lean_unsigned_to_nat(1u);
v___x_3940_ = lean_nat_sub(v_nargs_3937_, v___x_3939_);
lean_dec(v_nargs_3937_);
v___x_3941_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_3834_, v_post_3836_, v___y_3890_, v___x_3938_, v___x_3940_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3941_;
}
case 10:
{
lean_object* v_data_3942_; lean_object* v_expr_3943_; lean_object* v___x_3944_; 
v_data_3942_ = lean_ctor_get(v___y_3890_, 0);
v_expr_3943_ = lean_ctor_get(v___y_3890_, 1);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc(v___y_3837_);
lean_inc_ref(v_expr_3943_);
lean_inc_ref(v_post_3836_);
lean_inc_ref(v_pre_3834_);
v___x_3944_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3834_, v_post_3836_, v_expr_3943_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v_a_3945_; size_t v___x_3946_; size_t v___x_3947_; uint8_t v___x_3948_; 
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_a_3945_);
lean_dec_ref(v___x_3944_);
v___x_3946_ = lean_ptr_addr(v_expr_3943_);
v___x_3947_ = lean_ptr_addr(v_a_3945_);
v___x_3948_ = lean_usize_dec_eq(v___x_3946_, v___x_3947_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
lean_inc(v_data_3942_);
lean_dec_ref(v___y_3890_);
v___x_3949_ = l_Lean_Expr_mdata___override(v_data_3942_, v_a_3945_);
v___x_3950_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v___x_3949_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3950_;
}
else
{
lean_object* v___x_3951_; 
lean_dec(v_a_3945_);
v___x_3951_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v___y_3890_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3951_;
}
}
else
{
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v_post_3836_);
lean_dec_ref(v_pre_3834_);
return v___x_3944_;
}
}
case 11:
{
lean_object* v_typeName_3952_; lean_object* v_idx_3953_; lean_object* v_struct_3954_; lean_object* v___x_3955_; 
v_typeName_3952_ = lean_ctor_get(v___y_3890_, 0);
v_idx_3953_ = lean_ctor_get(v___y_3890_, 1);
v_struct_3954_ = lean_ctor_get(v___y_3890_, 2);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc(v___y_3837_);
lean_inc_ref(v_struct_3954_);
lean_inc_ref(v_post_3836_);
lean_inc_ref(v_pre_3834_);
v___x_3955_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3834_, v_post_3836_, v_struct_3954_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; size_t v___x_3957_; size_t v___x_3958_; uint8_t v___x_3959_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3956_);
lean_dec_ref(v___x_3955_);
v___x_3957_ = lean_ptr_addr(v_struct_3954_);
v___x_3958_ = lean_ptr_addr(v_a_3956_);
v___x_3959_ = lean_usize_dec_eq(v___x_3957_, v___x_3958_);
if (v___x_3959_ == 0)
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
lean_inc(v_idx_3953_);
lean_inc(v_typeName_3952_);
lean_dec_ref(v___y_3890_);
v___x_3960_ = l_Lean_Expr_proj___override(v_typeName_3952_, v_idx_3953_, v_a_3956_);
v___x_3961_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v___x_3960_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3961_;
}
else
{
lean_object* v___x_3962_; 
lean_dec(v_a_3956_);
v___x_3962_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v___y_3890_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3962_;
}
}
else
{
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v_post_3836_);
lean_dec_ref(v_pre_3834_);
return v___x_3955_;
}
}
default: 
{
lean_object* v___x_3963_; 
v___x_3963_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v___y_3890_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3963_;
}
}
}
}
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v_post_3836_);
lean_dec_ref(v_e_3835_);
lean_dec_ref(v_pre_3834_);
v_a_3975_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3884_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3884_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
v___jp_3841_:
{
if (v___y_3849_ == 0)
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
lean_dec_ref(v___y_3845_);
lean_dec_ref(v___y_3842_);
v___x_3850_ = l_Lean_Expr_letE___override(v___y_3846_, v___y_3848_, v___y_3844_, v___y_3843_, v___y_3847_);
v___x_3851_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v___x_3850_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3851_;
}
else
{
size_t v___x_3852_; size_t v___x_3853_; uint8_t v___x_3854_; 
v___x_3852_ = lean_ptr_addr(v___y_3842_);
lean_dec_ref(v___y_3842_);
v___x_3853_ = lean_ptr_addr(v___y_3843_);
v___x_3854_ = lean_usize_dec_eq(v___x_3852_, v___x_3853_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
lean_dec_ref(v___y_3845_);
v___x_3855_ = l_Lean_Expr_letE___override(v___y_3846_, v___y_3848_, v___y_3844_, v___y_3843_, v___y_3847_);
v___x_3856_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v___x_3855_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3856_;
}
else
{
lean_object* v___x_3857_; 
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3844_);
lean_dec_ref(v___y_3843_);
v___x_3857_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v___y_3845_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3857_;
}
}
}
v___jp_3858_:
{
if (v___y_3864_ == 0)
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
lean_dec_ref(v___y_3862_);
v___x_3865_ = l_Lean_Expr_lam___override(v___y_3859_, v___y_3863_, v___y_3861_, v___y_3860_);
v___x_3866_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v___x_3865_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3866_;
}
else
{
uint8_t v___x_3867_; 
v___x_3867_ = l_Lean_instBEqBinderInfo_beq(v___y_3860_, v___y_3860_);
if (v___x_3867_ == 0)
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
lean_dec_ref(v___y_3862_);
v___x_3868_ = l_Lean_Expr_lam___override(v___y_3859_, v___y_3863_, v___y_3861_, v___y_3860_);
v___x_3869_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v___x_3868_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3869_;
}
else
{
lean_object* v___x_3870_; 
lean_dec_ref(v___y_3863_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3859_);
v___x_3870_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v___y_3862_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3870_;
}
}
}
v___jp_3871_:
{
if (v___y_3877_ == 0)
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
lean_dec_ref(v___y_3874_);
v___x_3878_ = l_Lean_Expr_forallE___override(v___y_3876_, v___y_3873_, v___y_3875_, v___y_3872_);
v___x_3879_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v___x_3878_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3879_;
}
else
{
uint8_t v___x_3880_; 
v___x_3880_ = l_Lean_instBEqBinderInfo_beq(v___y_3872_, v___y_3872_);
if (v___x_3880_ == 0)
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
lean_dec_ref(v___y_3874_);
v___x_3881_ = l_Lean_Expr_forallE___override(v___y_3876_, v___y_3873_, v___y_3875_, v___y_3872_);
v___x_3882_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v___x_3881_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3882_;
}
else
{
lean_object* v___x_3883_; 
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec_ref(v___y_3873_);
v___x_3883_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3834_, v_post_3836_, v___y_3874_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(lean_object* v_pre_3983_, lean_object* v_e_3984_, lean_object* v_post_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(v_pre_3983_, v_e_3984_, v_post_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(lean_object* v_pre_3991_, lean_object* v_post_3992_, lean_object* v_e_3993_, lean_object* v_a_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
lean_inc(v_a_3994_);
v___x_3998_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3998_, 0, lean_box(0));
lean_closure_set(v___x_3998_, 1, lean_box(0));
lean_closure_set(v___x_3998_, 2, v_a_3994_);
v___x_3999_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___x_3998_, v___y_3995_, v___y_3996_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4030_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4002_ = v___x_3999_;
v_isShared_4003_ = v_isSharedCheck_4030_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3999_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4030_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4004_; 
v___x_4004_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_4000_, v_e_3993_);
lean_dec(v_a_4000_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v___f_4005_; lean_object* v___x_4006_; 
lean_del_object(v___x_4002_);
lean_inc_ref(v_e_3993_);
v___f_4005_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4005_, 0, v_pre_3991_);
lean_closure_set(v___f_4005_, 1, v_e_3993_);
lean_closure_set(v___f_4005_, 2, v_post_3992_);
lean_inc(v___y_3996_);
lean_inc_ref(v___y_3995_);
lean_inc(v_a_3994_);
v___x_4006_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v___f_4005_, v_a_3994_, v___y_3995_, v___y_3996_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v___f_4008_; lean_object* v___x_4009_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref(v___x_4006_);
lean_inc(v_a_4007_);
v___f_4008_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4008_, 0, v_a_3994_);
lean_closure_set(v___f_4008_, 1, v_e_3993_);
lean_closure_set(v___f_4008_, 2, v_a_4007_);
v___x_4009_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___f_4008_, v___y_3995_, v___y_3996_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4016_ == 0)
{
lean_object* v_unused_4017_; 
v_unused_4017_ = lean_ctor_get(v___x_4009_, 0);
lean_dec(v_unused_4017_);
v___x_4011_ = v___x_4009_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_dec(v___x_4009_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v_a_4007_);
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4007_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
lean_dec(v_a_4007_);
v_a_4018_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_4009_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4009_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
else
{
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v_a_3994_);
lean_dec_ref(v_e_3993_);
return v___x_4006_;
}
}
else
{
lean_object* v_val_4026_; lean_object* v___x_4028_; 
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v_a_3994_);
lean_dec_ref(v_e_3993_);
lean_dec_ref(v_post_3992_);
lean_dec_ref(v_pre_3991_);
v_val_4026_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_val_4026_);
lean_dec_ref(v___x_4004_);
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 0, v_val_4026_);
v___x_4028_ = v___x_4002_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_val_4026_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v_a_3994_);
lean_dec_ref(v_e_3993_);
lean_dec_ref(v_post_3992_);
lean_dec_ref(v_pre_3991_);
v_a_4031_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_3999_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_3999_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(lean_object* v_pre_4039_, lean_object* v_post_4040_, lean_object* v_e_4041_, lean_object* v_a_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v___x_4046_; 
lean_inc_ref(v_post_4040_);
lean_inc(v___y_4044_);
lean_inc_ref(v___y_4043_);
lean_inc_ref(v_e_4041_);
v___x_4046_ = lean_apply_4(v_post_4040_, v_e_4041_, v___y_4043_, v___y_4044_, lean_box(0));
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4065_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4065_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4065_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
switch(lean_obj_tag(v_a_4047_))
{
case 0:
{
lean_object* v_e_4051_; lean_object* v___x_4053_; 
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v_a_4042_);
lean_dec_ref(v_e_4041_);
lean_dec_ref(v_post_4040_);
lean_dec_ref(v_pre_4039_);
v_e_4051_ = lean_ctor_get(v_a_4047_, 0);
lean_inc_ref(v_e_4051_);
lean_dec_ref(v_a_4047_);
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v_e_4051_);
v___x_4053_ = v___x_4049_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_e_4051_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
case 1:
{
lean_object* v_e_4055_; lean_object* v___x_4056_; 
lean_del_object(v___x_4049_);
lean_dec_ref(v_e_4041_);
v_e_4055_ = lean_ctor_get(v_a_4047_, 0);
lean_inc_ref(v_e_4055_);
lean_dec_ref(v_a_4047_);
v___x_4056_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4039_, v_post_4040_, v_e_4055_, v_a_4042_, v___y_4043_, v___y_4044_);
return v___x_4056_;
}
default: 
{
lean_object* v_e_x3f_4057_; 
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v_a_4042_);
lean_dec_ref(v_post_4040_);
lean_dec_ref(v_pre_4039_);
v_e_x3f_4057_ = lean_ctor_get(v_a_4047_, 0);
lean_inc(v_e_x3f_4057_);
lean_dec_ref(v_a_4047_);
if (lean_obj_tag(v_e_x3f_4057_) == 0)
{
lean_object* v___x_4059_; 
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v_e_4041_);
v___x_4059_ = v___x_4049_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_e_4041_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
else
{
lean_object* v_val_4061_; lean_object* v___x_4063_; 
lean_dec_ref(v_e_4041_);
v_val_4061_ = lean_ctor_get(v_e_x3f_4057_, 0);
lean_inc(v_val_4061_);
lean_dec_ref(v_e_x3f_4057_);
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v_val_4061_);
v___x_4063_ = v___x_4049_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_val_4061_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
}
}
else
{
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4073_; 
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v_a_4042_);
lean_dec_ref(v_e_4041_);
lean_dec_ref(v_post_4040_);
lean_dec_ref(v_pre_4039_);
v_a_4066_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4068_ = v___x_4046_;
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v___x_4046_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4071_; 
if (v_isShared_4069_ == 0)
{
v___x_4071_ = v___x_4068_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4066_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4074_, lean_object* v_post_4075_, lean_object* v_e_4076_, lean_object* v_a_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4074_, v_post_4075_, v_e_4076_, v_a_4077_, v___y_4078_, v___y_4079_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4082_, lean_object* v_post_4083_, lean_object* v_sz_4084_, lean_object* v_i_4085_, lean_object* v_bs_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
size_t v_sz_boxed_4091_; size_t v_i_boxed_4092_; lean_object* v_res_4093_; 
v_sz_boxed_4091_ = lean_unbox_usize(v_sz_4084_);
lean_dec(v_sz_4084_);
v_i_boxed_4092_ = lean_unbox_usize(v_i_4085_);
lean_dec(v_i_4085_);
v_res_4093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_4082_, v_post_4083_, v_sz_boxed_4091_, v_i_boxed_4092_, v_bs_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___boxed(lean_object* v_pre_4094_, lean_object* v_post_4095_, lean_object* v_x_4096_, lean_object* v_x_4097_, lean_object* v_x_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_4094_, v_post_4095_, v_x_4096_, v_x_4097_, v_x_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___boxed(lean_object* v_pre_4104_, lean_object* v_post_4105_, lean_object* v_e_4106_, lean_object* v_a_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4104_, v_post_4105_, v_e_4106_, v_a_4107_, v___y_4108_, v___y_4109_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_object* v_00_u03b1_4112_, lean_object* v_x_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4117_ = lean_apply_1(v_x_4113_, lean_box(0));
v___x_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0___boxed(lean_object* v_00_u03b1_4119_, lean_object* v_x_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(v_00_u03b1_4119_, v_x_4120_, v___y_4121_, v___y_4122_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(lean_object* v_input_4125_, lean_object* v_pre_4126_, lean_object* v_post_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v_a_4133_; lean_object* v___x_4134_; 
v___x_4131_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_4132_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_4131_, v___y_4128_, v___y_4129_);
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_a_4133_);
lean_dec_ref(v___x_4132_);
lean_inc(v___y_4129_);
lean_inc_ref(v___y_4128_);
lean_inc(v_a_4133_);
v___x_4134_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4126_, v_post_4127_, v_input_4125_, v_a_4133_, v___y_4128_, v___y_4129_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4135_);
lean_dec_ref(v___x_4134_);
v___x_4136_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4136_, 0, lean_box(0));
lean_closure_set(v___x_4136_, 1, lean_box(0));
lean_closure_set(v___x_4136_, 2, v_a_4133_);
v___x_4137_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_4136_, v___y_4128_, v___y_4129_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4144_ == 0)
{
lean_object* v_unused_4145_; 
v_unused_4145_ = lean_ctor_get(v___x_4137_, 0);
lean_dec(v_unused_4145_);
v___x_4139_ = v___x_4137_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_dec(v___x_4137_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 0, v_a_4135_);
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4135_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
else
{
lean_dec(v_a_4133_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
return v___x_4134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___boxed(lean_object* v_input_4146_, lean_object* v_pre_4147_, lean_object* v_post_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_input_4146_, v_pre_4147_, v_post_4148_, v___y_4149_, v___y_4150_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object* v_e_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
uint8_t v___x_4159_; 
v___x_4159_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_4155_);
if (v___x_4159_ == 0)
{
lean_object* v_pre_4160_; lean_object* v___f_4161_; lean_object* v___x_4162_; 
v_pre_4160_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__0));
v___f_4161_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__1));
v___x_4162_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_e_4155_, v_pre_4160_, v___f_4161_, v_a_4156_, v_a_4157_);
return v___x_4162_;
}
else
{
lean_object* v___x_4163_; 
lean_dec(v_a_4157_);
lean_dec_ref(v_a_4156_);
v___x_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4163_, 0, v_e_4155_);
return v___x_4163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___boxed(lean_object* v_e_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Lean_Meta_Sym_normalizeLevels(v_e_4164_, v_a_4165_, v_a_4166_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4169_, lean_object* v_ref_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v___x_4174_; 
v___x_4174_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_4170_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4175_, lean_object* v_ref_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4175_, v_ref_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(lean_object* v_00_u03b1_4181_, lean_object* v_x_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v_x_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b1_4188_, lean_object* v_x_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_00_u03b1_4188_, v_x_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v_res_4194_;
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
