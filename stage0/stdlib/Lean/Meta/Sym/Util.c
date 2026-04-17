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
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
size_t v_x_9235__boxed_1824_; size_t v_x_9236__boxed_1825_; lean_object* v_res_1826_; 
v_x_9235__boxed_1824_ = lean_unbox_usize(v_x_1820_);
lean_dec(v_x_1820_);
v_x_9236__boxed_1825_ = lean_unbox_usize(v_x_1821_);
lean_dec(v_x_1821_);
v_res_1826_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_1819_, v_x_9235__boxed_1824_, v_x_9236__boxed_1825_, v_x_1822_, v_x_1823_);
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
lean_object* v_cs_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; size_t v_sz_2115_; size_t v___x_2116_; lean_object* v___x_2117_; 
v_cs_2112_ = lean_ctor_get(v_n_2103_, 0);
v___x_2113_ = lean_box(0);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v_b_2104_);
v_sz_2115_ = lean_array_size(v_cs_2112_);
v___x_2116_ = ((size_t)0ULL);
v___x_2117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_2102_, v_cs_2112_, v_sz_2115_, v___x_2116_, v___x_2114_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2132_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2132_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2132_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v_fst_2122_; 
v_fst_2122_ = lean_ctor_get(v_a_2118_, 0);
if (lean_obj_tag(v_fst_2122_) == 0)
{
lean_object* v_snd_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v_snd_2123_ = lean_ctor_get(v_a_2118_, 1);
lean_inc(v_snd_2123_);
lean_dec(v_a_2118_);
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v_snd_2123_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2124_);
v___x_2126_ = v___x_2120_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
else
{
lean_object* v_val_2128_; lean_object* v___x_2130_; 
lean_inc_ref(v_fst_2122_);
lean_dec(v_a_2118_);
v_val_2128_ = lean_ctor_get(v_fst_2122_, 0);
lean_inc(v_val_2128_);
lean_dec_ref(v_fst_2122_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v_val_2128_);
v___x_2130_ = v___x_2120_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_val_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
v_a_2133_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2117_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2117_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
else
{
lean_object* v_vs_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; size_t v_sz_2144_; size_t v___x_2145_; lean_object* v___x_2146_; 
v_vs_2141_ = lean_ctor_get(v_n_2103_, 0);
v___x_2142_ = lean_box(0);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v_b_2104_);
v_sz_2144_ = lean_array_size(v_vs_2141_);
v___x_2145_ = ((size_t)0ULL);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_vs_2141_, v_sz_2144_, v___x_2145_, v___x_2143_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2161_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2149_ = v___x_2146_;
v_isShared_2150_ = v_isSharedCheck_2161_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2146_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2161_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v_fst_2151_; 
v_fst_2151_ = lean_ctor_get(v_a_2147_, 0);
if (lean_obj_tag(v_fst_2151_) == 0)
{
lean_object* v_snd_2152_; lean_object* v___x_2153_; lean_object* v___x_2155_; 
v_snd_2152_ = lean_ctor_get(v_a_2147_, 1);
lean_inc(v_snd_2152_);
lean_dec(v_a_2147_);
v___x_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_snd_2152_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2153_);
v___x_2155_ = v___x_2149_;
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
else
{
lean_object* v_val_2157_; lean_object* v___x_2159_; 
lean_inc_ref(v_fst_2151_);
lean_dec(v_a_2147_);
v_val_2157_ = lean_ctor_get(v_fst_2151_, 0);
lean_inc(v_val_2157_);
lean_dec_ref(v_fst_2151_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v_val_2157_);
v___x_2159_ = v___x_2149_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_val_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
v_a_2162_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2146_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2146_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(lean_object* v_init_2170_, lean_object* v_as_2171_, size_t v_sz_2172_, size_t v_i_2173_, lean_object* v_b_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
uint8_t v___x_2182_; 
v___x_2182_ = lean_usize_dec_lt(v_i_2173_, v_sz_2172_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v_b_2174_);
return v___x_2183_;
}
else
{
lean_object* v_snd_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2218_; 
v_snd_2184_ = lean_ctor_get(v_b_2174_, 1);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_b_2174_);
if (v_isSharedCheck_2218_ == 0)
{
lean_object* v_unused_2219_; 
v_unused_2219_ = lean_ctor_get(v_b_2174_, 0);
lean_dec(v_unused_2219_);
v___x_2186_ = v_b_2174_;
v_isShared_2187_ = v_isSharedCheck_2218_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snd_2184_);
lean_dec(v_b_2174_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2218_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v_a_2188_; lean_object* v___x_2189_; 
v_a_2188_ = lean_array_uget_borrowed(v_as_2171_, v_i_2173_);
lean_inc(v_snd_2184_);
v___x_2189_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_2170_, v_a_2188_, v_snd_2184_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2209_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2209_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2209_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
if (lean_obj_tag(v_a_2190_) == 0)
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v_a_2190_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2194_);
v___x_2196_ = v___x_2186_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_snd_2184_);
v___x_2196_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2198_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v___x_2196_);
v___x_2198_ = v___x_2192_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2202_; lean_object* v___x_2204_; 
lean_del_object(v___x_2192_);
lean_dec(v_snd_2184_);
v_a_2201_ = lean_ctor_get(v_a_2190_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v_a_2190_);
v___x_2202_ = lean_box(0);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 1, v_a_2201_);
lean_ctor_set(v___x_2186_, 0, v___x_2202_);
v___x_2204_ = v___x_2186_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2202_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_a_2201_);
v___x_2204_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
size_t v___x_2205_; size_t v___x_2206_; 
v___x_2205_ = ((size_t)1ULL);
v___x_2206_ = lean_usize_add(v_i_2173_, v___x_2205_);
v_i_2173_ = v___x_2206_;
v_b_2174_ = v___x_2204_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_del_object(v___x_2186_);
lean_dec(v_snd_2184_);
v_a_2210_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2189_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2189_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_init_2220_, lean_object* v_as_2221_, lean_object* v_sz_2222_, lean_object* v_i_2223_, lean_object* v_b_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
size_t v_sz_boxed_2232_; size_t v_i_boxed_2233_; lean_object* v_res_2234_; 
v_sz_boxed_2232_ = lean_unbox_usize(v_sz_2222_);
lean_dec(v_sz_2222_);
v_i_boxed_2233_ = lean_unbox_usize(v_i_2223_);
lean_dec(v_i_2223_);
v_res_2234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_2220_, v_as_2221_, v_sz_boxed_2232_, v_i_boxed_2233_, v_b_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec_ref(v_as_2221_);
lean_dec_ref(v_init_2220_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2___boxed(lean_object* v_init_2235_, lean_object* v_n_2236_, lean_object* v_b_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_2235_, v_n_2236_, v_b_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec_ref(v_n_2236_);
lean_dec_ref(v_init_2235_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(lean_object* v_as_2246_, size_t v_sz_2247_, size_t v_i_2248_, lean_object* v_b_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
uint8_t v___x_2257_; 
v___x_2257_ = lean_usize_dec_lt(v_i_2248_, v_sz_2247_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v_b_2249_);
return v___x_2258_;
}
else
{
lean_object* v_snd_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2364_; 
v_snd_2259_ = lean_ctor_get(v_b_2249_, 1);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_b_2249_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; 
v_unused_2365_ = lean_ctor_get(v_b_2249_, 0);
lean_dec(v_unused_2365_);
v___x_2261_ = v_b_2249_;
v_isShared_2262_ = v_isSharedCheck_2364_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_snd_2259_);
lean_dec(v_b_2249_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2364_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2263_; lean_object* v_a_2265_; lean_object* v_a_2272_; 
v___x_2263_ = lean_box(0);
v_a_2272_ = lean_array_uget(v_as_2246_, v_i_2248_);
if (lean_obj_tag(v_a_2272_) == 0)
{
v_a_2265_ = v_snd_2259_;
goto v___jp_2264_;
}
else
{
lean_object* v_snd_2273_; lean_object* v_val_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2363_; 
v_snd_2273_ = lean_ctor_get(v_snd_2259_, 1);
lean_inc(v_snd_2273_);
v_val_2274_ = lean_ctor_get(v_a_2272_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_a_2272_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2276_ = v_a_2272_;
v_isShared_2277_ = v_isSharedCheck_2363_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_val_2274_);
lean_dec(v_a_2272_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2363_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v_fst_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2361_; 
v_fst_2278_ = lean_ctor_get(v_snd_2259_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_snd_2259_);
if (v_isSharedCheck_2361_ == 0)
{
lean_object* v_unused_2362_; 
v_unused_2362_ = lean_ctor_get(v_snd_2259_, 1);
lean_dec(v_unused_2362_);
v___x_2280_ = v_snd_2259_;
v_isShared_2281_ = v_isSharedCheck_2361_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_fst_2278_);
lean_dec(v_snd_2259_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2361_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v_fst_2282_; lean_object* v_snd_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2360_; 
v_fst_2282_ = lean_ctor_get(v_snd_2273_, 0);
v_snd_2283_ = lean_ctor_get(v_snd_2273_, 1);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_snd_2273_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2285_ = v_snd_2273_;
v_isShared_2286_ = v_isSharedCheck_2360_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_snd_2283_);
lean_inc(v_fst_2282_);
lean_dec(v_snd_2273_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2360_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v_decl_2288_; 
if (lean_obj_tag(v_val_2274_) == 0)
{
lean_object* v_fvarId_2303_; lean_object* v_userName_2304_; lean_object* v_type_2305_; uint8_t v_bi_2306_; uint8_t v_kind_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2324_; 
v_fvarId_2303_ = lean_ctor_get(v_val_2274_, 1);
v_userName_2304_ = lean_ctor_get(v_val_2274_, 2);
v_type_2305_ = lean_ctor_get(v_val_2274_, 3);
v_bi_2306_ = lean_ctor_get_uint8(v_val_2274_, sizeof(void*)*4);
v_kind_2307_ = lean_ctor_get_uint8(v_val_2274_, sizeof(void*)*4 + 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_val_2274_);
if (v_isSharedCheck_2324_ == 0)
{
lean_object* v_unused_2325_; 
v_unused_2325_ = lean_ctor_get(v_val_2274_, 0);
lean_dec(v_unused_2325_);
v___x_2309_ = v_val_2274_;
v_isShared_2310_ = v_isSharedCheck_2324_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_type_2305_);
lean_inc(v_userName_2304_);
lean_inc(v_fvarId_2303_);
lean_dec(v_val_2274_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2324_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; 
v___x_2311_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2305_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref(v___x_2311_);
lean_inc(v_snd_2283_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 3, v_a_2312_);
lean_ctor_set(v___x_2309_, 0, v_snd_2283_);
v___x_2314_ = v___x_2309_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_snd_2283_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_fvarId_2303_);
lean_ctor_set(v_reuseFailAlloc_2315_, 2, v_userName_2304_);
lean_ctor_set(v_reuseFailAlloc_2315_, 3, v_a_2312_);
lean_ctor_set_uint8(v_reuseFailAlloc_2315_, sizeof(void*)*4, v_bi_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2315_, sizeof(void*)*4 + 1, v_kind_2307_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
v_decl_2288_ = v___x_2314_;
goto v___jp_2287_;
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_del_object(v___x_2309_);
lean_dec(v_userName_2304_);
lean_dec(v_fvarId_2303_);
lean_del_object(v___x_2285_);
lean_dec(v_snd_2283_);
lean_dec(v_fst_2282_);
lean_del_object(v___x_2280_);
lean_dec(v_fst_2278_);
lean_del_object(v___x_2276_);
lean_del_object(v___x_2261_);
v_a_2316_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2311_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2311_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2326_; lean_object* v_userName_2327_; lean_object* v_type_2328_; lean_object* v_value_2329_; uint8_t v_nondep_2330_; uint8_t v_kind_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2358_; 
v_fvarId_2326_ = lean_ctor_get(v_val_2274_, 1);
v_userName_2327_ = lean_ctor_get(v_val_2274_, 2);
v_type_2328_ = lean_ctor_get(v_val_2274_, 3);
v_value_2329_ = lean_ctor_get(v_val_2274_, 4);
v_nondep_2330_ = lean_ctor_get_uint8(v_val_2274_, sizeof(void*)*5);
v_kind_2331_ = lean_ctor_get_uint8(v_val_2274_, sizeof(void*)*5 + 1);
v_isSharedCheck_2358_ = !lean_is_exclusive(v_val_2274_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v_val_2274_, 0);
lean_dec(v_unused_2359_);
v___x_2333_ = v_val_2274_;
v_isShared_2334_ = v_isSharedCheck_2358_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_value_2329_);
lean_inc(v_type_2328_);
lean_inc(v_userName_2327_);
lean_inc(v_fvarId_2326_);
lean_dec(v_val_2274_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2358_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; 
v___x_2335_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2328_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref(v___x_2335_);
v___x_2337_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2329_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2340_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref(v___x_2337_);
lean_inc(v_snd_2283_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 4, v_a_2338_);
lean_ctor_set(v___x_2333_, 3, v_a_2336_);
lean_ctor_set(v___x_2333_, 0, v_snd_2283_);
v___x_2340_ = v___x_2333_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_snd_2283_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_fvarId_2326_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_userName_2327_);
lean_ctor_set(v_reuseFailAlloc_2341_, 3, v_a_2336_);
lean_ctor_set(v_reuseFailAlloc_2341_, 4, v_a_2338_);
lean_ctor_set_uint8(v_reuseFailAlloc_2341_, sizeof(void*)*5, v_nondep_2330_);
lean_ctor_set_uint8(v_reuseFailAlloc_2341_, sizeof(void*)*5 + 1, v_kind_2331_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
v_decl_2288_ = v___x_2340_;
goto v___jp_2287_;
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_a_2336_);
lean_del_object(v___x_2333_);
lean_dec(v_userName_2327_);
lean_dec(v_fvarId_2326_);
lean_del_object(v___x_2285_);
lean_dec(v_snd_2283_);
lean_dec(v_fst_2282_);
lean_del_object(v___x_2280_);
lean_dec(v_fst_2278_);
lean_del_object(v___x_2276_);
lean_del_object(v___x_2261_);
v_a_2342_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2337_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2337_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_del_object(v___x_2333_);
lean_dec_ref(v_value_2329_);
lean_dec(v_userName_2327_);
lean_dec(v_fvarId_2326_);
lean_del_object(v___x_2285_);
lean_dec(v_snd_2283_);
lean_dec(v_fst_2282_);
lean_del_object(v___x_2280_);
lean_dec(v_fst_2278_);
lean_del_object(v___x_2276_);
lean_del_object(v___x_2261_);
v_a_2350_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2335_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2335_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
v___jp_2287_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2289_ = lean_unsigned_to_nat(1u);
v___x_2290_ = lean_nat_add(v_snd_2283_, v___x_2289_);
lean_dec(v_snd_2283_);
lean_inc_ref(v_decl_2288_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v_decl_2288_);
v___x_2292_ = v___x_2276_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_decl_2288_);
v___x_2292_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2293_ = l_Lean_PersistentArray_push___redArg(v_fst_2282_, v___x_2292_);
v___x_2294_ = l_Lean_LocalDecl_fvarId(v_decl_2288_);
v___x_2295_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2278_, v___x_2294_, v_decl_2288_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 1, v___x_2290_);
lean_ctor_set(v___x_2285_, 0, v___x_2293_);
v___x_2297_ = v___x_2285_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2293_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v___x_2290_);
v___x_2297_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2299_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 1, v___x_2297_);
lean_ctor_set(v___x_2280_, 0, v___x_2295_);
v___x_2299_ = v___x_2280_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
v_a_2265_ = v___x_2299_;
goto v___jp_2264_;
}
}
}
}
}
}
}
}
v___jp_2264_:
{
lean_object* v___x_2267_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 1, v_a_2265_);
lean_ctor_set(v___x_2261_, 0, v___x_2263_);
v___x_2267_ = v___x_2261_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_a_2265_);
v___x_2267_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
size_t v___x_2268_; size_t v___x_2269_; 
v___x_2268_ = ((size_t)1ULL);
v___x_2269_ = lean_usize_add(v_i_2248_, v___x_2268_);
v_i_2248_ = v___x_2269_;
v_b_2249_ = v___x_2267_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8___boxed(lean_object* v_as_2366_, lean_object* v_sz_2367_, lean_object* v_i_2368_, lean_object* v_b_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
size_t v_sz_boxed_2377_; size_t v_i_boxed_2378_; lean_object* v_res_2379_; 
v_sz_boxed_2377_ = lean_unbox_usize(v_sz_2367_);
lean_dec(v_sz_2367_);
v_i_boxed_2378_ = lean_unbox_usize(v_i_2368_);
lean_dec(v_i_2368_);
v_res_2379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_2366_, v_sz_boxed_2377_, v_i_boxed_2378_, v_b_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec_ref(v_as_2366_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(lean_object* v_as_2380_, size_t v_sz_2381_, size_t v_i_2382_, lean_object* v_b_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_usize_dec_lt(v_i_2382_, v_sz_2381_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v_b_2383_);
return v___x_2392_;
}
else
{
lean_object* v_snd_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2498_; 
v_snd_2393_ = lean_ctor_get(v_b_2383_, 1);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_b_2383_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; 
v_unused_2499_ = lean_ctor_get(v_b_2383_, 0);
lean_dec(v_unused_2499_);
v___x_2395_ = v_b_2383_;
v_isShared_2396_ = v_isSharedCheck_2498_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_snd_2393_);
lean_dec(v_b_2383_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2498_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2397_; lean_object* v_a_2399_; lean_object* v_a_2406_; 
v___x_2397_ = lean_box(0);
v_a_2406_ = lean_array_uget(v_as_2380_, v_i_2382_);
if (lean_obj_tag(v_a_2406_) == 0)
{
v_a_2399_ = v_snd_2393_;
goto v___jp_2398_;
}
else
{
lean_object* v_snd_2407_; lean_object* v_val_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2497_; 
v_snd_2407_ = lean_ctor_get(v_snd_2393_, 1);
lean_inc(v_snd_2407_);
v_val_2408_ = lean_ctor_get(v_a_2406_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_a_2406_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2410_ = v_a_2406_;
v_isShared_2411_ = v_isSharedCheck_2497_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_val_2408_);
lean_dec(v_a_2406_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2497_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v_fst_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2495_; 
v_fst_2412_ = lean_ctor_get(v_snd_2393_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_snd_2393_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; 
v_unused_2496_ = lean_ctor_get(v_snd_2393_, 1);
lean_dec(v_unused_2496_);
v___x_2414_ = v_snd_2393_;
v_isShared_2415_ = v_isSharedCheck_2495_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_fst_2412_);
lean_dec(v_snd_2393_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2495_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v_fst_2416_; lean_object* v_snd_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2494_; 
v_fst_2416_ = lean_ctor_get(v_snd_2407_, 0);
v_snd_2417_ = lean_ctor_get(v_snd_2407_, 1);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_snd_2407_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2419_ = v_snd_2407_;
v_isShared_2420_ = v_isSharedCheck_2494_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_snd_2417_);
lean_inc(v_fst_2416_);
lean_dec(v_snd_2407_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2494_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v_decl_2422_; 
if (lean_obj_tag(v_val_2408_) == 0)
{
lean_object* v_fvarId_2437_; lean_object* v_userName_2438_; lean_object* v_type_2439_; uint8_t v_bi_2440_; uint8_t v_kind_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2458_; 
v_fvarId_2437_ = lean_ctor_get(v_val_2408_, 1);
v_userName_2438_ = lean_ctor_get(v_val_2408_, 2);
v_type_2439_ = lean_ctor_get(v_val_2408_, 3);
v_bi_2440_ = lean_ctor_get_uint8(v_val_2408_, sizeof(void*)*4);
v_kind_2441_ = lean_ctor_get_uint8(v_val_2408_, sizeof(void*)*4 + 1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_val_2408_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; 
v_unused_2459_ = lean_ctor_get(v_val_2408_, 0);
lean_dec(v_unused_2459_);
v___x_2443_ = v_val_2408_;
v_isShared_2444_ = v_isSharedCheck_2458_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_type_2439_);
lean_inc(v_userName_2438_);
lean_inc(v_fvarId_2437_);
lean_dec(v_val_2408_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2458_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; 
v___x_2445_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2439_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref(v___x_2445_);
lean_inc(v_snd_2417_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 3, v_a_2446_);
lean_ctor_set(v___x_2443_, 0, v_snd_2417_);
v___x_2448_ = v___x_2443_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_snd_2417_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_fvarId_2437_);
lean_ctor_set(v_reuseFailAlloc_2449_, 2, v_userName_2438_);
lean_ctor_set(v_reuseFailAlloc_2449_, 3, v_a_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2449_, sizeof(void*)*4, v_bi_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2449_, sizeof(void*)*4 + 1, v_kind_2441_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
v_decl_2422_ = v___x_2448_;
goto v___jp_2421_;
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_del_object(v___x_2443_);
lean_dec(v_userName_2438_);
lean_dec(v_fvarId_2437_);
lean_del_object(v___x_2419_);
lean_dec(v_snd_2417_);
lean_dec(v_fst_2416_);
lean_del_object(v___x_2414_);
lean_dec(v_fst_2412_);
lean_del_object(v___x_2410_);
lean_del_object(v___x_2395_);
v_a_2450_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2445_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2445_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2460_; lean_object* v_userName_2461_; lean_object* v_type_2462_; lean_object* v_value_2463_; uint8_t v_nondep_2464_; uint8_t v_kind_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2492_; 
v_fvarId_2460_ = lean_ctor_get(v_val_2408_, 1);
v_userName_2461_ = lean_ctor_get(v_val_2408_, 2);
v_type_2462_ = lean_ctor_get(v_val_2408_, 3);
v_value_2463_ = lean_ctor_get(v_val_2408_, 4);
v_nondep_2464_ = lean_ctor_get_uint8(v_val_2408_, sizeof(void*)*5);
v_kind_2465_ = lean_ctor_get_uint8(v_val_2408_, sizeof(void*)*5 + 1);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_val_2408_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; 
v_unused_2493_ = lean_ctor_get(v_val_2408_, 0);
lean_dec(v_unused_2493_);
v___x_2467_ = v_val_2408_;
v_isShared_2468_ = v_isSharedCheck_2492_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_value_2463_);
lean_inc(v_type_2462_);
lean_inc(v_userName_2461_);
lean_inc(v_fvarId_2460_);
lean_dec(v_val_2408_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2492_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; 
v___x_2469_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2462_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2471_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref(v___x_2469_);
v___x_2471_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2463_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2474_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref(v___x_2471_);
lean_inc(v_snd_2417_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 4, v_a_2472_);
lean_ctor_set(v___x_2467_, 3, v_a_2470_);
lean_ctor_set(v___x_2467_, 0, v_snd_2417_);
v___x_2474_ = v___x_2467_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_snd_2417_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_fvarId_2460_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_userName_2461_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_a_2470_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_a_2472_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, sizeof(void*)*5, v_nondep_2464_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, sizeof(void*)*5 + 1, v_kind_2465_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
v_decl_2422_ = v___x_2474_;
goto v___jp_2421_;
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec(v_a_2470_);
lean_del_object(v___x_2467_);
lean_dec(v_userName_2461_);
lean_dec(v_fvarId_2460_);
lean_del_object(v___x_2419_);
lean_dec(v_snd_2417_);
lean_dec(v_fst_2416_);
lean_del_object(v___x_2414_);
lean_dec(v_fst_2412_);
lean_del_object(v___x_2410_);
lean_del_object(v___x_2395_);
v_a_2476_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2471_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2471_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_del_object(v___x_2467_);
lean_dec_ref(v_value_2463_);
lean_dec(v_userName_2461_);
lean_dec(v_fvarId_2460_);
lean_del_object(v___x_2419_);
lean_dec(v_snd_2417_);
lean_dec(v_fst_2416_);
lean_del_object(v___x_2414_);
lean_dec(v_fst_2412_);
lean_del_object(v___x_2410_);
lean_del_object(v___x_2395_);
v_a_2484_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2469_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2469_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
v___jp_2421_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2423_ = lean_unsigned_to_nat(1u);
v___x_2424_ = lean_nat_add(v_snd_2417_, v___x_2423_);
lean_dec(v_snd_2417_);
lean_inc_ref(v_decl_2422_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v_decl_2422_);
v___x_2426_ = v___x_2410_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_decl_2422_);
v___x_2426_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2427_ = l_Lean_PersistentArray_push___redArg(v_fst_2416_, v___x_2426_);
v___x_2428_ = l_Lean_LocalDecl_fvarId(v_decl_2422_);
v___x_2429_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2412_, v___x_2428_, v_decl_2422_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 1, v___x_2424_);
lean_ctor_set(v___x_2419_, 0, v___x_2427_);
v___x_2431_ = v___x_2419_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v___x_2424_);
v___x_2431_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2433_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 1, v___x_2431_);
lean_ctor_set(v___x_2414_, 0, v___x_2429_);
v___x_2433_ = v___x_2414_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
v_a_2399_ = v___x_2433_;
goto v___jp_2398_;
}
}
}
}
}
}
}
}
v___jp_2398_:
{
lean_object* v___x_2401_; 
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 1, v_a_2399_);
lean_ctor_set(v___x_2395_, 0, v___x_2397_);
v___x_2401_ = v___x_2395_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2397_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_a_2399_);
v___x_2401_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
size_t v___x_2402_; size_t v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = ((size_t)1ULL);
v___x_2403_ = lean_usize_add(v_i_2382_, v___x_2402_);
v___x_2404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_2380_, v_sz_2381_, v___x_2403_, v___x_2401_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
return v___x_2404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3___boxed(lean_object* v_as_2500_, lean_object* v_sz_2501_, lean_object* v_i_2502_, lean_object* v_b_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
size_t v_sz_boxed_2511_; size_t v_i_boxed_2512_; lean_object* v_res_2513_; 
v_sz_boxed_2511_ = lean_unbox_usize(v_sz_2501_);
lean_dec(v_sz_2501_);
v_i_boxed_2512_ = lean_unbox_usize(v_i_2502_);
lean_dec(v_i_2502_);
v_res_2513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_as_2500_, v_sz_boxed_2511_, v_i_boxed_2512_, v_b_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec_ref(v_as_2500_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(lean_object* v_t_2514_, lean_object* v_init_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_root_2523_; lean_object* v_tail_2524_; lean_object* v___x_2525_; 
v_root_2523_ = lean_ctor_get(v_t_2514_, 0);
v_tail_2524_ = lean_ctor_get(v_t_2514_, 1);
lean_inc_ref(v_init_2515_);
v___x_2525_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_2515_, v_root_2523_, v_init_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec_ref(v_init_2515_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2562_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2562_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2562_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
if (lean_obj_tag(v_a_2526_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; 
v_a_2530_ = lean_ctor_get(v_a_2526_, 0);
lean_inc(v_a_2530_);
lean_dec_ref(v_a_2526_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v_a_2530_);
v___x_2532_ = v___x_2528_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; size_t v_sz_2537_; size_t v___x_2538_; lean_object* v___x_2539_; 
lean_del_object(v___x_2528_);
v_a_2534_ = lean_ctor_get(v_a_2526_, 0);
lean_inc(v_a_2534_);
lean_dec_ref(v_a_2526_);
v___x_2535_ = lean_box(0);
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
lean_ctor_set(v___x_2536_, 1, v_a_2534_);
v_sz_2537_ = lean_array_size(v_tail_2524_);
v___x_2538_ = ((size_t)0ULL);
v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_tail_2524_, v_sz_2537_, v___x_2538_, v___x_2536_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2553_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2553_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2553_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v_fst_2544_; 
v_fst_2544_ = lean_ctor_get(v_a_2540_, 0);
if (lean_obj_tag(v_fst_2544_) == 0)
{
lean_object* v_snd_2545_; lean_object* v___x_2547_; 
v_snd_2545_ = lean_ctor_get(v_a_2540_, 1);
lean_inc(v_snd_2545_);
lean_dec(v_a_2540_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v_snd_2545_);
v___x_2547_ = v___x_2542_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_snd_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
else
{
lean_object* v_val_2549_; lean_object* v___x_2551_; 
lean_inc_ref(v_fst_2544_);
lean_dec(v_a_2540_);
v_val_2549_ = lean_ctor_get(v_fst_2544_, 0);
lean_inc(v_val_2549_);
lean_dec_ref(v_fst_2544_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v_val_2549_);
v___x_2551_ = v___x_2542_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_val_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
v_a_2554_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2539_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2539_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
v_a_2563_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2525_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2525_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1___boxed(lean_object* v_t_2571_, lean_object* v_init_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_t_2571_, v_init_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec_ref(v_t_2571_);
return v_res_2580_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0(void){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = lean_unsigned_to_nat(32u);
v___x_2582_ = lean_mk_empty_array_with_capacity(v___x_2581_);
v___x_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2582_);
return v___x_2583_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1(void){
_start:
{
size_t v___x_2584_; lean_object* v_index_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v_decls_2589_; 
v___x_2584_ = ((size_t)5ULL);
v_index_2585_ = lean_unsigned_to_nat(0u);
v___x_2586_ = lean_unsigned_to_nat(32u);
v___x_2587_ = lean_mk_empty_array_with_capacity(v___x_2586_);
v___x_2588_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0);
v_decls_2589_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_decls_2589_, 0, v___x_2588_);
lean_ctor_set(v_decls_2589_, 1, v___x_2587_);
lean_ctor_set(v_decls_2589_, 2, v_index_2585_);
lean_ctor_set(v_decls_2589_, 3, v_index_2585_);
lean_ctor_set_usize(v_decls_2589_, 4, v___x_2584_);
return v_decls_2589_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2(void){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2590_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3(void){
_start:
{
lean_object* v___x_2591_; lean_object* v_fvarIdToDecl_2592_; 
v___x_2591_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2);
v_fvarIdToDecl_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fvarIdToDecl_2592_, 0, v___x_2591_);
return v_fvarIdToDecl_2592_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4(void){
_start:
{
lean_object* v_index_2593_; lean_object* v_decls_2594_; lean_object* v___x_2595_; 
v_index_2593_ = lean_unsigned_to_nat(0u);
v_decls_2594_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1);
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v_decls_2594_);
lean_ctor_set(v___x_2595_, 1, v_index_2593_);
return v___x_2595_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5(void){
_start:
{
lean_object* v___x_2596_; lean_object* v_fvarIdToDecl_2597_; lean_object* v___x_2598_; 
v___x_2596_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4);
v_fvarIdToDecl_2597_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3);
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v_fvarIdToDecl_2597_);
lean_ctor_set(v___x_2598_, 1, v___x_2596_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(lean_object* v_lctx_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v_decls_2607_; lean_object* v_auxDeclToFullName_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2636_; 
v_decls_2607_ = lean_ctor_get(v_lctx_2599_, 1);
v_auxDeclToFullName_2608_ = lean_ctor_get(v_lctx_2599_, 2);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_lctx_2599_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; 
v_unused_2637_ = lean_ctor_get(v_lctx_2599_, 0);
lean_dec(v_unused_2637_);
v___x_2610_ = v_lctx_2599_;
v_isShared_2611_ = v_isSharedCheck_2636_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_auxDeclToFullName_2608_);
lean_inc(v_decls_2607_);
lean_dec(v_lctx_2599_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2636_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5);
v___x_2613_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_decls_2607_, v___x_2612_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
lean_dec_ref(v_decls_2607_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2627_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2627_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2627_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v_snd_2618_; lean_object* v_fst_2619_; lean_object* v_fst_2620_; lean_object* v___x_2622_; 
v_snd_2618_ = lean_ctor_get(v_a_2614_, 1);
lean_inc(v_snd_2618_);
v_fst_2619_ = lean_ctor_get(v_a_2614_, 0);
lean_inc(v_fst_2619_);
lean_dec(v_a_2614_);
v_fst_2620_ = lean_ctor_get(v_snd_2618_, 0);
lean_inc(v_fst_2620_);
lean_dec(v_snd_2618_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 1, v_fst_2620_);
lean_ctor_set(v___x_2610_, 0, v_fst_2619_);
v___x_2622_ = v___x_2610_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_fst_2619_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_fst_2620_);
lean_ctor_set(v_reuseFailAlloc_2626_, 2, v_auxDeclToFullName_2608_);
v___x_2622_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2624_; 
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2622_);
v___x_2624_ = v___x_2616_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_del_object(v___x_2610_);
lean_dec(v_auxDeclToFullName_2608_);
v_a_2628_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2613_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2613_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___boxed(lean_object* v_lctx_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0(lean_object* v_00_u03b2_2647_, lean_object* v_x_2648_, lean_object* v_x_2649_, lean_object* v_x_2650_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_x_2648_, v_x_2649_, v_x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(lean_object* v_00_u03b2_2652_, lean_object* v_x_2653_, size_t v_x_2654_, size_t v_x_2655_, lean_object* v_x_2656_, lean_object* v_x_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_2653_, v_x_2654_, v_x_2655_, v_x_2656_, v_x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2659_, lean_object* v_x_2660_, lean_object* v_x_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_, lean_object* v_x_2664_){
_start:
{
size_t v_x_10744__boxed_2665_; size_t v_x_10745__boxed_2666_; lean_object* v_res_2667_; 
v_x_10744__boxed_2665_ = lean_unbox_usize(v_x_2661_);
lean_dec(v_x_2661_);
v_x_10745__boxed_2666_ = lean_unbox_usize(v_x_2662_);
lean_dec(v_x_2662_);
v_res_2667_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(v_00_u03b2_2659_, v_x_2660_, v_x_10744__boxed_2665_, v_x_10745__boxed_2666_, v_x_2663_, v_x_2664_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2668_, lean_object* v_n_2669_, lean_object* v_k_2670_, lean_object* v_v_2671_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v_n_2669_, v_k_2670_, v_v_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2673_, size_t v_depth_2674_, lean_object* v_keys_2675_, lean_object* v_vals_2676_, lean_object* v_heq_2677_, lean_object* v_i_2678_, lean_object* v_entries_2679_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_2674_, v_keys_2675_, v_vals_2676_, v_i_2678_, v_entries_2679_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2681_, lean_object* v_depth_2682_, lean_object* v_keys_2683_, lean_object* v_vals_2684_, lean_object* v_heq_2685_, lean_object* v_i_2686_, lean_object* v_entries_2687_){
_start:
{
size_t v_depth_boxed_2688_; lean_object* v_res_2689_; 
v_depth_boxed_2688_ = lean_unbox_usize(v_depth_2682_);
lean_dec(v_depth_2682_);
v_res_2689_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(v_00_u03b2_2681_, v_depth_boxed_2688_, v_keys_2683_, v_vals_2684_, v_heq_2685_, v_i_2686_, v_entries_2687_);
lean_dec_ref(v_vals_2684_);
lean_dec_ref(v_keys_2683_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2690_, lean_object* v_x_2691_, lean_object* v_x_2692_, lean_object* v_x_2693_, lean_object* v_x_2694_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2691_, v_x_2692_, v_x_2693_, v_x_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2696_, lean_object* v_x_2697_, lean_object* v_x_2698_, lean_object* v_x_2699_){
_start:
{
lean_object* v_ks_2700_; lean_object* v_vs_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2725_; 
v_ks_2700_ = lean_ctor_get(v_x_2696_, 0);
v_vs_2701_ = lean_ctor_get(v_x_2696_, 1);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_x_2696_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2703_ = v_x_2696_;
v_isShared_2704_ = v_isSharedCheck_2725_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_vs_2701_);
lean_inc(v_ks_2700_);
lean_dec(v_x_2696_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2725_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; uint8_t v___x_2706_; 
v___x_2705_ = lean_array_get_size(v_ks_2700_);
v___x_2706_ = lean_nat_dec_lt(v_x_2697_, v___x_2705_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2710_; 
lean_dec(v_x_2697_);
v___x_2707_ = lean_array_push(v_ks_2700_, v_x_2698_);
v___x_2708_ = lean_array_push(v_vs_2701_, v_x_2699_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 1, v___x_2708_);
lean_ctor_set(v___x_2703_, 0, v___x_2707_);
v___x_2710_ = v___x_2703_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2707_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
else
{
lean_object* v_k_x27_2712_; uint8_t v___x_2713_; 
v_k_x27_2712_ = lean_array_fget_borrowed(v_ks_2700_, v_x_2697_);
v___x_2713_ = l_Lean_instBEqMVarId_beq(v_x_2698_, v_k_x27_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2715_; 
if (v_isShared_2704_ == 0)
{
v___x_2715_ = v___x_2703_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_ks_2700_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v_vs_2701_);
v___x_2715_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = lean_unsigned_to_nat(1u);
v___x_2717_ = lean_nat_add(v_x_2697_, v___x_2716_);
lean_dec(v_x_2697_);
v_x_2696_ = v___x_2715_;
v_x_2697_ = v___x_2717_;
goto _start;
}
}
else
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2723_; 
v___x_2720_ = lean_array_fset(v_ks_2700_, v_x_2697_, v_x_2698_);
v___x_2721_ = lean_array_fset(v_vs_2701_, v_x_2697_, v_x_2699_);
lean_dec(v_x_2697_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 1, v___x_2721_);
lean_ctor_set(v___x_2703_, 0, v___x_2720_);
v___x_2723_ = v___x_2703_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_2726_, lean_object* v_k_2727_, lean_object* v_v_2728_){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2729_ = lean_unsigned_to_nat(0u);
v___x_2730_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_2726_, v___x_2729_, v_k_2727_, v_v_2728_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2731_, size_t v_x_2732_, size_t v_x_2733_, lean_object* v_x_2734_, lean_object* v_x_2735_){
_start:
{
if (lean_obj_tag(v_x_2731_) == 0)
{
lean_object* v_es_2736_; size_t v___x_2737_; size_t v___x_2738_; size_t v___x_2739_; size_t v___x_2740_; lean_object* v_j_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v_es_2736_ = lean_ctor_get(v_x_2731_, 0);
v___x_2737_ = ((size_t)5ULL);
v___x_2738_ = ((size_t)1ULL);
v___x_2739_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
v___x_2740_ = lean_usize_land(v_x_2732_, v___x_2739_);
v_j_2741_ = lean_usize_to_nat(v___x_2740_);
v___x_2742_ = lean_array_get_size(v_es_2736_);
v___x_2743_ = lean_nat_dec_lt(v_j_2741_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_dec(v_j_2741_);
lean_dec(v_x_2735_);
lean_dec(v_x_2734_);
return v_x_2731_;
}
else
{
lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2780_; 
lean_inc_ref(v_es_2736_);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_x_2731_);
if (v_isSharedCheck_2780_ == 0)
{
lean_object* v_unused_2781_; 
v_unused_2781_ = lean_ctor_get(v_x_2731_, 0);
lean_dec(v_unused_2781_);
v___x_2745_ = v_x_2731_;
v_isShared_2746_ = v_isSharedCheck_2780_;
goto v_resetjp_2744_;
}
else
{
lean_dec(v_x_2731_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2780_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v_v_2747_; lean_object* v___x_2748_; lean_object* v_xs_x27_2749_; lean_object* v___y_2751_; 
v_v_2747_ = lean_array_fget(v_es_2736_, v_j_2741_);
v___x_2748_ = lean_box(0);
v_xs_x27_2749_ = lean_array_fset(v_es_2736_, v_j_2741_, v___x_2748_);
switch(lean_obj_tag(v_v_2747_))
{
case 0:
{
lean_object* v_key_2756_; lean_object* v_val_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2767_; 
v_key_2756_ = lean_ctor_get(v_v_2747_, 0);
v_val_2757_ = lean_ctor_get(v_v_2747_, 1);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_v_2747_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2759_ = v_v_2747_;
v_isShared_2760_ = v_isSharedCheck_2767_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_val_2757_);
lean_inc(v_key_2756_);
lean_dec(v_v_2747_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2767_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
uint8_t v___x_2761_; 
v___x_2761_ = l_Lean_instBEqMVarId_beq(v_x_2734_, v_key_2756_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_del_object(v___x_2759_);
v___x_2762_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2756_, v_val_2757_, v_x_2734_, v_x_2735_);
v___x_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
v___y_2751_ = v___x_2763_;
goto v___jp_2750_;
}
else
{
lean_object* v___x_2765_; 
lean_dec(v_val_2757_);
lean_dec(v_key_2756_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 1, v_x_2735_);
lean_ctor_set(v___x_2759_, 0, v_x_2734_);
v___x_2765_ = v___x_2759_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_x_2734_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v_x_2735_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
v___y_2751_ = v___x_2765_;
goto v___jp_2750_;
}
}
}
}
case 1:
{
lean_object* v_node_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2778_; 
v_node_2768_ = lean_ctor_get(v_v_2747_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_v_2747_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2770_ = v_v_2747_;
v_isShared_2771_ = v_isSharedCheck_2778_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_node_2768_);
lean_dec(v_v_2747_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2778_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
size_t v___x_2772_; size_t v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2772_ = lean_usize_shift_right(v_x_2732_, v___x_2737_);
v___x_2773_ = lean_usize_add(v_x_2733_, v___x_2738_);
v___x_2774_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_node_2768_, v___x_2772_, v___x_2773_, v_x_2734_, v_x_2735_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v___x_2774_);
v___x_2776_ = v___x_2770_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
v___y_2751_ = v___x_2776_;
goto v___jp_2750_;
}
}
}
default: 
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2779_, 0, v_x_2734_);
lean_ctor_set(v___x_2779_, 1, v_x_2735_);
v___y_2751_ = v___x_2779_;
goto v___jp_2750_;
}
}
v___jp_2750_:
{
lean_object* v___x_2752_; lean_object* v___x_2754_; 
v___x_2752_ = lean_array_fset(v_xs_x27_2749_, v_j_2741_, v___y_2751_);
lean_dec(v_j_2741_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2752_);
v___x_2754_ = v___x_2745_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
}
else
{
lean_object* v_ks_2782_; lean_object* v_vs_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2803_; 
v_ks_2782_ = lean_ctor_get(v_x_2731_, 0);
v_vs_2783_ = lean_ctor_get(v_x_2731_, 1);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_x_2731_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2785_ = v_x_2731_;
v_isShared_2786_ = v_isSharedCheck_2803_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_vs_2783_);
lean_inc(v_ks_2782_);
lean_dec(v_x_2731_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2803_;
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
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_ks_2782_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_vs_2783_);
v___x_2788_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v_newNode_2789_; uint8_t v___y_2791_; size_t v___x_2797_; uint8_t v___x_2798_; 
v_newNode_2789_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v___x_2788_, v_x_2734_, v_x_2735_);
v___x_2797_ = ((size_t)7ULL);
v___x_2798_ = lean_usize_dec_le(v___x_2797_, v_x_2733_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
v___x_2799_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2789_);
v___x_2800_ = lean_unsigned_to_nat(4u);
v___x_2801_ = lean_nat_dec_lt(v___x_2799_, v___x_2800_);
lean_dec(v___x_2799_);
v___y_2791_ = v___x_2801_;
goto v___jp_2790_;
}
else
{
v___y_2791_ = v___x_2798_;
goto v___jp_2790_;
}
v___jp_2790_:
{
if (v___y_2791_ == 0)
{
lean_object* v_ks_2792_; lean_object* v_vs_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v_ks_2792_ = lean_ctor_get(v_newNode_2789_, 0);
lean_inc_ref(v_ks_2792_);
v_vs_2793_ = lean_ctor_get(v_newNode_2789_, 1);
lean_inc_ref(v_vs_2793_);
lean_dec_ref(v_newNode_2789_);
v___x_2794_ = lean_unsigned_to_nat(0u);
v___x_2795_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2);
v___x_2796_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2733_, v_ks_2792_, v_vs_2793_, v___x_2794_, v___x_2795_);
lean_dec_ref(v_vs_2793_);
lean_dec_ref(v_ks_2792_);
return v___x_2796_;
}
else
{
return v_newNode_2789_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_2804_, lean_object* v_keys_2805_, lean_object* v_vals_2806_, lean_object* v_i_2807_, lean_object* v_entries_2808_){
_start:
{
lean_object* v___x_2809_; uint8_t v___x_2810_; 
v___x_2809_ = lean_array_get_size(v_keys_2805_);
v___x_2810_ = lean_nat_dec_lt(v_i_2807_, v___x_2809_);
if (v___x_2810_ == 0)
{
lean_dec(v_i_2807_);
return v_entries_2808_;
}
else
{
lean_object* v_k_2811_; lean_object* v_v_2812_; uint64_t v___x_2813_; size_t v_h_2814_; size_t v___x_2815_; lean_object* v___x_2816_; size_t v___x_2817_; size_t v___x_2818_; size_t v___x_2819_; size_t v_h_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v_k_2811_ = lean_array_fget_borrowed(v_keys_2805_, v_i_2807_);
v_v_2812_ = lean_array_fget_borrowed(v_vals_2806_, v_i_2807_);
v___x_2813_ = l_Lean_instHashableMVarId_hash(v_k_2811_);
v_h_2814_ = lean_uint64_to_usize(v___x_2813_);
v___x_2815_ = ((size_t)5ULL);
v___x_2816_ = lean_unsigned_to_nat(1u);
v___x_2817_ = ((size_t)1ULL);
v___x_2818_ = lean_usize_sub(v_depth_2804_, v___x_2817_);
v___x_2819_ = lean_usize_mul(v___x_2815_, v___x_2818_);
v_h_2820_ = lean_usize_shift_right(v_h_2814_, v___x_2819_);
v___x_2821_ = lean_nat_add(v_i_2807_, v___x_2816_);
lean_dec(v_i_2807_);
lean_inc(v_v_2812_);
lean_inc(v_k_2811_);
v___x_2822_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_entries_2808_, v_h_2820_, v_depth_2804_, v_k_2811_, v_v_2812_);
v_i_2807_ = v___x_2821_;
v_entries_2808_ = v___x_2822_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2824_, lean_object* v_keys_2825_, lean_object* v_vals_2826_, lean_object* v_i_2827_, lean_object* v_entries_2828_){
_start:
{
size_t v_depth_boxed_2829_; lean_object* v_res_2830_; 
v_depth_boxed_2829_ = lean_unbox_usize(v_depth_2824_);
lean_dec(v_depth_2824_);
v_res_2830_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_2829_, v_keys_2825_, v_vals_2826_, v_i_2827_, v_entries_2828_);
lean_dec_ref(v_vals_2826_);
lean_dec_ref(v_keys_2825_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2831_, lean_object* v_x_2832_, lean_object* v_x_2833_, lean_object* v_x_2834_, lean_object* v_x_2835_){
_start:
{
size_t v_x_2256__boxed_2836_; size_t v_x_2257__boxed_2837_; lean_object* v_res_2838_; 
v_x_2256__boxed_2836_ = lean_unbox_usize(v_x_2832_);
lean_dec(v_x_2832_);
v_x_2257__boxed_2837_ = lean_unbox_usize(v_x_2833_);
lean_dec(v_x_2833_);
v_res_2838_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_2831_, v_x_2256__boxed_2836_, v_x_2257__boxed_2837_, v_x_2834_, v_x_2835_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(lean_object* v_x_2839_, lean_object* v_x_2840_, lean_object* v_x_2841_){
_start:
{
uint64_t v___x_2842_; size_t v___x_2843_; size_t v___x_2844_; lean_object* v___x_2845_; 
v___x_2842_ = l_Lean_instHashableMVarId_hash(v_x_2840_);
v___x_2843_ = lean_uint64_to_usize(v___x_2842_);
v___x_2844_ = ((size_t)1ULL);
v___x_2845_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_2839_, v___x_2843_, v___x_2844_, v_x_2840_, v_x_2841_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(lean_object* v_mvarId_2846_, lean_object* v_val_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v___x_2850_; lean_object* v_mctx_2851_; lean_object* v_cache_2852_; lean_object* v_zetaDeltaFVarIds_2853_; lean_object* v_postponed_2854_; lean_object* v_diag_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2883_; 
v___x_2850_ = lean_st_ref_take(v___y_2848_);
v_mctx_2851_ = lean_ctor_get(v___x_2850_, 0);
v_cache_2852_ = lean_ctor_get(v___x_2850_, 1);
v_zetaDeltaFVarIds_2853_ = lean_ctor_get(v___x_2850_, 2);
v_postponed_2854_ = lean_ctor_get(v___x_2850_, 3);
v_diag_2855_ = lean_ctor_get(v___x_2850_, 4);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2857_ = v___x_2850_;
v_isShared_2858_ = v_isSharedCheck_2883_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_diag_2855_);
lean_inc(v_postponed_2854_);
lean_inc(v_zetaDeltaFVarIds_2853_);
lean_inc(v_cache_2852_);
lean_inc(v_mctx_2851_);
lean_dec(v___x_2850_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2883_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v_depth_2859_; lean_object* v_levelAssignDepth_2860_; lean_object* v_lmvarCounter_2861_; lean_object* v_mvarCounter_2862_; lean_object* v_lDecls_2863_; lean_object* v_decls_2864_; lean_object* v_userNames_2865_; lean_object* v_lAssignment_2866_; lean_object* v_eAssignment_2867_; lean_object* v_dAssignment_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2882_; 
v_depth_2859_ = lean_ctor_get(v_mctx_2851_, 0);
v_levelAssignDepth_2860_ = lean_ctor_get(v_mctx_2851_, 1);
v_lmvarCounter_2861_ = lean_ctor_get(v_mctx_2851_, 2);
v_mvarCounter_2862_ = lean_ctor_get(v_mctx_2851_, 3);
v_lDecls_2863_ = lean_ctor_get(v_mctx_2851_, 4);
v_decls_2864_ = lean_ctor_get(v_mctx_2851_, 5);
v_userNames_2865_ = lean_ctor_get(v_mctx_2851_, 6);
v_lAssignment_2866_ = lean_ctor_get(v_mctx_2851_, 7);
v_eAssignment_2867_ = lean_ctor_get(v_mctx_2851_, 8);
v_dAssignment_2868_ = lean_ctor_get(v_mctx_2851_, 9);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_mctx_2851_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2870_ = v_mctx_2851_;
v_isShared_2871_ = v_isSharedCheck_2882_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_dAssignment_2868_);
lean_inc(v_eAssignment_2867_);
lean_inc(v_lAssignment_2866_);
lean_inc(v_userNames_2865_);
lean_inc(v_decls_2864_);
lean_inc(v_lDecls_2863_);
lean_inc(v_mvarCounter_2862_);
lean_inc(v_lmvarCounter_2861_);
lean_inc(v_levelAssignDepth_2860_);
lean_inc(v_depth_2859_);
lean_dec(v_mctx_2851_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2882_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2872_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_eAssignment_2867_, v_mvarId_2846_, v_val_2847_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 8, v___x_2872_);
v___x_2874_ = v___x_2870_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_depth_2859_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_levelAssignDepth_2860_);
lean_ctor_set(v_reuseFailAlloc_2881_, 2, v_lmvarCounter_2861_);
lean_ctor_set(v_reuseFailAlloc_2881_, 3, v_mvarCounter_2862_);
lean_ctor_set(v_reuseFailAlloc_2881_, 4, v_lDecls_2863_);
lean_ctor_set(v_reuseFailAlloc_2881_, 5, v_decls_2864_);
lean_ctor_set(v_reuseFailAlloc_2881_, 6, v_userNames_2865_);
lean_ctor_set(v_reuseFailAlloc_2881_, 7, v_lAssignment_2866_);
lean_ctor_set(v_reuseFailAlloc_2881_, 8, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2881_, 9, v_dAssignment_2868_);
v___x_2874_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2876_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2874_);
v___x_2876_ = v___x_2857_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2874_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_cache_2852_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_zetaDeltaFVarIds_2853_);
lean_ctor_set(v_reuseFailAlloc_2880_, 3, v_postponed_2854_);
lean_ctor_set(v_reuseFailAlloc_2880_, 4, v_diag_2855_);
v___x_2876_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = lean_st_ref_set(v___y_2848_, v___x_2876_);
v___x_2878_ = lean_box(0);
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
return v___x_2879_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg___boxed(lean_object* v_mvarId_2884_, lean_object* v_val_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_2884_, v_val_2885_, v___y_2886_);
lean_dec(v___y_2886_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object* v_mvarId_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v___x_2897_; 
lean_inc(v_mvarId_2889_);
v___x_2897_ = l_Lean_MVarId_getDecl(v_mvarId_2889_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v_userName_2899_; lean_object* v_lctx_2900_; lean_object* v_type_2901_; lean_object* v_localInstances_2902_; lean_object* v___x_2903_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___x_2897_);
v_userName_2899_ = lean_ctor_get(v_a_2898_, 0);
lean_inc(v_userName_2899_);
v_lctx_2900_ = lean_ctor_get(v_a_2898_, 1);
lean_inc_ref(v_lctx_2900_);
v_type_2901_ = lean_ctor_get(v_a_2898_, 2);
lean_inc_ref(v_type_2901_);
v_localInstances_2902_ = lean_ctor_get(v_a_2898_, 4);
lean_inc_ref(v_localInstances_2902_);
lean_dec(v_a_2898_);
v___x_2903_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_2900_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref(v___x_2903_);
v___x_2905_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2901_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; uint8_t v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref(v___x_2905_);
v___x_2907_ = 2;
v___x_2908_ = lean_unsigned_to_nat(0u);
v___x_2909_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_2904_, v_localInstances_2902_, v_a_2906_, v___x_2907_, v_userName_2899_, v___x_2908_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2919_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc_n(v_a_2910_, 2);
lean_dec_ref(v___x_2909_);
v___x_2911_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_2889_, v_a_2910_, v_a_2893_);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v___x_2911_, 0);
lean_dec(v_unused_2920_);
v___x_2913_ = v___x_2911_;
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
else
{
lean_dec(v___x_2911_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2915_ = l_Lean_Expr_mvarId_x21(v_a_2910_);
lean_dec(v_a_2910_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2915_);
v___x_2917_ = v___x_2913_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec(v_mvarId_2889_);
v_a_2921_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2909_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2909_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
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
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec(v_a_2904_);
lean_dec_ref(v_localInstances_2902_);
lean_dec(v_userName_2899_);
lean_dec(v_mvarId_2889_);
v_a_2929_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2905_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2905_);
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
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec_ref(v_localInstances_2902_);
lean_dec_ref(v_type_2901_);
lean_dec(v_userName_2899_);
lean_dec(v_mvarId_2889_);
v_a_2937_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2903_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2903_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v_mvarId_2889_);
v_a_2945_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2897_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2897_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar___boxed(lean_object* v_mvarId_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
lean_dec(v_a_2959_);
lean_dec_ref(v_a_2958_);
lean_dec(v_a_2957_);
lean_dec_ref(v_a_2956_);
lean_dec(v_a_2955_);
lean_dec_ref(v_a_2954_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(lean_object* v_mvarId_2962_, lean_object* v_val_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_2962_, v_val_2963_, v___y_2967_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___boxed(lean_object* v_mvarId_2972_, lean_object* v_val_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(v_mvarId_2972_, v_val_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0(lean_object* v_00_u03b2_2982_, lean_object* v_x_2983_, lean_object* v_x_2984_, lean_object* v_x_2985_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_x_2983_, v_x_2984_, v_x_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2987_, lean_object* v_x_2988_, size_t v_x_2989_, size_t v_x_2990_, lean_object* v_x_2991_, lean_object* v_x_2992_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_2988_, v_x_2989_, v_x_2990_, v_x_2991_, v_x_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2994_, lean_object* v_x_2995_, lean_object* v_x_2996_, lean_object* v_x_2997_, lean_object* v_x_2998_, lean_object* v_x_2999_){
_start:
{
size_t v_x_2610__boxed_3000_; size_t v_x_2611__boxed_3001_; lean_object* v_res_3002_; 
v_x_2610__boxed_3000_ = lean_unbox_usize(v_x_2996_);
lean_dec(v_x_2996_);
v_x_2611__boxed_3001_ = lean_unbox_usize(v_x_2997_);
lean_dec(v_x_2997_);
v_res_3002_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(v_00_u03b2_2994_, v_x_2995_, v_x_2610__boxed_3000_, v_x_2611__boxed_3001_, v_x_2998_, v_x_2999_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3003_, lean_object* v_n_3004_, lean_object* v_k_3005_, lean_object* v_v_3006_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v_n_3004_, v_k_3005_, v_v_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3008_, size_t v_depth_3009_, lean_object* v_keys_3010_, lean_object* v_vals_3011_, lean_object* v_heq_3012_, lean_object* v_i_3013_, lean_object* v_entries_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_3009_, v_keys_3010_, v_vals_3011_, v_i_3013_, v_entries_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3016_, lean_object* v_depth_3017_, lean_object* v_keys_3018_, lean_object* v_vals_3019_, lean_object* v_heq_3020_, lean_object* v_i_3021_, lean_object* v_entries_3022_){
_start:
{
size_t v_depth_boxed_3023_; lean_object* v_res_3024_; 
v_depth_boxed_3023_ = lean_unbox_usize(v_depth_3017_);
lean_dec(v_depth_3017_);
v_res_3024_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3016_, v_depth_boxed_3023_, v_keys_3018_, v_vals_3019_, v_heq_3020_, v_i_3021_, v_entries_3022_);
lean_dec_ref(v_vals_3019_);
lean_dec_ref(v_keys_3018_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3025_, lean_object* v_x_3026_, lean_object* v_x_3027_, lean_object* v_x_3028_, lean_object* v_x_3029_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_3026_, v_x_3027_, v_x_3028_, v_x_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(lean_object* v_msgData_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v___x_3037_; lean_object* v_env_3038_; lean_object* v___x_3039_; lean_object* v_mctx_3040_; lean_object* v_lctx_3041_; lean_object* v_options_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3037_ = lean_st_ref_get(v___y_3035_);
v_env_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc_ref(v_env_3038_);
lean_dec(v___x_3037_);
v___x_3039_ = lean_st_ref_get(v___y_3033_);
v_mctx_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc_ref(v_mctx_3040_);
lean_dec(v___x_3039_);
v_lctx_3041_ = lean_ctor_get(v___y_3032_, 2);
v_options_3042_ = lean_ctor_get(v___y_3034_, 2);
lean_inc_ref(v_options_3042_);
lean_inc_ref(v_lctx_3041_);
v___x_3043_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3043_, 0, v_env_3038_);
lean_ctor_set(v___x_3043_, 1, v_mctx_3040_);
lean_ctor_set(v___x_3043_, 2, v_lctx_3041_);
lean_ctor_set(v___x_3043_, 3, v_options_3042_);
v___x_3044_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
lean_ctor_set(v___x_3044_, 1, v_msgData_3031_);
v___x_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0___boxed(lean_object* v_msgData_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msgData_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(lean_object* v_msg_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_ref_3059_; lean_object* v___x_3060_; lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3069_; 
v_ref_3059_ = lean_ctor_get(v___y_3056_, 5);
v___x_3060_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msg_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3063_ = v___x_3060_;
v_isShared_3064_ = v_isSharedCheck_3069_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3069_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3065_; lean_object* v___x_3067_; 
lean_inc(v_ref_3059_);
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_ref_3059_);
lean_ctor_set(v___x_3065_, 1, v_a_3061_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set_tag(v___x_3063_, 1);
lean_ctor_set(v___x_3063_, 0, v___x_3065_);
v___x_3067_ = v___x_3063_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3065_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg___boxed(lean_object* v_msg_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
return v_res_3076_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0));
v___x_3079_ = l_Lean_stringToMessageData(v___x_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(lean_object* v_msg_3083_, lean_object* v_e_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v___y_3093_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v___x_3100_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2));
v___x_3101_ = lean_string_dec_eq(v_msg_3083_, v___x_3100_);
if (v___x_3101_ == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3102_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3));
v___x_3103_ = lean_string_append(v___x_3102_, v_msg_3083_);
lean_dec_ref(v_msg_3083_);
v___x_3104_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__4));
v___x_3105_ = lean_string_append(v___x_3103_, v___x_3104_);
v___y_3093_ = v___x_3105_;
goto v___jp_3092_;
}
else
{
v___y_3093_ = v_msg_3083_;
goto v___jp_3092_;
}
v___jp_3092_:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3094_ = l_Lean_stringToMessageData(v___y_3093_);
v___x_3095_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1);
v___x_3096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3094_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
v___x_3097_ = l_Lean_indentExpr(v_e_3084_);
v___x_3098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v___x_3098_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
return v___x_3099_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___boxed(lean_object* v_msg_3106_, lean_object* v_e_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3106_, v_e_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_);
lean_dec(v_a_3113_);
lean_dec_ref(v_a_3112_);
lean_dec(v_a_3111_);
lean_dec_ref(v_a_3110_);
lean_dec(v_a_3109_);
lean_dec_ref(v_a_3108_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(lean_object* v_00_u03b1_3116_, lean_object* v_msg_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_3117_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___boxed(lean_object* v_00_u03b1_3126_, lean_object* v_msg_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(v_00_u03b1_3126_, v_msg_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3136_, lean_object* v_vals_3137_, lean_object* v_i_3138_, lean_object* v_k_3139_){
_start:
{
lean_object* v___x_3140_; uint8_t v___x_3141_; 
v___x_3140_ = lean_array_get_size(v_keys_3136_);
v___x_3141_ = lean_nat_dec_lt(v_i_3138_, v___x_3140_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; 
lean_dec_ref(v_k_3139_);
lean_dec(v_i_3138_);
v___x_3142_ = lean_box(0);
return v___x_3142_;
}
else
{
lean_object* v_k_x27_3143_; uint8_t v___x_3144_; 
v_k_x27_3143_ = lean_array_fget_borrowed(v_keys_3136_, v_i_3138_);
lean_inc(v_k_x27_3143_);
lean_inc_ref(v_k_3139_);
v___x_3144_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_3139_, v_k_x27_3143_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = lean_unsigned_to_nat(1u);
v___x_3146_ = lean_nat_add(v_i_3138_, v___x_3145_);
lean_dec(v_i_3138_);
v_i_3138_ = v___x_3146_;
goto _start;
}
else
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec_ref(v_k_3139_);
v___x_3148_ = lean_array_fget_borrowed(v_vals_3137_, v_i_3138_);
lean_dec(v_i_3138_);
lean_inc(v___x_3148_);
lean_inc(v_k_x27_3143_);
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v_k_x27_3143_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
v___x_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
return v___x_3150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3151_, lean_object* v_vals_3152_, lean_object* v_i_3153_, lean_object* v_k_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_3151_, v_vals_3152_, v_i_3153_, v_k_3154_);
lean_dec_ref(v_vals_3152_);
lean_dec_ref(v_keys_3151_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(lean_object* v_x_3156_, size_t v_x_3157_, lean_object* v_x_3158_){
_start:
{
if (lean_obj_tag(v_x_3156_) == 0)
{
lean_object* v_es_3159_; lean_object* v___x_3160_; size_t v___x_3161_; size_t v___x_3162_; size_t v___x_3163_; lean_object* v_j_3164_; lean_object* v___x_3165_; 
v_es_3159_ = lean_ctor_get(v_x_3156_, 0);
lean_inc_ref(v_es_3159_);
lean_dec_ref(v_x_3156_);
v___x_3160_ = lean_box(2);
v___x_3161_ = ((size_t)5ULL);
v___x_3162_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
v___x_3163_ = lean_usize_land(v_x_3157_, v___x_3162_);
v_j_3164_ = lean_usize_to_nat(v___x_3163_);
v___x_3165_ = lean_array_get(v___x_3160_, v_es_3159_, v_j_3164_);
lean_dec(v_j_3164_);
lean_dec_ref(v_es_3159_);
switch(lean_obj_tag(v___x_3165_))
{
case 0:
{
lean_object* v_key_3166_; lean_object* v_val_3167_; uint8_t v___x_3168_; 
v_key_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc_n(v_key_3166_, 2);
v_val_3167_ = lean_ctor_get(v___x_3165_, 1);
lean_inc(v_val_3167_);
lean_dec_ref(v___x_3165_);
v___x_3168_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_3158_, v_key_3166_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; 
lean_dec(v_val_3167_);
lean_dec(v_key_3166_);
v___x_3169_ = lean_box(0);
return v___x_3169_;
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3170_, 0, v_key_3166_);
lean_ctor_set(v___x_3170_, 1, v_val_3167_);
v___x_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
return v___x_3171_;
}
}
case 1:
{
lean_object* v_node_3172_; size_t v___x_3173_; 
v_node_3172_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_node_3172_);
lean_dec_ref(v___x_3165_);
v___x_3173_ = lean_usize_shift_right(v_x_3157_, v___x_3161_);
v_x_3156_ = v_node_3172_;
v_x_3157_ = v___x_3173_;
goto _start;
}
default: 
{
lean_object* v___x_3175_; 
lean_dec_ref(v_x_3158_);
v___x_3175_ = lean_box(0);
return v___x_3175_;
}
}
}
else
{
lean_object* v_ks_3176_; lean_object* v_vs_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_ks_3176_ = lean_ctor_get(v_x_3156_, 0);
lean_inc_ref(v_ks_3176_);
v_vs_3177_ = lean_ctor_get(v_x_3156_, 1);
lean_inc_ref(v_vs_3177_);
lean_dec_ref(v_x_3156_);
v___x_3178_ = lean_unsigned_to_nat(0u);
v___x_3179_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_ks_3176_, v_vs_3177_, v___x_3178_, v_x_3158_);
lean_dec_ref(v_vs_3177_);
lean_dec_ref(v_ks_3176_);
return v___x_3179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_3180_, lean_object* v_x_3181_, lean_object* v_x_3182_){
_start:
{
size_t v_x_7443__boxed_3183_; lean_object* v_res_3184_; 
v_x_7443__boxed_3183_ = lean_unbox_usize(v_x_3181_);
lean_dec(v_x_3181_);
v_res_3184_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3180_, v_x_7443__boxed_3183_, v_x_3182_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(lean_object* v_x_3185_, lean_object* v_x_3186_){
_start:
{
uint64_t v___x_3187_; size_t v___x_3188_; lean_object* v___x_3189_; 
v___x_3187_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3186_);
v___x_3188_ = lean_uint64_to_usize(v___x_3187_);
lean_inc_ref(v_x_3185_);
v___x_3189_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3185_, v___x_3188_, v_x_3186_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg___boxed(lean_object* v_x_3190_, lean_object* v_x_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_3190_, v_x_3191_);
lean_dec_ref(v_x_3190_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0(lean_object* v_msg_3193_, lean_object* v_e_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v___y_3207_; lean_object* v___x_3216_; lean_object* v_share_3217_; lean_object* v___x_3218_; 
v___x_3216_ = lean_st_ref_get(v___y_3196_);
v_share_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc_ref(v_share_3217_);
lean_dec(v___x_3216_);
lean_inc_ref(v_e_3194_);
v___x_3218_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_share_3217_, v_e_3194_);
lean_dec_ref(v_share_3217_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v___x_3219_; 
v___x_3219_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3193_, v_e_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
v___y_3207_ = v___x_3219_;
goto v___jp_3206_;
}
else
{
lean_object* v_val_3220_; lean_object* v_fst_3221_; uint8_t v___x_3222_; 
v_val_3220_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_val_3220_);
lean_dec_ref(v___x_3218_);
v_fst_3221_ = lean_ctor_get(v_val_3220_, 0);
lean_inc(v_fst_3221_);
lean_dec(v_val_3220_);
v___x_3222_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_3221_, v_e_3194_);
lean_dec(v_fst_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; 
v___x_3223_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3193_, v_e_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
v___y_3207_ = v___x_3223_;
goto v___jp_3206_;
}
else
{
lean_dec_ref(v_e_3194_);
lean_dec_ref(v_msg_3193_);
goto v___jp_3202_;
}
}
v___jp_3202_:
{
uint8_t v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3203_ = 1;
v___x_3204_ = lean_box(v___x_3203_);
v___x_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
return v___x_3205_;
}
v___jp_3206_:
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
v_a_3208_ = lean_ctor_get(v___y_3207_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___y_3207_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___y_3207_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___y_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0___boxed(lean_object* v_msg_3224_, lean_object* v_e_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Lean_Expr_checkMaxShared___lam__0(v_msg_3224_, v_e_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
return v_res_3233_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(lean_object* v_a_3234_, lean_object* v_x_3235_){
_start:
{
if (lean_obj_tag(v_x_3235_) == 0)
{
uint8_t v___x_3236_; 
v___x_3236_ = 0;
return v___x_3236_;
}
else
{
lean_object* v_key_3237_; lean_object* v_tail_3238_; uint8_t v___x_3239_; 
v_key_3237_ = lean_ctor_get(v_x_3235_, 0);
v_tail_3238_ = lean_ctor_get(v_x_3235_, 2);
v___x_3239_ = lean_expr_eqv(v_key_3237_, v_a_3234_);
if (v___x_3239_ == 0)
{
v_x_3235_ = v_tail_3238_;
goto _start;
}
else
{
return v___x_3239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_a_3241_, lean_object* v_x_3242_){
_start:
{
uint8_t v_res_3243_; lean_object* v_r_3244_; 
v_res_3243_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3241_, v_x_3242_);
lean_dec(v_x_3242_);
lean_dec_ref(v_a_3241_);
v_r_3244_ = lean_box(v_res_3243_);
return v_r_3244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(lean_object* v_a_3245_, lean_object* v_b_3246_, lean_object* v_x_3247_){
_start:
{
if (lean_obj_tag(v_x_3247_) == 0)
{
lean_dec(v_b_3246_);
lean_dec_ref(v_a_3245_);
return v_x_3247_;
}
else
{
lean_object* v_key_3248_; lean_object* v_value_3249_; lean_object* v_tail_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3262_; 
v_key_3248_ = lean_ctor_get(v_x_3247_, 0);
v_value_3249_ = lean_ctor_get(v_x_3247_, 1);
v_tail_3250_ = lean_ctor_get(v_x_3247_, 2);
v_isSharedCheck_3262_ = !lean_is_exclusive(v_x_3247_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3252_ = v_x_3247_;
v_isShared_3253_ = v_isSharedCheck_3262_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_tail_3250_);
lean_inc(v_value_3249_);
lean_inc(v_key_3248_);
lean_dec(v_x_3247_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3262_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
uint8_t v___x_3254_; 
v___x_3254_ = lean_expr_eqv(v_key_3248_, v_a_3245_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3255_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3245_, v_b_3246_, v_tail_3250_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 2, v___x_3255_);
v___x_3257_ = v___x_3252_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_key_3248_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_value_3249_);
lean_ctor_set(v_reuseFailAlloc_3258_, 2, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
else
{
lean_object* v___x_3260_; 
lean_dec(v_value_3249_);
lean_dec(v_key_3248_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 1, v_b_3246_);
lean_ctor_set(v___x_3252_, 0, v_a_3245_);
v___x_3260_ = v___x_3252_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3245_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v_b_3246_);
lean_ctor_set(v_reuseFailAlloc_3261_, 2, v_tail_3250_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(lean_object* v_x_3263_, lean_object* v_x_3264_){
_start:
{
if (lean_obj_tag(v_x_3264_) == 0)
{
return v_x_3263_;
}
else
{
lean_object* v_key_3265_; lean_object* v_value_3266_; lean_object* v_tail_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3290_; 
v_key_3265_ = lean_ctor_get(v_x_3264_, 0);
v_value_3266_ = lean_ctor_get(v_x_3264_, 1);
v_tail_3267_ = lean_ctor_get(v_x_3264_, 2);
v_isSharedCheck_3290_ = !lean_is_exclusive(v_x_3264_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3269_ = v_x_3264_;
v_isShared_3270_ = v_isSharedCheck_3290_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_tail_3267_);
lean_inc(v_value_3266_);
lean_inc(v_key_3265_);
lean_dec(v_x_3264_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3290_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; uint64_t v___x_3272_; uint64_t v___x_3273_; uint64_t v___x_3274_; uint64_t v_fold_3275_; uint64_t v___x_3276_; uint64_t v___x_3277_; uint64_t v___x_3278_; size_t v___x_3279_; size_t v___x_3280_; size_t v___x_3281_; size_t v___x_3282_; size_t v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3286_; 
v___x_3271_ = lean_array_get_size(v_x_3263_);
v___x_3272_ = l_Lean_Expr_hash(v_key_3265_);
v___x_3273_ = 32ULL;
v___x_3274_ = lean_uint64_shift_right(v___x_3272_, v___x_3273_);
v_fold_3275_ = lean_uint64_xor(v___x_3272_, v___x_3274_);
v___x_3276_ = 16ULL;
v___x_3277_ = lean_uint64_shift_right(v_fold_3275_, v___x_3276_);
v___x_3278_ = lean_uint64_xor(v_fold_3275_, v___x_3277_);
v___x_3279_ = lean_uint64_to_usize(v___x_3278_);
v___x_3280_ = lean_usize_of_nat(v___x_3271_);
v___x_3281_ = ((size_t)1ULL);
v___x_3282_ = lean_usize_sub(v___x_3280_, v___x_3281_);
v___x_3283_ = lean_usize_land(v___x_3279_, v___x_3282_);
v___x_3284_ = lean_array_uget_borrowed(v_x_3263_, v___x_3283_);
lean_inc(v___x_3284_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 2, v___x_3284_);
v___x_3286_ = v___x_3269_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_key_3265_);
lean_ctor_set(v_reuseFailAlloc_3289_, 1, v_value_3266_);
lean_ctor_set(v_reuseFailAlloc_3289_, 2, v___x_3284_);
v___x_3286_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
lean_object* v___x_3287_; 
v___x_3287_ = lean_array_uset(v_x_3263_, v___x_3283_, v___x_3286_);
v_x_3263_ = v___x_3287_;
v_x_3264_ = v_tail_3267_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(lean_object* v_i_3291_, lean_object* v_source_3292_, lean_object* v_target_3293_){
_start:
{
lean_object* v___x_3294_; uint8_t v___x_3295_; 
v___x_3294_ = lean_array_get_size(v_source_3292_);
v___x_3295_ = lean_nat_dec_lt(v_i_3291_, v___x_3294_);
if (v___x_3295_ == 0)
{
lean_dec_ref(v_source_3292_);
lean_dec(v_i_3291_);
return v_target_3293_;
}
else
{
lean_object* v_es_3296_; lean_object* v___x_3297_; lean_object* v_source_3298_; lean_object* v_target_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v_es_3296_ = lean_array_fget(v_source_3292_, v_i_3291_);
v___x_3297_ = lean_box(0);
v_source_3298_ = lean_array_fset(v_source_3292_, v_i_3291_, v___x_3297_);
v_target_3299_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_target_3293_, v_es_3296_);
v___x_3300_ = lean_unsigned_to_nat(1u);
v___x_3301_ = lean_nat_add(v_i_3291_, v___x_3300_);
lean_dec(v_i_3291_);
v_i_3291_ = v___x_3301_;
v_source_3292_ = v_source_3298_;
v_target_3293_ = v_target_3299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(lean_object* v_data_3303_){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v_nbuckets_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3304_ = lean_array_get_size(v_data_3303_);
v___x_3305_ = lean_unsigned_to_nat(2u);
v_nbuckets_3306_ = lean_nat_mul(v___x_3304_, v___x_3305_);
v___x_3307_ = lean_unsigned_to_nat(0u);
v___x_3308_ = lean_box(0);
v___x_3309_ = lean_mk_array(v_nbuckets_3306_, v___x_3308_);
v___x_3310_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v___x_3307_, v_data_3303_, v___x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(lean_object* v_m_3311_, lean_object* v_a_3312_, lean_object* v_b_3313_){
_start:
{
lean_object* v_size_3314_; lean_object* v_buckets_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3358_; 
v_size_3314_ = lean_ctor_get(v_m_3311_, 0);
v_buckets_3315_ = lean_ctor_get(v_m_3311_, 1);
v_isSharedCheck_3358_ = !lean_is_exclusive(v_m_3311_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3317_ = v_m_3311_;
v_isShared_3318_ = v_isSharedCheck_3358_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_buckets_3315_);
lean_inc(v_size_3314_);
lean_dec(v_m_3311_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3358_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3319_; uint64_t v___x_3320_; uint64_t v___x_3321_; uint64_t v___x_3322_; uint64_t v_fold_3323_; uint64_t v___x_3324_; uint64_t v___x_3325_; uint64_t v___x_3326_; size_t v___x_3327_; size_t v___x_3328_; size_t v___x_3329_; size_t v___x_3330_; size_t v___x_3331_; lean_object* v_bkt_3332_; uint8_t v___x_3333_; 
v___x_3319_ = lean_array_get_size(v_buckets_3315_);
v___x_3320_ = l_Lean_Expr_hash(v_a_3312_);
v___x_3321_ = 32ULL;
v___x_3322_ = lean_uint64_shift_right(v___x_3320_, v___x_3321_);
v_fold_3323_ = lean_uint64_xor(v___x_3320_, v___x_3322_);
v___x_3324_ = 16ULL;
v___x_3325_ = lean_uint64_shift_right(v_fold_3323_, v___x_3324_);
v___x_3326_ = lean_uint64_xor(v_fold_3323_, v___x_3325_);
v___x_3327_ = lean_uint64_to_usize(v___x_3326_);
v___x_3328_ = lean_usize_of_nat(v___x_3319_);
v___x_3329_ = ((size_t)1ULL);
v___x_3330_ = lean_usize_sub(v___x_3328_, v___x_3329_);
v___x_3331_ = lean_usize_land(v___x_3327_, v___x_3330_);
v_bkt_3332_ = lean_array_uget_borrowed(v_buckets_3315_, v___x_3331_);
v___x_3333_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3312_, v_bkt_3332_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; lean_object* v_size_x27_3335_; lean_object* v___x_3336_; lean_object* v_buckets_x27_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; uint8_t v___x_3343_; 
v___x_3334_ = lean_unsigned_to_nat(1u);
v_size_x27_3335_ = lean_nat_add(v_size_3314_, v___x_3334_);
lean_dec(v_size_3314_);
lean_inc(v_bkt_3332_);
v___x_3336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3336_, 0, v_a_3312_);
lean_ctor_set(v___x_3336_, 1, v_b_3313_);
lean_ctor_set(v___x_3336_, 2, v_bkt_3332_);
v_buckets_x27_3337_ = lean_array_uset(v_buckets_3315_, v___x_3331_, v___x_3336_);
v___x_3338_ = lean_unsigned_to_nat(4u);
v___x_3339_ = lean_nat_mul(v_size_x27_3335_, v___x_3338_);
v___x_3340_ = lean_unsigned_to_nat(3u);
v___x_3341_ = lean_nat_div(v___x_3339_, v___x_3340_);
lean_dec(v___x_3339_);
v___x_3342_ = lean_array_get_size(v_buckets_x27_3337_);
v___x_3343_ = lean_nat_dec_le(v___x_3341_, v___x_3342_);
lean_dec(v___x_3341_);
if (v___x_3343_ == 0)
{
lean_object* v_val_3344_; lean_object* v___x_3346_; 
v_val_3344_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_buckets_x27_3337_);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 1, v_val_3344_);
lean_ctor_set(v___x_3317_, 0, v_size_x27_3335_);
v___x_3346_ = v___x_3317_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_size_x27_3335_);
lean_ctor_set(v_reuseFailAlloc_3347_, 1, v_val_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
else
{
lean_object* v___x_3349_; 
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 1, v_buckets_x27_3337_);
lean_ctor_set(v___x_3317_, 0, v_size_x27_3335_);
v___x_3349_ = v___x_3317_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_size_x27_3335_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_buckets_x27_3337_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
else
{
lean_object* v___x_3351_; lean_object* v_buckets_x27_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3356_; 
lean_inc(v_bkt_3332_);
v___x_3351_ = lean_box(0);
v_buckets_x27_3352_ = lean_array_uset(v_buckets_3315_, v___x_3331_, v___x_3351_);
v___x_3353_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3312_, v_b_3313_, v_bkt_3332_);
v___x_3354_ = lean_array_uset(v_buckets_x27_3352_, v___x_3331_, v___x_3353_);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 1, v___x_3354_);
v___x_3356_ = v___x_3317_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_size_3314_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(lean_object* v_a_3359_, lean_object* v_x_3360_){
_start:
{
if (lean_obj_tag(v_x_3360_) == 0)
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_box(0);
return v___x_3361_;
}
else
{
lean_object* v_key_3362_; lean_object* v_value_3363_; lean_object* v_tail_3364_; uint8_t v___x_3365_; 
v_key_3362_ = lean_ctor_get(v_x_3360_, 0);
v_value_3363_ = lean_ctor_get(v_x_3360_, 1);
v_tail_3364_ = lean_ctor_get(v_x_3360_, 2);
v___x_3365_ = lean_expr_eqv(v_key_3362_, v_a_3359_);
if (v___x_3365_ == 0)
{
v_x_3360_ = v_tail_3364_;
goto _start;
}
else
{
lean_object* v___x_3367_; 
lean_inc(v_value_3363_);
v___x_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3367_, 0, v_value_3363_);
return v___x_3367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_3368_, lean_object* v_x_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3368_, v_x_3369_);
lean_dec(v_x_3369_);
lean_dec_ref(v_a_3368_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(lean_object* v_m_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_buckets_3373_; lean_object* v___x_3374_; uint64_t v___x_3375_; uint64_t v___x_3376_; uint64_t v___x_3377_; uint64_t v_fold_3378_; uint64_t v___x_3379_; uint64_t v___x_3380_; uint64_t v___x_3381_; size_t v___x_3382_; size_t v___x_3383_; size_t v___x_3384_; size_t v___x_3385_; size_t v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v_buckets_3373_ = lean_ctor_get(v_m_3371_, 1);
v___x_3374_ = lean_array_get_size(v_buckets_3373_);
v___x_3375_ = l_Lean_Expr_hash(v_a_3372_);
v___x_3376_ = 32ULL;
v___x_3377_ = lean_uint64_shift_right(v___x_3375_, v___x_3376_);
v_fold_3378_ = lean_uint64_xor(v___x_3375_, v___x_3377_);
v___x_3379_ = 16ULL;
v___x_3380_ = lean_uint64_shift_right(v_fold_3378_, v___x_3379_);
v___x_3381_ = lean_uint64_xor(v_fold_3378_, v___x_3380_);
v___x_3382_ = lean_uint64_to_usize(v___x_3381_);
v___x_3383_ = lean_usize_of_nat(v___x_3374_);
v___x_3384_ = ((size_t)1ULL);
v___x_3385_ = lean_usize_sub(v___x_3383_, v___x_3384_);
v___x_3386_ = lean_usize_land(v___x_3382_, v___x_3385_);
v___x_3387_ = lean_array_uget_borrowed(v_buckets_3373_, v___x_3386_);
v___x_3388_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3372_, v___x_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg___boxed(lean_object* v_m_3389_, lean_object* v_a_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_3389_, v_a_3390_);
lean_dec_ref(v_a_3390_);
lean_dec_ref(v_m_3389_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(lean_object* v_g_3392_, lean_object* v_e_3393_, lean_object* v_a_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v_a_3403_; lean_object* v___y_3409_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = lean_st_ref_get(v_a_3394_);
v___x_3412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v___x_3411_, v_e_3393_);
lean_dec(v___x_3411_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v___x_3413_; 
lean_inc_ref(v_g_3392_);
lean_inc(v___y_3400_);
lean_inc_ref(v___y_3399_);
lean_inc(v___y_3398_);
lean_inc_ref(v___y_3397_);
lean_inc(v___y_3396_);
lean_inc_ref(v___y_3395_);
lean_inc_ref(v_e_3393_);
v___x_3413_ = lean_apply_8(v_g_3392_, v_e_3393_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, lean_box(0));
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v_d_3416_; lean_object* v_b_3417_; lean_object* v___y_3418_; uint8_t v___x_3421_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref(v___x_3413_);
v___x_3421_ = lean_unbox(v_a_3414_);
lean_dec(v_a_3414_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; 
lean_dec_ref(v_g_3392_);
v___x_3422_ = lean_box(0);
v_a_3403_ = v___x_3422_;
goto v___jp_3402_;
}
else
{
switch(lean_obj_tag(v_e_3393_))
{
case 7:
{
lean_object* v_binderType_3423_; lean_object* v_body_3424_; 
v_binderType_3423_ = lean_ctor_get(v_e_3393_, 1);
v_body_3424_ = lean_ctor_get(v_e_3393_, 2);
lean_inc_ref(v_body_3424_);
lean_inc_ref(v_binderType_3423_);
v_d_3416_ = v_binderType_3423_;
v_b_3417_ = v_body_3424_;
v___y_3418_ = v_a_3394_;
goto v___jp_3415_;
}
case 6:
{
lean_object* v_binderType_3425_; lean_object* v_body_3426_; 
v_binderType_3425_ = lean_ctor_get(v_e_3393_, 1);
v_body_3426_ = lean_ctor_get(v_e_3393_, 2);
lean_inc_ref(v_body_3426_);
lean_inc_ref(v_binderType_3425_);
v_d_3416_ = v_binderType_3425_;
v_b_3417_ = v_body_3426_;
v___y_3418_ = v_a_3394_;
goto v___jp_3415_;
}
case 8:
{
lean_object* v_type_3427_; lean_object* v_value_3428_; lean_object* v_body_3429_; lean_object* v___x_3430_; 
v_type_3427_ = lean_ctor_get(v_e_3393_, 1);
v_value_3428_ = lean_ctor_get(v_e_3393_, 2);
v_body_3429_ = lean_ctor_get(v_e_3393_, 3);
lean_inc_ref(v_type_3427_);
lean_inc_ref(v_g_3392_);
v___x_3430_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3392_, v_type_3427_, v_a_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v___x_3431_; 
lean_dec_ref(v___x_3430_);
lean_inc_ref(v_value_3428_);
lean_inc_ref(v_g_3392_);
v___x_3431_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3392_, v_value_3428_, v_a_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v___x_3432_; 
lean_dec_ref(v___x_3431_);
lean_inc_ref(v_body_3429_);
v___x_3432_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3392_, v_body_3429_, v_a_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
v___y_3409_ = v___x_3432_;
goto v___jp_3408_;
}
else
{
lean_dec_ref(v_g_3392_);
v___y_3409_ = v___x_3431_;
goto v___jp_3408_;
}
}
else
{
lean_dec_ref(v_g_3392_);
v___y_3409_ = v___x_3430_;
goto v___jp_3408_;
}
}
case 5:
{
lean_object* v_fn_3433_; lean_object* v_arg_3434_; lean_object* v___x_3435_; 
v_fn_3433_ = lean_ctor_get(v_e_3393_, 0);
v_arg_3434_ = lean_ctor_get(v_e_3393_, 1);
lean_inc_ref(v_fn_3433_);
lean_inc_ref(v_g_3392_);
v___x_3435_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3392_, v_fn_3433_, v_a_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v___x_3436_; 
lean_dec_ref(v___x_3435_);
lean_inc_ref(v_arg_3434_);
v___x_3436_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3392_, v_arg_3434_, v_a_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
v___y_3409_ = v___x_3436_;
goto v___jp_3408_;
}
else
{
lean_dec_ref(v_g_3392_);
v___y_3409_ = v___x_3435_;
goto v___jp_3408_;
}
}
case 10:
{
lean_object* v_expr_3437_; lean_object* v___x_3438_; 
v_expr_3437_ = lean_ctor_get(v_e_3393_, 1);
lean_inc_ref(v_expr_3437_);
v___x_3438_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3392_, v_expr_3437_, v_a_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
v___y_3409_ = v___x_3438_;
goto v___jp_3408_;
}
case 11:
{
lean_object* v_struct_3439_; lean_object* v___x_3440_; 
v_struct_3439_ = lean_ctor_get(v_e_3393_, 2);
lean_inc_ref(v_struct_3439_);
v___x_3440_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3392_, v_struct_3439_, v_a_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
v___y_3409_ = v___x_3440_;
goto v___jp_3408_;
}
default: 
{
lean_object* v___x_3441_; 
lean_dec_ref(v_g_3392_);
v___x_3441_ = lean_box(0);
v_a_3403_ = v___x_3441_;
goto v___jp_3402_;
}
}
}
v___jp_3415_:
{
lean_object* v___x_3419_; 
lean_inc_ref(v_g_3392_);
v___x_3419_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3392_, v_d_3416_, v___y_3418_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v___x_3420_; 
lean_dec_ref(v___x_3419_);
v___x_3420_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3392_, v_b_3417_, v___y_3418_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
v___y_3409_ = v___x_3420_;
goto v___jp_3408_;
}
else
{
lean_dec_ref(v_b_3417_);
lean_dec_ref(v_g_3392_);
v___y_3409_ = v___x_3419_;
goto v___jp_3408_;
}
}
}
else
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec_ref(v_e_3393_);
lean_dec_ref(v_g_3392_);
v_a_3442_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___x_3413_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3413_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
else
{
lean_object* v_val_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
lean_dec_ref(v_e_3393_);
lean_dec_ref(v_g_3392_);
v_val_3450_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3412_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_val_3450_);
lean_dec(v___x_3412_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set_tag(v___x_3452_, 0);
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_val_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
v___jp_3402_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3404_ = lean_st_ref_take(v_a_3394_);
v___x_3405_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v___x_3404_, v_e_3393_, v_a_3403_);
v___x_3406_ = lean_st_ref_set(v_a_3394_, v___x_3405_);
v___x_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3407_, 0, v_a_3403_);
return v___x_3407_;
}
v___jp_3408_:
{
if (lean_obj_tag(v___y_3409_) == 0)
{
lean_object* v_a_3410_; 
v_a_3410_ = lean_ctor_get(v___y_3409_, 0);
lean_inc(v_a_3410_);
lean_dec_ref(v___y_3409_);
v_a_3403_ = v_a_3410_;
goto v___jp_3402_;
}
else
{
lean_dec_ref(v_e_3393_);
return v___y_3409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1___boxed(lean_object* v_g_3458_, lean_object* v_e_3459_, lean_object* v_a_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3458_, v_e_3459_, v_a_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v_a_3460_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared(lean_object* v_e_3469_, lean_object* v_msg_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___f_3480_; lean_object* v___x_3481_; 
v___x_3478_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_3479_ = lean_st_mk_ref(v___x_3478_);
v___f_3480_ = lean_alloc_closure((void*)(l_Lean_Expr_checkMaxShared___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3480_, 0, v_msg_3470_);
v___x_3481_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v___f_3480_, v_e_3469_, v___x_3479_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3490_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3490_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3490_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___x_3486_ = lean_st_ref_get(v___x_3479_);
lean_dec(v___x_3479_);
lean_dec(v___x_3486_);
if (v_isShared_3485_ == 0)
{
v___x_3488_ = v___x_3484_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3482_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
else
{
lean_dec(v___x_3479_);
return v___x_3481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___boxed(lean_object* v_e_3491_, lean_object* v_msg_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_Expr_checkMaxShared(v_e_3491_, v_msg_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_);
lean_dec(v_a_3498_);
lean_dec_ref(v_a_3497_);
lean_dec(v_a_3496_);
lean_dec_ref(v_a_3495_);
lean_dec(v_a_3494_);
lean_dec_ref(v_a_3493_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(lean_object* v_00_u03b2_3501_, lean_object* v_x_3502_, lean_object* v_x_3503_){
_start:
{
lean_object* v___x_3504_; 
v___x_3504_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_3502_, v_x_3503_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___boxed(lean_object* v_00_u03b2_3505_, lean_object* v_x_3506_, lean_object* v_x_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(v_00_u03b2_3505_, v_x_3506_, v_x_3507_);
lean_dec_ref(v_x_3506_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(lean_object* v_00_u03b2_3509_, lean_object* v_x_3510_, size_t v_x_3511_, lean_object* v_x_3512_){
_start:
{
lean_object* v___x_3513_; 
lean_inc_ref(v_x_3510_);
v___x_3513_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3510_, v_x_3511_, v_x_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3514_, lean_object* v_x_3515_, lean_object* v_x_3516_, lean_object* v_x_3517_){
_start:
{
size_t v_x_8018__boxed_3518_; lean_object* v_res_3519_; 
v_x_8018__boxed_3518_ = lean_unbox_usize(v_x_3516_);
lean_dec(v_x_3516_);
v_res_3519_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(v_00_u03b2_3514_, v_x_3515_, v_x_8018__boxed_3518_, v_x_3517_);
lean_dec_ref(v_x_3515_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(lean_object* v_00_u03b2_3520_, lean_object* v_m_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_3521_, v_a_3522_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3524_, lean_object* v_m_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(v_00_u03b2_3524_, v_m_3525_, v_a_3526_);
lean_dec_ref(v_a_3526_);
lean_dec_ref(v_m_3525_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(lean_object* v_00_u03b2_3528_, lean_object* v_m_3529_, lean_object* v_a_3530_, lean_object* v_b_3531_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v_m_3529_, v_a_3530_, v_b_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3533_, lean_object* v_keys_3534_, lean_object* v_vals_3535_, lean_object* v_heq_3536_, lean_object* v_i_3537_, lean_object* v_k_3538_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_3534_, v_vals_3535_, v_i_3537_, v_k_3538_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3540_, lean_object* v_keys_3541_, lean_object* v_vals_3542_, lean_object* v_heq_3543_, lean_object* v_i_3544_, lean_object* v_k_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(v_00_u03b2_3540_, v_keys_3541_, v_vals_3542_, v_heq_3543_, v_i_3544_, v_k_3545_);
lean_dec_ref(v_vals_3542_);
lean_dec_ref(v_keys_3541_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3547_, lean_object* v_a_3548_, lean_object* v_x_3549_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3548_, v_x_3549_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_3551_, lean_object* v_a_3552_, lean_object* v_x_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(v_00_u03b2_3551_, v_a_3552_, v_x_3553_);
lean_dec(v_x_3553_);
lean_dec_ref(v_a_3552_);
return v_res_3554_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_3555_, lean_object* v_a_3556_, lean_object* v_x_3557_){
_start:
{
uint8_t v___x_3558_; 
v___x_3558_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3556_, v_x_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3559_, lean_object* v_a_3560_, lean_object* v_x_3561_){
_start:
{
uint8_t v_res_3562_; lean_object* v_r_3563_; 
v_res_3562_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(v_00_u03b2_3559_, v_a_3560_, v_x_3561_);
lean_dec(v_x_3561_);
lean_dec_ref(v_a_3560_);
v_r_3563_ = lean_box(v_res_3562_);
return v_r_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3564_, lean_object* v_data_3565_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_data_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_3567_, lean_object* v_a_3568_, lean_object* v_b_3569_, lean_object* v_x_3570_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3568_, v_b_3569_, v_x_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_3572_, lean_object* v_i_3573_, lean_object* v_source_3574_, lean_object* v_target_3575_){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v_i_3573_, v_source_3574_, v_target_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9(lean_object* v_00_u03b2_3577_, lean_object* v_x_3578_, lean_object* v_x_3579_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_x_3578_, v_x_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared(lean_object* v_mvarId_3581_, lean_object* v_msg_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Lean_MVarId_getDecl(v_mvarId_3581_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v_type_3592_; lean_object* v___x_3593_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref(v___x_3590_);
v_type_3592_ = lean_ctor_get(v_a_3591_, 2);
lean_inc_ref(v_type_3592_);
lean_dec(v_a_3591_);
v___x_3593_ = l_Lean_Expr_checkMaxShared(v_type_3592_, v_msg_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
return v___x_3593_;
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec_ref(v_msg_3582_);
v_a_3594_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3590_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3590_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared___boxed(lean_object* v_mvarId_3602_, lean_object* v_msg_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_MVarId_checkMaxShared(v_mvarId_3602_, v_msg_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
lean_dec(v_a_3607_);
lean_dec_ref(v_a_3606_);
lean_dec(v_a_3605_);
lean_dec_ref(v_a_3604_);
return v_res_3611_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(lean_object* v_x_3612_){
_start:
{
if (lean_obj_tag(v_x_3612_) == 0)
{
uint8_t v___x_3613_; 
v___x_3613_ = 0;
return v___x_3613_;
}
else
{
lean_object* v_head_3614_; lean_object* v_tail_3615_; uint8_t v___x_3616_; 
v_head_3614_ = lean_ctor_get(v_x_3612_, 0);
v_tail_3615_ = lean_ctor_get(v_x_3612_, 1);
v___x_3616_ = l_Lean_Level_isAlreadyNormalizedCheap(v_head_3614_);
if (v___x_3616_ == 0)
{
uint8_t v___x_3617_; 
v___x_3617_ = 1;
return v___x_3617_;
}
else
{
v_x_3612_ = v_tail_3615_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0___boxed(lean_object* v_x_3619_){
_start:
{
uint8_t v_res_3620_; lean_object* v_r_3621_; 
v_res_3620_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_x_3619_);
lean_dec(v_x_3619_);
v_r_3621_ = lean_box(v_res_3620_);
return v_r_3621_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(lean_object* v_x_3622_){
_start:
{
switch(lean_obj_tag(v_x_3622_))
{
case 4:
{
lean_object* v_us_3623_; uint8_t v___x_3624_; 
v_us_3623_ = lean_ctor_get(v_x_3622_, 1);
v___x_3624_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_us_3623_);
return v___x_3624_;
}
case 3:
{
lean_object* v_u_3625_; uint8_t v___x_3626_; 
v_u_3625_ = lean_ctor_get(v_x_3622_, 0);
v___x_3626_ = l_Lean_Level_isAlreadyNormalizedCheap(v_u_3625_);
if (v___x_3626_ == 0)
{
uint8_t v___x_3627_; 
v___x_3627_ = 1;
return v___x_3627_;
}
else
{
uint8_t v___x_3628_; 
v___x_3628_ = 0;
return v___x_3628_;
}
}
default: 
{
uint8_t v___x_3629_; 
v___x_3629_ = 0;
return v___x_3629_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed(lean_object* v_x_3630_){
_start:
{
uint8_t v_res_3631_; lean_object* v_r_3632_; 
v_res_3631_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(v_x_3630_);
lean_dec_ref(v_x_3630_);
v_r_3632_ = lean_box(v_res_3631_);
return v_r_3632_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(lean_object* v_e_3634_){
_start:
{
lean_object* v___f_3635_; lean_object* v___x_3636_; 
v___f_3635_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0));
v___x_3636_ = lean_find_expr(v___f_3635_, v_e_3634_);
if (lean_obj_tag(v___x_3636_) == 0)
{
uint8_t v___x_3637_; 
v___x_3637_ = 1;
return v___x_3637_;
}
else
{
uint8_t v___x_3638_; 
lean_dec_ref(v___x_3636_);
v___x_3638_ = 0;
return v___x_3638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___boxed(lean_object* v_e_3639_){
_start:
{
uint8_t v_res_3640_; lean_object* v_r_3641_; 
v_res_3640_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_3639_);
lean_dec_ref(v_e_3639_);
v_r_3641_ = lean_box(v_res_3640_);
return v_r_3641_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(lean_object* v_a_3642_, lean_object* v_a_3643_){
_start:
{
if (lean_obj_tag(v_a_3642_) == 0)
{
lean_object* v___x_3644_; 
v___x_3644_ = l_List_reverse___redArg(v_a_3643_);
return v___x_3644_;
}
else
{
lean_object* v_head_3645_; lean_object* v_tail_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3655_; 
v_head_3645_ = lean_ctor_get(v_a_3642_, 0);
v_tail_3646_ = lean_ctor_get(v_a_3642_, 1);
v_isSharedCheck_3655_ = !lean_is_exclusive(v_a_3642_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3648_ = v_a_3642_;
v_isShared_3649_ = v_isSharedCheck_3655_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_tail_3646_);
lean_inc(v_head_3645_);
lean_dec(v_a_3642_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3655_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3650_; lean_object* v___x_3652_; 
v___x_3650_ = l_Lean_Level_normalize(v_head_3645_);
lean_dec(v_head_3645_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 1, v_a_3643_);
lean_ctor_set(v___x_3648_, 0, v___x_3650_);
v___x_3652_ = v___x_3648_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3650_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v_a_3643_);
v___x_3652_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
v_a_3642_ = v_tail_3646_;
v_a_3643_ = v___x_3652_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0(lean_object* v_e_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v___y_3661_; lean_object* v___y_3665_; 
switch(lean_obj_tag(v_e_3656_))
{
case 3:
{
lean_object* v_u_3668_; lean_object* v___x_3669_; size_t v___x_3670_; size_t v___x_3671_; uint8_t v___x_3672_; 
v_u_3668_ = lean_ctor_get(v_e_3656_, 0);
v___x_3669_ = l_Lean_Level_normalize(v_u_3668_);
v___x_3670_ = lean_ptr_addr(v_u_3668_);
v___x_3671_ = lean_ptr_addr(v___x_3669_);
v___x_3672_ = lean_usize_dec_eq(v___x_3670_, v___x_3671_);
if (v___x_3672_ == 0)
{
lean_object* v___x_3673_; 
lean_dec_ref(v_e_3656_);
v___x_3673_ = l_Lean_Expr_sort___override(v___x_3669_);
v___y_3661_ = v___x_3673_;
goto v___jp_3660_;
}
else
{
lean_dec(v___x_3669_);
v___y_3661_ = v_e_3656_;
goto v___jp_3660_;
}
}
case 4:
{
lean_object* v_declName_3674_; lean_object* v_us_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; uint8_t v___x_3678_; 
v_declName_3674_ = lean_ctor_get(v_e_3656_, 0);
v_us_3675_ = lean_ctor_get(v_e_3656_, 1);
v___x_3676_ = lean_box(0);
lean_inc(v_us_3675_);
v___x_3677_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(v_us_3675_, v___x_3676_);
v___x_3678_ = l_ptrEqList___redArg(v_us_3675_, v___x_3677_);
if (v___x_3678_ == 0)
{
lean_object* v___x_3679_; 
lean_inc(v_declName_3674_);
lean_dec_ref(v_e_3656_);
v___x_3679_ = l_Lean_Expr_const___override(v_declName_3674_, v___x_3677_);
v___y_3665_ = v___x_3679_;
goto v___jp_3664_;
}
else
{
lean_dec(v___x_3677_);
v___y_3665_ = v_e_3656_;
goto v___jp_3664_;
}
}
default: 
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
lean_dec_ref(v_e_3656_);
v___x_3680_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
return v___x_3681_;
}
}
v___jp_3660_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3662_, 0, v___y_3661_);
v___x_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
return v___x_3663_;
}
v___jp_3664_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3666_, 0, v___y_3665_);
v___x_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
return v___x_3667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed(lean_object* v_e_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_Lean_Meta_Sym_normalizeLevels___lam__0(v_e_3682_, v___y_3683_, v___y_3684_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1(lean_object* v_e_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3691_, 0, v_e_3687_);
v___x_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed(lean_object* v_e_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l_Lean_Meta_Sym_normalizeLevels___lam__1(v_e_3693_, v___y_3694_, v___y_3695_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_ref_3698_){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3700_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_3701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3701_, 0, v_ref_3698_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v___x_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_ref_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_3703_);
return v_res_3705_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3706_ = lean_box(0);
v___x_3707_ = l_Lean_interruptExceptionId;
v___x_3708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
lean_ctor_set(v___x_3708_, 1, v___x_3706_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg(){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0);
v___x_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v___y_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(lean_object* v_x_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v___y_3720_; lean_object* v___y_3730_; lean_object* v___y_3731_; uint8_t v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; uint8_t v___y_3745_; lean_object* v_fileName_3750_; lean_object* v_fileMap_3751_; lean_object* v_options_3752_; lean_object* v_currRecDepth_3753_; lean_object* v_maxRecDepth_3754_; lean_object* v_ref_3755_; lean_object* v_currNamespace_3756_; lean_object* v_openDecls_3757_; lean_object* v_initHeartbeats_3758_; lean_object* v_maxHeartbeats_3759_; lean_object* v_quotContext_3760_; lean_object* v_currMacroScope_3761_; uint8_t v_diag_3762_; lean_object* v_cancelTk_x3f_3763_; uint8_t v_suppressElabErrors_3764_; lean_object* v_inheritedTraceOptions_3765_; 
v_fileName_3750_ = lean_ctor_get(v___y_3716_, 0);
v_fileMap_3751_ = lean_ctor_get(v___y_3716_, 1);
v_options_3752_ = lean_ctor_get(v___y_3716_, 2);
v_currRecDepth_3753_ = lean_ctor_get(v___y_3716_, 3);
v_maxRecDepth_3754_ = lean_ctor_get(v___y_3716_, 4);
v_ref_3755_ = lean_ctor_get(v___y_3716_, 5);
v_currNamespace_3756_ = lean_ctor_get(v___y_3716_, 6);
v_openDecls_3757_ = lean_ctor_get(v___y_3716_, 7);
v_initHeartbeats_3758_ = lean_ctor_get(v___y_3716_, 8);
v_maxHeartbeats_3759_ = lean_ctor_get(v___y_3716_, 9);
v_quotContext_3760_ = lean_ctor_get(v___y_3716_, 10);
v_currMacroScope_3761_ = lean_ctor_get(v___y_3716_, 11);
v_diag_3762_ = lean_ctor_get_uint8(v___y_3716_, sizeof(void*)*14);
v_cancelTk_x3f_3763_ = lean_ctor_get(v___y_3716_, 12);
v_suppressElabErrors_3764_ = lean_ctor_get_uint8(v___y_3716_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3765_ = lean_ctor_get(v___y_3716_, 13);
if (lean_obj_tag(v_cancelTk_x3f_3763_) == 1)
{
lean_object* v_val_3771_; uint8_t v___x_3772_; 
v_val_3771_ = lean_ctor_get(v_cancelTk_x3f_3763_, 0);
v___x_3772_ = l_IO_CancelToken_isSet(v_val_3771_);
if (v___x_3772_ == 0)
{
goto v___jp_3766_;
}
else
{
lean_object* v___x_3773_; lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
lean_dec_ref(v_x_3714_);
v___x_3773_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___x_3773_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3773_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
else
{
goto v___jp_3766_;
}
v___jp_3719_:
{
if (lean_obj_tag(v___y_3720_) == 0)
{
return v___y_3720_;
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
v_a_3721_ = lean_ctor_get(v___y_3720_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___y_3720_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___y_3720_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___y_3720_);
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
v___jp_3729_:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3746_ = lean_unsigned_to_nat(1u);
v___x_3747_ = lean_nat_add(v___y_3735_, v___x_3746_);
lean_inc_ref(v___y_3737_);
lean_inc(v___y_3731_);
lean_inc(v___y_3734_);
lean_inc(v___y_3744_);
lean_inc(v___y_3742_);
lean_inc(v___y_3730_);
lean_inc(v___y_3740_);
lean_inc(v___y_3739_);
lean_inc(v___y_3741_);
lean_inc_ref(v___y_3743_);
lean_inc_ref(v___y_3736_);
lean_inc_ref(v___y_3738_);
v___x_3748_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3748_, 0, v___y_3738_);
lean_ctor_set(v___x_3748_, 1, v___y_3736_);
lean_ctor_set(v___x_3748_, 2, v___y_3743_);
lean_ctor_set(v___x_3748_, 3, v___x_3747_);
lean_ctor_set(v___x_3748_, 4, v___y_3741_);
lean_ctor_set(v___x_3748_, 5, v___y_3733_);
lean_ctor_set(v___x_3748_, 6, v___y_3739_);
lean_ctor_set(v___x_3748_, 7, v___y_3740_);
lean_ctor_set(v___x_3748_, 8, v___y_3730_);
lean_ctor_set(v___x_3748_, 9, v___y_3742_);
lean_ctor_set(v___x_3748_, 10, v___y_3744_);
lean_ctor_set(v___x_3748_, 11, v___y_3734_);
lean_ctor_set(v___x_3748_, 12, v___y_3731_);
lean_ctor_set(v___x_3748_, 13, v___y_3737_);
lean_ctor_set_uint8(v___x_3748_, sizeof(void*)*14, v___y_3732_);
lean_ctor_set_uint8(v___x_3748_, sizeof(void*)*14 + 1, v___y_3745_);
lean_inc(v___y_3717_);
lean_inc(v___y_3715_);
v___x_3749_ = lean_apply_4(v_x_3714_, v___y_3715_, v___x_3748_, v___y_3717_, lean_box(0));
v___y_3720_ = v___x_3749_;
goto v___jp_3719_;
}
v___jp_3766_:
{
lean_object* v___x_3767_; uint8_t v___x_3768_; 
v___x_3767_ = lean_unsigned_to_nat(0u);
v___x_3768_ = lean_nat_dec_eq(v_maxRecDepth_3754_, v___x_3767_);
if (v___x_3768_ == 0)
{
uint8_t v___x_3769_; 
v___x_3769_ = lean_nat_dec_eq(v_currRecDepth_3753_, v_maxRecDepth_3754_);
if (v___x_3769_ == 0)
{
lean_inc(v_ref_3755_);
v___y_3730_ = v_initHeartbeats_3758_;
v___y_3731_ = v_cancelTk_x3f_3763_;
v___y_3732_ = v_diag_3762_;
v___y_3733_ = v_ref_3755_;
v___y_3734_ = v_currMacroScope_3761_;
v___y_3735_ = v_currRecDepth_3753_;
v___y_3736_ = v_fileMap_3751_;
v___y_3737_ = v_inheritedTraceOptions_3765_;
v___y_3738_ = v_fileName_3750_;
v___y_3739_ = v_currNamespace_3756_;
v___y_3740_ = v_openDecls_3757_;
v___y_3741_ = v_maxRecDepth_3754_;
v___y_3742_ = v_maxHeartbeats_3759_;
v___y_3743_ = v_options_3752_;
v___y_3744_ = v_quotContext_3760_;
v___y_3745_ = v_suppressElabErrors_3764_;
goto v___jp_3729_;
}
else
{
lean_object* v___x_3770_; 
lean_dec_ref(v_x_3714_);
lean_inc(v_ref_3755_);
v___x_3770_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_3755_);
v___y_3720_ = v___x_3770_;
goto v___jp_3719_;
}
}
else
{
lean_inc(v_ref_3755_);
v___y_3730_ = v_initHeartbeats_3758_;
v___y_3731_ = v_cancelTk_x3f_3763_;
v___y_3732_ = v_diag_3762_;
v___y_3733_ = v_ref_3755_;
v___y_3734_ = v_currMacroScope_3761_;
v___y_3735_ = v_currRecDepth_3753_;
v___y_3736_ = v_fileMap_3751_;
v___y_3737_ = v_inheritedTraceOptions_3765_;
v___y_3738_ = v_fileName_3750_;
v___y_3739_ = v_currNamespace_3756_;
v___y_3740_ = v_openDecls_3757_;
v___y_3741_ = v_maxRecDepth_3754_;
v___y_3742_ = v_maxHeartbeats_3759_;
v___y_3743_ = v_options_3752_;
v___y_3744_ = v_quotContext_3760_;
v___y_3745_ = v_suppressElabErrors_3764_;
goto v___jp_3729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_x_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v_x_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3788_, lean_object* v_x_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3793_ = lean_apply_1(v_x_3789_, lean_box(0));
v___x_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3795_, lean_object* v_x_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(v_00_u03b1_3795_, v_x_3796_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(lean_object* v_pre_3801_, lean_object* v_post_3802_, size_t v_sz_3803_, size_t v_i_3804_, lean_object* v_bs_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
uint8_t v___x_3810_; 
v___x_3810_ = lean_usize_dec_lt(v_i_3804_, v_sz_3803_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; 
lean_dec_ref(v_post_3802_);
lean_dec_ref(v_pre_3801_);
v___x_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3811_, 0, v_bs_3805_);
return v___x_3811_;
}
else
{
lean_object* v_v_3812_; lean_object* v___x_3813_; 
v_v_3812_ = lean_array_uget_borrowed(v_bs_3805_, v_i_3804_);
lean_inc(v_v_3812_);
lean_inc_ref(v_post_3802_);
lean_inc_ref(v_pre_3801_);
v___x_3813_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3801_, v_post_3802_, v_v_3812_, v___y_3806_, v___y_3807_, v___y_3808_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v_a_3814_; lean_object* v___x_3815_; lean_object* v_bs_x27_3816_; size_t v___x_3817_; size_t v___x_3818_; lean_object* v___x_3819_; 
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3814_);
lean_dec_ref(v___x_3813_);
v___x_3815_ = lean_unsigned_to_nat(0u);
v_bs_x27_3816_ = lean_array_uset(v_bs_3805_, v_i_3804_, v___x_3815_);
v___x_3817_ = ((size_t)1ULL);
v___x_3818_ = lean_usize_add(v_i_3804_, v___x_3817_);
v___x_3819_ = lean_array_uset(v_bs_x27_3816_, v_i_3804_, v_a_3814_);
v_i_3804_ = v___x_3818_;
v_bs_3805_ = v___x_3819_;
goto _start;
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec_ref(v_bs_3805_);
lean_dec_ref(v_post_3802_);
lean_dec_ref(v_pre_3801_);
v_a_3821_ = lean_ctor_get(v___x_3813_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3813_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3813_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(lean_object* v_pre_3829_, lean_object* v_post_3830_, lean_object* v_x_3831_, lean_object* v_x_3832_, lean_object* v_x_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
if (lean_obj_tag(v_x_3831_) == 5)
{
lean_object* v_fn_3838_; lean_object* v_arg_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v_fn_3838_ = lean_ctor_get(v_x_3831_, 0);
lean_inc_ref(v_fn_3838_);
v_arg_3839_ = lean_ctor_get(v_x_3831_, 1);
lean_inc_ref(v_arg_3839_);
lean_dec_ref(v_x_3831_);
v___x_3840_ = lean_array_set(v_x_3832_, v_x_3833_, v_arg_3839_);
v___x_3841_ = lean_unsigned_to_nat(1u);
v___x_3842_ = lean_nat_sub(v_x_3833_, v___x_3841_);
lean_dec(v_x_3833_);
v_x_3831_ = v_fn_3838_;
v_x_3832_ = v___x_3840_;
v_x_3833_ = v___x_3842_;
goto _start;
}
else
{
lean_object* v___x_3844_; 
lean_dec(v_x_3833_);
lean_inc_ref(v_post_3830_);
lean_inc_ref(v_pre_3829_);
v___x_3844_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3829_, v_post_3830_, v_x_3831_, v___y_3834_, v___y_3835_, v___y_3836_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; size_t v_sz_3846_; size_t v___x_3847_; lean_object* v___x_3848_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref(v___x_3844_);
v_sz_3846_ = lean_array_size(v_x_3832_);
v___x_3847_ = ((size_t)0ULL);
lean_inc_ref(v_post_3830_);
lean_inc_ref(v_pre_3829_);
v___x_3848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_3829_, v_post_3830_, v_sz_3846_, v___x_3847_, v_x_3832_, v___y_3834_, v___y_3835_, v___y_3836_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
lean_dec_ref(v___x_3848_);
v___x_3850_ = l_Lean_mkAppN(v_a_3845_, v_a_3849_);
lean_dec(v_a_3849_);
v___x_3851_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3829_, v_post_3830_, v___x_3850_, v___y_3834_, v___y_3835_, v___y_3836_);
return v___x_3851_;
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_dec(v_a_3845_);
lean_dec_ref(v_post_3830_);
lean_dec_ref(v_pre_3829_);
v_a_3852_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3848_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3848_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
else
{
lean_dec_ref(v_x_3832_);
lean_dec_ref(v_post_3830_);
lean_dec_ref(v_pre_3829_);
return v___x_3844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(lean_object* v___x_3860_, lean_object* v_pre_3861_, lean_object* v_e_3862_, lean_object* v_post_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; uint8_t v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; uint8_t v___y_3876_; lean_object* v___y_3886_; lean_object* v___y_3887_; uint8_t v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; uint8_t v___y_3891_; lean_object* v___y_3899_; uint8_t v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; uint8_t v___y_3904_; lean_object* v___x_3911_; 
v___x_3911_ = l_Lean_Core_checkSystem(v___x_3860_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v___x_3912_; 
lean_dec_ref(v___x_3911_);
lean_inc_ref(v_pre_3861_);
lean_inc(v___y_3866_);
lean_inc_ref(v___y_3865_);
lean_inc_ref(v_e_3862_);
v___x_3912_ = lean_apply_4(v_pre_3861_, v_e_3862_, v___y_3865_, v___y_3866_, lean_box(0));
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_4002_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3915_ = v___x_3912_;
v_isShared_3916_ = v_isSharedCheck_4002_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3912_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_4002_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___y_3918_; 
switch(lean_obj_tag(v_a_3913_))
{
case 0:
{
lean_object* v_e_3992_; lean_object* v___x_3994_; 
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_e_3862_);
lean_dec_ref(v_pre_3861_);
v_e_3992_ = lean_ctor_get(v_a_3913_, 0);
lean_inc_ref(v_e_3992_);
lean_dec_ref(v_a_3913_);
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 0, v_e_3992_);
v___x_3994_ = v___x_3915_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_e_3992_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
case 1:
{
lean_object* v_e_3996_; lean_object* v___x_3997_; 
lean_del_object(v___x_3915_);
lean_dec_ref(v_e_3862_);
v_e_3996_ = lean_ctor_get(v_a_3913_, 0);
lean_inc_ref(v_e_3996_);
lean_dec_ref(v_a_3913_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3997_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3861_, v_post_3863_, v_e_3996_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v___x_3999_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_a_3998_);
lean_dec_ref(v___x_3997_);
v___x_3999_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v_a_3998_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3999_;
}
else
{
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3997_;
}
}
default: 
{
lean_object* v_e_x3f_4000_; 
lean_del_object(v___x_3915_);
v_e_x3f_4000_ = lean_ctor_get(v_a_3913_, 0);
lean_inc(v_e_x3f_4000_);
lean_dec_ref(v_a_3913_);
if (lean_obj_tag(v_e_x3f_4000_) == 0)
{
v___y_3918_ = v_e_3862_;
goto v___jp_3917_;
}
else
{
lean_object* v_val_4001_; 
lean_dec_ref(v_e_3862_);
v_val_4001_ = lean_ctor_get(v_e_x3f_4000_, 0);
lean_inc(v_val_4001_);
lean_dec_ref(v_e_x3f_4000_);
v___y_3918_ = v_val_4001_;
goto v___jp_3917_;
}
}
}
v___jp_3917_:
{
switch(lean_obj_tag(v___y_3918_))
{
case 7:
{
lean_object* v_binderName_3919_; lean_object* v_binderType_3920_; lean_object* v_body_3921_; uint8_t v_binderInfo_3922_; lean_object* v___x_3923_; 
v_binderName_3919_ = lean_ctor_get(v___y_3918_, 0);
lean_inc(v_binderName_3919_);
v_binderType_3920_ = lean_ctor_get(v___y_3918_, 1);
v_body_3921_ = lean_ctor_get(v___y_3918_, 2);
v_binderInfo_3922_ = lean_ctor_get_uint8(v___y_3918_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3920_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3923_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3861_, v_post_3863_, v_binderType_3920_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3925_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref(v___x_3923_);
lean_inc_ref(v_body_3921_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3925_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3861_, v_post_3863_, v_body_3921_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; size_t v___x_3927_; size_t v___x_3928_; uint8_t v___x_3929_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3926_);
lean_dec_ref(v___x_3925_);
v___x_3927_ = lean_ptr_addr(v_binderType_3920_);
v___x_3928_ = lean_ptr_addr(v_a_3924_);
v___x_3929_ = lean_usize_dec_eq(v___x_3927_, v___x_3928_);
if (v___x_3929_ == 0)
{
v___y_3899_ = v_binderName_3919_;
v___y_3900_ = v_binderInfo_3922_;
v___y_3901_ = v_a_3926_;
v___y_3902_ = v_a_3924_;
v___y_3903_ = v___y_3918_;
v___y_3904_ = v___x_3929_;
goto v___jp_3898_;
}
else
{
size_t v___x_3930_; size_t v___x_3931_; uint8_t v___x_3932_; 
v___x_3930_ = lean_ptr_addr(v_body_3921_);
v___x_3931_ = lean_ptr_addr(v_a_3926_);
v___x_3932_ = lean_usize_dec_eq(v___x_3930_, v___x_3931_);
v___y_3899_ = v_binderName_3919_;
v___y_3900_ = v_binderInfo_3922_;
v___y_3901_ = v_a_3926_;
v___y_3902_ = v_a_3924_;
v___y_3903_ = v___y_3918_;
v___y_3904_ = v___x_3932_;
goto v___jp_3898_;
}
}
else
{
lean_dec(v_a_3924_);
lean_dec(v_binderName_3919_);
lean_dec_ref(v___y_3918_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3925_;
}
}
else
{
lean_dec(v_binderName_3919_);
lean_dec_ref(v___y_3918_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3923_;
}
}
case 6:
{
lean_object* v_binderName_3933_; lean_object* v_binderType_3934_; lean_object* v_body_3935_; uint8_t v_binderInfo_3936_; lean_object* v___x_3937_; 
v_binderName_3933_ = lean_ctor_get(v___y_3918_, 0);
lean_inc(v_binderName_3933_);
v_binderType_3934_ = lean_ctor_get(v___y_3918_, 1);
v_body_3935_ = lean_ctor_get(v___y_3918_, 2);
v_binderInfo_3936_ = lean_ctor_get_uint8(v___y_3918_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3934_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3937_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3861_, v_post_3863_, v_binderType_3934_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3939_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref(v___x_3937_);
lean_inc_ref(v_body_3935_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3939_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3861_, v_post_3863_, v_body_3935_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; size_t v___x_3941_; size_t v___x_3942_; uint8_t v___x_3943_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3940_);
lean_dec_ref(v___x_3939_);
v___x_3941_ = lean_ptr_addr(v_binderType_3934_);
v___x_3942_ = lean_ptr_addr(v_a_3938_);
v___x_3943_ = lean_usize_dec_eq(v___x_3941_, v___x_3942_);
if (v___x_3943_ == 0)
{
v___y_3886_ = v_a_3938_;
v___y_3887_ = v_binderName_3933_;
v___y_3888_ = v_binderInfo_3936_;
v___y_3889_ = v_a_3940_;
v___y_3890_ = v___y_3918_;
v___y_3891_ = v___x_3943_;
goto v___jp_3885_;
}
else
{
size_t v___x_3944_; size_t v___x_3945_; uint8_t v___x_3946_; 
v___x_3944_ = lean_ptr_addr(v_body_3935_);
v___x_3945_ = lean_ptr_addr(v_a_3940_);
v___x_3946_ = lean_usize_dec_eq(v___x_3944_, v___x_3945_);
v___y_3886_ = v_a_3938_;
v___y_3887_ = v_binderName_3933_;
v___y_3888_ = v_binderInfo_3936_;
v___y_3889_ = v_a_3940_;
v___y_3890_ = v___y_3918_;
v___y_3891_ = v___x_3946_;
goto v___jp_3885_;
}
}
else
{
lean_dec(v_a_3938_);
lean_dec(v_binderName_3933_);
lean_dec_ref(v___y_3918_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3939_;
}
}
else
{
lean_dec(v_binderName_3933_);
lean_dec_ref(v___y_3918_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3937_;
}
}
case 8:
{
lean_object* v_declName_3947_; lean_object* v_type_3948_; lean_object* v_value_3949_; lean_object* v_body_3950_; uint8_t v_nondep_3951_; lean_object* v___x_3952_; 
v_declName_3947_ = lean_ctor_get(v___y_3918_, 0);
lean_inc(v_declName_3947_);
v_type_3948_ = lean_ctor_get(v___y_3918_, 1);
v_value_3949_ = lean_ctor_get(v___y_3918_, 2);
v_body_3950_ = lean_ctor_get(v___y_3918_, 3);
lean_inc_ref(v_body_3950_);
v_nondep_3951_ = lean_ctor_get_uint8(v___y_3918_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_3948_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3952_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3861_, v_post_3863_, v_type_3948_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3954_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3953_);
lean_dec_ref(v___x_3952_);
lean_inc_ref(v_value_3949_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3954_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3861_, v_post_3863_, v_value_3949_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3956_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3955_);
lean_dec_ref(v___x_3954_);
lean_inc_ref(v_body_3950_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3956_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3861_, v_post_3863_, v_body_3950_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; size_t v___x_3958_; size_t v___x_3959_; uint8_t v___x_3960_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc(v_a_3957_);
lean_dec_ref(v___x_3956_);
v___x_3958_ = lean_ptr_addr(v_type_3948_);
v___x_3959_ = lean_ptr_addr(v_a_3953_);
v___x_3960_ = lean_usize_dec_eq(v___x_3958_, v___x_3959_);
if (v___x_3960_ == 0)
{
v___y_3869_ = v_body_3950_;
v___y_3870_ = v_a_3953_;
v___y_3871_ = v_declName_3947_;
v___y_3872_ = v_a_3955_;
v___y_3873_ = v_nondep_3951_;
v___y_3874_ = v_a_3957_;
v___y_3875_ = v___y_3918_;
v___y_3876_ = v___x_3960_;
goto v___jp_3868_;
}
else
{
size_t v___x_3961_; size_t v___x_3962_; uint8_t v___x_3963_; 
v___x_3961_ = lean_ptr_addr(v_value_3949_);
v___x_3962_ = lean_ptr_addr(v_a_3955_);
v___x_3963_ = lean_usize_dec_eq(v___x_3961_, v___x_3962_);
v___y_3869_ = v_body_3950_;
v___y_3870_ = v_a_3953_;
v___y_3871_ = v_declName_3947_;
v___y_3872_ = v_a_3955_;
v___y_3873_ = v_nondep_3951_;
v___y_3874_ = v_a_3957_;
v___y_3875_ = v___y_3918_;
v___y_3876_ = v___x_3963_;
goto v___jp_3868_;
}
}
else
{
lean_dec(v_a_3955_);
lean_dec(v_a_3953_);
lean_dec_ref(v_body_3950_);
lean_dec_ref(v___y_3918_);
lean_dec(v_declName_3947_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3956_;
}
}
else
{
lean_dec(v_a_3953_);
lean_dec_ref(v_body_3950_);
lean_dec(v_declName_3947_);
lean_dec_ref(v___y_3918_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3954_;
}
}
else
{
lean_dec_ref(v_body_3950_);
lean_dec(v_declName_3947_);
lean_dec_ref(v___y_3918_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3952_;
}
}
case 5:
{
lean_object* v_dummy_3964_; lean_object* v_nargs_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v_dummy_3964_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_3965_ = l_Lean_Expr_getAppNumArgs(v___y_3918_);
lean_inc(v_nargs_3965_);
v___x_3966_ = lean_mk_array(v_nargs_3965_, v_dummy_3964_);
v___x_3967_ = lean_unsigned_to_nat(1u);
v___x_3968_ = lean_nat_sub(v_nargs_3965_, v___x_3967_);
lean_dec(v_nargs_3965_);
v___x_3969_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_3861_, v_post_3863_, v___y_3918_, v___x_3966_, v___x_3968_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3969_;
}
case 10:
{
lean_object* v_data_3970_; lean_object* v_expr_3971_; lean_object* v___x_3972_; 
v_data_3970_ = lean_ctor_get(v___y_3918_, 0);
v_expr_3971_ = lean_ctor_get(v___y_3918_, 1);
lean_inc_ref(v_expr_3971_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3972_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3861_, v_post_3863_, v_expr_3971_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; size_t v___x_3974_; size_t v___x_3975_; uint8_t v___x_3976_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref(v___x_3972_);
v___x_3974_ = lean_ptr_addr(v_expr_3971_);
v___x_3975_ = lean_ptr_addr(v_a_3973_);
v___x_3976_ = lean_usize_dec_eq(v___x_3974_, v___x_3975_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
lean_inc(v_data_3970_);
lean_dec_ref(v___y_3918_);
v___x_3977_ = l_Lean_Expr_mdata___override(v_data_3970_, v_a_3973_);
v___x_3978_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v___x_3977_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3978_;
}
else
{
lean_object* v___x_3979_; 
lean_dec(v_a_3973_);
v___x_3979_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v___y_3918_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3979_;
}
}
else
{
lean_dec_ref(v___y_3918_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3972_;
}
}
case 11:
{
lean_object* v_typeName_3980_; lean_object* v_idx_3981_; lean_object* v_struct_3982_; lean_object* v___x_3983_; 
v_typeName_3980_ = lean_ctor_get(v___y_3918_, 0);
v_idx_3981_ = lean_ctor_get(v___y_3918_, 1);
v_struct_3982_ = lean_ctor_get(v___y_3918_, 2);
lean_inc_ref(v_struct_3982_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3861_);
v___x_3983_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_3861_, v_post_3863_, v_struct_3982_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; size_t v___x_3985_; size_t v___x_3986_; uint8_t v___x_3987_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_a_3984_);
lean_dec_ref(v___x_3983_);
v___x_3985_ = lean_ptr_addr(v_struct_3982_);
v___x_3986_ = lean_ptr_addr(v_a_3984_);
v___x_3987_ = lean_usize_dec_eq(v___x_3985_, v___x_3986_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
lean_inc(v_idx_3981_);
lean_inc(v_typeName_3980_);
lean_dec_ref(v___y_3918_);
v___x_3988_ = l_Lean_Expr_proj___override(v_typeName_3980_, v_idx_3981_, v_a_3984_);
v___x_3989_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v___x_3988_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3989_;
}
else
{
lean_object* v___x_3990_; 
lean_dec(v_a_3984_);
v___x_3990_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v___y_3918_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3990_;
}
}
else
{
lean_dec_ref(v___y_3918_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3861_);
return v___x_3983_;
}
}
default: 
{
lean_object* v___x_3991_; 
v___x_3991_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v___y_3918_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3991_;
}
}
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_e_3862_);
lean_dec_ref(v_pre_3861_);
v_a_4003_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3912_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3912_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_e_3862_);
lean_dec_ref(v_pre_3861_);
v_a_4011_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_3911_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_3911_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
v___jp_3868_:
{
if (v___y_3876_ == 0)
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
lean_dec_ref(v___y_3875_);
lean_dec_ref(v___y_3869_);
v___x_3877_ = l_Lean_Expr_letE___override(v___y_3871_, v___y_3870_, v___y_3872_, v___y_3874_, v___y_3873_);
v___x_3878_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v___x_3877_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3878_;
}
else
{
size_t v___x_3879_; size_t v___x_3880_; uint8_t v___x_3881_; 
v___x_3879_ = lean_ptr_addr(v___y_3869_);
lean_dec_ref(v___y_3869_);
v___x_3880_ = lean_ptr_addr(v___y_3874_);
v___x_3881_ = lean_usize_dec_eq(v___x_3879_, v___x_3880_);
if (v___x_3881_ == 0)
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
lean_dec_ref(v___y_3875_);
v___x_3882_ = l_Lean_Expr_letE___override(v___y_3871_, v___y_3870_, v___y_3872_, v___y_3874_, v___y_3873_);
v___x_3883_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v___x_3882_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3883_;
}
else
{
lean_object* v___x_3884_; 
lean_dec_ref(v___y_3874_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
v___x_3884_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v___y_3875_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3884_;
}
}
}
v___jp_3885_:
{
if (v___y_3891_ == 0)
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
lean_dec_ref(v___y_3890_);
v___x_3892_ = l_Lean_Expr_lam___override(v___y_3887_, v___y_3886_, v___y_3889_, v___y_3888_);
v___x_3893_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v___x_3892_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3893_;
}
else
{
uint8_t v___x_3894_; 
v___x_3894_ = l_Lean_instBEqBinderInfo_beq(v___y_3888_, v___y_3888_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
lean_dec_ref(v___y_3890_);
v___x_3895_ = l_Lean_Expr_lam___override(v___y_3887_, v___y_3886_, v___y_3889_, v___y_3888_);
v___x_3896_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v___x_3895_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3896_;
}
else
{
lean_object* v___x_3897_; 
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
v___x_3897_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v___y_3890_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3897_;
}
}
}
v___jp_3898_:
{
if (v___y_3904_ == 0)
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
lean_dec_ref(v___y_3903_);
v___x_3905_ = l_Lean_Expr_forallE___override(v___y_3899_, v___y_3902_, v___y_3901_, v___y_3900_);
v___x_3906_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v___x_3905_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3906_;
}
else
{
uint8_t v___x_3907_; 
v___x_3907_ = l_Lean_instBEqBinderInfo_beq(v___y_3900_, v___y_3900_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
lean_dec_ref(v___y_3903_);
v___x_3908_ = l_Lean_Expr_forallE___override(v___y_3899_, v___y_3902_, v___y_3901_, v___y_3900_);
v___x_3909_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v___x_3908_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3909_;
}
else
{
lean_object* v___x_3910_; 
lean_dec_ref(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3899_);
v___x_3910_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3863_, v___y_3903_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4019_, lean_object* v_pre_4020_, lean_object* v_e_4021_, lean_object* v_post_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(v___x_4019_, v_pre_4020_, v_e_4021_, v_post_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(lean_object* v_pre_4028_, lean_object* v_post_4029_, lean_object* v_e_4030_, lean_object* v_a_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
lean_inc(v_a_4031_);
v___x_4035_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4035_, 0, lean_box(0));
lean_closure_set(v___x_4035_, 1, lean_box(0));
lean_closure_set(v___x_4035_, 2, v_a_4031_);
v___x_4036_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___x_4035_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4068_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4039_ = v___x_4036_;
v_isShared_4040_ = v_isSharedCheck_4068_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4036_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4068_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_4037_, v_e_4030_);
lean_dec(v_a_4037_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v___x_4042_; lean_object* v___f_4043_; lean_object* v___x_4044_; 
lean_del_object(v___x_4039_);
v___x_4042_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_4030_);
v___f_4043_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed), 8, 4);
lean_closure_set(v___f_4043_, 0, v___x_4042_);
lean_closure_set(v___f_4043_, 1, v_pre_4028_);
lean_closure_set(v___f_4043_, 2, v_e_4030_);
lean_closure_set(v___f_4043_, 3, v_post_4029_);
v___x_4044_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v___f_4043_, v_a_4031_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4044_) == 0)
{
lean_object* v_a_4045_; lean_object* v___f_4046_; lean_object* v___x_4047_; 
v_a_4045_ = lean_ctor_get(v___x_4044_, 0);
lean_inc_n(v_a_4045_, 2);
lean_dec_ref(v___x_4044_);
lean_inc(v_a_4031_);
v___f_4046_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4046_, 0, v_a_4031_);
lean_closure_set(v___f_4046_, 1, v_e_4030_);
lean_closure_set(v___f_4046_, 2, v_a_4045_);
v___x_4047_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___f_4046_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4054_ == 0)
{
lean_object* v_unused_4055_; 
v_unused_4055_ = lean_ctor_get(v___x_4047_, 0);
lean_dec(v_unused_4055_);
v___x_4049_ = v___x_4047_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_dec(v___x_4047_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v_a_4045_);
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4045_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
lean_dec(v_a_4045_);
v_a_4056_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4047_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4047_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
else
{
lean_dec_ref(v_e_4030_);
return v___x_4044_;
}
}
else
{
lean_object* v_val_4064_; lean_object* v___x_4066_; 
lean_dec_ref(v_e_4030_);
lean_dec_ref(v_post_4029_);
lean_dec_ref(v_pre_4028_);
v_val_4064_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_val_4064_);
lean_dec_ref(v___x_4041_);
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v_val_4064_);
v___x_4066_ = v___x_4039_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_val_4064_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
else
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4076_; 
lean_dec_ref(v_e_4030_);
lean_dec_ref(v_post_4029_);
lean_dec_ref(v_pre_4028_);
v_a_4069_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4071_ = v___x_4036_;
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4036_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(lean_object* v_pre_4077_, lean_object* v_post_4078_, lean_object* v_e_4079_, lean_object* v_a_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v___x_4084_; 
lean_inc_ref(v_post_4078_);
lean_inc(v___y_4082_);
lean_inc_ref(v___y_4081_);
lean_inc_ref(v_e_4079_);
v___x_4084_ = lean_apply_4(v_post_4078_, v_e_4079_, v___y_4081_, v___y_4082_, lean_box(0));
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4103_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4087_ = v___x_4084_;
v_isShared_4088_ = v_isSharedCheck_4103_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4084_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4103_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
switch(lean_obj_tag(v_a_4085_))
{
case 0:
{
lean_object* v_e_4089_; lean_object* v___x_4091_; 
lean_dec_ref(v_e_4079_);
lean_dec_ref(v_post_4078_);
lean_dec_ref(v_pre_4077_);
v_e_4089_ = lean_ctor_get(v_a_4085_, 0);
lean_inc_ref(v_e_4089_);
lean_dec_ref(v_a_4085_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v_e_4089_);
v___x_4091_ = v___x_4087_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_e_4089_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
case 1:
{
lean_object* v_e_4093_; lean_object* v___x_4094_; 
lean_del_object(v___x_4087_);
lean_dec_ref(v_e_4079_);
v_e_4093_ = lean_ctor_get(v_a_4085_, 0);
lean_inc_ref(v_e_4093_);
lean_dec_ref(v_a_4085_);
v___x_4094_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4077_, v_post_4078_, v_e_4093_, v_a_4080_, v___y_4081_, v___y_4082_);
return v___x_4094_;
}
default: 
{
lean_object* v_e_x3f_4095_; 
lean_dec_ref(v_post_4078_);
lean_dec_ref(v_pre_4077_);
v_e_x3f_4095_ = lean_ctor_get(v_a_4085_, 0);
lean_inc(v_e_x3f_4095_);
lean_dec_ref(v_a_4085_);
if (lean_obj_tag(v_e_x3f_4095_) == 0)
{
lean_object* v___x_4097_; 
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v_e_4079_);
v___x_4097_ = v___x_4087_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_e_4079_);
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
lean_object* v_val_4099_; lean_object* v___x_4101_; 
lean_dec_ref(v_e_4079_);
v_val_4099_ = lean_ctor_get(v_e_x3f_4095_, 0);
lean_inc(v_val_4099_);
lean_dec_ref(v_e_x3f_4095_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v_val_4099_);
v___x_4101_ = v___x_4087_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_val_4099_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
}
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_dec_ref(v_e_4079_);
lean_dec_ref(v_post_4078_);
lean_dec_ref(v_pre_4077_);
v_a_4104_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4084_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4084_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4112_, lean_object* v_post_4113_, lean_object* v_e_4114_, lean_object* v_a_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4112_, v_post_4113_, v_e_4114_, v_a_4115_, v___y_4116_, v___y_4117_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v_a_4115_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4120_, lean_object* v_post_4121_, lean_object* v_sz_4122_, lean_object* v_i_4123_, lean_object* v_bs_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
size_t v_sz_boxed_4129_; size_t v_i_boxed_4130_; lean_object* v_res_4131_; 
v_sz_boxed_4129_ = lean_unbox_usize(v_sz_4122_);
lean_dec(v_sz_4122_);
v_i_boxed_4130_ = lean_unbox_usize(v_i_4123_);
lean_dec(v_i_4123_);
v_res_4131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_4120_, v_post_4121_, v_sz_boxed_4129_, v_i_boxed_4130_, v_bs_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___boxed(lean_object* v_pre_4132_, lean_object* v_post_4133_, lean_object* v_x_4134_, lean_object* v_x_4135_, lean_object* v_x_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_4132_, v_post_4133_, v_x_4134_, v_x_4135_, v_x_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
lean_dec(v___y_4137_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___boxed(lean_object* v_pre_4142_, lean_object* v_post_4143_, lean_object* v_e_4144_, lean_object* v_a_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4142_, v_post_4143_, v_e_4144_, v_a_4145_, v___y_4146_, v___y_4147_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v_a_4145_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_object* v_00_u03b1_4150_, lean_object* v_x_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4155_ = lean_apply_1(v_x_4151_, lean_box(0));
v___x_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0___boxed(lean_object* v_00_u03b1_4157_, lean_object* v_x_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(v_00_u03b1_4157_, v_x_4158_, v___y_4159_, v___y_4160_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(lean_object* v_input_4163_, lean_object* v_pre_4164_, lean_object* v_post_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v_a_4171_; lean_object* v___x_4172_; 
v___x_4169_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_4170_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_4169_, v___y_4166_, v___y_4167_);
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4171_);
lean_dec_ref(v___x_4170_);
v___x_4172_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4164_, v_post_4165_, v_input_4163_, v_a_4171_, v___y_4166_, v___y_4167_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
lean_dec_ref(v___x_4172_);
v___x_4174_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4174_, 0, lean_box(0));
lean_closure_set(v___x_4174_, 1, lean_box(0));
lean_closure_set(v___x_4174_, 2, v_a_4171_);
v___x_4175_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_4174_, v___y_4166_, v___y_4167_);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4182_ == 0)
{
lean_object* v_unused_4183_; 
v_unused_4183_ = lean_ctor_get(v___x_4175_, 0);
lean_dec(v_unused_4183_);
v___x_4177_ = v___x_4175_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_dec(v___x_4175_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 0, v_a_4173_);
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4173_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
else
{
lean_dec(v_a_4171_);
return v___x_4172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___boxed(lean_object* v_input_4184_, lean_object* v_pre_4185_, lean_object* v_post_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_input_4184_, v_pre_4185_, v_post_4186_, v___y_4187_, v___y_4188_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object* v_e_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
uint8_t v___x_4197_; 
v___x_4197_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_4193_);
if (v___x_4197_ == 0)
{
lean_object* v_pre_4198_; lean_object* v___f_4199_; lean_object* v___x_4200_; 
v_pre_4198_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__0));
v___f_4199_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__1));
v___x_4200_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_e_4193_, v_pre_4198_, v___f_4199_, v_a_4194_, v_a_4195_);
return v___x_4200_;
}
else
{
lean_object* v___x_4201_; 
v___x_4201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4201_, 0, v_e_4193_);
return v___x_4201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___boxed(lean_object* v_e_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l_Lean_Meta_Sym_normalizeLevels(v_e_4202_, v_a_4203_, v_a_4204_);
lean_dec(v_a_4204_);
lean_dec_ref(v_a_4203_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4207_, lean_object* v_ref_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_4208_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4213_, lean_object* v_ref_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4213_, v_ref_4214_, v___y_4215_, v___y_4216_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7(v_00_u03b1_4224_, v___y_4225_, v___y_4226_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(lean_object* v_00_u03b1_4229_, lean_object* v_x_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v_x_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b1_4236_, lean_object* v_x_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_00_u03b1_4236_, v_x_4237_, v___y_4238_, v___y_4239_, v___y_4240_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
lean_dec(v___y_4238_);
return v_res_4242_;
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
