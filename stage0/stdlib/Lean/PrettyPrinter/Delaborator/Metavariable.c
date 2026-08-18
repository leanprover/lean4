// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.Metavariable
// Imports: public import Lean.PrettyPrinter.Delaborator.Basic import all Lean.Elab.ErrorUtils
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
lean_object* lean_string_append(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t l_Lean_getPPMVars(lean_object*);
uint8_t l_Lean_getPPMVarsAnonymous(lean_object*);
lean_object* l_Lean_MVarId_findDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MetavarContext_findUserName_x3f(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_hasValue(lean_object*, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_PPContext_runMetaM___redArg(lean_object*, lean_object*);
lean_object* l_Lean_getPPMVarsAnonymous___boxed(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_getPPMVars___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
extern lean_object* l_Lean_reservedMacroScope;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 239, 73, 172, 230, 126, 139, 134)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__1_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__3_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_mvar"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__4 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(160, 189, 119, 183, 234, 3, 131, 163)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__5 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__0_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__1_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__2_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__6 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_delabMVar"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 43, 235, 14, 84, 75, 70, 222)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPMVars___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPMVarsAnonymous___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__2___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2_value)} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " (unreachable)"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__0_value;
static const lean_closure_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__1_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\?_"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__2_value;
static const lean_closure_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__2___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__2_value)} };
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "\n\nAdditional "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__0_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "variable"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__1_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "variables"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__2_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = " in this metavariable's local context: "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__3_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__0_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Variable"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__1_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Variables"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__2_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = " absent from this metavariable's local context: "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = " Substitution is awaiting assignment of the following "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__0_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "metavariable"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__1_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "metavariables"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__2_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__3_value;
static const lean_array_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__4 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 225, .m_capacity = 225, .m_length = 224, .m_data = "Substitution is delayed until the metavariable's value contains no metavariables, since all occurrences of the variables from its local context will need to be replaced with expressions that are valid in the current context."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__0_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "Part of the encoding of the *delayed assignment* mechanism. Represents the metavariable "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = ", which has additional local context variables. "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 125, .m_capacity = 125, .m_length = 124, .m_data = "[Error: This delayed assignment refers to a metavariable not present in the metavariable context. Please report this issue.]"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "\n\nThis metavariable has been assigned."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "\n\nThis metavariable has been assigned, but it appears here via a *delayed assignment*. "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "\n\nThis metavariable cannot be assigned due to the current metavariable context depth."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "\n\nThis metavariable appears here via a *delayed assignment*. "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "\n\nThis metavariable has a name but it is unreachable."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__8 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__8_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 221, .m_capacity = 221, .m_length = 220, .m_data = "A metavariable representing an expression that should be solved for by unification during the elaboration process. They are created during elaboration as placeholders for implicit arguments and by `_` placeholder syntax."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__9 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__9_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 240, .m_capacity = 240, .m_length = 239, .m_data = "A metavariable representing a typeclass instance whose synthesis is still pending. They can be solved for by unification during the elaboration process, but the inferred expression and the synthesized instance must be definitionally equal."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__10 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__10_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 235, .m_capacity = 235, .m_length = 234, .m_data = "A metavariable representing a tactic goal or an expression whose elaboration is still pending. They usually act like constants until they are completely solved for. They can be created using `\?_` and `\?n` synthetic placeholder syntax."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__11 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__11_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "[Error: This metavariable is not present in the metavariable context. Please report this issue.]"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__12 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
else
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
}
else
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 0;
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v_val_7_; uint8_t v___x_8_; 
v_val_6_ = lean_ctor_get(v_x_1_, 0);
v_val_7_ = lean_ctor_get(v_x_2_, 0);
v___x_8_ = l_Lean_instBEqMVarId_beq(v_val_6_, v_val_7_);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(v_x_9_, v_x_10_);
lean_dec(v_x_10_);
lean_dec(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(lean_object* v_m_22_, lean_object* v_mkMVarPlaceholder_23_, lean_object* v_mkMVar_24_, lean_object* v_mkMVarDead_25_, uint8_t v_ppMVars_26_, uint8_t v_ppMVarsAnonymous_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
if (v_ppMVars_26_ == 0)
{
lean_object* v___x_33_; 
lean_dec_ref(v_mkMVarDead_25_);
lean_dec_ref(v_mkMVar_24_);
lean_dec(v_m_22_);
lean_inc(v_a_31_);
lean_inc_ref(v_a_30_);
lean_inc(v_a_29_);
lean_inc_ref(v_a_28_);
v___x_33_ = lean_apply_5(v_mkMVarPlaceholder_23_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, lean_box(0));
return v___x_33_;
}
else
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_MVarId_findDecl_x3f___redArg(v_m_22_, v_a_29_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v_a_35_; 
v_a_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_a_35_);
lean_dec_ref_known(v___x_34_, 1);
if (lean_obj_tag(v_a_35_) == 1)
{
lean_object* v_val_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_57_; 
v_val_36_ = lean_ctor_get(v_a_35_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v_a_35_);
if (v_isSharedCheck_57_ == 0)
{
v___x_38_ = v_a_35_;
v_isShared_39_ = v_isSharedCheck_57_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_val_36_);
lean_dec(v_a_35_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_57_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v_userName_40_; 
v_userName_40_ = lean_ctor_get(v_val_36_, 0);
if (lean_obj_tag(v_userName_40_) == 0)
{
lean_del_object(v___x_38_);
lean_dec_ref(v_mkMVarDead_25_);
lean_dec(v_m_22_);
if (v_ppMVarsAnonymous_27_ == 0)
{
lean_object* v___x_41_; 
lean_dec(v_val_36_);
lean_dec_ref(v_mkMVar_24_);
lean_inc(v_a_31_);
lean_inc_ref(v_a_30_);
lean_inc(v_a_29_);
lean_inc_ref(v_a_28_);
v___x_41_ = lean_apply_5(v_mkMVarPlaceholder_23_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, lean_box(0));
return v___x_41_;
}
else
{
lean_object* v_index_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec_ref(v_mkMVarPlaceholder_23_);
v_index_42_ = lean_ctor_get(v_val_36_, 6);
lean_inc(v_index_42_);
lean_dec(v_val_36_);
v___x_43_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__1));
v___x_44_ = lean_unsigned_to_nat(1u);
v___x_45_ = lean_nat_add(v_index_42_, v___x_44_);
lean_dec(v_index_42_);
v___x_46_ = l_Lean_Name_num___override(v___x_43_, v___x_45_);
lean_inc(v_a_31_);
lean_inc_ref(v_a_30_);
lean_inc(v_a_29_);
lean_inc_ref(v_a_28_);
v___x_47_ = lean_apply_6(v_mkMVar_24_, v___x_46_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, lean_box(0));
return v___x_47_;
}
}
else
{
lean_object* v___x_48_; lean_object* v_mctx_49_; lean_object* v___x_51_; 
lean_inc(v_userName_40_);
lean_dec(v_val_36_);
lean_dec_ref(v_mkMVarPlaceholder_23_);
v___x_48_ = lean_st_ref_get(v_a_29_);
v_mctx_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc_ref(v_mctx_49_);
lean_dec(v___x_48_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 0, v_m_22_);
v___x_51_ = v___x_38_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_m_22_);
v___x_51_ = v_reuseFailAlloc_56_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = l_Lean_MetavarContext_findUserName_x3f(v_mctx_49_, v_userName_40_);
lean_dec_ref(v_mctx_49_);
v___x_53_ = l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(v___x_51_, v___x_52_);
lean_dec(v___x_52_);
lean_dec_ref(v___x_51_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
lean_dec_ref(v_mkMVar_24_);
lean_inc(v_a_31_);
lean_inc_ref(v_a_30_);
lean_inc(v_a_29_);
lean_inc_ref(v_a_28_);
v___x_54_ = lean_apply_6(v_mkMVarDead_25_, v_userName_40_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, lean_box(0));
return v___x_54_;
}
else
{
lean_object* v___x_55_; 
lean_dec_ref(v_mkMVarDead_25_);
lean_inc(v_a_31_);
lean_inc_ref(v_a_30_);
lean_inc(v_a_29_);
lean_inc_ref(v_a_28_);
v___x_55_ = lean_apply_6(v_mkMVar_24_, v_userName_40_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, lean_box(0));
return v___x_55_;
}
}
}
}
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
lean_dec(v_a_35_);
lean_dec_ref(v_mkMVarDead_25_);
lean_dec_ref(v_mkMVarPlaceholder_23_);
v___x_58_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__3));
v___x_59_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__5));
v___x_60_ = l_Lean_Name_replacePrefix(v_m_22_, v___x_58_, v___x_59_);
lean_inc(v_a_31_);
lean_inc_ref(v_a_30_);
lean_inc(v_a_29_);
lean_inc_ref(v_a_28_);
v___x_61_ = lean_apply_6(v_mkMVar_24_, v___x_60_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, lean_box(0));
return v___x_61_;
}
}
else
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
lean_dec_ref(v_mkMVarDead_25_);
lean_dec_ref(v_mkMVar_24_);
lean_dec_ref(v_mkMVarPlaceholder_23_);
lean_dec(v_m_22_);
v_a_62_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v___x_34_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_34_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___boxed(lean_object* v_m_70_, lean_object* v_mkMVarPlaceholder_71_, lean_object* v_mkMVar_72_, lean_object* v_mkMVarDead_73_, lean_object* v_ppMVars_74_, lean_object* v_ppMVarsAnonymous_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
uint8_t v_ppMVars_boxed_81_; uint8_t v_ppMVarsAnonymous_boxed_82_; lean_object* v_res_83_; 
v_ppMVars_boxed_81_ = lean_unbox(v_ppMVars_74_);
v_ppMVarsAnonymous_boxed_82_ = lean_unbox(v_ppMVarsAnonymous_75_);
v_res_83_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(v_m_70_, v_mkMVarPlaceholder_71_, v_mkMVar_72_, v_mkMVarDead_73_, v_ppMVars_boxed_81_, v_ppMVarsAnonymous_boxed_82_, v_a_76_, v_a_77_, v_a_78_, v_a_79_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux(lean_object* v_00_u03b1_84_, lean_object* v_m_85_, lean_object* v_mkMVarPlaceholder_86_, lean_object* v_mkMVar_87_, lean_object* v_mkMVarDead_88_, uint8_t v_ppMVars_89_, uint8_t v_ppMVarsAnonymous_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(v_m_85_, v_mkMVarPlaceholder_86_, v_mkMVar_87_, v_mkMVarDead_88_, v_ppMVars_89_, v_ppMVarsAnonymous_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___boxed(lean_object* v_00_u03b1_97_, lean_object* v_m_98_, lean_object* v_mkMVarPlaceholder_99_, lean_object* v_mkMVar_100_, lean_object* v_mkMVarDead_101_, lean_object* v_ppMVars_102_, lean_object* v_ppMVarsAnonymous_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
uint8_t v_ppMVars_boxed_109_; uint8_t v_ppMVarsAnonymous_boxed_110_; lean_object* v_res_111_; 
v_ppMVars_boxed_109_ = lean_unbox(v_ppMVars_102_);
v_ppMVarsAnonymous_boxed_110_ = lean_unbox(v_ppMVarsAnonymous_103_);
v_res_111_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux(v_00_u03b1_97_, v_m_98_, v_mkMVarPlaceholder_99_, v_mkMVar_100_, v_mkMVarDead_101_, v_ppMVars_boxed_109_, v_ppMVarsAnonymous_boxed_110_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0(lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_ref_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_ref_117_ = lean_ctor_get(v___y_114_, 5);
v___x_118_ = 0;
v___x_119_ = l_Lean_SourceInfo_fromRef(v_ref_117_, v___x_118_);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0___boxed(lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0(v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1(lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_ref_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_ref_143_ = lean_ctor_get(v___y_140_, 5);
v___x_144_ = 0;
v___x_145_ = l_Lean_SourceInfo_fromRef(v_ref_143_, v___x_144_);
v___x_146_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4));
v___x_147_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5));
lean_inc_n(v___x_145_, 2);
v___x_148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_145_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__6));
v___x_150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_145_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = l_Lean_Syntax_node2(v___x_145_, v___x_146_, v___x_148_, v___x_150_);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___boxed(lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1(v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__2(lean_object* v___f_159_, lean_object* v_n_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; 
lean_inc(v___y_164_);
lean_inc_ref(v___y_163_);
lean_inc(v___y_162_);
lean_inc_ref(v___y_161_);
v___x_166_ = lean_apply_5(v___f_159_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, lean_box(0));
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_179_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_179_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_179_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_179_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_171_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4));
v___x_172_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5));
lean_inc(v_a_167_);
v___x_173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_173_, 0, v_a_167_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = l_Lean_mkIdent(v_n_160_);
v___x_175_ = l_Lean_Syntax_node2(v_a_167_, v___x_171_, v___x_173_, v___x_174_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_175_);
v___x_177_ = v___x_169_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_dec(v_n_160_);
v_a_180_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_166_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_166_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__2___boxed(lean_object* v___f_188_, lean_object* v_n_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__2(v___f_188_, v_n_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3(lean_object* v___f_199_, lean_object* v_m_200_, lean_object* v_n_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; 
lean_inc(v___y_205_);
lean_inc_ref(v___y_204_);
lean_inc(v___y_203_);
lean_inc_ref(v___y_202_);
v___x_207_ = lean_apply_5(v___f_199_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, lean_box(0));
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_224_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_224_ == 0)
{
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_224_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_224_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_212_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__1));
v___x_213_ = l_Lean_Name_append(v___x_212_, v_m_200_);
v___x_214_ = l_Lean_reservedMacroScope;
v___x_215_ = l_Lean_addMacroScope(v___x_213_, v_n_201_, v___x_214_);
v___x_216_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4));
v___x_217_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5));
lean_inc(v_a_208_);
v___x_218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_218_, 0, v_a_208_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = l_Lean_mkIdent(v___x_215_);
v___x_220_ = l_Lean_Syntax_node2(v_a_208_, v___x_216_, v___x_218_, v___x_219_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_220_);
v___x_222_ = v___x_210_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec(v_n_201_);
lean_dec(v_m_200_);
v_a_225_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_207_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_207_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___boxed(lean_object* v___f_233_, lean_object* v_m_234_, lean_object* v_n_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3(v___f_233_, v_m_234_, v_n_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux(lean_object* v_m_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0));
v___x_257_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_256_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref_known(v___x_257_, 1);
v___x_259_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1));
v___x_260_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_259_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___f_262_; lean_object* v___f_263_; lean_object* v___f_264_; lean_object* v___f_265_; uint8_t v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_260_, 1);
v___f_262_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2));
v___f_263_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3));
v___f_264_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__4));
lean_inc(v_m_248_);
v___f_265_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___boxed), 8, 2);
lean_closure_set(v___f_265_, 0, v___f_262_);
lean_closure_set(v___f_265_, 1, v_m_248_);
v___x_266_ = lean_unbox(v_a_258_);
lean_dec(v_a_258_);
v___x_267_ = lean_unbox(v_a_261_);
lean_dec(v_a_261_);
v___x_268_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(v_m_248_, v___f_263_, v___f_264_, v___f_265_, v___x_266_, v___x_267_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
return v___x_268_;
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_a_258_);
lean_dec(v_m_248_);
v_a_269_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_260_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_260_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec(v_m_248_);
v_a_277_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_257_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_257_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___boxed(lean_object* v_m_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux(v_m_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0(lean_object* v_n_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_301_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5));
v___x_302_ = 1;
v___x_303_ = l_Lean_Name_toString(v_n_295_, v___x_302_);
v___x_304_ = lean_string_append(v___x_301_, v___x_303_);
lean_dec_ref(v___x_303_);
v___x_305_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0));
v___x_306_ = lean_string_append(v___x_304_, v___x_305_);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___boxed(lean_object* v_n_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0(v_n_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__1(lean_object* v_n_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_321_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5));
v___x_322_ = 1;
v___x_323_ = l_Lean_Name_toString(v_n_315_, v___x_322_);
v___x_324_ = lean_string_append(v___x_321_, v___x_323_);
lean_dec_ref(v___x_323_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__1___boxed(lean_object* v_n_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__1(v_n_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__2(lean_object* v___x_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_333_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__2___boxed(lean_object* v___x_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__2(v___x_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(lean_object* v_m_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_options_358_; lean_object* v___f_359_; lean_object* v___f_360_; lean_object* v___f_361_; uint8_t v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; 
v_options_358_ = lean_ctor_get(v_a_355_, 2);
v___f_359_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__0));
v___f_360_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__1));
v___f_361_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__3));
v___x_362_ = l_Lean_getPPMVars(v_options_358_);
v___x_363_ = l_Lean_getPPMVarsAnonymous(v_options_358_);
v___x_364_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(v_m_352_, v___f_361_, v___f_360_, v___f_359_, v___x_362_, v___x_363_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___boxed(lean_object* v_m_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(v_m_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(lean_object* v_m_372_, lean_object* v_query_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
lean_object* v_zero_377_; uint8_t v_isZero_378_; 
v_zero_377_ = lean_unsigned_to_nat(0u);
v_isZero_378_ = lean_nat_dec_eq(v_x_375_, v_zero_377_);
if (v_isZero_378_ == 1)
{
lean_dec(v_x_376_);
lean_dec(v_x_375_);
if (lean_obj_tag(v_x_374_) == 0)
{
lean_object* v___x_379_; 
v___x_379_ = lean_box(2);
return v___x_379_;
}
else
{
lean_object* v_val_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
v_val_380_ = lean_ctor_get(v_x_374_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v_x_374_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v_x_374_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_val_380_);
lean_dec(v_x_374_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_val_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
else
{
lean_object* v_keyArray_388_; lean_object* v_valueArray_389_; lean_object* v___x_390_; uint8_t v_isSome_391_; 
v_keyArray_388_ = lean_ctor_get(v_m_372_, 1);
v_valueArray_389_ = lean_ctor_get(v_m_372_, 2);
v___x_390_ = lean_array_fget_borrowed(v_keyArray_388_, v_x_376_);
v_isSome_391_ = lean_noption_is_some(v___x_390_);
if (v_isSome_391_ == 0)
{
lean_dec(v_x_375_);
if (lean_obj_tag(v_x_374_) == 0)
{
lean_object* v___x_392_; 
v___x_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_392_, 0, v_x_376_);
return v___x_392_;
}
else
{
lean_object* v_val_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v_x_376_);
v_val_393_ = lean_ctor_get(v_x_374_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v_x_374_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v_x_374_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_val_393_);
lean_dec(v_x_374_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_val_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_object* v_one_401_; lean_object* v_n_402_; lean_object* v___y_404_; 
v_one_401_ = lean_unsigned_to_nat(1u);
v_n_402_ = lean_nat_sub(v_x_375_, v_one_401_);
lean_dec(v_x_375_);
if (v_isSome_391_ == 0)
{
goto v___jp_410_;
}
else
{
lean_object* v___x_412_; uint8_t v_isSome_413_; 
v___x_412_ = lean_array_fget_borrowed(v_valueArray_389_, v_x_376_);
v_isSome_413_ = lean_noption_is_some(v___x_412_);
if (v_isSome_413_ == 0)
{
goto v___jp_410_;
}
else
{
lean_object* v_val_414_; uint8_t v___x_415_; 
lean_inc(v___x_390_);
v_val_414_ = lean_noption_get(v___x_390_);
v___x_415_ = l_Lean_instBEqFVarId_beq(v_val_414_, v_query_373_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
lean_dec(v_val_414_);
v___x_416_ = lean_array_get_size(v_keyArray_388_);
v___x_417_ = lean_nat_add(v_x_376_, v_one_401_);
lean_dec(v_x_376_);
v___x_418_ = lean_nat_dec_lt(v___x_417_, v___x_416_);
if (v___x_418_ == 0)
{
lean_dec(v___x_417_);
v_x_375_ = v_n_402_;
v_x_376_ = v_zero_377_;
goto _start;
}
else
{
v_x_375_ = v_n_402_;
v_x_376_ = v___x_417_;
goto _start;
}
}
else
{
lean_object* v_val_421_; lean_object* v___x_422_; 
lean_dec(v_n_402_);
lean_dec(v_x_374_);
lean_inc(v___x_412_);
v_val_421_ = lean_noption_get(v___x_412_);
v___x_422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_422_, 0, v_x_376_);
lean_ctor_set(v___x_422_, 1, v_val_414_);
lean_ctor_set(v___x_422_, 2, v_val_421_);
return v___x_422_;
}
}
}
v___jp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_405_ = lean_array_get_size(v_keyArray_388_);
v___x_406_ = lean_nat_add(v_x_376_, v_one_401_);
lean_dec(v_x_376_);
v___x_407_ = lean_nat_dec_lt(v___x_406_, v___x_405_);
if (v___x_407_ == 0)
{
lean_dec(v___x_406_);
v_x_374_ = v___y_404_;
v_x_375_ = v_n_402_;
v_x_376_ = v_zero_377_;
goto _start;
}
else
{
v_x_374_ = v___y_404_;
v_x_375_ = v_n_402_;
v_x_376_ = v___x_406_;
goto _start;
}
}
v___jp_410_:
{
if (lean_obj_tag(v_x_374_) == 0)
{
lean_object* v___x_411_; 
lean_inc(v_x_376_);
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v_x_376_);
v___y_404_ = v___x_411_;
goto v___jp_403_;
}
else
{
v___y_404_ = v_x_374_;
goto v___jp_403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg___boxed(lean_object* v_m_423_, lean_object* v_query_424_, lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(v_m_423_, v_query_424_, v_x_425_, v_x_426_, v_x_427_);
lean_dec(v_query_424_);
lean_dec_ref(v_m_423_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(lean_object* v_m_429_, lean_object* v_query_430_){
_start:
{
lean_object* v_keyArray_431_; lean_object* v___x_432_; uint64_t v___x_433_; uint64_t v___x_434_; uint64_t v___x_435_; uint64_t v_fold_436_; uint64_t v___x_437_; uint64_t v___x_438_; uint64_t v___x_439_; size_t v___x_440_; size_t v___x_441_; size_t v___x_442_; size_t v___x_443_; size_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_keyArray_431_ = lean_ctor_get(v_m_429_, 1);
v___x_432_ = lean_array_get_size(v_keyArray_431_);
v___x_433_ = l_Lean_instHashableFVarId_hash(v_query_430_);
v___x_434_ = 32ULL;
v___x_435_ = lean_uint64_shift_right(v___x_433_, v___x_434_);
v_fold_436_ = lean_uint64_xor(v___x_433_, v___x_435_);
v___x_437_ = 16ULL;
v___x_438_ = lean_uint64_shift_right(v_fold_436_, v___x_437_);
v___x_439_ = lean_uint64_xor(v_fold_436_, v___x_438_);
v___x_440_ = lean_uint64_to_usize(v___x_439_);
v___x_441_ = lean_usize_of_nat(v___x_432_);
v___x_442_ = ((size_t)1ULL);
v___x_443_ = lean_usize_sub(v___x_441_, v___x_442_);
v___x_444_ = lean_usize_land(v___x_440_, v___x_443_);
v___x_445_ = lean_usize_to_nat(v___x_444_);
v___x_446_ = lean_box(0);
v___x_447_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(v_m_429_, v_query_430_, v___x_446_, v___x_432_, v___x_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg___boxed(lean_object* v_m_448_, lean_object* v_query_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v_m_448_, v_query_449_);
lean_dec(v_query_449_);
lean_dec_ref(v_m_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4_spec__5___redArg(lean_object* v_b_451_, lean_object* v_acc_452_, lean_object* v_i_453_){
_start:
{
lean_object* v___y_455_; lean_object* v_keyArray_463_; lean_object* v_valueArray_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_keyArray_463_ = lean_ctor_get(v_b_451_, 1);
v_valueArray_464_ = lean_ctor_get(v_b_451_, 2);
v___x_465_ = lean_array_get_size(v_keyArray_463_);
v___x_466_ = lean_nat_dec_lt(v_i_453_, v___x_465_);
if (v___x_466_ == 0)
{
lean_dec(v_i_453_);
return v_acc_452_;
}
else
{
lean_object* v___x_467_; uint8_t v_isSome_468_; 
v___x_467_ = lean_array_fget_borrowed(v_keyArray_463_, v_i_453_);
v_isSome_468_ = lean_noption_is_some(v___x_467_);
if (v_isSome_468_ == 0)
{
goto v___jp_459_;
}
else
{
lean_object* v___x_469_; uint8_t v_isSome_470_; 
v___x_469_ = lean_array_fget_borrowed(v_valueArray_464_, v_i_453_);
v_isSome_470_ = lean_noption_is_some(v___x_469_);
if (v_isSome_470_ == 0)
{
goto v___jp_459_;
}
else
{
lean_object* v_val_471_; lean_object* v_val_472_; lean_object* v_i_474_; lean_object* v___x_479_; 
lean_inc(v___x_467_);
v_val_471_ = lean_noption_get(v___x_467_);
lean_inc(v___x_469_);
v_val_472_ = lean_noption_get(v___x_469_);
v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v_acc_452_, v_val_471_);
switch(lean_obj_tag(v___x_479_))
{
case 0:
{
lean_object* v_index_480_; lean_object* v_size_481_; lean_object* v___x_482_; 
v_index_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_index_480_);
lean_dec_ref_known(v___x_479_, 3);
v_size_481_ = lean_ctor_get(v_acc_452_, 0);
lean_inc(v_size_481_);
v___x_482_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_452_, v_size_481_, v_index_480_, v_val_471_, v_val_472_);
lean_dec(v_index_480_);
v___y_455_ = v___x_482_;
goto v___jp_454_;
}
case 1:
{
lean_object* v_index_483_; 
v_index_483_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_index_483_);
lean_dec_ref_known(v___x_479_, 1);
v_i_474_ = v_index_483_;
goto v___jp_473_;
}
default: 
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_452_, v___x_484_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_index_486_; 
v_index_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_index_486_);
lean_dec_ref_known(v___x_485_, 1);
v_i_474_ = v_index_486_;
goto v___jp_473_;
}
else
{
lean_dec(v_val_472_);
lean_dec(v_val_471_);
v___y_455_ = v_acc_452_;
goto v___jp_454_;
}
}
}
v___jp_473_:
{
lean_object* v_size_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_size_475_ = lean_ctor_get(v_acc_452_, 0);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_add(v_size_475_, v___x_476_);
v___x_478_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_452_, v___x_477_, v_i_474_, v_val_471_, v_val_472_);
lean_dec(v_i_474_);
v___y_455_ = v___x_478_;
goto v___jp_454_;
}
}
}
}
v___jp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_nat_add(v_i_453_, v___x_456_);
lean_dec(v_i_453_);
v_acc_452_ = v___y_455_;
v_i_453_ = v___x_457_;
goto _start;
}
v___jp_459_:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_add(v_i_453_, v___x_460_);
lean_dec(v_i_453_);
v_i_453_ = v___x_461_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_487_, lean_object* v_acc_488_, lean_object* v_i_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4_spec__5___redArg(v_b_487_, v_acc_488_, v_i_489_);
lean_dec_ref(v_b_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4___redArg(lean_object* v_init_491_, lean_object* v_b_492_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4_spec__5___redArg(v_b_492_, v_init_491_, v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4___redArg___boxed(lean_object* v_init_495_, lean_object* v_b_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4___redArg(v_init_495_, v_b_496_);
lean_dec_ref(v_b_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(lean_object* v_m_498_){
_start:
{
lean_object* v_keyArray_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v_cellCount_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v_target_506_; lean_object* v___x_507_; 
v_keyArray_499_ = lean_ctor_get(v_m_498_, 1);
v___x_500_ = lean_array_get_size(v_keyArray_499_);
v___x_501_ = lean_unsigned_to_nat(2u);
v_cellCount_502_ = lean_nat_mul(v___x_500_, v___x_501_);
v___x_503_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_502_);
v___x_504_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_502_);
v___x_505_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_502_);
v_target_506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_506_, 0, v___x_503_);
lean_ctor_set(v_target_506_, 1, v___x_504_);
lean_ctor_set(v_target_506_, 2, v___x_505_);
v___x_507_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4___redArg(v_target_506_, v_m_498_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___boxed(lean_object* v_m_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_m_508_);
lean_dec_ref(v_m_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(lean_object* v_m_510_, lean_object* v_query_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v_m_510_, v_query_511_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_index_513_; lean_object* v_key_514_; lean_object* v_value_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
v_index_513_ = lean_ctor_get(v___x_512_, 0);
v_key_514_ = lean_ctor_get(v___x_512_, 1);
v_value_515_ = lean_ctor_get(v___x_512_, 2);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_512_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_value_515_);
lean_inc(v_key_514_);
lean_inc(v_index_513_);
lean_dec(v___x_512_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_index_513_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_key_514_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_value_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
lean_object* v___x_523_; 
lean_dec(v___x_512_);
v___x_523_ = lean_box(1);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_m_524_, lean_object* v_query_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_m_524_, v_query_525_);
lean_dec(v_query_525_);
lean_dec_ref(v_m_524_);
return v_res_526_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(lean_object* v_m_527_, lean_object* v_a_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_m_527_, v_a_528_);
if (lean_obj_tag(v___x_529_) == 0)
{
uint8_t v___x_530_; 
lean_dec_ref_known(v___x_529_, 3);
v___x_530_ = 1;
return v___x_530_;
}
else
{
uint8_t v___x_531_; 
v___x_531_ = 0;
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg___boxed(lean_object* v_m_532_, lean_object* v_a_533_){
_start:
{
uint8_t v_res_534_; lean_object* v_r_535_; 
v_res_534_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_m_532_, v_a_533_);
lean_dec(v_a_533_);
lean_dec_ref(v_m_532_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___redArg(lean_object* v_val_539_, lean_object* v_as_540_, size_t v_sz_541_, size_t v_i_542_, lean_object* v_b_543_){
_start:
{
lean_object* v_a_546_; uint8_t v___x_550_; 
v___x_550_ = lean_usize_dec_lt(v_i_542_, v_sz_541_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_dec_ref(v_val_539_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v_b_543_);
return v___x_551_;
}
else
{
lean_object* v_snd_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_684_; 
v_snd_552_ = lean_ctor_get(v_b_543_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_b_543_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; 
v_unused_685_ = lean_ctor_get(v_b_543_, 0);
lean_dec(v_unused_685_);
v___x_554_ = v_b_543_;
v_isShared_555_ = v_isSharedCheck_684_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_snd_552_);
lean_dec(v_b_543_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_684_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_snd_556_; lean_object* v_fst_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_683_; 
v_snd_556_ = lean_ctor_get(v_snd_552_, 1);
v_fst_557_ = lean_ctor_get(v_snd_552_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v_snd_552_);
if (v_isSharedCheck_683_ == 0)
{
v___x_559_ = v_snd_552_;
v_isShared_560_ = v_isSharedCheck_683_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_snd_556_);
lean_inc(v_fst_557_);
lean_dec(v_snd_552_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_683_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v_array_561_; lean_object* v_start_562_; lean_object* v_stop_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_array_561_ = lean_ctor_get(v_snd_556_, 0);
v_start_562_ = lean_ctor_get(v_snd_556_, 1);
v_stop_563_ = lean_ctor_get(v_snd_556_, 2);
v___x_564_ = lean_box(0);
v___x_565_ = lean_nat_dec_lt(v_start_562_, v_stop_563_);
if (v___x_565_ == 0)
{
lean_object* v___x_567_; 
lean_dec_ref(v_val_539_);
if (v_isShared_560_ == 0)
{
v___x_567_ = v___x_559_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_fst_557_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_snd_556_);
v___x_567_ = v_reuseFailAlloc_572_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_569_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v___x_567_);
lean_ctor_set(v___x_554_, 0, v___x_564_);
v___x_569_ = v___x_554_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_567_);
v___x_569_ = v_reuseFailAlloc_571_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; 
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
}
else
{
lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_679_; 
lean_inc(v_stop_563_);
lean_inc(v_start_562_);
lean_inc_ref(v_array_561_);
v_isSharedCheck_679_ = !lean_is_exclusive(v_snd_556_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; lean_object* v_unused_681_; lean_object* v_unused_682_; 
v_unused_680_ = lean_ctor_get(v_snd_556_, 2);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_snd_556_, 1);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v_snd_556_, 0);
lean_dec(v_unused_682_);
v___x_574_ = v_snd_556_;
v_isShared_575_ = v_isSharedCheck_679_;
goto v_resetjp_573_;
}
else
{
lean_dec(v_snd_556_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_679_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_lctx_576_; lean_object* v___x_577_; lean_object* v_a_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v_lctx_576_ = lean_ctor_get(v_val_539_, 1);
v___x_577_ = lean_array_fget(v_array_561_, v_start_562_);
v_a_578_ = lean_array_uget_borrowed(v_as_540_, v_i_542_);
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_add(v_start_562_, v___x_579_);
lean_dec(v_start_562_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 1, v___x_580_);
v___x_582_ = v___x_574_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_array_561_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_stop_563_);
v___x_582_ = v_reuseFailAlloc_678_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___y_584_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = l_Lean_Expr_fvarId_x21(v_a_578_);
lean_inc_ref(v_lctx_576_);
v___x_592_ = lean_local_ctx_find(v_lctx_576_, v___x_591_);
if (lean_obj_tag(v___x_592_) == 1)
{
lean_object* v_val_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_673_; 
v_val_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_673_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_673_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_val_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_673_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
uint8_t v___x_597_; uint8_t v___x_598_; 
v___x_597_ = 0;
v___x_598_ = l_Lean_LocalDecl_hasValue(v_val_593_, v___x_597_);
lean_dec(v_val_593_);
if (v___x_598_ == 0)
{
if (lean_obj_tag(v___x_577_) == 1)
{
lean_object* v_fvarId_599_; uint8_t v___x_600_; 
v_fvarId_599_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_fvarId_599_);
lean_dec_ref_known(v___x_577_, 1);
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_fst_557_, v_fvarId_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___y_603_; lean_object* v_i_604_; lean_object* v___y_609_; lean_object* v___y_619_; lean_object* v_i_620_; lean_object* v___x_634_; 
lean_del_object(v___x_595_);
v___x_601_ = lean_box(0);
v___x_634_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v_fst_557_, v_fvarId_599_);
switch(lean_obj_tag(v___x_634_))
{
case 0:
{
lean_dec_ref_known(v___x_634_, 3);
lean_dec(v_fvarId_599_);
v___y_584_ = v_fst_557_;
goto v___jp_583_;
}
case 1:
{
lean_object* v_index_635_; lean_object* v_size_636_; lean_object* v_keyArray_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_index_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_index_635_);
lean_dec_ref_known(v___x_634_, 1);
v_size_636_ = lean_ctor_get(v_fst_557_, 0);
v_keyArray_637_ = lean_ctor_get(v_fst_557_, 1);
v___x_638_ = lean_nat_add(v_size_636_, v___x_579_);
v___x_639_ = lean_array_get_size(v_keyArray_637_);
v___x_640_ = lean_nat_dec_lt(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_dec(v___x_638_);
lean_dec(v_index_635_);
goto v___jp_624_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_641_ = lean_unsigned_to_nat(4u);
v___x_642_ = lean_nat_mul(v___x_638_, v___x_641_);
v___x_643_ = lean_unsigned_to_nat(3u);
v___x_644_ = lean_nat_mul(v___x_639_, v___x_643_);
v___x_645_ = lean_nat_dec_le(v___x_642_, v___x_644_);
lean_dec(v___x_644_);
lean_dec(v___x_642_);
if (v___x_645_ == 0)
{
lean_dec(v___x_638_);
lean_dec(v_index_635_);
goto v___jp_624_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_557_, v___x_638_, v_index_635_, v_fvarId_599_, v___x_601_);
lean_dec(v_index_635_);
v___y_584_ = v___x_646_;
goto v___jp_583_;
}
}
}
default: 
{
lean_object* v_size_647_; lean_object* v_keyArray_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_size_647_ = lean_ctor_get(v_fst_557_, 0);
v_keyArray_648_ = lean_ctor_get(v_fst_557_, 1);
v___x_649_ = lean_nat_add(v_size_647_, v___x_579_);
v___x_650_ = lean_array_get_size(v_keyArray_648_);
v___x_651_ = lean_nat_dec_lt(v___x_649_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_dec(v___x_649_);
v___x_652_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_fst_557_);
lean_dec(v_fst_557_);
v___y_609_ = v___x_652_;
goto v___jp_608_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_653_ = lean_unsigned_to_nat(4u);
v___x_654_ = lean_nat_mul(v___x_649_, v___x_653_);
lean_dec(v___x_649_);
v___x_655_ = lean_unsigned_to_nat(3u);
v___x_656_ = lean_nat_mul(v___x_650_, v___x_655_);
v___x_657_ = lean_nat_dec_le(v___x_654_, v___x_656_);
lean_dec(v___x_656_);
lean_dec(v___x_654_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
v___x_658_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_fst_557_);
lean_dec(v_fst_557_);
v___y_609_ = v___x_658_;
goto v___jp_608_;
}
else
{
v___y_609_ = v_fst_557_;
goto v___jp_608_;
}
}
}
}
v___jp_602_:
{
lean_object* v_size_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_size_605_ = lean_ctor_get(v___y_603_, 0);
v___x_606_ = lean_nat_add(v_size_605_, v___x_579_);
v___x_607_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_603_, v___x_606_, v_i_604_, v_fvarId_599_, v___x_601_);
lean_dec(v_i_604_);
v___y_584_ = v___x_607_;
goto v___jp_583_;
}
v___jp_608_:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v___y_609_, v_fvarId_599_);
switch(lean_obj_tag(v___x_610_))
{
case 0:
{
lean_object* v_index_611_; lean_object* v_size_612_; lean_object* v___x_613_; 
v_index_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_index_611_);
lean_dec_ref_known(v___x_610_, 3);
v_size_612_ = lean_ctor_get(v___y_609_, 0);
lean_inc(v_size_612_);
v___x_613_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_609_, v_size_612_, v_index_611_, v_fvarId_599_, v___x_601_);
lean_dec(v_index_611_);
v___y_584_ = v___x_613_;
goto v___jp_583_;
}
case 1:
{
lean_object* v_index_614_; 
v_index_614_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_index_614_);
lean_dec_ref_known(v___x_610_, 1);
v___y_603_ = v___y_609_;
v_i_604_ = v_index_614_;
goto v___jp_602_;
}
default: 
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_609_, v___x_615_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_index_617_; 
v_index_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_index_617_);
lean_dec_ref_known(v___x_616_, 1);
v___y_603_ = v___y_609_;
v_i_604_ = v_index_617_;
goto v___jp_602_;
}
else
{
lean_dec(v_fvarId_599_);
v___y_584_ = v___y_609_;
goto v___jp_583_;
}
}
}
}
v___jp_618_:
{
lean_object* v_size_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_size_621_ = lean_ctor_get(v___y_619_, 0);
v___x_622_ = lean_nat_add(v_size_621_, v___x_579_);
v___x_623_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_619_, v___x_622_, v_i_620_, v_fvarId_599_, v___x_601_);
lean_dec(v_i_620_);
v___y_584_ = v___x_623_;
goto v___jp_583_;
}
v___jp_624_:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_fst_557_);
lean_dec(v_fst_557_);
v___x_626_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v___x_625_, v_fvarId_599_);
switch(lean_obj_tag(v___x_626_))
{
case 0:
{
lean_object* v_index_627_; lean_object* v_size_628_; lean_object* v___x_629_; 
v_index_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_index_627_);
lean_dec_ref_known(v___x_626_, 3);
v_size_628_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_size_628_);
v___x_629_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_625_, v_size_628_, v_index_627_, v_fvarId_599_, v___x_601_);
lean_dec(v_index_627_);
v___y_584_ = v___x_629_;
goto v___jp_583_;
}
case 1:
{
lean_object* v_index_630_; 
v_index_630_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_index_630_);
lean_dec_ref_known(v___x_626_, 1);
v___y_619_ = v___x_625_;
v_i_620_ = v_index_630_;
goto v___jp_618_;
}
default: 
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_625_, v___x_631_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_index_633_; 
v_index_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_index_633_);
lean_dec_ref_known(v___x_632_, 1);
v___y_619_ = v___x_625_;
v_i_620_ = v_index_633_;
goto v___jp_618_;
}
else
{
lean_dec(v_fvarId_599_);
v___y_584_ = v___x_625_;
goto v___jp_583_;
}
}
}
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
lean_dec(v_fvarId_599_);
lean_del_object(v___x_559_);
lean_del_object(v___x_554_);
lean_dec_ref(v_val_539_);
v___x_659_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___redArg___closed__0));
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v_fst_557_);
lean_ctor_set(v___x_660_, 1, v___x_582_);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
if (v_isShared_596_ == 0)
{
lean_ctor_set_tag(v___x_595_, 0);
lean_ctor_set(v___x_595_, 0, v___x_661_);
v___x_663_ = v___x_595_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
lean_dec(v___x_577_);
lean_del_object(v___x_559_);
lean_del_object(v___x_554_);
lean_dec_ref(v_val_539_);
v___x_665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___redArg___closed__0));
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v_fst_557_);
lean_ctor_set(v___x_666_, 1, v___x_582_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
if (v_isShared_596_ == 0)
{
lean_ctor_set_tag(v___x_595_, 0);
lean_ctor_set(v___x_595_, 0, v___x_667_);
v___x_669_ = v___x_595_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; 
lean_del_object(v___x_595_);
lean_dec(v___x_577_);
lean_del_object(v___x_559_);
lean_del_object(v___x_554_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v_fst_557_);
lean_ctor_set(v___x_671_, 1, v___x_582_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_564_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v_a_546_ = v___x_672_;
goto v___jp_545_;
}
}
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v___x_592_);
lean_dec(v___x_577_);
lean_del_object(v___x_559_);
lean_del_object(v___x_554_);
lean_dec_ref(v_val_539_);
v___x_674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___redArg___closed__0));
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_fst_557_);
lean_ctor_set(v___x_675_, 1, v___x_582_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
v___jp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 1, v___x_582_);
lean_ctor_set(v___x_559_, 0, v___y_584_);
v___x_586_ = v___x_559_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___y_584_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___x_582_);
v___x_586_ = v_reuseFailAlloc_590_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_588_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v___x_586_);
lean_ctor_set(v___x_554_, 0, v___x_564_);
v___x_588_ = v___x_554_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
v_a_546_ = v___x_588_;
goto v___jp_545_;
}
}
}
}
}
}
}
}
}
v___jp_545_:
{
size_t v___x_547_; size_t v___x_548_; 
v___x_547_ = ((size_t)1ULL);
v___x_548_ = lean_usize_add(v_i_542_, v___x_547_);
v_i_542_ = v___x_548_;
v_b_543_ = v_a_546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___redArg___boxed(lean_object* v_val_686_, lean_object* v_as_687_, lean_object* v_sz_688_, lean_object* v_i_689_, lean_object* v_b_690_, lean_object* v___y_691_){
_start:
{
size_t v_sz_boxed_692_; size_t v_i_boxed_693_; lean_object* v_res_694_; 
v_sz_boxed_692_ = lean_unbox_usize(v_sz_688_);
lean_dec(v_sz_688_);
v_i_boxed_693_ = lean_unbox_usize(v_i_689_);
lean_dec(v_i_689_);
v_res_694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___redArg(v_val_686_, v_as_687_, v_sz_boxed_692_, v_i_boxed_693_, v_b_690_);
lean_dec_ref(v_as_687_);
return v_res_694_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0(void){
_start:
{
lean_object* v___x_695_; lean_object* v_dummy_696_; 
v___x_695_ = lean_box(0);
v_dummy_696_ = l_Lean_Expr_sort___override(v___x_695_);
return v_dummy_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(lean_object* v_e_697_, lean_object* v_decl_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_fvars_704_; lean_object* v_mvarIdPending_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_773_; 
v_fvars_704_ = lean_ctor_get(v_decl_698_, 0);
v_mvarIdPending_705_ = lean_ctor_get(v_decl_698_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_decl_698_);
if (v_isSharedCheck_773_ == 0)
{
v___x_707_ = v_decl_698_;
v_isShared_708_ = v_isSharedCheck_773_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_mvarIdPending_705_);
lean_inc(v_fvars_704_);
lean_dec(v_decl_698_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_773_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_709_ = l_Lean_Expr_getAppNumArgs(v_e_697_);
v___x_710_ = lean_array_get_size(v_fvars_704_);
v___x_711_ = lean_nat_dec_eq(v___x_709_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec(v___x_709_);
lean_del_object(v___x_707_);
lean_dec(v_mvarIdPending_705_);
lean_dec_ref(v_fvars_704_);
lean_dec_ref(v_e_697_);
v___x_712_ = lean_box(v___x_711_);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
else
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_MVarId_findDecl_x3f___redArg(v_mvarIdPending_705_, v_a_700_);
lean_dec(v_mvarIdPending_705_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_764_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_764_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_764_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_764_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
if (lean_obj_tag(v_a_715_) == 1)
{
lean_object* v_val_719_; lean_object* v___x_720_; lean_object* v_dummy_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
lean_del_object(v___x_717_);
v_val_719_ = lean_ctor_get(v_a_715_, 0);
lean_inc(v_val_719_);
lean_dec_ref_known(v_a_715_, 1);
v___x_720_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v_dummy_721_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0, &l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0);
lean_inc(v___x_709_);
v___x_722_ = lean_mk_array(v___x_709_, v_dummy_721_);
v___x_723_ = lean_unsigned_to_nat(1u);
v___x_724_ = lean_nat_sub(v___x_709_, v___x_723_);
lean_dec(v___x_709_);
v___x_725_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_697_, v___x_722_, v___x_724_);
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = lean_array_get_size(v___x_725_);
v___x_728_ = l_Array_toSubarray___redArg(v___x_725_, v___x_726_, v___x_727_);
v___x_729_ = lean_box(0);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___x_728_);
lean_ctor_set(v___x_707_, 0, v___x_720_);
v___x_731_ = v___x_707_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_728_);
v___x_731_ = v_reuseFailAlloc_758_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_732_; size_t v_sz_733_; size_t v___x_734_; lean_object* v___x_735_; 
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_729_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v_sz_733_ = lean_array_size(v_fvars_704_);
v___x_734_ = ((size_t)0ULL);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___redArg(v_val_719_, v_fvars_704_, v_sz_733_, v___x_734_, v___x_732_);
lean_dec_ref(v_fvars_704_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_749_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_749_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_749_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_749_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_fst_740_; 
v_fst_740_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_fst_740_);
lean_dec(v_a_736_);
if (lean_obj_tag(v_fst_740_) == 0)
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = lean_box(v___x_711_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_741_);
v___x_743_ = v___x_738_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
else
{
lean_object* v_val_745_; lean_object* v___x_747_; 
v_val_745_ = lean_ctor_get(v_fst_740_, 0);
lean_inc(v_val_745_);
lean_dec_ref_known(v_fst_740_, 1);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v_val_745_);
v___x_747_ = v___x_738_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_val_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
v_a_750_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_735_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_735_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
else
{
uint8_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
lean_dec(v_a_715_);
lean_dec(v___x_709_);
lean_del_object(v___x_707_);
lean_dec_ref(v_fvars_704_);
lean_dec_ref(v_e_697_);
v___x_759_ = 0;
v___x_760_ = lean_box(v___x_759_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_760_);
v___x_762_ = v___x_717_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v___x_709_);
lean_del_object(v___x_707_);
lean_dec_ref(v_fvars_704_);
lean_dec_ref(v_e_697_);
v_a_765_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_714_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_714_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___boxed(lean_object* v_e_774_, lean_object* v_decl_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(v_e_774_, v_decl_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
return v_res_781_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0(lean_object* v_00_u03b2_782_, lean_object* v_m_783_, lean_object* v_a_784_){
_start:
{
uint8_t v___x_785_; 
v___x_785_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_m_783_, v_a_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___boxed(lean_object* v_00_u03b2_786_, lean_object* v_m_787_, lean_object* v_a_788_){
_start:
{
uint8_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0(v_00_u03b2_786_, v_m_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_m_787_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1(lean_object* v_00_u03b2_791_, lean_object* v_m_792_, lean_object* v_query_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v_m_792_, v_query_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___boxed(lean_object* v_00_u03b2_795_, lean_object* v_m_796_, lean_object* v_query_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1(v_00_u03b2_795_, v_m_796_, v_query_797_);
lean_dec(v_query_797_);
lean_dec_ref(v_m_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2(lean_object* v_00_u03b2_799_, lean_object* v_m_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_m_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___boxed(lean_object* v_00_u03b2_802_, lean_object* v_m_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2(v_00_u03b2_802_, v_m_803_);
lean_dec_ref(v_m_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3(lean_object* v_val_805_, lean_object* v_as_806_, size_t v_sz_807_, size_t v_i_808_, lean_object* v_b_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___redArg(v_val_805_, v_as_806_, v_sz_807_, v_i_808_, v_b_809_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3___boxed(lean_object* v_val_816_, lean_object* v_as_817_, lean_object* v_sz_818_, lean_object* v_i_819_, lean_object* v_b_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
size_t v_sz_boxed_826_; size_t v_i_boxed_827_; lean_object* v_res_828_; 
v_sz_boxed_826_ = lean_unbox_usize(v_sz_818_);
lean_dec(v_sz_818_);
v_i_boxed_827_ = lean_unbox_usize(v_i_819_);
lean_dec(v_i_819_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__3(v_val_816_, v_as_817_, v_sz_boxed_826_, v_i_boxed_827_, v_b_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec_ref(v_as_817_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0(lean_object* v_00_u03b2_829_, lean_object* v_m_830_, lean_object* v_query_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_m_830_, v_query_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_833_, lean_object* v_m_834_, lean_object* v_query_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0(v_00_u03b2_833_, v_m_834_, v_query_835_);
lean_dec(v_query_835_);
lean_dec_ref(v_m_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2(lean_object* v_00_u03b2_837_, lean_object* v_m_838_, lean_object* v_query_839_, lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(v_m_838_, v_query_839_, v_x_840_, v_x_841_, v_x_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___boxed(lean_object* v_00_u03b2_845_, lean_object* v_m_846_, lean_object* v_query_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2(v_00_u03b2_845_, v_m_846_, v_query_847_, v_x_848_, v_x_849_, v_x_850_, v_x_851_);
lean_dec(v_query_847_);
lean_dec_ref(v_m_846_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4(lean_object* v_00_u03b2_853_, lean_object* v_init_854_, lean_object* v_b_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4___redArg(v_init_854_, v_b_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4___boxed(lean_object* v_00_u03b2_857_, lean_object* v_init_858_, lean_object* v_b_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4(v_00_u03b2_857_, v_init_858_, v_b_859_);
lean_dec_ref(v_b_859_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_861_, lean_object* v_b_862_, lean_object* v_acc_863_, lean_object* v_i_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4_spec__5___redArg(v_b_862_, v_acc_863_, v_i_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_866_, lean_object* v_b_867_, lean_object* v_acc_868_, lean_object* v_i_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2_spec__4_spec__5(v_00_u03b2_866_, v_b_867_, v_acc_868_, v_i_869_);
lean_dec_ref(v_b_867_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(lean_object* v_mvarId_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___x_874_; lean_object* v_mctx_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_874_ = lean_st_ref_get(v___y_872_);
v_mctx_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc_ref(v_mctx_875_);
lean_dec(v___x_874_);
v___x_876_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_875_, v_mvarId_871_);
lean_dec_ref(v_mctx_875_);
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg___boxed(lean_object* v_mvarId_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarId_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec(v_mvarId_878_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0(lean_object* v_mvarId_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarId_882_, v___y_884_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___boxed(lean_object* v_mvarId_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0(v_mvarId_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v_mvarId_889_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(lean_object* v_e_896_, lean_object* v___y_897_){
_start:
{
uint8_t v___x_899_; 
v___x_899_ = l_Lean_Expr_hasMVar(v_e_896_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v_e_896_);
return v___x_900_;
}
else
{
lean_object* v___x_901_; lean_object* v_mctx_902_; lean_object* v___x_903_; lean_object* v_fst_904_; lean_object* v_snd_905_; lean_object* v___x_906_; lean_object* v_cache_907_; lean_object* v_zetaDeltaFVarIds_908_; lean_object* v_postponed_909_; lean_object* v_diag_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_919_; 
v___x_901_ = lean_st_ref_get(v___y_897_);
v_mctx_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc_ref(v_mctx_902_);
lean_dec(v___x_901_);
v___x_903_ = l_Lean_instantiateMVarsCore(v_mctx_902_, v_e_896_);
v_fst_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_fst_904_);
v_snd_905_ = lean_ctor_get(v___x_903_, 1);
lean_inc(v_snd_905_);
lean_dec_ref(v___x_903_);
v___x_906_ = lean_st_ref_take(v___y_897_);
v_cache_907_ = lean_ctor_get(v___x_906_, 1);
v_zetaDeltaFVarIds_908_ = lean_ctor_get(v___x_906_, 2);
v_postponed_909_ = lean_ctor_get(v___x_906_, 3);
v_diag_910_ = lean_ctor_get(v___x_906_, 4);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; 
v_unused_920_ = lean_ctor_get(v___x_906_, 0);
lean_dec(v_unused_920_);
v___x_912_ = v___x_906_;
v_isShared_913_ = v_isSharedCheck_919_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_diag_910_);
lean_inc(v_postponed_909_);
lean_inc(v_zetaDeltaFVarIds_908_);
lean_inc(v_cache_907_);
lean_dec(v___x_906_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_919_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v_snd_905_);
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_snd_905_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_cache_907_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_zetaDeltaFVarIds_908_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_postponed_909_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_diag_910_);
v___x_915_ = v_reuseFailAlloc_918_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_st_ref_put(v___y_897_, v___x_915_);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v_fst_904_);
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg___boxed(lean_object* v_e_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_e_921_, v___y_922_);
lean_dec(v___y_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1(lean_object* v_e_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_e_925_, v___y_927_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___boxed(lean_object* v_e_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1(v_e_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(lean_object* v_mvarId_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; lean_object* v_mctx_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_942_ = lean_st_ref_get(v___y_940_);
v_mctx_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc_ref(v_mctx_943_);
lean_dec(v___x_942_);
v___x_944_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_943_, v_mvarId_939_);
lean_dec_ref(v_mctx_943_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg___boxed(lean_object* v_mvarId_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec(v_mvarId_946_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2(lean_object* v_mvarId_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_950_, v___y_952_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___boxed(lean_object* v_mvarId_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2(v_mvarId_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v_mvarId_957_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(lean_object* v_mvarIdPending_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarIdPending_964_, v_a_966_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1046_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_1046_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1046_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
if (lean_obj_tag(v_a_971_) == 1)
{
lean_object* v_val_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v_val_975_ = lean_ctor_get(v_a_971_, 0);
lean_inc(v_val_975_);
lean_dec_ref_known(v_a_971_, 1);
v___x_976_ = l_Lean_Expr_getAppFn_x27(v_val_975_);
v___x_977_ = l_Lean_Expr_isMVar(v___x_976_);
lean_dec_ref(v___x_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_979_; 
lean_dec(v_val_975_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v_mvarIdPending_964_);
v___x_979_ = v___x_973_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_mvarIdPending_964_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
else
{
lean_object* v___x_981_; 
lean_del_object(v___x_973_);
v___x_981_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_val_975_, v_a_966_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1034_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_1034_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1034_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_Expr_consumeMData(v_a_982_);
lean_dec(v_a_982_);
if (lean_obj_tag(v___x_986_) == 2)
{
lean_object* v_mvarId_987_; lean_object* v___x_989_; 
lean_dec(v_mvarIdPending_964_);
v_mvarId_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_mvarId_987_);
lean_dec_ref_known(v___x_986_, 1);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v_mvarId_987_);
v___x_989_ = v___x_984_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_mvarId_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
else
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Expr_getAppFn_x27(v___x_986_);
if (lean_obj_tag(v___x_991_) == 2)
{
lean_object* v_mvarId_992_; lean_object* v___x_993_; 
lean_del_object(v___x_984_);
v_mvarId_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_mvarId_992_);
lean_dec_ref_known(v___x_991_, 1);
v___x_993_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_992_, v_a_966_);
lean_dec(v_mvarId_992_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1022_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1022_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1022_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
if (lean_obj_tag(v_a_994_) == 1)
{
lean_object* v_val_998_; lean_object* v___x_999_; 
lean_del_object(v___x_996_);
v_val_998_ = lean_ctor_get(v_a_994_, 0);
lean_inc_n(v_val_998_, 2);
lean_dec_ref_known(v_a_994_, 1);
v___x_999_ = l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(v___x_986_, v_val_998_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1010_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1010_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1010_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_unbox(v_a_1000_);
lean_dec(v_a_1000_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1006_; 
lean_dec(v_val_998_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v_mvarIdPending_964_);
v___x_1006_ = v___x_1002_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_mvarIdPending_964_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
else
{
lean_object* v_mvarIdPending_1008_; 
lean_del_object(v___x_1002_);
lean_dec(v_mvarIdPending_964_);
v_mvarIdPending_1008_ = lean_ctor_get(v_val_998_, 1);
lean_inc(v_mvarIdPending_1008_);
lean_dec(v_val_998_);
v_mvarIdPending_964_ = v_mvarIdPending_1008_;
goto _start;
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v_val_998_);
lean_dec(v_mvarIdPending_964_);
v_a_1011_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_999_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_999_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
else
{
lean_object* v___x_1020_; 
lean_dec(v_a_994_);
lean_dec_ref(v___x_986_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v_mvarIdPending_964_);
v___x_1020_ = v___x_996_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_mvarIdPending_964_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v___x_986_);
lean_dec(v_mvarIdPending_964_);
v_a_1023_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_993_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_993_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v___x_1032_; 
lean_dec_ref(v___x_991_);
lean_dec_ref(v___x_986_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v_mvarIdPending_964_);
v___x_1032_ = v___x_984_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_mvarIdPending_964_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v_mvarIdPending_964_);
v_a_1035_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_981_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_981_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
else
{
lean_object* v___x_1044_; 
lean_dec(v_a_971_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v_mvarIdPending_964_);
v___x_1044_ = v___x_973_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_mvarIdPending_964_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_mvarIdPending_964_);
v_a_1047_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_970_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_970_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending___boxed(lean_object* v_mvarIdPending_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(v_mvarIdPending_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(lean_object* v_n_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___closed__0));
v___x_1065_ = lean_string_append(v___x_1064_, v_n_1063_);
v___x_1066_ = lean_string_append(v___x_1065_, v___x_1064_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___boxed(lean_object* v_n_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v_n_1067_);
lean_dec_ref(v_n_1067_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString_spec__0(lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
if (lean_obj_tag(v_a_1069_) == 0)
{
lean_object* v___x_1071_; 
v___x_1071_ = l_List_reverse___redArg(v_a_1070_);
return v___x_1071_;
}
else
{
lean_object* v_head_1072_; lean_object* v_tail_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1092_; 
v_head_1072_ = lean_ctor_get(v_a_1069_, 0);
v_tail_1073_ = lean_ctor_get(v_a_1069_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_a_1069_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1075_ = v_a_1069_;
v_isShared_1076_ = v_isSharedCheck_1092_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_tail_1073_);
lean_inc(v_head_1072_);
lean_dec(v_a_1069_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1092_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___y_1078_; uint8_t v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = l_Lean_Name_hasMacroScopes(v_head_1072_);
v___x_1084_ = 1;
if (v___x_1083_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = l_Lean_Name_toString(v_head_1072_, v___x_1084_);
v___x_1086_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v___x_1085_);
lean_dec_ref(v___x_1085_);
v___y_1078_ = v___x_1086_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1087_ = l_Lean_Name_eraseMacroScopes(v_head_1072_);
lean_dec(v_head_1072_);
v___x_1088_ = l_Lean_Name_toString(v___x_1087_, v___x_1084_);
v___x_1089_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0));
v___x_1090_ = lean_string_append(v___x_1088_, v___x_1089_);
v___x_1091_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v___x_1090_);
lean_dec_ref(v___x_1090_);
v___y_1078_ = v___x_1091_;
goto v___jp_1077_;
}
v___jp_1077_:
{
lean_object* v___x_1080_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v_a_1070_);
lean_ctor_set(v___x_1075_, 0, v___y_1078_);
v___x_1080_ = v___x_1075_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___y_1078_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_a_1070_);
v___x_1080_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
v_a_1069_ = v_tail_1073_;
v_a_1070_ = v___x_1080_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString(lean_object* v_ns_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1095_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0));
v___x_1096_ = lean_box(0);
v___x_1097_ = l_List_mapTR_loop___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString_spec__0(v_ns_1094_, v___x_1096_);
v___x_1098_ = l_String_intercalate(v___x_1095_, v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(lean_object* v_count_1099_, lean_object* v_singular_1100_, lean_object* v_plural_1101_){
_start:
{
lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = lean_unsigned_to_nat(1u);
v___x_1103_ = lean_nat_dec_eq(v_count_1099_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_inc_ref(v_plural_1101_);
return v_plural_1101_;
}
else
{
lean_inc_ref(v_singular_1100_);
return v_singular_1100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1___boxed(lean_object* v_count_1104_, lean_object* v_singular_1105_, lean_object* v_plural_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v_count_1104_, v_singular_1105_, v_plural_1106_);
lean_dec_ref(v_plural_1106_);
lean_dec_ref(v_singular_1105_);
lean_dec(v_count_1104_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(lean_object* v___x_1108_, lean_object* v_as_1109_, size_t v_i_1110_, size_t v_stop_1111_, lean_object* v_b_1112_){
_start:
{
uint8_t v___x_1113_; 
v___x_1113_ = lean_usize_dec_eq(v_i_1110_, v_stop_1111_);
if (v___x_1113_ == 0)
{
size_t v___x_1114_; size_t v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = ((size_t)1ULL);
v___x_1115_ = lean_usize_sub(v_i_1110_, v___x_1114_);
v___x_1116_ = lean_array_uget_borrowed(v_as_1109_, v___x_1115_);
if (lean_obj_tag(v___x_1116_) == 0)
{
v_i_1110_ = v___x_1115_;
goto _start;
}
else
{
lean_object* v_val_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v_val_1118_ = lean_ctor_get(v___x_1116_, 0);
v___x_1119_ = l_Lean_LocalDecl_fvarId(v_val_1118_);
v___x_1120_ = l_Lean_LocalContext_contains(v___x_1108_, v___x_1119_);
lean_dec(v___x_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = l_Lean_LocalDecl_userName(v_val_1118_);
v___x_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v_b_1112_);
v_i_1110_ = v___x_1115_;
v_b_1112_ = v___x_1122_;
goto _start;
}
else
{
v_i_1110_ = v___x_1115_;
goto _start;
}
}
}
else
{
return v_b_1112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3___boxed(lean_object* v___x_1125_, lean_object* v_as_1126_, lean_object* v_i_1127_, lean_object* v_stop_1128_, lean_object* v_b_1129_){
_start:
{
size_t v_i_boxed_1130_; size_t v_stop_boxed_1131_; lean_object* v_res_1132_; 
v_i_boxed_1130_ = lean_unbox_usize(v_i_1127_);
lean_dec(v_i_1127_);
v_stop_boxed_1131_ = lean_unbox_usize(v_stop_1128_);
lean_dec(v_stop_1128_);
v_res_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_1125_, v_as_1126_, v_i_boxed_1130_, v_stop_boxed_1131_, v_b_1129_);
lean_dec_ref(v_as_1126_);
lean_dec_ref(v___x_1125_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(lean_object* v___x_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_){
_start:
{
if (lean_obj_tag(v_x_1134_) == 0)
{
lean_object* v_cs_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v_cs_1136_ = lean_ctor_get(v_x_1134_, 0);
v___x_1137_ = lean_array_get_size(v_cs_1136_);
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_nat_dec_lt(v___x_1138_, v___x_1137_);
if (v___x_1139_ == 0)
{
return v_x_1135_;
}
else
{
size_t v___x_1140_; size_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_usize_of_nat(v___x_1137_);
v___x_1141_ = ((size_t)0ULL);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(v___x_1133_, v_cs_1136_, v___x_1140_, v___x_1141_, v_x_1135_);
return v___x_1142_;
}
}
else
{
lean_object* v_vs_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v_vs_1143_ = lean_ctor_get(v_x_1134_, 0);
v___x_1144_ = lean_array_get_size(v_vs_1143_);
v___x_1145_ = lean_unsigned_to_nat(0u);
v___x_1146_ = lean_nat_dec_lt(v___x_1145_, v___x_1144_);
if (v___x_1146_ == 0)
{
return v_x_1135_;
}
else
{
size_t v___x_1147_; size_t v___x_1148_; lean_object* v___x_1149_; 
v___x_1147_ = lean_usize_of_nat(v___x_1144_);
v___x_1148_ = ((size_t)0ULL);
v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_1133_, v_vs_1143_, v___x_1147_, v___x_1148_, v_x_1135_);
return v___x_1149_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(lean_object* v___x_1150_, lean_object* v_as_1151_, size_t v_i_1152_, size_t v_stop_1153_, lean_object* v_b_1154_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_usize_dec_eq(v_i_1152_, v_stop_1153_);
if (v___x_1155_ == 0)
{
size_t v___x_1156_; size_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1156_ = ((size_t)1ULL);
v___x_1157_ = lean_usize_sub(v_i_1152_, v___x_1156_);
v___x_1158_ = lean_array_uget_borrowed(v_as_1151_, v___x_1157_);
v___x_1159_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_1150_, v___x_1158_, v_b_1154_);
v_i_1152_ = v___x_1157_;
v_b_1154_ = v___x_1159_;
goto _start;
}
else
{
return v_b_1154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v___x_1161_, lean_object* v_as_1162_, lean_object* v_i_1163_, lean_object* v_stop_1164_, lean_object* v_b_1165_){
_start:
{
size_t v_i_boxed_1166_; size_t v_stop_boxed_1167_; lean_object* v_res_1168_; 
v_i_boxed_1166_ = lean_unbox_usize(v_i_1163_);
lean_dec(v_i_1163_);
v_stop_boxed_1167_ = lean_unbox_usize(v_stop_1164_);
lean_dec(v_stop_1164_);
v_res_1168_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(v___x_1161_, v_as_1162_, v_i_boxed_1166_, v_stop_boxed_1167_, v_b_1165_);
lean_dec_ref(v_as_1162_);
lean_dec_ref(v___x_1161_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2___boxed(lean_object* v___x_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_1169_, v_x_1170_, v_x_1171_);
lean_dec_ref(v_x_1170_);
lean_dec_ref(v___x_1169_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(lean_object* v___x_1173_, lean_object* v_t_1174_, lean_object* v_init_1175_){
_start:
{
lean_object* v_root_1176_; lean_object* v_tail_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v_root_1176_ = lean_ctor_get(v_t_1174_, 0);
v_tail_1177_ = lean_ctor_get(v_t_1174_, 1);
v___x_1178_ = lean_array_get_size(v_tail_1177_);
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = lean_nat_dec_lt(v___x_1179_, v___x_1178_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; 
v___x_1181_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_1173_, v_root_1176_, v_init_1175_);
return v___x_1181_;
}
else
{
size_t v___x_1182_; size_t v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1182_ = lean_usize_of_nat(v___x_1178_);
v___x_1183_ = ((size_t)0ULL);
v___x_1184_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_1173_, v_tail_1177_, v___x_1182_, v___x_1183_, v_init_1175_);
v___x_1185_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_1173_, v_root_1176_, v___x_1184_);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0___boxed(lean_object* v___x_1186_, lean_object* v_t_1187_, lean_object* v_init_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(v___x_1186_, v_t_1187_, v_init_1188_);
lean_dec_ref(v_t_1187_);
lean_dec_ref(v___x_1186_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(lean_object* v___x_1190_, lean_object* v_lctx_1191_, lean_object* v_init_1192_){
_start:
{
lean_object* v_decls_1193_; lean_object* v___x_1194_; 
v_decls_1193_ = lean_ctor_get(v_lctx_1191_, 1);
v___x_1194_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(v___x_1190_, v_decls_1193_, v_init_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0___boxed(lean_object* v___x_1195_, lean_object* v_lctx_1196_, lean_object* v_init_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(v___x_1195_, v_lctx_1196_, v_init_1197_);
lean_dec_ref(v_lctx_1196_);
lean_dec_ref(v___x_1195_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(lean_object* v_mdecl_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_lctx_1207_; lean_object* v_lctx_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_lctx_1207_ = lean_ctor_get(v_a_1205_, 2);
v_lctx_1208_ = lean_ctor_get(v_mdecl_1204_, 1);
v___x_1209_ = lean_box(0);
v___x_1210_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(v_lctx_1207_, v_lctx_1208_, v___x_1209_);
v___x_1211_ = l_List_isEmpty___redArg(v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1212_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__0));
v___x_1213_ = l_List_lengthTR___redArg(v___x_1210_);
v___x_1214_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__1));
v___x_1215_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__2));
v___x_1216_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v___x_1213_, v___x_1214_, v___x_1215_);
lean_dec(v___x_1213_);
v___x_1217_ = lean_string_append(v___x_1212_, v___x_1216_);
lean_dec_ref(v___x_1216_);
v___x_1218_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__3));
v___x_1219_ = lean_string_append(v___x_1217_, v___x_1218_);
v___x_1220_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString(v___x_1210_);
v___x_1221_ = lean_string_append(v___x_1219_, v___x_1220_);
lean_dec_ref(v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec(v___x_1210_);
v___x_1223_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4));
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___boxed(lean_object* v_mdecl_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_mdecl_1225_, v_a_1226_);
lean_dec_ref(v_a_1226_);
lean_dec_ref(v_mdecl_1225_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars(lean_object* v_mdecl_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_mdecl_1229_, v_a_1230_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___boxed(lean_object* v_mdecl_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars(v_mdecl_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec_ref(v_mdecl_1236_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(lean_object* v_lctxInitIndices_1243_, lean_object* v_mdecl_1244_, lean_object* v_as_1245_, size_t v_i_1246_, size_t v_stop_1247_, lean_object* v_b_1248_){
_start:
{
uint8_t v___x_1249_; 
v___x_1249_ = lean_usize_dec_eq(v_i_1246_, v_stop_1247_);
if (v___x_1249_ == 0)
{
size_t v___x_1250_; size_t v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = ((size_t)1ULL);
v___x_1251_ = lean_usize_sub(v_i_1246_, v___x_1250_);
v___x_1252_ = lean_array_uget_borrowed(v_as_1245_, v___x_1251_);
if (lean_obj_tag(v___x_1252_) == 0)
{
v_i_1246_ = v___x_1251_;
goto _start;
}
else
{
lean_object* v_val_1254_; uint8_t v___y_1256_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_val_1254_ = lean_ctor_get(v___x_1252_, 0);
v___x_1261_ = l_Lean_LocalDecl_index(v_val_1254_);
v___x_1262_ = lean_nat_dec_le(v_lctxInitIndices_1243_, v___x_1261_);
lean_dec(v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v_lctx_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_lctx_1263_ = lean_ctor_get(v_mdecl_1244_, 1);
v___x_1264_ = l_Lean_LocalDecl_fvarId(v_val_1254_);
v___x_1265_ = l_Lean_LocalContext_contains(v_lctx_1263_, v___x_1264_);
lean_dec(v___x_1264_);
v___y_1256_ = v___x_1265_;
goto v___jp_1255_;
}
else
{
v___y_1256_ = v___x_1262_;
goto v___jp_1255_;
}
v___jp_1255_:
{
if (v___y_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = l_Lean_LocalDecl_userName(v_val_1254_);
v___x_1258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v_b_1248_);
v_i_1246_ = v___x_1251_;
v_b_1248_ = v___x_1258_;
goto _start;
}
else
{
v_i_1246_ = v___x_1251_;
goto _start;
}
}
}
}
else
{
return v_b_1248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2___boxed(lean_object* v_lctxInitIndices_1266_, lean_object* v_mdecl_1267_, lean_object* v_as_1268_, lean_object* v_i_1269_, lean_object* v_stop_1270_, lean_object* v_b_1271_){
_start:
{
size_t v_i_boxed_1272_; size_t v_stop_boxed_1273_; lean_object* v_res_1274_; 
v_i_boxed_1272_ = lean_unbox_usize(v_i_1269_);
lean_dec(v_i_1269_);
v_stop_boxed_1273_ = lean_unbox_usize(v_stop_1270_);
lean_dec(v_stop_1270_);
v_res_1274_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(v_lctxInitIndices_1266_, v_mdecl_1267_, v_as_1268_, v_i_boxed_1272_, v_stop_boxed_1273_, v_b_1271_);
lean_dec_ref(v_as_1268_);
lean_dec_ref(v_mdecl_1267_);
lean_dec(v_lctxInitIndices_1266_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(lean_object* v_lctxInitIndices_1275_, lean_object* v_mdecl_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
if (lean_obj_tag(v_x_1277_) == 0)
{
lean_object* v_cs_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v_cs_1279_ = lean_ctor_get(v_x_1277_, 0);
v___x_1280_ = lean_array_get_size(v_cs_1279_);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = lean_nat_dec_lt(v___x_1281_, v___x_1280_);
if (v___x_1282_ == 0)
{
return v_x_1278_;
}
else
{
size_t v___x_1283_; size_t v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = lean_usize_of_nat(v___x_1280_);
v___x_1284_ = ((size_t)0ULL);
v___x_1285_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2(v_lctxInitIndices_1275_, v_mdecl_1276_, v_cs_1279_, v___x_1283_, v___x_1284_, v_x_1278_);
return v___x_1285_;
}
}
else
{
lean_object* v_vs_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_vs_1286_ = lean_ctor_get(v_x_1277_, 0);
v___x_1287_ = lean_array_get_size(v_vs_1286_);
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = lean_nat_dec_lt(v___x_1288_, v___x_1287_);
if (v___x_1289_ == 0)
{
return v_x_1278_;
}
else
{
size_t v___x_1290_; size_t v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_usize_of_nat(v___x_1287_);
v___x_1291_ = ((size_t)0ULL);
v___x_1292_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(v_lctxInitIndices_1275_, v_mdecl_1276_, v_vs_1286_, v___x_1290_, v___x_1291_, v_x_1278_);
return v___x_1292_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2(lean_object* v_lctxInitIndices_1293_, lean_object* v_mdecl_1294_, lean_object* v_as_1295_, size_t v_i_1296_, size_t v_stop_1297_, lean_object* v_b_1298_){
_start:
{
uint8_t v___x_1299_; 
v___x_1299_ = lean_usize_dec_eq(v_i_1296_, v_stop_1297_);
if (v___x_1299_ == 0)
{
size_t v___x_1300_; size_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1300_ = ((size_t)1ULL);
v___x_1301_ = lean_usize_sub(v_i_1296_, v___x_1300_);
v___x_1302_ = lean_array_uget_borrowed(v_as_1295_, v___x_1301_);
v___x_1303_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_1293_, v_mdecl_1294_, v___x_1302_, v_b_1298_);
v_i_1296_ = v___x_1301_;
v_b_1298_ = v___x_1303_;
goto _start;
}
else
{
return v_b_1298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_lctxInitIndices_1305_, lean_object* v_mdecl_1306_, lean_object* v_as_1307_, lean_object* v_i_1308_, lean_object* v_stop_1309_, lean_object* v_b_1310_){
_start:
{
size_t v_i_boxed_1311_; size_t v_stop_boxed_1312_; lean_object* v_res_1313_; 
v_i_boxed_1311_ = lean_unbox_usize(v_i_1308_);
lean_dec(v_i_1308_);
v_stop_boxed_1312_ = lean_unbox_usize(v_stop_1309_);
lean_dec(v_stop_1309_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2(v_lctxInitIndices_1305_, v_mdecl_1306_, v_as_1307_, v_i_boxed_1311_, v_stop_boxed_1312_, v_b_1310_);
lean_dec_ref(v_as_1307_);
lean_dec_ref(v_mdecl_1306_);
lean_dec(v_lctxInitIndices_1305_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1___boxed(lean_object* v_lctxInitIndices_1314_, lean_object* v_mdecl_1315_, lean_object* v_x_1316_, lean_object* v_x_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_1314_, v_mdecl_1315_, v_x_1316_, v_x_1317_);
lean_dec_ref(v_x_1316_);
lean_dec_ref(v_mdecl_1315_);
lean_dec(v_lctxInitIndices_1314_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0(lean_object* v_lctxInitIndices_1319_, lean_object* v_mdecl_1320_, lean_object* v_t_1321_, lean_object* v_init_1322_){
_start:
{
lean_object* v_root_1323_; lean_object* v_tail_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v_root_1323_ = lean_ctor_get(v_t_1321_, 0);
v_tail_1324_ = lean_ctor_get(v_t_1321_, 1);
v___x_1325_ = lean_array_get_size(v_tail_1324_);
v___x_1326_ = lean_unsigned_to_nat(0u);
v___x_1327_ = lean_nat_dec_lt(v___x_1326_, v___x_1325_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
v___x_1328_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_1319_, v_mdecl_1320_, v_root_1323_, v_init_1322_);
return v___x_1328_;
}
else
{
size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1329_ = lean_usize_of_nat(v___x_1325_);
v___x_1330_ = ((size_t)0ULL);
v___x_1331_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(v_lctxInitIndices_1319_, v_mdecl_1320_, v_tail_1324_, v___x_1329_, v___x_1330_, v_init_1322_);
v___x_1332_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_1319_, v_mdecl_1320_, v_root_1323_, v___x_1331_);
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0___boxed(lean_object* v_lctxInitIndices_1333_, lean_object* v_mdecl_1334_, lean_object* v_t_1335_, lean_object* v_init_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0(v_lctxInitIndices_1333_, v_mdecl_1334_, v_t_1335_, v_init_1336_);
lean_dec_ref(v_t_1335_);
lean_dec_ref(v_mdecl_1334_);
lean_dec(v_lctxInitIndices_1333_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0(lean_object* v_lctxInitIndices_1338_, lean_object* v_mdecl_1339_, lean_object* v_lctx_1340_, lean_object* v_init_1341_){
_start:
{
lean_object* v_decls_1342_; lean_object* v___x_1343_; 
v_decls_1342_ = lean_ctor_get(v_lctx_1340_, 1);
v___x_1343_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0(v_lctxInitIndices_1338_, v_mdecl_1339_, v_decls_1342_, v_init_1341_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0___boxed(lean_object* v_lctxInitIndices_1344_, lean_object* v_mdecl_1345_, lean_object* v_lctx_1346_, lean_object* v_init_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0(v_lctxInitIndices_1344_, v_mdecl_1345_, v_lctx_1346_, v_init_1347_);
lean_dec_ref(v_lctx_1346_);
lean_dec_ref(v_mdecl_1345_);
lean_dec(v_lctxInitIndices_1344_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(lean_object* v_lctxInitIndices_1353_, lean_object* v_mdecl_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v_lctx_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v_lctx_1357_ = lean_ctor_get(v_a_1355_, 2);
v___x_1358_ = lean_box(0);
v___x_1359_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0(v_lctxInitIndices_1353_, v_mdecl_1354_, v_lctx_1357_, v___x_1358_);
v___x_1360_ = l_List_isEmpty___redArg(v___x_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1361_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__0));
v___x_1362_ = l_List_lengthTR___redArg(v___x_1359_);
v___x_1363_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__1));
v___x_1364_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__2));
v___x_1365_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v___x_1362_, v___x_1363_, v___x_1364_);
lean_dec(v___x_1362_);
v___x_1366_ = lean_string_append(v___x_1361_, v___x_1365_);
lean_dec_ref(v___x_1365_);
v___x_1367_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__3));
v___x_1368_ = lean_string_append(v___x_1366_, v___x_1367_);
v___x_1369_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString(v___x_1359_);
v___x_1370_ = lean_string_append(v___x_1368_, v___x_1369_);
lean_dec_ref(v___x_1369_);
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_dec(v___x_1359_);
v___x_1372_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4));
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___boxed(lean_object* v_lctxInitIndices_1374_, lean_object* v_mdecl_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(v_lctxInitIndices_1374_, v_mdecl_1375_, v_a_1376_);
lean_dec_ref(v_a_1376_);
lean_dec_ref(v_mdecl_1375_);
lean_dec(v_lctxInitIndices_1374_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars(lean_object* v_lctxInitIndices_1379_, lean_object* v_mdecl_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(v_lctxInitIndices_1379_, v_mdecl_1380_, v_a_1381_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___boxed(lean_object* v_lctxInitIndices_1387_, lean_object* v_mdecl_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars(v_lctxInitIndices_1387_, v_mdecl_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec_ref(v_mdecl_1388_);
lean_dec(v_lctxInitIndices_1387_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0(size_t v_sz_1395_, size_t v_i_1396_, lean_object* v_bs_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
uint8_t v___x_1403_; 
v___x_1403_ = lean_usize_dec_lt(v_i_1396_, v_sz_1395_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1404_, 0, v_bs_1397_);
return v___x_1404_;
}
else
{
lean_object* v_v_1405_; lean_object* v___x_1406_; lean_object* v_bs_x27_1407_; lean_object* v_a_1409_; lean_object* v___x_1414_; 
v_v_1405_ = lean_array_uget(v_bs_1397_, v_i_1396_);
v___x_1406_ = lean_unsigned_to_nat(0u);
v_bs_x27_1407_ = lean_array_uset(v_bs_1397_, v_i_1396_, v___x_1406_);
v___x_1414_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(v_v_1405_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1416_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1416_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v_a_1415_);
lean_dec(v_a_1415_);
v_a_1409_ = v___x_1416_;
goto v___jp_1408_;
}
else
{
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1417_; 
v_a_1417_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1414_, 1);
v_a_1409_ = v_a_1417_;
goto v___jp_1408_;
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref(v_bs_x27_1407_);
v_a_1418_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1414_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1414_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
v___jp_1408_:
{
size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = ((size_t)1ULL);
v___x_1411_ = lean_usize_add(v_i_1396_, v___x_1410_);
v___x_1412_ = lean_array_uset(v_bs_x27_1407_, v_i_1396_, v_a_1409_);
v_i_1396_ = v___x_1411_;
v_bs_1397_ = v___x_1412_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0___boxed(lean_object* v_sz_1426_, lean_object* v_i_1427_, lean_object* v_bs_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
size_t v_sz_boxed_1434_; size_t v_i_boxed_1435_; lean_object* v_res_1436_; 
v_sz_boxed_1434_ = lean_unbox_usize(v_sz_1426_);
lean_dec(v_sz_1426_);
v_i_boxed_1435_ = lean_unbox_usize(v_i_1427_);
lean_dec(v_i_1427_);
v_res_1436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0(v_sz_boxed_1434_, v_i_boxed_1435_, v_bs_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(lean_object* v___x_1439_, lean_object* v_as_1440_, size_t v_i_1441_, size_t v_stop_1442_, lean_object* v_b_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_a_1450_; uint8_t v___x_1454_; 
v___x_1454_ = lean_usize_dec_eq(v_i_1441_, v_stop_1442_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_array_uget_borrowed(v_as_1440_, v_i_1441_);
lean_inc(v___x_1455_);
v___x_1456_ = l_Lean_MVarId_getDecl(v___x_1455_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v_lctx_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v_lctx_1458_ = lean_ctor_get(v_a_1457_, 1);
lean_inc_ref(v_lctx_1458_);
lean_dec(v_a_1457_);
v___x_1459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0));
v___x_1460_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_1458_, v___x_1439_, v___x_1459_);
lean_dec_ref(v_lctx_1458_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; 
lean_inc(v___x_1455_);
v___x_1461_ = lean_array_push(v_b_1443_, v___x_1455_);
v_a_1450_ = v___x_1461_;
goto v___jp_1449_;
}
else
{
v_a_1450_ = v_b_1443_;
goto v___jp_1449_;
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec_ref(v_b_1443_);
v_a_1462_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1456_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1456_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v_b_1443_);
return v___x_1470_;
}
v___jp_1449_:
{
size_t v___x_1451_; size_t v___x_1452_; 
v___x_1451_ = ((size_t)1ULL);
v___x_1452_ = lean_usize_add(v_i_1441_, v___x_1451_);
v_i_1441_ = v___x_1452_;
v_b_1443_ = v_a_1450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___boxed(lean_object* v___x_1471_, lean_object* v_as_1472_, lean_object* v_i_1473_, lean_object* v_stop_1474_, lean_object* v_b_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
size_t v_i_boxed_1481_; size_t v_stop_boxed_1482_; lean_object* v_res_1483_; 
v_i_boxed_1481_ = lean_unbox_usize(v_i_1473_);
lean_dec(v_i_1473_);
v_stop_boxed_1482_ = lean_unbox_usize(v_stop_1474_);
lean_dec(v_stop_1474_);
v_res_1483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(v___x_1471_, v_as_1472_, v_i_boxed_1481_, v_stop_boxed_1482_, v_b_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec_ref(v_as_1472_);
lean_dec_ref(v___x_1471_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(lean_object* v_e_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_awaitingMVars_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___x_1538_; 
v___x_1538_ = l_Lean_Meta_getMVarsNoDelayed(v_e_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v_a_1541_; lean_object* v___y_1546_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = lean_array_get_size(v_a_1539_);
v___x_1558_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__4));
v___x_1559_ = lean_nat_dec_lt(v___x_1556_, v___x_1557_);
if (v___x_1559_ == 0)
{
v_a_1541_ = v___x_1558_;
goto v___jp_1540_;
}
else
{
lean_object* v_lctx_1560_; uint8_t v___x_1561_; 
v_lctx_1560_ = lean_ctor_get(v_a_1491_, 2);
v___x_1561_ = lean_nat_dec_le(v___x_1557_, v___x_1557_);
if (v___x_1561_ == 0)
{
if (v___x_1559_ == 0)
{
v_a_1541_ = v___x_1558_;
goto v___jp_1540_;
}
else
{
size_t v___x_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = lean_usize_of_nat(v___x_1557_);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(v_lctx_1560_, v_a_1539_, v___x_1562_, v___x_1563_, v___x_1558_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
v___y_1546_ = v___x_1564_;
goto v___jp_1545_;
}
}
else
{
size_t v___x_1565_; size_t v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = ((size_t)0ULL);
v___x_1566_ = lean_usize_of_nat(v___x_1557_);
v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(v_lctx_1560_, v_a_1539_, v___x_1565_, v___x_1566_, v___x_1558_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
v___y_1546_ = v___x_1567_;
goto v___jp_1545_;
}
}
v___jp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1542_ = lean_array_get_size(v_a_1541_);
v___x_1543_ = lean_unsigned_to_nat(0u);
v___x_1544_ = lean_nat_dec_eq(v___x_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_dec(v_a_1539_);
v_awaitingMVars_1497_ = v_a_1541_;
v___y_1498_ = v_a_1491_;
v___y_1499_ = v_a_1492_;
v___y_1500_ = v_a_1493_;
v___y_1501_ = v_a_1494_;
goto v___jp_1496_;
}
else
{
lean_dec_ref(v_a_1541_);
v_awaitingMVars_1497_ = v_a_1539_;
v___y_1498_ = v_a_1491_;
v___y_1499_ = v_a_1492_;
v___y_1500_ = v_a_1493_;
v___y_1501_ = v_a_1494_;
goto v___jp_1496_;
}
}
v___jp_1545_:
{
if (lean_obj_tag(v___y_1546_) == 0)
{
lean_object* v_a_1547_; 
v_a_1547_ = lean_ctor_get(v___y_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___y_1546_, 1);
v_a_1541_ = v_a_1547_;
goto v___jp_1540_;
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec(v_a_1539_);
v_a_1548_ = lean_ctor_get(v___y_1546_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___y_1546_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___y_1546_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___y_1546_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
v_a_1568_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1538_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1538_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
v___jp_1496_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1502_ = lean_array_get_size(v_awaitingMVars_1497_);
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = lean_nat_dec_eq(v___x_1502_, v___x_1503_);
if (v___x_1504_ == 0)
{
size_t v_sz_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
v_sz_1505_ = lean_array_size(v_awaitingMVars_1497_);
v___x_1506_ = ((size_t)0ULL);
v___x_1507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0(v_sz_1505_, v___x_1506_, v_awaitingMVars_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1527_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1527_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1527_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1512_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__0));
v___x_1513_ = lean_array_get_size(v_a_1508_);
v___x_1514_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__1));
v___x_1515_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__2));
v___x_1516_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v___x_1513_, v___x_1514_, v___x_1515_);
v___x_1517_ = lean_string_append(v___x_1512_, v___x_1516_);
lean_dec_ref(v___x_1516_);
v___x_1518_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__3));
v___x_1519_ = lean_string_append(v___x_1517_, v___x_1518_);
v___x_1520_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0));
v___x_1521_ = lean_array_to_list(v_a_1508_);
v___x_1522_ = l_String_intercalate(v___x_1520_, v___x_1521_);
v___x_1523_ = lean_string_append(v___x_1519_, v___x_1522_);
lean_dec_ref(v___x_1522_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1523_);
v___x_1525_ = v___x_1510_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
v_a_1528_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1507_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1507_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec_ref(v_awaitingMVars_1497_);
v___x_1536_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4));
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___boxed(lean_object* v_e_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_e_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(lean_object* v_mvarId_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; lean_object* v_mctx_1587_; lean_object* v_decl_1588_; lean_object* v_depth_1589_; lean_object* v_depth_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1586_ = lean_st_ref_get(v___y_1584_);
v_mctx_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc_ref(v_mctx_1587_);
lean_dec(v___x_1586_);
v_decl_1588_ = l_Lean_MetavarContext_getDecl(v_mctx_1587_, v_mvarId_1583_);
v_depth_1589_ = lean_ctor_get(v_decl_1588_, 3);
lean_inc(v_depth_1589_);
lean_dec_ref(v_decl_1588_);
v_depth_1590_ = lean_ctor_get(v_mctx_1587_, 0);
lean_inc(v_depth_1590_);
lean_dec_ref(v_mctx_1587_);
v___x_1591_ = lean_nat_dec_eq(v_depth_1589_, v_depth_1590_);
lean_dec(v_depth_1590_);
lean_dec(v_depth_1589_);
v___x_1592_ = lean_box(v___x_1591_);
v___x_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg___boxed(lean_object* v_mvarId_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_1594_, v___y_1595_);
lean_dec(v___y_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0(lean_object* v_mvarId_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_1598_, v___y_1600_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___boxed(lean_object* v_mvarId_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0(v_mvarId_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar(lean_object* v_mvarId_1625_, lean_object* v_lctxInitIndices_1626_, uint8_t v_fromDelayed_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_MVarId_findDecl_x3f___redArg(v_mvarId_1625_, v_a_1629_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1794_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1794_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1794_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
if (lean_obj_tag(v_a_1634_) == 1)
{
lean_object* v_val_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1789_; 
lean_del_object(v___x_1636_);
v_val_1638_ = lean_ctor_get(v_a_1634_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_a_1634_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1640_ = v_a_1634_;
v_isShared_1641_ = v_isSharedCheck_1789_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_val_1638_);
lean_dec(v_a_1634_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1789_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___x_1655_; lean_object* v_a_1656_; lean_object* v_delayedExpl_1657_; 
v___x_1655_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_1625_, v_a_1629_);
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref(v___x_1655_);
v_delayedExpl_1657_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__0));
if (lean_obj_tag(v_a_1656_) == 1)
{
lean_object* v_val_1658_; lean_object* v_mvarIdPending_1659_; lean_object* v___x_1660_; 
lean_del_object(v___x_1640_);
lean_dec(v_val_1638_);
lean_dec(v_mvarId_1625_);
v_val_1658_ = lean_ctor_get(v_a_1656_, 0);
lean_inc(v_val_1658_);
lean_dec_ref_known(v_a_1656_, 1);
v_mvarIdPending_1659_ = lean_ctor_get(v_val_1658_, 1);
lean_inc(v_mvarIdPending_1659_);
lean_dec(v_val_1658_);
v___x_1660_ = l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(v_mvarIdPending_1659_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1662_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v___x_1662_ = l_Lean_MVarId_findDecl_x3f___redArg(v_a_1661_, v_a_1629_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1702_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1702_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1702_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
if (lean_obj_tag(v_a_1663_) == 1)
{
lean_object* v_val_1667_; lean_object* v_msg_1669_; lean_object* v___y_1670_; lean_object* v_a_1682_; lean_object* v___x_1694_; 
lean_del_object(v___x_1665_);
v_val_1667_ = lean_ctor_get(v_a_1663_, 0);
lean_inc(v_val_1667_);
lean_dec_ref_known(v_a_1663_, 1);
lean_inc(v_a_1661_);
v___x_1694_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(v_a_1661_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1696_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
v___x_1696_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v_a_1695_);
lean_dec(v_a_1695_);
v_a_1682_ = v___x_1696_;
goto v___jp_1681_;
}
else
{
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1697_; 
v_a_1697_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1694_, 1);
v_a_1682_ = v_a_1697_;
goto v___jp_1681_;
}
else
{
lean_dec(v_val_1667_);
lean_dec(v_a_1661_);
return v___x_1694_;
}
}
v___jp_1668_:
{
lean_object* v___x_1671_; lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1680_; 
v___x_1671_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_val_1667_, v___y_1670_);
lean_dec(v_val_1667_);
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = lean_string_append(v_msg_1669_, v_a_1672_);
lean_dec(v_a_1672_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1676_);
v___x_1678_ = v___x_1674_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
v___jp_1681_:
{
lean_object* v___x_1683_; lean_object* v_a_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1683_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_a_1661_, v_a_1629_);
lean_dec(v_a_1661_);
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1683_);
v___x_1685_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1));
v___x_1686_ = lean_string_append(v___x_1685_, v_a_1682_);
lean_dec_ref(v_a_1682_);
v___x_1687_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2));
v___x_1688_ = lean_string_append(v___x_1686_, v___x_1687_);
v___x_1689_ = lean_string_append(v___x_1688_, v_delayedExpl_1657_);
if (lean_obj_tag(v_a_1684_) == 1)
{
lean_object* v_val_1690_; lean_object* v___x_1691_; 
v_val_1690_ = lean_ctor_get(v_a_1684_, 0);
lean_inc(v_val_1690_);
lean_dec_ref_known(v_a_1684_, 1);
v___x_1691_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_val_1690_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1693_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
v___x_1693_ = lean_string_append(v___x_1689_, v_a_1692_);
lean_dec(v_a_1692_);
v_msg_1669_ = v___x_1693_;
v___y_1670_ = v_a_1628_;
goto v___jp_1668_;
}
else
{
lean_dec_ref(v___x_1689_);
lean_dec(v_val_1667_);
return v___x_1691_;
}
}
else
{
lean_dec(v_a_1684_);
v_msg_1669_ = v___x_1689_;
v___y_1670_ = v_a_1628_;
goto v___jp_1668_;
}
}
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
lean_dec(v_a_1663_);
lean_dec(v_a_1661_);
v___x_1698_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3));
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1698_);
v___x_1700_ = v___x_1665_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_a_1661_);
v_a_1703_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1662_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1662_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
v_a_1711_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1660_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1660_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_object* v_userName_1719_; lean_object* v_lctx_1720_; uint8_t v_kind_1721_; lean_object* v_msg_1723_; lean_object* v___y_1724_; lean_object* v_msg_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; uint8_t v___y_1769_; lean_object* v_msg_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; 
lean_dec(v_a_1656_);
v_userName_1719_ = lean_ctor_get(v_val_1638_, 0);
v_lctx_1720_ = lean_ctor_get(v_val_1638_, 1);
v_kind_1721_ = lean_ctor_get_uint8(v_val_1638_, sizeof(void*)*7);
switch(v_kind_1721_)
{
case 0:
{
lean_object* v___x_1786_; 
v___x_1786_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__9));
v_msg_1773_ = v___x_1786_;
v___y_1774_ = v_a_1628_;
v___y_1775_ = v_a_1629_;
v___y_1776_ = v_a_1630_;
v___y_1777_ = v_a_1631_;
goto v___jp_1772_;
}
case 1:
{
lean_object* v___x_1787_; 
v___x_1787_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__10));
v_msg_1773_ = v___x_1787_;
v___y_1774_ = v_a_1628_;
v___y_1775_ = v_a_1629_;
v___y_1776_ = v_a_1630_;
v___y_1777_ = v_a_1631_;
goto v___jp_1772_;
}
default: 
{
lean_object* v___x_1788_; 
v___x_1788_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__11));
v_msg_1773_ = v___x_1788_;
v___y_1774_ = v_a_1628_;
v___y_1775_ = v_a_1629_;
v___y_1776_ = v_a_1630_;
v___y_1777_ = v_a_1631_;
goto v___jp_1772_;
}
}
v___jp_1722_:
{
if (v_fromDelayed_1627_ == 0)
{
v___y_1643_ = v_msg_1723_;
v___y_1644_ = v___y_1724_;
goto v___jp_1642_;
}
else
{
lean_object* v_lctx_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
v_lctx_1725_ = lean_ctor_get(v___y_1724_, 2);
v___x_1726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0));
v___x_1727_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_1720_, v_lctx_1725_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1737_; 
v___x_1728_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_val_1638_, v___y_1724_);
lean_dec(v_val_1638_);
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = lean_string_append(v_msg_1723_, v_a_1729_);
lean_dec(v_a_1729_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1733_);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
else
{
v___y_1643_ = v_msg_1723_;
v___y_1644_ = v___y_1724_;
goto v___jp_1642_;
}
}
}
v___jp_1738_:
{
lean_object* v___x_1744_; lean_object* v_a_1745_; 
v___x_1744_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarId_1625_, v___y_1741_);
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1745_);
lean_dec_ref(v___x_1744_);
if (lean_obj_tag(v_a_1745_) == 1)
{
lean_dec(v_mvarId_1625_);
if (v_fromDelayed_1627_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec_ref_known(v_a_1745_, 1);
v___x_1746_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4));
v___x_1747_ = lean_string_append(v_msg_1739_, v___x_1746_);
v_msg_1723_ = v___x_1747_;
v___y_1724_ = v___y_1740_;
goto v___jp_1722_;
}
else
{
lean_object* v_val_1748_; lean_object* v___x_1749_; 
v_val_1748_ = lean_ctor_get(v_a_1745_, 0);
lean_inc(v_val_1748_);
lean_dec_ref_known(v_a_1745_, 1);
v___x_1749_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_val_1748_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5));
v___x_1752_ = lean_string_append(v_msg_1739_, v___x_1751_);
v___x_1753_ = lean_string_append(v___x_1752_, v_delayedExpl_1657_);
v___x_1754_ = lean_string_append(v___x_1753_, v_a_1750_);
lean_dec(v_a_1750_);
v_msg_1723_ = v___x_1754_;
v___y_1724_ = v___y_1740_;
goto v___jp_1722_;
}
else
{
lean_dec_ref(v_msg_1739_);
lean_dec(v_val_1638_);
return v___x_1749_;
}
}
}
else
{
lean_object* v___x_1755_; lean_object* v_a_1756_; uint8_t v___x_1757_; 
lean_dec(v_a_1745_);
v___x_1755_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_1625_, v___y_1741_);
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = lean_unbox(v_a_1756_);
lean_dec(v_a_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6));
v___x_1759_ = lean_string_append(v_msg_1739_, v___x_1758_);
v_msg_1723_ = v___x_1759_;
v___y_1724_ = v___y_1740_;
goto v___jp_1722_;
}
else
{
if (v_fromDelayed_1627_ == 0)
{
v_msg_1723_ = v_msg_1739_;
v___y_1724_ = v___y_1740_;
goto v___jp_1722_;
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7));
v___x_1761_ = lean_string_append(v_msg_1739_, v___x_1760_);
v___x_1762_ = lean_string_append(v___x_1761_, v_delayedExpl_1657_);
v_msg_1723_ = v___x_1762_;
v___y_1724_ = v___y_1740_;
goto v___jp_1722_;
}
}
}
}
v___jp_1763_:
{
if (v___y_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__8));
lean_inc_ref(v___y_1764_);
v___x_1771_ = lean_string_append(v___y_1764_, v___x_1770_);
v_msg_1739_ = v___x_1771_;
v___y_1740_ = v___y_1768_;
v___y_1741_ = v___y_1766_;
v___y_1742_ = v___y_1765_;
v___y_1743_ = v___y_1767_;
goto v___jp_1738_;
}
else
{
lean_inc_ref(v___y_1764_);
v_msg_1739_ = v___y_1764_;
v___y_1740_ = v___y_1768_;
v___y_1741_ = v___y_1766_;
v___y_1742_ = v___y_1765_;
v___y_1743_ = v___y_1767_;
goto v___jp_1738_;
}
}
v___jp_1772_:
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = lean_st_ref_get(v___y_1775_);
v___x_1779_ = l_Lean_Name_isAnonymous(v_userName_1719_);
if (v___x_1779_ == 0)
{
lean_object* v_mctx_1780_; lean_object* v___x_1782_; 
v_mctx_1780_ = lean_ctor_get(v___x_1778_, 0);
lean_inc_ref(v_mctx_1780_);
lean_dec(v___x_1778_);
lean_inc(v_mvarId_1625_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v_mvarId_1625_);
v___x_1782_ = v___x_1640_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_mvarId_1625_);
v___x_1782_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = l_Lean_MetavarContext_findUserName_x3f(v_mctx_1780_, v_userName_1719_);
lean_dec_ref(v_mctx_1780_);
v___x_1784_ = l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(v___x_1782_, v___x_1783_);
lean_dec(v___x_1783_);
lean_dec_ref(v___x_1782_);
v___y_1764_ = v_msg_1773_;
v___y_1765_ = v___y_1776_;
v___y_1766_ = v___y_1775_;
v___y_1767_ = v___y_1777_;
v___y_1768_ = v___y_1774_;
v___y_1769_ = v___x_1784_;
goto v___jp_1763_;
}
}
else
{
lean_dec(v___x_1778_);
lean_del_object(v___x_1640_);
v___y_1764_ = v_msg_1773_;
v___y_1765_ = v___y_1776_;
v___y_1766_ = v___y_1775_;
v___y_1767_ = v___y_1777_;
v___y_1768_ = v___y_1774_;
v___y_1769_ = v___x_1779_;
goto v___jp_1763_;
}
}
}
v___jp_1642_:
{
lean_object* v___x_1645_; lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1654_; 
v___x_1645_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(v_lctxInitIndices_1626_, v_val_1638_, v___y_1644_);
lean_dec(v_val_1638_);
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = lean_string_append(v___y_1643_, v_a_1646_);
lean_dec(v_a_1646_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1650_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1792_; 
lean_dec(v_a_1634_);
lean_dec(v_mvarId_1625_);
v___x_1790_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__12));
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1790_);
v___x_1792_ = v___x_1636_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_mvarId_1625_);
v_a_1795_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1633_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1633_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___boxed(lean_object* v_mvarId_1803_, lean_object* v_lctxInitIndices_1804_, lean_object* v_fromDelayed_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
uint8_t v_fromDelayed_boxed_1811_; lean_object* v_res_1812_; 
v_fromDelayed_boxed_1811_ = lean_unbox(v_fromDelayed_1805_);
v_res_1812_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar(v_mvarId_1803_, v_lctxInitIndices_1804_, v_fromDelayed_boxed_1811_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_lctxInitIndices_1804_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0(lean_object* v_mvarId_1813_, lean_object* v_lctxInitIndices_1814_, uint8_t v_fromDelayed_1815_, lean_object* v_ppCtx_1816_){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = lean_box(v_fromDelayed_1815_);
v___x_1819_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___boxed), 8, 3);
lean_closure_set(v___x_1819_, 0, v_mvarId_1813_);
lean_closure_set(v___x_1819_, 1, v_lctxInitIndices_1814_);
lean_closure_set(v___x_1819_, 2, v___x_1818_);
v___x_1820_ = l_Lean_PPContext_runMetaM___redArg(v_ppCtx_1816_, v___x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0___boxed(lean_object* v_mvarId_1821_, lean_object* v_lctxInitIndices_1822_, lean_object* v_fromDelayed_1823_, lean_object* v_ppCtx_1824_, lean_object* v___y_1825_){
_start:
{
uint8_t v_fromDelayed_boxed_1826_; lean_object* v_res_1827_; 
v_fromDelayed_boxed_1826_ = lean_unbox(v_fromDelayed_1823_);
v_res_1827_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0(v_mvarId_1821_, v_lctxInitIndices_1822_, v_fromDelayed_boxed_1826_, v_ppCtx_1824_);
lean_dec_ref(v_ppCtx_1824_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(lean_object* v_mvarId_1828_, uint8_t v_fromDelayed_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v_lctxInitIndices_1832_; lean_object* v___x_1833_; lean_object* v___f_1834_; lean_object* v___x_1835_; 
v_lctxInitIndices_1832_ = lean_ctor_get(v_a_1830_, 5);
v___x_1833_ = lean_box(v_fromDelayed_1829_);
lean_inc(v_lctxInitIndices_1832_);
v___f_1834_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1834_, 0, v_mvarId_1828_);
lean_closure_set(v___f_1834_, 1, v_lctxInitIndices_1832_);
lean_closure_set(v___f_1834_, 2, v___x_1833_);
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___f_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___boxed(lean_object* v_mvarId_1836_, lean_object* v_fromDelayed_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
uint8_t v_fromDelayed_boxed_1840_; lean_object* v_res_1841_; 
v_fromDelayed_boxed_1840_ = lean_unbox(v_fromDelayed_1837_);
v_res_1841_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(v_mvarId_1836_, v_fromDelayed_boxed_1840_, v_a_1838_);
lean_dec_ref(v_a_1838_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar(lean_object* v_mvarId_1842_, uint8_t v_fromDelayed_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(v_mvarId_1842_, v_fromDelayed_1843_, v_a_1844_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___boxed(lean_object* v_mvarId_1852_, lean_object* v_fromDelayed_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
uint8_t v_fromDelayed_boxed_1861_; lean_object* v_res_1862_; 
v_fromDelayed_boxed_1861_ = lean_unbox(v_fromDelayed_1853_);
v_res_1862_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar(v_mvarId_1852_, v_fromDelayed_boxed_1861_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
return v_res_1862_;
}
}
lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ErrorUtils(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_Metavariable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ErrorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_PrettyPrinter_Delaborator_Metavariable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_PrettyPrinter_Delaborator_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_ErrorUtils(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Delaborator_Metavariable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ErrorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Metavariable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_PrettyPrinter_Delaborator_Metavariable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_PrettyPrinter_Delaborator_Metavariable(builtin);
}
#ifdef __cplusplus
}
#endif
