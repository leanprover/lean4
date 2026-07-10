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
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_hasValue(lean_object*, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "\n\nThis metavariable has been assigned, but it appears here via a *delayed assignment*. "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "\n\nThis metavariable has been assigned."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "\n\nThis metavariable appears here via a *delayed assignment*. "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "\n\nThis metavariable cannot be assigned due to the current metavariable context depth."};
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(lean_object* v_a_372_, lean_object* v_x_373_){
_start:
{
if (lean_obj_tag(v_x_373_) == 0)
{
uint8_t v___x_374_; 
v___x_374_ = 0;
return v___x_374_;
}
else
{
lean_object* v_key_375_; lean_object* v_tail_376_; uint8_t v___x_377_; 
v_key_375_ = lean_ctor_get(v_x_373_, 0);
v_tail_376_ = lean_ctor_get(v_x_373_, 2);
v___x_377_ = l_Lean_instBEqFVarId_beq(v_key_375_, v_a_372_);
if (v___x_377_ == 0)
{
v_x_373_ = v_tail_376_;
goto _start;
}
else
{
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_a_379_, lean_object* v_x_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_a_379_, v_x_380_);
lean_dec(v_x_380_);
lean_dec(v_a_379_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(lean_object* v_m_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_buckets_385_; lean_object* v___x_386_; uint64_t v___x_387_; uint64_t v___x_388_; uint64_t v___x_389_; uint64_t v_fold_390_; uint64_t v___x_391_; uint64_t v___x_392_; uint64_t v___x_393_; size_t v___x_394_; size_t v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v_buckets_385_ = lean_ctor_get(v_m_383_, 1);
v___x_386_ = lean_array_get_size(v_buckets_385_);
v___x_387_ = l_Lean_instHashableFVarId_hash(v_a_384_);
v___x_388_ = 32ULL;
v___x_389_ = lean_uint64_shift_right(v___x_387_, v___x_388_);
v_fold_390_ = lean_uint64_xor(v___x_387_, v___x_389_);
v___x_391_ = 16ULL;
v___x_392_ = lean_uint64_shift_right(v_fold_390_, v___x_391_);
v___x_393_ = lean_uint64_xor(v_fold_390_, v___x_392_);
v___x_394_ = lean_uint64_to_usize(v___x_393_);
v___x_395_ = lean_usize_of_nat(v___x_386_);
v___x_396_ = ((size_t)1ULL);
v___x_397_ = lean_usize_sub(v___x_395_, v___x_396_);
v___x_398_ = lean_usize_land(v___x_394_, v___x_397_);
v___x_399_ = lean_array_uget_borrowed(v_buckets_385_, v___x_398_);
v___x_400_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_a_384_, v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg___boxed(lean_object* v_m_401_, lean_object* v_a_402_){
_start:
{
uint8_t v_res_403_; lean_object* v_r_404_; 
v_res_403_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_m_401_, v_a_402_);
lean_dec(v_a_402_);
lean_dec_ref(v_m_401_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_405_, lean_object* v_x_406_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
return v_x_405_;
}
else
{
lean_object* v_key_407_; lean_object* v_value_408_; lean_object* v_tail_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_432_; 
v_key_407_ = lean_ctor_get(v_x_406_, 0);
v_value_408_ = lean_ctor_get(v_x_406_, 1);
v_tail_409_ = lean_ctor_get(v_x_406_, 2);
v_isSharedCheck_432_ = !lean_is_exclusive(v_x_406_);
if (v_isSharedCheck_432_ == 0)
{
v___x_411_ = v_x_406_;
v_isShared_412_ = v_isSharedCheck_432_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_tail_409_);
lean_inc(v_value_408_);
lean_inc(v_key_407_);
lean_dec(v_x_406_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_432_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v_fold_417_; uint64_t v___x_418_; uint64_t v___x_419_; uint64_t v___x_420_; size_t v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; size_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_413_ = lean_array_get_size(v_x_405_);
v___x_414_ = l_Lean_instHashableFVarId_hash(v_key_407_);
v___x_415_ = 32ULL;
v___x_416_ = lean_uint64_shift_right(v___x_414_, v___x_415_);
v_fold_417_ = lean_uint64_xor(v___x_414_, v___x_416_);
v___x_418_ = 16ULL;
v___x_419_ = lean_uint64_shift_right(v_fold_417_, v___x_418_);
v___x_420_ = lean_uint64_xor(v_fold_417_, v___x_419_);
v___x_421_ = lean_uint64_to_usize(v___x_420_);
v___x_422_ = lean_usize_of_nat(v___x_413_);
v___x_423_ = ((size_t)1ULL);
v___x_424_ = lean_usize_sub(v___x_422_, v___x_423_);
v___x_425_ = lean_usize_land(v___x_421_, v___x_424_);
v___x_426_ = lean_array_uget_borrowed(v_x_405_, v___x_425_);
lean_inc(v___x_426_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 2, v___x_426_);
v___x_428_ = v___x_411_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_key_407_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_value_408_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v___x_426_);
v___x_428_ = v_reuseFailAlloc_431_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; 
v___x_429_ = lean_array_uset(v_x_405_, v___x_425_, v___x_428_);
v_x_405_ = v___x_429_;
v_x_406_ = v_tail_409_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3___redArg(lean_object* v_i_433_, lean_object* v_source_434_, lean_object* v_target_435_){
_start:
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_array_get_size(v_source_434_);
v___x_437_ = lean_nat_dec_lt(v_i_433_, v___x_436_);
if (v___x_437_ == 0)
{
lean_dec_ref(v_source_434_);
lean_dec(v_i_433_);
return v_target_435_;
}
else
{
lean_object* v_es_438_; lean_object* v___x_439_; lean_object* v_source_440_; lean_object* v_target_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_es_438_ = lean_array_fget(v_source_434_, v_i_433_);
v___x_439_ = lean_box(0);
v_source_440_ = lean_array_fset(v_source_434_, v_i_433_, v___x_439_);
v_target_441_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5___redArg(v_target_435_, v_es_438_);
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_add(v_i_433_, v___x_442_);
lean_dec(v_i_433_);
v_i_433_ = v___x_443_;
v_source_434_ = v_source_440_;
v_target_435_ = v_target_441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(lean_object* v_data_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v_nbuckets_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_446_ = lean_array_get_size(v_data_445_);
v___x_447_ = lean_unsigned_to_nat(2u);
v_nbuckets_448_ = lean_nat_mul(v___x_446_, v___x_447_);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_box(0);
v___x_451_ = lean_mk_array(v_nbuckets_448_, v___x_450_);
v___x_452_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3___redArg(v___x_449_, v_data_445_, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(lean_object* v_m_453_, lean_object* v_a_454_, lean_object* v_b_455_){
_start:
{
lean_object* v_size_456_; lean_object* v_buckets_457_; lean_object* v___x_458_; uint64_t v___x_459_; uint64_t v___x_460_; uint64_t v___x_461_; uint64_t v_fold_462_; uint64_t v___x_463_; uint64_t v___x_464_; uint64_t v___x_465_; size_t v___x_466_; size_t v___x_467_; size_t v___x_468_; size_t v___x_469_; size_t v___x_470_; lean_object* v_bkt_471_; uint8_t v___x_472_; 
v_size_456_ = lean_ctor_get(v_m_453_, 0);
v_buckets_457_ = lean_ctor_get(v_m_453_, 1);
v___x_458_ = lean_array_get_size(v_buckets_457_);
v___x_459_ = l_Lean_instHashableFVarId_hash(v_a_454_);
v___x_460_ = 32ULL;
v___x_461_ = lean_uint64_shift_right(v___x_459_, v___x_460_);
v_fold_462_ = lean_uint64_xor(v___x_459_, v___x_461_);
v___x_463_ = 16ULL;
v___x_464_ = lean_uint64_shift_right(v_fold_462_, v___x_463_);
v___x_465_ = lean_uint64_xor(v_fold_462_, v___x_464_);
v___x_466_ = lean_uint64_to_usize(v___x_465_);
v___x_467_ = lean_usize_of_nat(v___x_458_);
v___x_468_ = ((size_t)1ULL);
v___x_469_ = lean_usize_sub(v___x_467_, v___x_468_);
v___x_470_ = lean_usize_land(v___x_466_, v___x_469_);
v_bkt_471_ = lean_array_uget_borrowed(v_buckets_457_, v___x_470_);
v___x_472_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_a_454_, v_bkt_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_493_; 
lean_inc_ref(v_buckets_457_);
lean_inc(v_size_456_);
v_isSharedCheck_493_ = !lean_is_exclusive(v_m_453_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; lean_object* v_unused_495_; 
v_unused_494_ = lean_ctor_get(v_m_453_, 1);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_m_453_, 0);
lean_dec(v_unused_495_);
v___x_474_ = v_m_453_;
v_isShared_475_ = v_isSharedCheck_493_;
goto v_resetjp_473_;
}
else
{
lean_dec(v_m_453_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_493_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v_size_x27_477_; lean_object* v___x_478_; lean_object* v_buckets_x27_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_476_ = lean_unsigned_to_nat(1u);
v_size_x27_477_ = lean_nat_add(v_size_456_, v___x_476_);
lean_dec(v_size_456_);
lean_inc(v_bkt_471_);
v___x_478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_478_, 0, v_a_454_);
lean_ctor_set(v___x_478_, 1, v_b_455_);
lean_ctor_set(v___x_478_, 2, v_bkt_471_);
v_buckets_x27_479_ = lean_array_uset(v_buckets_457_, v___x_470_, v___x_478_);
v___x_480_ = lean_unsigned_to_nat(4u);
v___x_481_ = lean_nat_mul(v_size_x27_477_, v___x_480_);
v___x_482_ = lean_unsigned_to_nat(3u);
v___x_483_ = lean_nat_div(v___x_481_, v___x_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_array_get_size(v_buckets_x27_479_);
v___x_485_ = lean_nat_dec_le(v___x_483_, v___x_484_);
lean_dec(v___x_483_);
if (v___x_485_ == 0)
{
lean_object* v_val_486_; lean_object* v___x_488_; 
v_val_486_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(v_buckets_x27_479_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v_val_486_);
lean_ctor_set(v___x_474_, 0, v_size_x27_477_);
v___x_488_ = v___x_474_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_size_x27_477_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_val_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
else
{
lean_object* v___x_491_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v_buckets_x27_479_);
lean_ctor_set(v___x_474_, 0, v_size_x27_477_);
v___x_491_ = v___x_474_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_size_x27_477_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_buckets_x27_479_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
else
{
lean_dec(v_b_455_);
lean_dec(v_a_454_);
return v_m_453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(lean_object* v_val_499_, lean_object* v_as_500_, size_t v_sz_501_, size_t v_i_502_, lean_object* v_b_503_){
_start:
{
lean_object* v_a_506_; uint8_t v___x_510_; 
v___x_510_ = lean_usize_dec_lt(v_i_502_, v_sz_501_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec_ref(v_val_499_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v_b_503_);
return v___x_511_;
}
else
{
lean_object* v_snd_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_602_; 
v_snd_512_ = lean_ctor_get(v_b_503_, 1);
v_isSharedCheck_602_ = !lean_is_exclusive(v_b_503_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v_b_503_, 0);
lean_dec(v_unused_603_);
v___x_514_ = v_b_503_;
v_isShared_515_ = v_isSharedCheck_602_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_snd_512_);
lean_dec(v_b_503_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_602_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_snd_516_; lean_object* v_fst_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_601_; 
v_snd_516_ = lean_ctor_get(v_snd_512_, 1);
v_fst_517_ = lean_ctor_get(v_snd_512_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v_snd_512_);
if (v_isSharedCheck_601_ == 0)
{
v___x_519_ = v_snd_512_;
v_isShared_520_ = v_isSharedCheck_601_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_snd_516_);
lean_inc(v_fst_517_);
lean_dec(v_snd_512_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_601_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_array_521_; lean_object* v_start_522_; lean_object* v_stop_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v_array_521_ = lean_ctor_get(v_snd_516_, 0);
v_start_522_ = lean_ctor_get(v_snd_516_, 1);
v_stop_523_ = lean_ctor_get(v_snd_516_, 2);
v___x_524_ = lean_box(0);
v___x_525_ = lean_nat_dec_lt(v_start_522_, v_stop_523_);
if (v___x_525_ == 0)
{
lean_object* v___x_527_; 
lean_dec_ref(v_val_499_);
if (v_isShared_520_ == 0)
{
v___x_527_ = v___x_519_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_fst_517_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_snd_516_);
v___x_527_ = v_reuseFailAlloc_532_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_529_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_527_);
lean_ctor_set(v___x_514_, 0, v___x_524_);
v___x_529_ = v___x_514_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v___x_527_);
v___x_529_ = v_reuseFailAlloc_531_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; 
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
}
else
{
lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_597_; 
lean_inc(v_stop_523_);
lean_inc(v_start_522_);
lean_inc_ref(v_array_521_);
v_isSharedCheck_597_ = !lean_is_exclusive(v_snd_516_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; lean_object* v_unused_599_; lean_object* v_unused_600_; 
v_unused_598_ = lean_ctor_get(v_snd_516_, 2);
lean_dec(v_unused_598_);
v_unused_599_ = lean_ctor_get(v_snd_516_, 1);
lean_dec(v_unused_599_);
v_unused_600_ = lean_ctor_get(v_snd_516_, 0);
lean_dec(v_unused_600_);
v___x_534_ = v_snd_516_;
v_isShared_535_ = v_isSharedCheck_597_;
goto v_resetjp_533_;
}
else
{
lean_dec(v_snd_516_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_597_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_lctx_536_; lean_object* v___x_537_; lean_object* v_a_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v_lctx_536_ = lean_ctor_get(v_val_499_, 1);
v___x_537_ = lean_array_fget(v_array_521_, v_start_522_);
v_a_538_ = lean_array_uget_borrowed(v_as_500_, v_i_502_);
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_add(v_start_522_, v___x_539_);
lean_dec(v_start_522_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v___x_540_);
v___x_542_ = v___x_534_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_array_521_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_stop_523_);
v___x_542_ = v_reuseFailAlloc_596_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = l_Lean_Expr_fvarId_x21(v_a_538_);
lean_inc_ref(v_lctx_536_);
v___x_544_ = lean_local_ctx_find(v_lctx_536_, v___x_543_);
if (lean_obj_tag(v___x_544_) == 1)
{
lean_object* v_val_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_587_; 
v_val_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_587_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_587_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_val_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_587_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
uint8_t v___x_549_; uint8_t v___x_550_; 
v___x_549_ = 0;
v___x_550_ = l_Lean_LocalDecl_hasValue(v_val_545_, v___x_549_);
lean_dec(v_val_545_);
if (v___x_550_ == 0)
{
if (lean_obj_tag(v___x_537_) == 1)
{
lean_object* v_fvarId_551_; uint8_t v___x_552_; 
v_fvarId_551_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_fvarId_551_);
lean_dec_ref_known(v___x_537_, 1);
v___x_552_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_fst_517_, v_fvarId_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
lean_del_object(v___x_547_);
v___x_553_ = lean_box(0);
v___x_554_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v_fst_517_, v_fvarId_551_, v___x_553_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v___x_542_);
lean_ctor_set(v___x_519_, 0, v___x_554_);
v___x_556_ = v___x_519_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_542_);
v___x_556_ = v_reuseFailAlloc_560_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_556_);
lean_ctor_set(v___x_514_, 0, v___x_524_);
v___x_558_ = v___x_514_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
v_a_506_ = v___x_558_;
goto v___jp_505_;
}
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_563_; 
lean_dec(v_fvarId_551_);
lean_dec_ref(v_val_499_);
v___x_561_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0));
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v___x_542_);
v___x_563_ = v___x_519_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_fst_517_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v___x_542_);
v___x_563_ = v_reuseFailAlloc_570_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_565_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_563_);
lean_ctor_set(v___x_514_, 0, v___x_561_);
v___x_565_ = v___x_514_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v___x_563_);
v___x_565_ = v_reuseFailAlloc_569_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_567_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 0);
lean_ctor_set(v___x_547_, 0, v___x_565_);
v___x_567_ = v___x_547_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_573_; 
lean_dec(v___x_537_);
lean_dec_ref(v_val_499_);
v___x_571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0));
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v___x_542_);
v___x_573_ = v___x_519_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_fst_517_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_542_);
v___x_573_ = v_reuseFailAlloc_580_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_575_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_573_);
lean_ctor_set(v___x_514_, 0, v___x_571_);
v___x_575_ = v___x_514_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___x_573_);
v___x_575_ = v_reuseFailAlloc_579_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_577_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 0);
lean_ctor_set(v___x_547_, 0, v___x_575_);
v___x_577_ = v___x_547_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
else
{
lean_object* v___x_582_; 
lean_del_object(v___x_547_);
lean_dec(v___x_537_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v___x_542_);
v___x_582_ = v___x_519_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_fst_517_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v___x_542_);
v___x_582_ = v_reuseFailAlloc_586_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_584_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_582_);
lean_ctor_set(v___x_514_, 0, v___x_524_);
v___x_584_ = v___x_514_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
v_a_506_ = v___x_584_;
goto v___jp_505_;
}
}
}
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_590_; 
lean_dec(v___x_544_);
lean_dec(v___x_537_);
lean_dec_ref(v_val_499_);
v___x_588_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0));
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v___x_542_);
v___x_590_ = v___x_519_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_fst_517_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_542_);
v___x_590_ = v_reuseFailAlloc_595_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_590_);
lean_ctor_set(v___x_514_, 0, v___x_588_);
v___x_592_ = v___x_514_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___x_590_);
v___x_592_ = v_reuseFailAlloc_594_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; 
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
}
}
}
}
}
}
}
v___jp_505_:
{
size_t v___x_507_; size_t v___x_508_; 
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_add(v_i_502_, v___x_507_);
v_i_502_ = v___x_508_;
v_b_503_ = v_a_506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___boxed(lean_object* v_val_604_, lean_object* v_as_605_, lean_object* v_sz_606_, lean_object* v_i_607_, lean_object* v_b_608_, lean_object* v___y_609_){
_start:
{
size_t v_sz_boxed_610_; size_t v_i_boxed_611_; lean_object* v_res_612_; 
v_sz_boxed_610_ = lean_unbox_usize(v_sz_606_);
lean_dec(v_sz_606_);
v_i_boxed_611_ = lean_unbox_usize(v_i_607_);
lean_dec(v_i_607_);
v_res_612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_val_604_, v_as_605_, v_sz_boxed_610_, v_i_boxed_611_, v_b_608_);
lean_dec_ref(v_as_605_);
return v_res_612_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0(void){
_start:
{
lean_object* v___x_613_; lean_object* v_dummy_614_; 
v___x_613_ = lean_box(0);
v_dummy_614_ = l_Lean_Expr_sort___override(v___x_613_);
return v_dummy_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(lean_object* v_e_615_, lean_object* v_decl_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_fvars_622_; lean_object* v_mvarIdPending_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_691_; 
v_fvars_622_ = lean_ctor_get(v_decl_616_, 0);
v_mvarIdPending_623_ = lean_ctor_get(v_decl_616_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v_decl_616_);
if (v_isSharedCheck_691_ == 0)
{
v___x_625_ = v_decl_616_;
v_isShared_626_ = v_isSharedCheck_691_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_mvarIdPending_623_);
lean_inc(v_fvars_622_);
lean_dec(v_decl_616_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_691_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = l_Lean_Expr_getAppNumArgs(v_e_615_);
v___x_628_ = lean_array_get_size(v_fvars_622_);
v___x_629_ = lean_nat_dec_eq(v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec(v___x_627_);
lean_del_object(v___x_625_);
lean_dec(v_mvarIdPending_623_);
lean_dec_ref(v_fvars_622_);
lean_dec_ref(v_e_615_);
v___x_630_ = lean_box(v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
else
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_MVarId_findDecl_x3f___redArg(v_mvarIdPending_623_, v_a_618_);
lean_dec(v_mvarIdPending_623_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_682_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_682_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_682_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_682_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
if (lean_obj_tag(v_a_633_) == 1)
{
lean_object* v_val_637_; lean_object* v___x_638_; lean_object* v_dummy_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
lean_del_object(v___x_635_);
v_val_637_ = lean_ctor_get(v_a_633_, 0);
lean_inc(v_val_637_);
lean_dec_ref_known(v_a_633_, 1);
v___x_638_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v_dummy_639_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0, &l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0);
lean_inc(v___x_627_);
v___x_640_ = lean_mk_array(v___x_627_, v_dummy_639_);
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_nat_sub(v___x_627_, v___x_641_);
lean_dec(v___x_627_);
v___x_643_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_615_, v___x_640_, v___x_642_);
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = lean_array_get_size(v___x_643_);
v___x_646_ = l_Array_toSubarray___redArg(v___x_643_, v___x_644_, v___x_645_);
v___x_647_ = lean_box(0);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_646_);
lean_ctor_set(v___x_625_, 0, v___x_638_);
v___x_649_ = v___x_625_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_646_);
v___x_649_ = v_reuseFailAlloc_676_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; size_t v_sz_651_; size_t v___x_652_; lean_object* v___x_653_; 
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_647_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v_sz_651_ = lean_array_size(v_fvars_622_);
v___x_652_ = ((size_t)0ULL);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_val_637_, v_fvars_622_, v_sz_651_, v___x_652_, v___x_650_);
lean_dec_ref(v_fvars_622_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_667_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_667_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_667_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_667_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_fst_658_; 
v_fst_658_ = lean_ctor_get(v_a_654_, 0);
lean_inc(v_fst_658_);
lean_dec(v_a_654_);
if (lean_obj_tag(v_fst_658_) == 0)
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_box(v___x_629_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_659_);
v___x_661_ = v___x_656_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
lean_object* v_val_663_; lean_object* v___x_665_; 
v_val_663_ = lean_ctor_get(v_fst_658_, 0);
lean_inc(v_val_663_);
lean_dec_ref_known(v_fst_658_, 1);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v_val_663_);
v___x_665_ = v___x_656_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_val_663_);
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
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
v_a_668_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_653_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_653_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
else
{
uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
lean_dec(v_a_633_);
lean_dec(v___x_627_);
lean_del_object(v___x_625_);
lean_dec_ref(v_fvars_622_);
lean_dec_ref(v_e_615_);
v___x_677_ = 0;
v___x_678_ = lean_box(v___x_677_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_678_);
v___x_680_ = v___x_635_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v___x_627_);
lean_del_object(v___x_625_);
lean_dec_ref(v_fvars_622_);
lean_dec_ref(v_e_615_);
v_a_683_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_632_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_632_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___boxed(lean_object* v_e_692_, lean_object* v_decl_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(v_e_692_, v_decl_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
return v_res_699_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0(lean_object* v_00_u03b2_700_, lean_object* v_m_701_, lean_object* v_a_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_m_701_, v_a_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___boxed(lean_object* v_00_u03b2_704_, lean_object* v_m_705_, lean_object* v_a_706_){
_start:
{
uint8_t v_res_707_; lean_object* v_r_708_; 
v_res_707_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0(v_00_u03b2_704_, v_m_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_m_705_);
v_r_708_ = lean_box(v_res_707_);
return v_r_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1(lean_object* v_00_u03b2_709_, lean_object* v_m_710_, lean_object* v_a_711_, lean_object* v_b_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v_m_710_, v_a_711_, v_b_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2(lean_object* v_val_714_, lean_object* v_as_715_, size_t v_sz_716_, size_t v_i_717_, lean_object* v_b_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_val_714_, v_as_715_, v_sz_716_, v_i_717_, v_b_718_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___boxed(lean_object* v_val_725_, lean_object* v_as_726_, lean_object* v_sz_727_, lean_object* v_i_728_, lean_object* v_b_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
size_t v_sz_boxed_735_; size_t v_i_boxed_736_; lean_object* v_res_737_; 
v_sz_boxed_735_ = lean_unbox_usize(v_sz_727_);
lean_dec(v_sz_727_);
v_i_boxed_736_ = lean_unbox_usize(v_i_728_);
lean_dec(v_i_728_);
v_res_737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2(v_val_725_, v_as_726_, v_sz_boxed_735_, v_i_boxed_736_, v_b_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec_ref(v_as_726_);
return v_res_737_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0(lean_object* v_00_u03b2_738_, lean_object* v_a_739_, lean_object* v_x_740_){
_start:
{
uint8_t v___x_741_; 
v___x_741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_a_739_, v_x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_742_, lean_object* v_a_743_, lean_object* v_x_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0(v_00_u03b2_742_, v_a_743_, v_x_744_);
lean_dec(v_x_744_);
lean_dec(v_a_743_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2(lean_object* v_00_u03b2_747_, lean_object* v_data_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(v_data_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_750_, lean_object* v_i_751_, lean_object* v_source_752_, lean_object* v_target_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3___redArg(v_i_751_, v_source_752_, v_target_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_755_, lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5___redArg(v_x_756_, v_x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(lean_object* v_mvarId_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; lean_object* v_mctx_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_762_ = lean_st_ref_get(v___y_760_);
v_mctx_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc_ref(v_mctx_763_);
lean_dec(v___x_762_);
v___x_764_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_763_, v_mvarId_759_);
lean_dec_ref(v_mctx_763_);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg___boxed(lean_object* v_mvarId_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarId_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec(v_mvarId_766_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0(lean_object* v_mvarId_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarId_770_, v___y_772_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___boxed(lean_object* v_mvarId_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0(v_mvarId_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v_mvarId_777_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(lean_object* v_e_784_, lean_object* v___y_785_){
_start:
{
uint8_t v___x_787_; uint8_t v___x_788_; 
v___x_787_ = l_Lean_Expr_hasMVar(v_e_784_);
v___x_788_ = lean_bool_not(v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v_mctx_790_; lean_object* v___x_791_; lean_object* v_fst_792_; lean_object* v_snd_793_; lean_object* v___x_794_; lean_object* v_cache_795_; lean_object* v_zetaDeltaFVarIds_796_; lean_object* v_postponed_797_; lean_object* v_diag_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_807_; 
v___x_789_ = lean_st_ref_get(v___y_785_);
v_mctx_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc_ref(v_mctx_790_);
lean_dec(v___x_789_);
v___x_791_ = l_Lean_instantiateMVarsCore(v_mctx_790_, v_e_784_);
v_fst_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_fst_792_);
v_snd_793_ = lean_ctor_get(v___x_791_, 1);
lean_inc(v_snd_793_);
lean_dec_ref(v___x_791_);
v___x_794_ = lean_st_ref_take(v___y_785_);
v_cache_795_ = lean_ctor_get(v___x_794_, 1);
v_zetaDeltaFVarIds_796_ = lean_ctor_get(v___x_794_, 2);
v_postponed_797_ = lean_ctor_get(v___x_794_, 3);
v_diag_798_ = lean_ctor_get(v___x_794_, 4);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v___x_794_, 0);
lean_dec(v_unused_808_);
v___x_800_ = v___x_794_;
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_diag_798_);
lean_inc(v_postponed_797_);
lean_inc(v_zetaDeltaFVarIds_796_);
lean_inc(v_cache_795_);
lean_dec(v___x_794_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v_snd_793_);
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_snd_793_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_cache_795_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_zetaDeltaFVarIds_796_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v_postponed_797_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v_diag_798_);
v___x_803_ = v_reuseFailAlloc_806_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_st_ref_set(v___y_785_, v___x_803_);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v_fst_792_);
return v___x_805_;
}
}
}
else
{
lean_object* v___x_809_; 
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v_e_784_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg___boxed(lean_object* v_e_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_e_810_, v___y_811_);
lean_dec(v___y_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1(lean_object* v_e_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_e_814_, v___y_816_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___boxed(lean_object* v_e_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1(v_e_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(lean_object* v_mvarId_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; lean_object* v_mctx_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_831_ = lean_st_ref_get(v___y_829_);
v_mctx_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc_ref(v_mctx_832_);
lean_dec(v___x_831_);
v___x_833_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_832_, v_mvarId_828_);
lean_dec_ref(v_mctx_832_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg___boxed(lean_object* v_mvarId_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec(v_mvarId_835_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2(lean_object* v_mvarId_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_839_, v___y_841_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___boxed(lean_object* v_mvarId_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2(v_mvarId_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v_mvarId_846_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(lean_object* v_mvarIdPending_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarIdPending_853_, v_a_855_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_935_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_935_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_935_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_935_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
if (lean_obj_tag(v_a_860_) == 1)
{
lean_object* v_val_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v_val_864_ = lean_ctor_get(v_a_860_, 0);
lean_inc(v_val_864_);
lean_dec_ref_known(v_a_860_, 1);
v___x_865_ = l_Lean_Expr_getAppFn_x27(v_val_864_);
v___x_866_ = l_Lean_Expr_isMVar(v___x_865_);
lean_dec_ref(v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_868_; 
lean_dec(v_val_864_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v_mvarIdPending_853_);
v___x_868_ = v___x_862_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_mvarIdPending_853_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
else
{
lean_object* v___x_870_; 
lean_del_object(v___x_862_);
v___x_870_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_val_864_, v_a_855_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_923_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_923_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_923_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_923_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Expr_consumeMData(v_a_871_);
lean_dec(v_a_871_);
if (lean_obj_tag(v___x_875_) == 2)
{
lean_object* v_mvarId_876_; lean_object* v___x_878_; 
lean_dec(v_mvarIdPending_853_);
v_mvarId_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_mvarId_876_);
lean_dec_ref_known(v___x_875_, 1);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v_mvarId_876_);
v___x_878_ = v___x_873_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_mvarId_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
else
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_Expr_getAppFn_x27(v___x_875_);
if (lean_obj_tag(v___x_880_) == 2)
{
lean_object* v_mvarId_881_; lean_object* v___x_882_; 
lean_del_object(v___x_873_);
v_mvarId_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_mvarId_881_);
lean_dec_ref_known(v___x_880_, 1);
v___x_882_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_881_, v_a_855_);
lean_dec(v_mvarId_881_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_911_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_911_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_911_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_911_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
if (lean_obj_tag(v_a_883_) == 1)
{
lean_object* v_val_887_; lean_object* v___x_888_; 
lean_del_object(v___x_885_);
v_val_887_ = lean_ctor_get(v_a_883_, 0);
lean_inc_n(v_val_887_, 2);
lean_dec_ref_known(v_a_883_, 1);
v___x_888_ = l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(v___x_875_, v_val_887_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_899_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_899_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_899_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_899_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
uint8_t v___x_893_; 
v___x_893_ = lean_unbox(v_a_889_);
lean_dec(v_a_889_);
if (v___x_893_ == 0)
{
lean_object* v___x_895_; 
lean_dec(v_val_887_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v_mvarIdPending_853_);
v___x_895_ = v___x_891_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_mvarIdPending_853_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
else
{
lean_object* v_mvarIdPending_897_; 
lean_del_object(v___x_891_);
lean_dec(v_mvarIdPending_853_);
v_mvarIdPending_897_ = lean_ctor_get(v_val_887_, 1);
lean_inc(v_mvarIdPending_897_);
lean_dec(v_val_887_);
v_mvarIdPending_853_ = v_mvarIdPending_897_;
goto _start;
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec(v_val_887_);
lean_dec(v_mvarIdPending_853_);
v_a_900_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_888_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_888_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
else
{
lean_object* v___x_909_; 
lean_dec(v_a_883_);
lean_dec_ref(v___x_875_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v_mvarIdPending_853_);
v___x_909_ = v___x_885_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_mvarIdPending_853_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v___x_875_);
lean_dec(v_mvarIdPending_853_);
v_a_912_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_882_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_882_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v___x_921_; 
lean_dec_ref(v___x_880_);
lean_dec_ref(v___x_875_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v_mvarIdPending_853_);
v___x_921_ = v___x_873_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_mvarIdPending_853_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_mvarIdPending_853_);
v_a_924_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_870_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_870_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
else
{
lean_object* v___x_933_; 
lean_dec(v_a_860_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v_mvarIdPending_853_);
v___x_933_ = v___x_862_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_mvarIdPending_853_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v_mvarIdPending_853_);
v_a_936_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_859_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_859_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending___boxed(lean_object* v_mvarIdPending_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(v_mvarIdPending_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(lean_object* v_n_952_){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___closed__0));
v___x_954_ = lean_string_append(v___x_953_, v_n_952_);
v___x_955_ = lean_string_append(v___x_954_, v___x_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___boxed(lean_object* v_n_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v_n_956_);
lean_dec_ref(v_n_956_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString_spec__0(lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
if (lean_obj_tag(v_a_958_) == 0)
{
lean_object* v___x_960_; 
v___x_960_ = l_List_reverse___redArg(v_a_959_);
return v___x_960_;
}
else
{
lean_object* v_head_961_; lean_object* v_tail_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_981_; 
v_head_961_ = lean_ctor_get(v_a_958_, 0);
v_tail_962_ = lean_ctor_get(v_a_958_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v_a_958_);
if (v_isSharedCheck_981_ == 0)
{
v___x_964_ = v_a_958_;
v_isShared_965_ = v_isSharedCheck_981_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_tail_962_);
lean_inc(v_head_961_);
lean_dec(v_a_958_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_981_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___y_967_; uint8_t v___x_972_; uint8_t v___x_973_; 
v___x_972_ = l_Lean_Name_hasMacroScopes(v_head_961_);
v___x_973_ = 1;
if (v___x_972_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = l_Lean_Name_toString(v_head_961_, v___x_973_);
v___x_975_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v___x_974_);
lean_dec_ref(v___x_974_);
v___y_967_ = v___x_975_;
goto v___jp_966_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_976_ = l_Lean_Name_eraseMacroScopes(v_head_961_);
lean_dec(v_head_961_);
v___x_977_ = l_Lean_Name_toString(v___x_976_, v___x_973_);
v___x_978_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0));
v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
v___x_980_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v___x_979_);
lean_dec_ref(v___x_979_);
v___y_967_ = v___x_980_;
goto v___jp_966_;
}
v___jp_966_:
{
lean_object* v___x_969_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v_a_959_);
lean_ctor_set(v___x_964_, 0, v___y_967_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___y_967_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_a_959_);
v___x_969_ = v_reuseFailAlloc_971_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
v_a_958_ = v_tail_962_;
v_a_959_ = v___x_969_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString(lean_object* v_ns_983_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_984_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0));
v___x_985_ = lean_box(0);
v___x_986_ = l_List_mapTR_loop___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString_spec__0(v_ns_983_, v___x_985_);
v___x_987_ = l_String_intercalate(v___x_984_, v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(lean_object* v_count_988_, lean_object* v_singular_989_, lean_object* v_plural_990_){
_start:
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_unsigned_to_nat(1u);
v___x_992_ = lean_nat_dec_eq(v_count_988_, v___x_991_);
if (v___x_992_ == 0)
{
lean_inc_ref(v_plural_990_);
return v_plural_990_;
}
else
{
lean_inc_ref(v_singular_989_);
return v_singular_989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1___boxed(lean_object* v_count_993_, lean_object* v_singular_994_, lean_object* v_plural_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v_count_993_, v_singular_994_, v_plural_995_);
lean_dec_ref(v_plural_995_);
lean_dec_ref(v_singular_994_);
lean_dec(v_count_993_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(lean_object* v___x_997_, lean_object* v_as_998_, size_t v_i_999_, size_t v_stop_1000_, lean_object* v_b_1001_){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_usize_dec_eq(v_i_999_, v_stop_1000_);
if (v___x_1002_ == 0)
{
size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_sub(v_i_999_, v___x_1003_);
v___x_1005_ = lean_array_uget_borrowed(v_as_998_, v___x_1004_);
if (lean_obj_tag(v___x_1005_) == 0)
{
v_i_999_ = v___x_1004_;
goto _start;
}
else
{
lean_object* v_val_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v_val_1007_ = lean_ctor_get(v___x_1005_, 0);
v___x_1008_ = l_Lean_LocalDecl_fvarId(v_val_1007_);
v___x_1009_ = l_Lean_LocalContext_contains(v___x_997_, v___x_1008_);
lean_dec(v___x_1008_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = l_Lean_LocalDecl_userName(v_val_1007_);
v___x_1011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v_b_1001_);
v_i_999_ = v___x_1004_;
v_b_1001_ = v___x_1011_;
goto _start;
}
else
{
v_i_999_ = v___x_1004_;
goto _start;
}
}
}
else
{
return v_b_1001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3___boxed(lean_object* v___x_1014_, lean_object* v_as_1015_, lean_object* v_i_1016_, lean_object* v_stop_1017_, lean_object* v_b_1018_){
_start:
{
size_t v_i_boxed_1019_; size_t v_stop_boxed_1020_; lean_object* v_res_1021_; 
v_i_boxed_1019_ = lean_unbox_usize(v_i_1016_);
lean_dec(v_i_1016_);
v_stop_boxed_1020_ = lean_unbox_usize(v_stop_1017_);
lean_dec(v_stop_1017_);
v_res_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_1014_, v_as_1015_, v_i_boxed_1019_, v_stop_boxed_1020_, v_b_1018_);
lean_dec_ref(v_as_1015_);
lean_dec_ref(v___x_1014_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(lean_object* v___x_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
if (lean_obj_tag(v_x_1023_) == 0)
{
lean_object* v_cs_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v_cs_1025_ = lean_ctor_get(v_x_1023_, 0);
v___x_1026_ = lean_array_get_size(v_cs_1025_);
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = lean_nat_dec_lt(v___x_1027_, v___x_1026_);
if (v___x_1028_ == 0)
{
return v_x_1024_;
}
else
{
size_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_usize_of_nat(v___x_1026_);
v___x_1030_ = ((size_t)0ULL);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(v___x_1022_, v_cs_1025_, v___x_1029_, v___x_1030_, v_x_1024_);
return v___x_1031_;
}
}
else
{
lean_object* v_vs_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_vs_1032_ = lean_ctor_get(v_x_1023_, 0);
v___x_1033_ = lean_array_get_size(v_vs_1032_);
v___x_1034_ = lean_unsigned_to_nat(0u);
v___x_1035_ = lean_nat_dec_lt(v___x_1034_, v___x_1033_);
if (v___x_1035_ == 0)
{
return v_x_1024_;
}
else
{
size_t v___x_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = lean_usize_of_nat(v___x_1033_);
v___x_1037_ = ((size_t)0ULL);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_1022_, v_vs_1032_, v___x_1036_, v___x_1037_, v_x_1024_);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(lean_object* v___x_1039_, lean_object* v_as_1040_, size_t v_i_1041_, size_t v_stop_1042_, lean_object* v_b_1043_){
_start:
{
uint8_t v___x_1044_; 
v___x_1044_ = lean_usize_dec_eq(v_i_1041_, v_stop_1042_);
if (v___x_1044_ == 0)
{
size_t v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1045_ = ((size_t)1ULL);
v___x_1046_ = lean_usize_sub(v_i_1041_, v___x_1045_);
v___x_1047_ = lean_array_uget_borrowed(v_as_1040_, v___x_1046_);
v___x_1048_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_1039_, v___x_1047_, v_b_1043_);
v_i_1041_ = v___x_1046_;
v_b_1043_ = v___x_1048_;
goto _start;
}
else
{
return v_b_1043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v___x_1050_, lean_object* v_as_1051_, lean_object* v_i_1052_, lean_object* v_stop_1053_, lean_object* v_b_1054_){
_start:
{
size_t v_i_boxed_1055_; size_t v_stop_boxed_1056_; lean_object* v_res_1057_; 
v_i_boxed_1055_ = lean_unbox_usize(v_i_1052_);
lean_dec(v_i_1052_);
v_stop_boxed_1056_ = lean_unbox_usize(v_stop_1053_);
lean_dec(v_stop_1053_);
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(v___x_1050_, v_as_1051_, v_i_boxed_1055_, v_stop_boxed_1056_, v_b_1054_);
lean_dec_ref(v_as_1051_);
lean_dec_ref(v___x_1050_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2___boxed(lean_object* v___x_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_1058_, v_x_1059_, v_x_1060_);
lean_dec_ref(v_x_1059_);
lean_dec_ref(v___x_1058_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(lean_object* v___x_1062_, lean_object* v_t_1063_, lean_object* v_init_1064_){
_start:
{
lean_object* v_root_1065_; lean_object* v_tail_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v_root_1065_ = lean_ctor_get(v_t_1063_, 0);
v_tail_1066_ = lean_ctor_get(v_t_1063_, 1);
v___x_1067_ = lean_array_get_size(v_tail_1066_);
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = lean_nat_dec_lt(v___x_1068_, v___x_1067_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; 
v___x_1070_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_1062_, v_root_1065_, v_init_1064_);
return v___x_1070_;
}
else
{
size_t v___x_1071_; size_t v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1071_ = lean_usize_of_nat(v___x_1067_);
v___x_1072_ = ((size_t)0ULL);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_1062_, v_tail_1066_, v___x_1071_, v___x_1072_, v_init_1064_);
v___x_1074_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_1062_, v_root_1065_, v___x_1073_);
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0___boxed(lean_object* v___x_1075_, lean_object* v_t_1076_, lean_object* v_init_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(v___x_1075_, v_t_1076_, v_init_1077_);
lean_dec_ref(v_t_1076_);
lean_dec_ref(v___x_1075_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(lean_object* v___x_1079_, lean_object* v_lctx_1080_, lean_object* v_init_1081_){
_start:
{
lean_object* v_decls_1082_; lean_object* v___x_1083_; 
v_decls_1082_ = lean_ctor_get(v_lctx_1080_, 1);
v___x_1083_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(v___x_1079_, v_decls_1082_, v_init_1081_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0___boxed(lean_object* v___x_1084_, lean_object* v_lctx_1085_, lean_object* v_init_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(v___x_1084_, v_lctx_1085_, v_init_1086_);
lean_dec_ref(v_lctx_1085_);
lean_dec_ref(v___x_1084_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(lean_object* v_mdecl_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_lctx_1096_; lean_object* v_lctx_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v_lctx_1096_ = lean_ctor_get(v_a_1094_, 2);
v_lctx_1097_ = lean_ctor_get(v_mdecl_1093_, 1);
v___x_1098_ = lean_box(0);
v___x_1099_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(v_lctx_1096_, v_lctx_1097_, v___x_1098_);
v___x_1100_ = l_List_isEmpty___redArg(v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1101_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__0));
v___x_1102_ = l_List_lengthTR___redArg(v___x_1099_);
v___x_1103_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__1));
v___x_1104_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__2));
v___x_1105_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v___x_1102_, v___x_1103_, v___x_1104_);
lean_dec(v___x_1102_);
v___x_1106_ = lean_string_append(v___x_1101_, v___x_1105_);
lean_dec_ref(v___x_1105_);
v___x_1107_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__3));
v___x_1108_ = lean_string_append(v___x_1106_, v___x_1107_);
v___x_1109_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString(v___x_1099_);
v___x_1110_ = lean_string_append(v___x_1108_, v___x_1109_);
lean_dec_ref(v___x_1109_);
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
return v___x_1111_;
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_dec(v___x_1099_);
v___x_1112_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4));
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___boxed(lean_object* v_mdecl_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_mdecl_1114_, v_a_1115_);
lean_dec_ref(v_a_1115_);
lean_dec_ref(v_mdecl_1114_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars(lean_object* v_mdecl_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_mdecl_1118_, v_a_1119_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___boxed(lean_object* v_mdecl_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars(v_mdecl_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec_ref(v_mdecl_1125_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(lean_object* v_lctxInitIndices_1132_, lean_object* v_mdecl_1133_, lean_object* v_as_1134_, size_t v_i_1135_, size_t v_stop_1136_, lean_object* v_b_1137_){
_start:
{
uint8_t v___x_1138_; 
v___x_1138_ = lean_usize_dec_eq(v_i_1135_, v_stop_1136_);
if (v___x_1138_ == 0)
{
size_t v___x_1139_; size_t v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = ((size_t)1ULL);
v___x_1140_ = lean_usize_sub(v_i_1135_, v___x_1139_);
v___x_1141_ = lean_array_uget_borrowed(v_as_1134_, v___x_1140_);
if (lean_obj_tag(v___x_1141_) == 0)
{
v_i_1135_ = v___x_1140_;
goto _start;
}
else
{
lean_object* v_val_1143_; uint8_t v___y_1145_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v_val_1143_ = lean_ctor_get(v___x_1141_, 0);
v___x_1150_ = l_Lean_LocalDecl_index(v_val_1143_);
v___x_1151_ = lean_nat_dec_le(v_lctxInitIndices_1132_, v___x_1150_);
lean_dec(v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v_lctx_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_lctx_1152_ = lean_ctor_get(v_mdecl_1133_, 1);
v___x_1153_ = l_Lean_LocalDecl_fvarId(v_val_1143_);
v___x_1154_ = l_Lean_LocalContext_contains(v_lctx_1152_, v___x_1153_);
lean_dec(v___x_1153_);
v___y_1145_ = v___x_1154_;
goto v___jp_1144_;
}
else
{
v___y_1145_ = v___x_1151_;
goto v___jp_1144_;
}
v___jp_1144_:
{
if (v___y_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = l_Lean_LocalDecl_userName(v_val_1143_);
v___x_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v_b_1137_);
v_i_1135_ = v___x_1140_;
v_b_1137_ = v___x_1147_;
goto _start;
}
else
{
v_i_1135_ = v___x_1140_;
goto _start;
}
}
}
}
else
{
return v_b_1137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2___boxed(lean_object* v_lctxInitIndices_1155_, lean_object* v_mdecl_1156_, lean_object* v_as_1157_, lean_object* v_i_1158_, lean_object* v_stop_1159_, lean_object* v_b_1160_){
_start:
{
size_t v_i_boxed_1161_; size_t v_stop_boxed_1162_; lean_object* v_res_1163_; 
v_i_boxed_1161_ = lean_unbox_usize(v_i_1158_);
lean_dec(v_i_1158_);
v_stop_boxed_1162_ = lean_unbox_usize(v_stop_1159_);
lean_dec(v_stop_1159_);
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(v_lctxInitIndices_1155_, v_mdecl_1156_, v_as_1157_, v_i_boxed_1161_, v_stop_boxed_1162_, v_b_1160_);
lean_dec_ref(v_as_1157_);
lean_dec_ref(v_mdecl_1156_);
lean_dec(v_lctxInitIndices_1155_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(lean_object* v_lctxInitIndices_1164_, lean_object* v_mdecl_1165_, lean_object* v_x_1166_, lean_object* v_x_1167_){
_start:
{
if (lean_obj_tag(v_x_1166_) == 0)
{
lean_object* v_cs_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v_cs_1168_ = lean_ctor_get(v_x_1166_, 0);
v___x_1169_ = lean_array_get_size(v_cs_1168_);
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_nat_dec_lt(v___x_1170_, v___x_1169_);
if (v___x_1171_ == 0)
{
return v_x_1167_;
}
else
{
size_t v___x_1172_; size_t v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = lean_usize_of_nat(v___x_1169_);
v___x_1173_ = ((size_t)0ULL);
v___x_1174_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2(v_lctxInitIndices_1164_, v_mdecl_1165_, v_cs_1168_, v___x_1172_, v___x_1173_, v_x_1167_);
return v___x_1174_;
}
}
else
{
lean_object* v_vs_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_vs_1175_ = lean_ctor_get(v_x_1166_, 0);
v___x_1176_ = lean_array_get_size(v_vs_1175_);
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = lean_nat_dec_lt(v___x_1177_, v___x_1176_);
if (v___x_1178_ == 0)
{
return v_x_1167_;
}
else
{
size_t v___x_1179_; size_t v___x_1180_; lean_object* v___x_1181_; 
v___x_1179_ = lean_usize_of_nat(v___x_1176_);
v___x_1180_ = ((size_t)0ULL);
v___x_1181_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(v_lctxInitIndices_1164_, v_mdecl_1165_, v_vs_1175_, v___x_1179_, v___x_1180_, v_x_1167_);
return v___x_1181_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2(lean_object* v_lctxInitIndices_1182_, lean_object* v_mdecl_1183_, lean_object* v_as_1184_, size_t v_i_1185_, size_t v_stop_1186_, lean_object* v_b_1187_){
_start:
{
uint8_t v___x_1188_; 
v___x_1188_ = lean_usize_dec_eq(v_i_1185_, v_stop_1186_);
if (v___x_1188_ == 0)
{
size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1189_ = ((size_t)1ULL);
v___x_1190_ = lean_usize_sub(v_i_1185_, v___x_1189_);
v___x_1191_ = lean_array_uget_borrowed(v_as_1184_, v___x_1190_);
v___x_1192_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_1182_, v_mdecl_1183_, v___x_1191_, v_b_1187_);
v_i_1185_ = v___x_1190_;
v_b_1187_ = v___x_1192_;
goto _start;
}
else
{
return v_b_1187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_lctxInitIndices_1194_, lean_object* v_mdecl_1195_, lean_object* v_as_1196_, lean_object* v_i_1197_, lean_object* v_stop_1198_, lean_object* v_b_1199_){
_start:
{
size_t v_i_boxed_1200_; size_t v_stop_boxed_1201_; lean_object* v_res_1202_; 
v_i_boxed_1200_ = lean_unbox_usize(v_i_1197_);
lean_dec(v_i_1197_);
v_stop_boxed_1201_ = lean_unbox_usize(v_stop_1198_);
lean_dec(v_stop_1198_);
v_res_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2(v_lctxInitIndices_1194_, v_mdecl_1195_, v_as_1196_, v_i_boxed_1200_, v_stop_boxed_1201_, v_b_1199_);
lean_dec_ref(v_as_1196_);
lean_dec_ref(v_mdecl_1195_);
lean_dec(v_lctxInitIndices_1194_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1___boxed(lean_object* v_lctxInitIndices_1203_, lean_object* v_mdecl_1204_, lean_object* v_x_1205_, lean_object* v_x_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_1203_, v_mdecl_1204_, v_x_1205_, v_x_1206_);
lean_dec_ref(v_x_1205_);
lean_dec_ref(v_mdecl_1204_);
lean_dec(v_lctxInitIndices_1203_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0(lean_object* v_lctxInitIndices_1208_, lean_object* v_mdecl_1209_, lean_object* v_t_1210_, lean_object* v_init_1211_){
_start:
{
lean_object* v_root_1212_; lean_object* v_tail_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v_root_1212_ = lean_ctor_get(v_t_1210_, 0);
v_tail_1213_ = lean_ctor_get(v_t_1210_, 1);
v___x_1214_ = lean_array_get_size(v_tail_1213_);
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = lean_nat_dec_lt(v___x_1215_, v___x_1214_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; 
v___x_1217_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_1208_, v_mdecl_1209_, v_root_1212_, v_init_1211_);
return v___x_1217_;
}
else
{
size_t v___x_1218_; size_t v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1218_ = lean_usize_of_nat(v___x_1214_);
v___x_1219_ = ((size_t)0ULL);
v___x_1220_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(v_lctxInitIndices_1208_, v_mdecl_1209_, v_tail_1213_, v___x_1218_, v___x_1219_, v_init_1211_);
v___x_1221_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_1208_, v_mdecl_1209_, v_root_1212_, v___x_1220_);
return v___x_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0___boxed(lean_object* v_lctxInitIndices_1222_, lean_object* v_mdecl_1223_, lean_object* v_t_1224_, lean_object* v_init_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0(v_lctxInitIndices_1222_, v_mdecl_1223_, v_t_1224_, v_init_1225_);
lean_dec_ref(v_t_1224_);
lean_dec_ref(v_mdecl_1223_);
lean_dec(v_lctxInitIndices_1222_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0(lean_object* v_lctxInitIndices_1227_, lean_object* v_mdecl_1228_, lean_object* v_lctx_1229_, lean_object* v_init_1230_){
_start:
{
lean_object* v_decls_1231_; lean_object* v___x_1232_; 
v_decls_1231_ = lean_ctor_get(v_lctx_1229_, 1);
v___x_1232_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0(v_lctxInitIndices_1227_, v_mdecl_1228_, v_decls_1231_, v_init_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0___boxed(lean_object* v_lctxInitIndices_1233_, lean_object* v_mdecl_1234_, lean_object* v_lctx_1235_, lean_object* v_init_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0(v_lctxInitIndices_1233_, v_mdecl_1234_, v_lctx_1235_, v_init_1236_);
lean_dec_ref(v_lctx_1235_);
lean_dec_ref(v_mdecl_1234_);
lean_dec(v_lctxInitIndices_1233_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(lean_object* v_lctxInitIndices_1242_, lean_object* v_mdecl_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_lctx_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_lctx_1246_ = lean_ctor_get(v_a_1244_, 2);
v___x_1247_ = lean_box(0);
v___x_1248_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0(v_lctxInitIndices_1242_, v_mdecl_1243_, v_lctx_1246_, v___x_1247_);
v___x_1249_ = l_List_isEmpty___redArg(v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1250_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__0));
v___x_1251_ = l_List_lengthTR___redArg(v___x_1248_);
v___x_1252_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__1));
v___x_1253_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__2));
v___x_1254_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v___x_1251_, v___x_1252_, v___x_1253_);
lean_dec(v___x_1251_);
v___x_1255_ = lean_string_append(v___x_1250_, v___x_1254_);
lean_dec_ref(v___x_1254_);
v___x_1256_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__3));
v___x_1257_ = lean_string_append(v___x_1255_, v___x_1256_);
v___x_1258_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString(v___x_1248_);
v___x_1259_ = lean_string_append(v___x_1257_, v___x_1258_);
lean_dec_ref(v___x_1258_);
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec(v___x_1248_);
v___x_1261_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4));
v___x_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___boxed(lean_object* v_lctxInitIndices_1263_, lean_object* v_mdecl_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(v_lctxInitIndices_1263_, v_mdecl_1264_, v_a_1265_);
lean_dec_ref(v_a_1265_);
lean_dec_ref(v_mdecl_1264_);
lean_dec(v_lctxInitIndices_1263_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars(lean_object* v_lctxInitIndices_1268_, lean_object* v_mdecl_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(v_lctxInitIndices_1268_, v_mdecl_1269_, v_a_1270_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___boxed(lean_object* v_lctxInitIndices_1276_, lean_object* v_mdecl_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars(v_lctxInitIndices_1276_, v_mdecl_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec_ref(v_mdecl_1277_);
lean_dec(v_lctxInitIndices_1276_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0(size_t v_sz_1284_, size_t v_i_1285_, lean_object* v_bs_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
uint8_t v___x_1292_; 
v___x_1292_ = lean_usize_dec_lt(v_i_1285_, v_sz_1284_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_bs_1286_);
return v___x_1293_;
}
else
{
lean_object* v_v_1294_; lean_object* v___x_1295_; lean_object* v_bs_x27_1296_; lean_object* v_a_1298_; lean_object* v___x_1303_; 
v_v_1294_ = lean_array_uget(v_bs_1286_, v_i_1285_);
v___x_1295_ = lean_unsigned_to_nat(0u);
v_bs_x27_1296_ = lean_array_uset(v_bs_1286_, v_i_1285_, v___x_1295_);
v___x_1303_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(v_v_1294_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1305_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v_a_1304_);
lean_dec(v_a_1304_);
v_a_1298_ = v___x_1305_;
goto v___jp_1297_;
}
else
{
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1306_; 
v_a_1306_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1303_, 1);
v_a_1298_ = v_a_1306_;
goto v___jp_1297_;
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec_ref(v_bs_x27_1296_);
v_a_1307_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1303_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1303_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
v___jp_1297_:
{
size_t v___x_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_add(v_i_1285_, v___x_1299_);
v___x_1301_ = lean_array_uset(v_bs_x27_1296_, v_i_1285_, v_a_1298_);
v_i_1285_ = v___x_1300_;
v_bs_1286_ = v___x_1301_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0___boxed(lean_object* v_sz_1315_, lean_object* v_i_1316_, lean_object* v_bs_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
size_t v_sz_boxed_1323_; size_t v_i_boxed_1324_; lean_object* v_res_1325_; 
v_sz_boxed_1323_ = lean_unbox_usize(v_sz_1315_);
lean_dec(v_sz_1315_);
v_i_boxed_1324_ = lean_unbox_usize(v_i_1316_);
lean_dec(v_i_1316_);
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0(v_sz_boxed_1323_, v_i_boxed_1324_, v_bs_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(lean_object* v___x_1328_, lean_object* v_as_1329_, size_t v_i_1330_, size_t v_stop_1331_, lean_object* v_b_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_a_1339_; uint8_t v___x_1343_; 
v___x_1343_ = lean_usize_dec_eq(v_i_1330_, v_stop_1331_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_array_uget_borrowed(v_as_1329_, v_i_1330_);
lean_inc(v___x_1344_);
v___x_1345_ = l_Lean_MVarId_getDecl(v___x_1344_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v_lctx_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; uint8_t v___x_1350_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v_lctx_1347_ = lean_ctor_get(v_a_1346_, 1);
lean_inc_ref(v_lctx_1347_);
lean_dec(v_a_1346_);
v___x_1348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0));
v___x_1349_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_1347_, v___x_1328_, v___x_1348_);
lean_dec_ref(v_lctx_1347_);
v___x_1350_ = lean_bool_not(v___x_1349_);
if (v___x_1350_ == 0)
{
v_a_1339_ = v_b_1332_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1351_; 
lean_inc(v___x_1344_);
v___x_1351_ = lean_array_push(v_b_1332_, v___x_1344_);
v_a_1339_ = v___x_1351_;
goto v___jp_1338_;
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref(v_b_1332_);
v_a_1352_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1345_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1345_);
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
else
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v_b_1332_);
return v___x_1360_;
}
v___jp_1338_:
{
size_t v___x_1340_; size_t v___x_1341_; 
v___x_1340_ = ((size_t)1ULL);
v___x_1341_ = lean_usize_add(v_i_1330_, v___x_1340_);
v_i_1330_ = v___x_1341_;
v_b_1332_ = v_a_1339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___boxed(lean_object* v___x_1361_, lean_object* v_as_1362_, lean_object* v_i_1363_, lean_object* v_stop_1364_, lean_object* v_b_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
size_t v_i_boxed_1371_; size_t v_stop_boxed_1372_; lean_object* v_res_1373_; 
v_i_boxed_1371_ = lean_unbox_usize(v_i_1363_);
lean_dec(v_i_1363_);
v_stop_boxed_1372_ = lean_unbox_usize(v_stop_1364_);
lean_dec(v_stop_1364_);
v_res_1373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(v___x_1361_, v_as_1362_, v_i_boxed_1371_, v_stop_boxed_1372_, v_b_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec_ref(v_as_1362_);
lean_dec_ref(v___x_1361_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(lean_object* v_e_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v_awaitingMVars_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_Meta_getMVarsNoDelayed(v_e_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v_a_1431_; lean_object* v___y_1436_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = lean_array_get_size(v_a_1429_);
v___x_1448_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__4));
v___x_1449_ = lean_nat_dec_lt(v___x_1446_, v___x_1447_);
if (v___x_1449_ == 0)
{
v_a_1431_ = v___x_1448_;
goto v___jp_1430_;
}
else
{
lean_object* v_lctx_1450_; uint8_t v___x_1451_; 
v_lctx_1450_ = lean_ctor_get(v_a_1381_, 2);
v___x_1451_ = lean_nat_dec_le(v___x_1447_, v___x_1447_);
if (v___x_1451_ == 0)
{
if (v___x_1449_ == 0)
{
v_a_1431_ = v___x_1448_;
goto v___jp_1430_;
}
else
{
size_t v___x_1452_; size_t v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = ((size_t)0ULL);
v___x_1453_ = lean_usize_of_nat(v___x_1447_);
v___x_1454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(v_lctx_1450_, v_a_1429_, v___x_1452_, v___x_1453_, v___x_1448_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
v___y_1436_ = v___x_1454_;
goto v___jp_1435_;
}
}
else
{
size_t v___x_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = ((size_t)0ULL);
v___x_1456_ = lean_usize_of_nat(v___x_1447_);
v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(v_lctx_1450_, v_a_1429_, v___x_1455_, v___x_1456_, v___x_1448_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
v___y_1436_ = v___x_1457_;
goto v___jp_1435_;
}
}
v___jp_1430_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = lean_array_get_size(v_a_1431_);
v___x_1433_ = lean_unsigned_to_nat(0u);
v___x_1434_ = lean_nat_dec_eq(v___x_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_dec(v_a_1429_);
v_awaitingMVars_1387_ = v_a_1431_;
v___y_1388_ = v_a_1381_;
v___y_1389_ = v_a_1382_;
v___y_1390_ = v_a_1383_;
v___y_1391_ = v_a_1384_;
goto v___jp_1386_;
}
else
{
lean_dec_ref(v_a_1431_);
v_awaitingMVars_1387_ = v_a_1429_;
v___y_1388_ = v_a_1381_;
v___y_1389_ = v_a_1382_;
v___y_1390_ = v_a_1383_;
v___y_1391_ = v_a_1384_;
goto v___jp_1386_;
}
}
v___jp_1435_:
{
if (lean_obj_tag(v___y_1436_) == 0)
{
lean_object* v_a_1437_; 
v_a_1437_ = lean_ctor_get(v___y_1436_, 0);
lean_inc(v_a_1437_);
lean_dec_ref_known(v___y_1436_, 1);
v_a_1431_ = v_a_1437_;
goto v___jp_1430_;
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec(v_a_1429_);
v_a_1438_ = lean_ctor_get(v___y_1436_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___y_1436_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___y_1436_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___y_1436_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v_a_1458_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1428_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1428_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
v___jp_1386_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1392_ = lean_array_get_size(v_awaitingMVars_1387_);
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = lean_nat_dec_eq(v___x_1392_, v___x_1393_);
if (v___x_1394_ == 0)
{
size_t v_sz_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
v_sz_1395_ = lean_array_size(v_awaitingMVars_1387_);
v___x_1396_ = ((size_t)0ULL);
v___x_1397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0(v_sz_1395_, v___x_1396_, v_awaitingMVars_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1417_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1417_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1417_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1402_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__0));
v___x_1403_ = lean_array_get_size(v_a_1398_);
v___x_1404_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__1));
v___x_1405_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__2));
v___x_1406_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v___x_1403_, v___x_1404_, v___x_1405_);
v___x_1407_ = lean_string_append(v___x_1402_, v___x_1406_);
lean_dec_ref(v___x_1406_);
v___x_1408_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__3));
v___x_1409_ = lean_string_append(v___x_1407_, v___x_1408_);
v___x_1410_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0));
v___x_1411_ = lean_array_to_list(v_a_1398_);
v___x_1412_ = l_String_intercalate(v___x_1410_, v___x_1411_);
v___x_1413_ = lean_string_append(v___x_1409_, v___x_1412_);
lean_dec_ref(v___x_1412_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1413_);
v___x_1415_ = v___x_1400_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
v_a_1418_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1397_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1397_);
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
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec_ref(v_awaitingMVars_1387_);
v___x_1426_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4));
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___boxed(lean_object* v_e_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_e_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(lean_object* v_mvarId_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v_mctx_1477_; lean_object* v_decl_1478_; lean_object* v_depth_1479_; lean_object* v_depth_1480_; uint8_t v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1476_ = lean_st_ref_get(v___y_1474_);
v_mctx_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc_ref(v_mctx_1477_);
lean_dec(v___x_1476_);
v_decl_1478_ = l_Lean_MetavarContext_getDecl(v_mctx_1477_, v_mvarId_1473_);
v_depth_1479_ = lean_ctor_get(v_decl_1478_, 3);
lean_inc(v_depth_1479_);
lean_dec_ref(v_decl_1478_);
v_depth_1480_ = lean_ctor_get(v_mctx_1477_, 0);
lean_inc(v_depth_1480_);
lean_dec_ref(v_mctx_1477_);
v___x_1481_ = lean_nat_dec_eq(v_depth_1479_, v_depth_1480_);
lean_dec(v_depth_1480_);
lean_dec(v_depth_1479_);
v___x_1482_ = lean_box(v___x_1481_);
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg___boxed(lean_object* v_mvarId_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_1484_, v___y_1485_);
lean_dec(v___y_1485_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0(lean_object* v_mvarId_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_1488_, v___y_1490_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___boxed(lean_object* v_mvarId_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0(v_mvarId_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar(lean_object* v_mvarId_1515_, lean_object* v_lctxInitIndices_1516_, uint8_t v_fromDelayed_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_MVarId_findDecl_x3f___redArg(v_mvarId_1515_, v_a_1519_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1687_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1687_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1687_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
if (lean_obj_tag(v_a_1524_) == 1)
{
lean_object* v_val_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1682_; 
lean_del_object(v___x_1526_);
v_val_1528_ = lean_ctor_get(v_a_1524_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_a_1524_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1530_ = v_a_1524_;
v_isShared_1531_ = v_isSharedCheck_1682_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_val_1528_);
lean_dec(v_a_1524_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1682_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___x_1545_; lean_object* v_a_1546_; lean_object* v_delayedExpl_1547_; 
v___x_1545_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_1515_, v_a_1519_);
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref(v___x_1545_);
v_delayedExpl_1547_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__0));
if (lean_obj_tag(v_a_1546_) == 1)
{
lean_object* v_val_1548_; lean_object* v_mvarIdPending_1549_; lean_object* v___x_1550_; 
lean_del_object(v___x_1530_);
lean_dec(v_val_1528_);
lean_dec(v_mvarId_1515_);
v_val_1548_ = lean_ctor_get(v_a_1546_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v_a_1546_, 1);
v_mvarIdPending_1549_ = lean_ctor_get(v_val_1548_, 1);
lean_inc(v_mvarIdPending_1549_);
lean_dec(v_val_1548_);
v___x_1550_ = l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(v_mvarIdPending_1549_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1552_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1552_ = l_Lean_MVarId_findDecl_x3f___redArg(v_a_1551_, v_a_1519_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1592_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1592_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1592_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
if (lean_obj_tag(v_a_1553_) == 1)
{
lean_object* v_val_1557_; lean_object* v_msg_1559_; lean_object* v___y_1560_; lean_object* v_a_1572_; lean_object* v___x_1584_; 
lean_del_object(v___x_1555_);
v_val_1557_ = lean_ctor_get(v_a_1553_, 0);
lean_inc(v_val_1557_);
lean_dec_ref_known(v_a_1553_, 1);
lean_inc(v_a_1551_);
v___x_1584_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(v_a_1551_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v_a_1585_);
lean_dec(v_a_1585_);
v_a_1572_ = v___x_1586_;
goto v___jp_1571_;
}
else
{
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1587_; 
v_a_1587_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1584_, 1);
v_a_1572_ = v_a_1587_;
goto v___jp_1571_;
}
else
{
lean_dec(v_val_1557_);
lean_dec(v_a_1551_);
return v___x_1584_;
}
}
v___jp_1558_:
{
lean_object* v___x_1561_; lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1570_; 
v___x_1561_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_val_1557_, v___y_1560_);
lean_dec(v_val_1557_);
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1570_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1570_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1566_ = lean_string_append(v_msg_1559_, v_a_1562_);
lean_dec(v_a_1562_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1566_);
v___x_1568_ = v___x_1564_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
v___jp_1571_:
{
lean_object* v___x_1573_; lean_object* v_a_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1573_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_a_1551_, v_a_1519_);
lean_dec(v_a_1551_);
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref(v___x_1573_);
v___x_1575_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1));
v___x_1576_ = lean_string_append(v___x_1575_, v_a_1572_);
lean_dec_ref(v_a_1572_);
v___x_1577_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2));
v___x_1578_ = lean_string_append(v___x_1576_, v___x_1577_);
v___x_1579_ = lean_string_append(v___x_1578_, v_delayedExpl_1547_);
if (lean_obj_tag(v_a_1574_) == 1)
{
lean_object* v_val_1580_; lean_object* v___x_1581_; 
v_val_1580_ = lean_ctor_get(v_a_1574_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v_a_1574_, 1);
v___x_1581_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_val_1580_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = lean_string_append(v___x_1579_, v_a_1582_);
lean_dec(v_a_1582_);
v_msg_1559_ = v___x_1583_;
v___y_1560_ = v_a_1518_;
goto v___jp_1558_;
}
else
{
lean_dec_ref(v___x_1579_);
lean_dec(v_val_1557_);
return v___x_1581_;
}
}
else
{
lean_dec(v_a_1574_);
v_msg_1559_ = v___x_1579_;
v___y_1560_ = v_a_1518_;
goto v___jp_1558_;
}
}
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
lean_dec(v_a_1553_);
lean_dec(v_a_1551_);
v___x_1588_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3));
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1588_);
v___x_1590_ = v___x_1555_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec(v_a_1551_);
v_a_1593_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1552_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1552_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1601_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1550_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1550_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
else
{
lean_object* v_userName_1609_; lean_object* v_lctx_1610_; uint8_t v_kind_1611_; lean_object* v_msg_1613_; lean_object* v___y_1614_; lean_object* v_msg_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; uint8_t v___y_1662_; lean_object* v_msg_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; 
lean_dec(v_a_1546_);
v_userName_1609_ = lean_ctor_get(v_val_1528_, 0);
v_lctx_1610_ = lean_ctor_get(v_val_1528_, 1);
v_kind_1611_ = lean_ctor_get_uint8(v_val_1528_, sizeof(void*)*7);
switch(v_kind_1611_)
{
case 0:
{
lean_object* v___x_1679_; 
v___x_1679_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__9));
v_msg_1666_ = v___x_1679_;
v___y_1667_ = v_a_1518_;
v___y_1668_ = v_a_1519_;
v___y_1669_ = v_a_1520_;
v___y_1670_ = v_a_1521_;
goto v___jp_1665_;
}
case 1:
{
lean_object* v___x_1680_; 
v___x_1680_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__10));
v_msg_1666_ = v___x_1680_;
v___y_1667_ = v_a_1518_;
v___y_1668_ = v_a_1519_;
v___y_1669_ = v_a_1520_;
v___y_1670_ = v_a_1521_;
goto v___jp_1665_;
}
default: 
{
lean_object* v___x_1681_; 
v___x_1681_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__11));
v_msg_1666_ = v___x_1681_;
v___y_1667_ = v_a_1518_;
v___y_1668_ = v_a_1519_;
v___y_1669_ = v_a_1520_;
v___y_1670_ = v_a_1521_;
goto v___jp_1665_;
}
}
v___jp_1612_:
{
if (v_fromDelayed_1517_ == 0)
{
v___y_1533_ = v_msg_1613_;
v___y_1534_ = v___y_1614_;
goto v___jp_1532_;
}
else
{
lean_object* v_lctx_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; uint8_t v___x_1618_; 
v_lctx_1615_ = lean_ctor_get(v___y_1614_, 2);
v___x_1616_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0));
v___x_1617_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_1610_, v_lctx_1615_, v___x_1616_);
v___x_1618_ = lean_bool_not(v___x_1617_);
if (v___x_1618_ == 0)
{
v___y_1533_ = v_msg_1613_;
v___y_1534_ = v___y_1614_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1619_; lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1628_; 
v___x_1619_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_val_1528_, v___y_1614_);
lean_dec(v_val_1528_);
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1628_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1628_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1624_ = lean_string_append(v_msg_1613_, v_a_1620_);
lean_dec(v_a_1620_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1624_);
v___x_1626_ = v___x_1622_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
v___jp_1629_:
{
lean_object* v___x_1635_; lean_object* v_a_1636_; 
v___x_1635_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarId_1515_, v___y_1632_);
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref(v___x_1635_);
if (lean_obj_tag(v_a_1636_) == 1)
{
lean_object* v_val_1637_; uint8_t v___x_1638_; 
lean_dec(v_mvarId_1515_);
v_val_1637_ = lean_ctor_get(v_a_1636_, 0);
lean_inc(v_val_1637_);
lean_dec_ref_known(v_a_1636_, 1);
v___x_1638_ = lean_bool_not(v_fromDelayed_1517_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; 
v___x_1639_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_val_1637_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v___x_1641_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4));
v___x_1642_ = lean_string_append(v_msg_1630_, v___x_1641_);
v___x_1643_ = lean_string_append(v___x_1642_, v_delayedExpl_1547_);
v___x_1644_ = lean_string_append(v___x_1643_, v_a_1640_);
lean_dec(v_a_1640_);
v_msg_1613_ = v___x_1644_;
v___y_1614_ = v___y_1631_;
goto v___jp_1612_;
}
else
{
lean_dec_ref(v_msg_1630_);
lean_dec(v_val_1528_);
return v___x_1639_;
}
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v_val_1637_);
v___x_1645_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5));
v___x_1646_ = lean_string_append(v_msg_1630_, v___x_1645_);
v_msg_1613_ = v___x_1646_;
v___y_1614_ = v___y_1631_;
goto v___jp_1612_;
}
}
else
{
lean_object* v___x_1647_; lean_object* v_a_1648_; uint8_t v___x_1649_; uint8_t v___x_1650_; 
lean_dec(v_a_1636_);
v___x_1647_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_1515_, v___y_1632_);
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref(v___x_1647_);
v___x_1649_ = lean_unbox(v_a_1648_);
lean_dec(v_a_1648_);
v___x_1650_ = lean_bool_not(v___x_1649_);
if (v___x_1650_ == 0)
{
if (v_fromDelayed_1517_ == 0)
{
v_msg_1613_ = v_msg_1630_;
v___y_1614_ = v___y_1631_;
goto v___jp_1612_;
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1651_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6));
v___x_1652_ = lean_string_append(v_msg_1630_, v___x_1651_);
v___x_1653_ = lean_string_append(v___x_1652_, v_delayedExpl_1547_);
v_msg_1613_ = v___x_1653_;
v___y_1614_ = v___y_1631_;
goto v___jp_1612_;
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7));
v___x_1655_ = lean_string_append(v_msg_1630_, v___x_1654_);
v_msg_1613_ = v___x_1655_;
v___y_1614_ = v___y_1631_;
goto v___jp_1612_;
}
}
}
v___jp_1656_:
{
if (v___y_1662_ == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__8));
lean_inc_ref(v___y_1661_);
v___x_1664_ = lean_string_append(v___y_1661_, v___x_1663_);
v_msg_1630_ = v___x_1664_;
v___y_1631_ = v___y_1658_;
v___y_1632_ = v___y_1657_;
v___y_1633_ = v___y_1659_;
v___y_1634_ = v___y_1660_;
goto v___jp_1629_;
}
else
{
lean_inc_ref(v___y_1661_);
v_msg_1630_ = v___y_1661_;
v___y_1631_ = v___y_1658_;
v___y_1632_ = v___y_1657_;
v___y_1633_ = v___y_1659_;
v___y_1634_ = v___y_1660_;
goto v___jp_1629_;
}
}
v___jp_1665_:
{
lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1671_ = lean_st_ref_get(v___y_1668_);
v___x_1672_ = l_Lean_Name_isAnonymous(v_userName_1609_);
if (v___x_1672_ == 0)
{
lean_object* v_mctx_1673_; lean_object* v___x_1675_; 
v_mctx_1673_ = lean_ctor_get(v___x_1671_, 0);
lean_inc_ref(v_mctx_1673_);
lean_dec(v___x_1671_);
lean_inc(v_mvarId_1515_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v_mvarId_1515_);
v___x_1675_ = v___x_1530_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_mvarId_1515_);
v___x_1675_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1676_ = l_Lean_MetavarContext_findUserName_x3f(v_mctx_1673_, v_userName_1609_);
lean_dec_ref(v_mctx_1673_);
v___x_1677_ = l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(v___x_1675_, v___x_1676_);
lean_dec(v___x_1676_);
lean_dec_ref(v___x_1675_);
v___y_1657_ = v___y_1668_;
v___y_1658_ = v___y_1667_;
v___y_1659_ = v___y_1669_;
v___y_1660_ = v___y_1670_;
v___y_1661_ = v_msg_1666_;
v___y_1662_ = v___x_1677_;
goto v___jp_1656_;
}
}
else
{
lean_dec(v___x_1671_);
lean_del_object(v___x_1530_);
v___y_1657_ = v___y_1668_;
v___y_1658_ = v___y_1667_;
v___y_1659_ = v___y_1669_;
v___y_1660_ = v___y_1670_;
v___y_1661_ = v_msg_1666_;
v___y_1662_ = v___x_1672_;
goto v___jp_1656_;
}
}
}
v___jp_1532_:
{
lean_object* v___x_1535_; lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1544_; 
v___x_1535_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(v_lctxInitIndices_1516_, v_val_1528_, v___y_1534_);
lean_dec(v_val_1528_);
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1544_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1544_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1540_ = lean_string_append(v___y_1533_, v_a_1536_);
lean_dec(v_a_1536_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1540_);
v___x_1542_ = v___x_1538_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
lean_dec(v_a_1524_);
lean_dec(v_mvarId_1515_);
v___x_1683_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__12));
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1683_);
v___x_1685_ = v___x_1526_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec(v_mvarId_1515_);
v_a_1688_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1523_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1523_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___boxed(lean_object* v_mvarId_1696_, lean_object* v_lctxInitIndices_1697_, lean_object* v_fromDelayed_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
uint8_t v_fromDelayed_boxed_1704_; lean_object* v_res_1705_; 
v_fromDelayed_boxed_1704_ = lean_unbox(v_fromDelayed_1698_);
v_res_1705_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar(v_mvarId_1696_, v_lctxInitIndices_1697_, v_fromDelayed_boxed_1704_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec(v_lctxInitIndices_1697_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0(lean_object* v_mvarId_1706_, lean_object* v_lctxInitIndices_1707_, uint8_t v_fromDelayed_1708_, lean_object* v_ppCtx_1709_){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = lean_box(v_fromDelayed_1708_);
v___x_1712_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___boxed), 8, 3);
lean_closure_set(v___x_1712_, 0, v_mvarId_1706_);
lean_closure_set(v___x_1712_, 1, v_lctxInitIndices_1707_);
lean_closure_set(v___x_1712_, 2, v___x_1711_);
v___x_1713_ = l_Lean_PPContext_runMetaM___redArg(v_ppCtx_1709_, v___x_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0___boxed(lean_object* v_mvarId_1714_, lean_object* v_lctxInitIndices_1715_, lean_object* v_fromDelayed_1716_, lean_object* v_ppCtx_1717_, lean_object* v___y_1718_){
_start:
{
uint8_t v_fromDelayed_boxed_1719_; lean_object* v_res_1720_; 
v_fromDelayed_boxed_1719_ = lean_unbox(v_fromDelayed_1716_);
v_res_1720_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0(v_mvarId_1714_, v_lctxInitIndices_1715_, v_fromDelayed_boxed_1719_, v_ppCtx_1717_);
lean_dec_ref(v_ppCtx_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(lean_object* v_mvarId_1721_, uint8_t v_fromDelayed_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_lctxInitIndices_1725_; lean_object* v___x_1726_; lean_object* v___f_1727_; lean_object* v___x_1728_; 
v_lctxInitIndices_1725_ = lean_ctor_get(v_a_1723_, 5);
v___x_1726_ = lean_box(v_fromDelayed_1722_);
lean_inc(v_lctxInitIndices_1725_);
v___f_1727_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1727_, 0, v_mvarId_1721_);
lean_closure_set(v___f_1727_, 1, v_lctxInitIndices_1725_);
lean_closure_set(v___f_1727_, 2, v___x_1726_);
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___f_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___boxed(lean_object* v_mvarId_1729_, lean_object* v_fromDelayed_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
uint8_t v_fromDelayed_boxed_1733_; lean_object* v_res_1734_; 
v_fromDelayed_boxed_1733_ = lean_unbox(v_fromDelayed_1730_);
v_res_1734_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(v_mvarId_1729_, v_fromDelayed_boxed_1733_, v_a_1731_);
lean_dec_ref(v_a_1731_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar(lean_object* v_mvarId_1735_, uint8_t v_fromDelayed_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(v_mvarId_1735_, v_fromDelayed_1736_, v_a_1737_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___boxed(lean_object* v_mvarId_1745_, lean_object* v_fromDelayed_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
uint8_t v_fromDelayed_boxed_1754_; lean_object* v_res_1755_; 
v_fromDelayed_boxed_1754_ = lean_unbox(v_fromDelayed_1746_);
v_res_1755_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar(v_mvarId_1745_, v_fromDelayed_boxed_1754_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
lean_dec(v_a_1750_);
lean_dec_ref(v_a_1749_);
lean_dec(v_a_1748_);
lean_dec_ref(v_a_1747_);
return v_res_1755_;
}
}
lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ErrorUtils(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_Metavariable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
