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
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
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
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_hasValue(lean_object*, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_PPContext_runMetaM___redArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
extern lean_object* l_Lean_reservedMacroScope;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPMVars___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPMVarsAnonymous___boxed(lean_object*);
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
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__2___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0_value)} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPMVars___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPMVarsAnonymous___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "\n\nThis metavariable has been assigned."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "\n\nThis metavariable has been assigned, but it appears here via a *delayed assignment*. "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "\n\nThis metavariable cannot be assigned due to the current metavariable context depth."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "\n\nThis metavariable appears here via a *delayed assignment*. "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "\n\nThis metavariable has a name but it is unreachable."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "Part of the encoding of the *delayed assignment* mechanism. Represents the metavariable "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = ", which has additional local context variables. "};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7_value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 125, .m_capacity = 125, .m_length = 124, .m_data = "[Error: This delayed assignment refers to a metavariable not present in the metavariable context. Please report this issue.]"};
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
v_ref_117_ = lean_ctor_get(v___y_114_, 2);
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
v_ref_143_ = lean_ctor_get(v___y_140_, 2);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3(lean_object* v_m_199_, lean_object* v___f_200_, lean_object* v_n_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_207_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__1));
v___x_208_ = l_Lean_Name_append(v___x_207_, v_m_199_);
v___x_209_ = l_Lean_reservedMacroScope;
v___x_210_ = l_Lean_addMacroScope(v___x_208_, v_n_201_, v___x_209_);
lean_inc(v___y_205_);
lean_inc_ref(v___y_204_);
lean_inc(v___y_203_);
lean_inc_ref(v___y_202_);
v___x_211_ = lean_apply_5(v___f_200_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, lean_box(0));
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_224_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_224_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_224_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_224_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_216_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4));
v___x_217_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5));
lean_inc(v_a_212_);
v___x_218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_218_, 0, v_a_212_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = l_Lean_mkIdent(v___x_210_);
v___x_220_ = l_Lean_Syntax_node2(v_a_212_, v___x_216_, v___x_218_, v___x_219_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_220_);
v___x_222_ = v___x_214_;
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
lean_dec(v___x_210_);
v_a_225_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_211_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_211_);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___boxed(lean_object* v_m_233_, lean_object* v___f_234_, lean_object* v_n_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3(v_m_233_, v___f_234_, v_n_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
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
lean_object* v___f_256_; lean_object* v___f_257_; lean_object* v___f_258_; lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___f_256_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0));
v___f_257_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1));
v___f_258_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2));
lean_inc(v_m_248_);
v___f_259_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___boxed), 8, 2);
lean_closure_set(v___f_259_, 0, v_m_248_);
lean_closure_set(v___f_259_, 1, v___f_256_);
v___x_260_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3));
v___x_261_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_260_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
v___x_263_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__4));
v___x_264_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_263_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; uint8_t v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_264_, 1);
v___x_266_ = lean_unbox(v_a_262_);
lean_dec(v_a_262_);
v___x_267_ = lean_unbox(v_a_265_);
lean_dec(v_a_265_);
v___x_268_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(v_m_248_, v___f_257_, v___f_258_, v___f_259_, v___x_266_, v___x_267_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
return v___x_268_;
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_a_262_);
lean_dec_ref(v___f_259_);
lean_dec(v_m_248_);
v_a_269_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_264_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_264_);
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
lean_dec_ref(v___f_259_);
lean_dec(v_m_248_);
v_a_277_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_261_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_261_);
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
lean_object* v_toCold_358_; lean_object* v_options_359_; lean_object* v___f_360_; lean_object* v___f_361_; lean_object* v___f_362_; uint8_t v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; 
v_toCold_358_ = lean_ctor_get(v_a_355_, 0);
v_options_359_ = lean_ctor_get(v_toCold_358_, 2);
v___f_360_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__0));
v___f_361_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__1));
v___f_362_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__3));
v___x_363_ = l_Lean_getPPMVars(v_options_359_);
v___x_364_ = l_Lean_getPPMVarsAnonymous(v_options_359_);
v___x_365_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(v_m_352_, v___f_362_, v___f_361_, v___f_360_, v___x_363_, v___x_364_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___boxed(lean_object* v_m_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(v_m_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
return v_res_372_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(lean_object* v_a_373_, lean_object* v_x_374_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
uint8_t v___x_375_; 
v___x_375_ = 0;
return v___x_375_;
}
else
{
lean_object* v_key_376_; lean_object* v_tail_377_; uint8_t v___x_378_; 
v_key_376_ = lean_ctor_get(v_x_374_, 0);
v_tail_377_ = lean_ctor_get(v_x_374_, 2);
v___x_378_ = l_Lean_instBEqFVarId_beq(v_key_376_, v_a_373_);
if (v___x_378_ == 0)
{
v_x_374_ = v_tail_377_;
goto _start;
}
else
{
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_a_380_, lean_object* v_x_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_a_380_, v_x_381_);
lean_dec(v_x_381_);
lean_dec(v_a_380_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(lean_object* v_m_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_buckets_386_; lean_object* v___x_387_; uint64_t v___x_388_; uint64_t v___x_389_; uint64_t v___x_390_; uint64_t v_fold_391_; uint64_t v___x_392_; uint64_t v___x_393_; uint64_t v___x_394_; size_t v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_buckets_386_ = lean_ctor_get(v_m_384_, 1);
v___x_387_ = lean_array_get_size(v_buckets_386_);
v___x_388_ = l_Lean_instHashableFVarId_hash(v_a_385_);
v___x_389_ = 32ULL;
v___x_390_ = lean_uint64_shift_right(v___x_388_, v___x_389_);
v_fold_391_ = lean_uint64_xor(v___x_388_, v___x_390_);
v___x_392_ = 16ULL;
v___x_393_ = lean_uint64_shift_right(v_fold_391_, v___x_392_);
v___x_394_ = lean_uint64_xor(v_fold_391_, v___x_393_);
v___x_395_ = lean_uint64_to_usize(v___x_394_);
v___x_396_ = lean_usize_of_nat(v___x_387_);
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_sub(v___x_396_, v___x_397_);
v___x_399_ = lean_usize_land(v___x_395_, v___x_398_);
v___x_400_ = lean_array_uget_borrowed(v_buckets_386_, v___x_399_);
v___x_401_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_a_385_, v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg___boxed(lean_object* v_m_402_, lean_object* v_a_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_m_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_m_402_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
if (lean_obj_tag(v_x_407_) == 0)
{
return v_x_406_;
}
else
{
lean_object* v_key_408_; lean_object* v_value_409_; lean_object* v_tail_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_433_; 
v_key_408_ = lean_ctor_get(v_x_407_, 0);
v_value_409_ = lean_ctor_get(v_x_407_, 1);
v_tail_410_ = lean_ctor_get(v_x_407_, 2);
v_isSharedCheck_433_ = !lean_is_exclusive(v_x_407_);
if (v_isSharedCheck_433_ == 0)
{
v___x_412_ = v_x_407_;
v_isShared_413_ = v_isSharedCheck_433_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_tail_410_);
lean_inc(v_value_409_);
lean_inc(v_key_408_);
lean_dec(v_x_407_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_433_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v___x_417_; uint64_t v_fold_418_; uint64_t v___x_419_; uint64_t v___x_420_; uint64_t v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_414_ = lean_array_get_size(v_x_406_);
v___x_415_ = l_Lean_instHashableFVarId_hash(v_key_408_);
v___x_416_ = 32ULL;
v___x_417_ = lean_uint64_shift_right(v___x_415_, v___x_416_);
v_fold_418_ = lean_uint64_xor(v___x_415_, v___x_417_);
v___x_419_ = 16ULL;
v___x_420_ = lean_uint64_shift_right(v_fold_418_, v___x_419_);
v___x_421_ = lean_uint64_xor(v_fold_418_, v___x_420_);
v___x_422_ = lean_uint64_to_usize(v___x_421_);
v___x_423_ = lean_usize_of_nat(v___x_414_);
v___x_424_ = ((size_t)1ULL);
v___x_425_ = lean_usize_sub(v___x_423_, v___x_424_);
v___x_426_ = lean_usize_land(v___x_422_, v___x_425_);
v___x_427_ = lean_array_uget_borrowed(v_x_406_, v___x_426_);
lean_inc(v___x_427_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 2, v___x_427_);
v___x_429_ = v___x_412_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_key_408_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_value_409_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v___x_427_);
v___x_429_ = v_reuseFailAlloc_432_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; 
v___x_430_ = lean_array_uset(v_x_406_, v___x_426_, v___x_429_);
v_x_406_ = v___x_430_;
v_x_407_ = v_tail_410_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3___redArg(lean_object* v_i_434_, lean_object* v_source_435_, lean_object* v_target_436_){
_start:
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_array_get_size(v_source_435_);
v___x_438_ = lean_nat_dec_lt(v_i_434_, v___x_437_);
if (v___x_438_ == 0)
{
lean_dec_ref(v_source_435_);
lean_dec(v_i_434_);
return v_target_436_;
}
else
{
lean_object* v_es_439_; lean_object* v___x_440_; lean_object* v_source_441_; lean_object* v_target_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_es_439_ = lean_array_fget(v_source_435_, v_i_434_);
v___x_440_ = lean_box(0);
v_source_441_ = lean_array_fset(v_source_435_, v_i_434_, v___x_440_);
v_target_442_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5___redArg(v_target_436_, v_es_439_);
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_add(v_i_434_, v___x_443_);
lean_dec(v_i_434_);
v_i_434_ = v___x_444_;
v_source_435_ = v_source_441_;
v_target_436_ = v_target_442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(lean_object* v_data_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_nbuckets_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_447_ = lean_array_get_size(v_data_446_);
v___x_448_ = lean_unsigned_to_nat(2u);
v_nbuckets_449_ = lean_nat_mul(v___x_447_, v___x_448_);
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_box(0);
v___x_452_ = lean_mk_array(v_nbuckets_449_, v___x_451_);
v___x_453_ = lean_array_propagate_mark(v_data_446_, v___x_452_);
v___x_454_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3___redArg(v___x_450_, v_data_446_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(lean_object* v_m_455_, lean_object* v_a_456_, lean_object* v_b_457_){
_start:
{
lean_object* v_size_458_; lean_object* v_buckets_459_; lean_object* v___x_460_; uint64_t v___x_461_; uint64_t v___x_462_; uint64_t v___x_463_; uint64_t v_fold_464_; uint64_t v___x_465_; uint64_t v___x_466_; uint64_t v___x_467_; size_t v___x_468_; size_t v___x_469_; size_t v___x_470_; size_t v___x_471_; size_t v___x_472_; lean_object* v_bkt_473_; uint8_t v___x_474_; 
v_size_458_ = lean_ctor_get(v_m_455_, 0);
v_buckets_459_ = lean_ctor_get(v_m_455_, 1);
v___x_460_ = lean_array_get_size(v_buckets_459_);
v___x_461_ = l_Lean_instHashableFVarId_hash(v_a_456_);
v___x_462_ = 32ULL;
v___x_463_ = lean_uint64_shift_right(v___x_461_, v___x_462_);
v_fold_464_ = lean_uint64_xor(v___x_461_, v___x_463_);
v___x_465_ = 16ULL;
v___x_466_ = lean_uint64_shift_right(v_fold_464_, v___x_465_);
v___x_467_ = lean_uint64_xor(v_fold_464_, v___x_466_);
v___x_468_ = lean_uint64_to_usize(v___x_467_);
v___x_469_ = lean_usize_of_nat(v___x_460_);
v___x_470_ = ((size_t)1ULL);
v___x_471_ = lean_usize_sub(v___x_469_, v___x_470_);
v___x_472_ = lean_usize_land(v___x_468_, v___x_471_);
v_bkt_473_ = lean_array_uget_borrowed(v_buckets_459_, v___x_472_);
v___x_474_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_a_456_, v_bkt_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_495_; 
lean_inc_ref(v_buckets_459_);
lean_inc(v_size_458_);
v_isSharedCheck_495_ = !lean_is_exclusive(v_m_455_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; lean_object* v_unused_497_; 
v_unused_496_ = lean_ctor_get(v_m_455_, 1);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_m_455_, 0);
lean_dec(v_unused_497_);
v___x_476_ = v_m_455_;
v_isShared_477_ = v_isSharedCheck_495_;
goto v_resetjp_475_;
}
else
{
lean_dec(v_m_455_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_495_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v_size_x27_479_; lean_object* v___x_480_; lean_object* v_buckets_x27_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_478_ = lean_unsigned_to_nat(1u);
v_size_x27_479_ = lean_nat_add(v_size_458_, v___x_478_);
lean_dec(v_size_458_);
lean_inc(v_bkt_473_);
v___x_480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_480_, 0, v_a_456_);
lean_ctor_set(v___x_480_, 1, v_b_457_);
lean_ctor_set(v___x_480_, 2, v_bkt_473_);
v_buckets_x27_481_ = lean_array_uset(v_buckets_459_, v___x_472_, v___x_480_);
v___x_482_ = lean_unsigned_to_nat(4u);
v___x_483_ = lean_nat_mul(v_size_x27_479_, v___x_482_);
v___x_484_ = lean_unsigned_to_nat(3u);
v___x_485_ = lean_nat_div(v___x_483_, v___x_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_array_get_size(v_buckets_x27_481_);
v___x_487_ = lean_nat_dec_le(v___x_485_, v___x_486_);
lean_dec(v___x_485_);
if (v___x_487_ == 0)
{
lean_object* v_val_488_; lean_object* v___x_490_; 
v_val_488_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(v_buckets_x27_481_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v_val_488_);
lean_ctor_set(v___x_476_, 0, v_size_x27_479_);
v___x_490_ = v___x_476_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_size_x27_479_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_val_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
else
{
lean_object* v___x_493_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v_buckets_x27_481_);
lean_ctor_set(v___x_476_, 0, v_size_x27_479_);
v___x_493_ = v___x_476_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_size_x27_479_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_buckets_x27_481_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_dec(v_b_457_);
lean_dec(v_a_456_);
return v_m_455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(lean_object* v_val_501_, lean_object* v_as_502_, size_t v_sz_503_, size_t v_i_504_, lean_object* v_b_505_){
_start:
{
lean_object* v_a_508_; uint8_t v___x_512_; 
v___x_512_ = lean_usize_dec_lt(v_i_504_, v_sz_503_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec_ref(v_val_501_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v_b_505_);
return v___x_513_;
}
else
{
lean_object* v_snd_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_604_; 
v_snd_514_ = lean_ctor_get(v_b_505_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_b_505_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v_b_505_, 0);
lean_dec(v_unused_605_);
v___x_516_ = v_b_505_;
v_isShared_517_ = v_isSharedCheck_604_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_snd_514_);
lean_dec(v_b_505_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_604_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_snd_518_; lean_object* v_fst_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_603_; 
v_snd_518_ = lean_ctor_get(v_snd_514_, 1);
v_fst_519_ = lean_ctor_get(v_snd_514_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v_snd_514_);
if (v_isSharedCheck_603_ == 0)
{
v___x_521_ = v_snd_514_;
v_isShared_522_ = v_isSharedCheck_603_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_snd_518_);
lean_inc(v_fst_519_);
lean_dec(v_snd_514_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_603_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v_array_523_; lean_object* v_start_524_; lean_object* v_stop_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v_array_523_ = lean_ctor_get(v_snd_518_, 0);
v_start_524_ = lean_ctor_get(v_snd_518_, 1);
v_stop_525_ = lean_ctor_get(v_snd_518_, 2);
v___x_526_ = lean_box(0);
v___x_527_ = lean_nat_dec_lt(v_start_524_, v_stop_525_);
if (v___x_527_ == 0)
{
lean_object* v___x_529_; 
lean_dec_ref(v_val_501_);
if (v_isShared_522_ == 0)
{
v___x_529_ = v___x_521_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_fst_519_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_snd_518_);
v___x_529_ = v_reuseFailAlloc_534_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_531_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_529_);
lean_ctor_set(v___x_516_, 0, v___x_526_);
v___x_531_ = v___x_516_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_529_);
v___x_531_ = v_reuseFailAlloc_533_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
}
else
{
lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_599_; 
lean_inc(v_stop_525_);
lean_inc(v_start_524_);
lean_inc_ref(v_array_523_);
v_isSharedCheck_599_ = !lean_is_exclusive(v_snd_518_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; lean_object* v_unused_601_; lean_object* v_unused_602_; 
v_unused_600_ = lean_ctor_get(v_snd_518_, 2);
lean_dec(v_unused_600_);
v_unused_601_ = lean_ctor_get(v_snd_518_, 1);
lean_dec(v_unused_601_);
v_unused_602_ = lean_ctor_get(v_snd_518_, 0);
lean_dec(v_unused_602_);
v___x_536_ = v_snd_518_;
v_isShared_537_ = v_isSharedCheck_599_;
goto v_resetjp_535_;
}
else
{
lean_dec(v_snd_518_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_599_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v_lctx_538_; lean_object* v___x_539_; lean_object* v_a_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v_lctx_538_ = lean_ctor_get(v_val_501_, 1);
v___x_539_ = lean_array_fget(v_array_523_, v_start_524_);
v_a_540_ = lean_array_uget_borrowed(v_as_502_, v_i_504_);
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = lean_nat_add(v_start_524_, v___x_541_);
lean_dec(v_start_524_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v___x_542_);
v___x_544_ = v___x_536_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_array_523_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_stop_525_);
v___x_544_ = v_reuseFailAlloc_598_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = l_Lean_Expr_fvarId_x21(v_a_540_);
lean_inc_ref(v_lctx_538_);
v___x_546_ = lean_local_ctx_find(v_lctx_538_, v___x_545_);
if (lean_obj_tag(v___x_546_) == 1)
{
lean_object* v_val_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_589_; 
v_val_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_589_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_589_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_val_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_589_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
uint8_t v___x_551_; uint8_t v___x_552_; 
v___x_551_ = 0;
v___x_552_ = l_Lean_LocalDecl_hasValue(v_val_547_, v___x_551_);
lean_dec(v_val_547_);
if (v___x_552_ == 0)
{
if (lean_obj_tag(v___x_539_) == 1)
{
lean_object* v_fvarId_553_; uint8_t v___x_554_; 
v_fvarId_553_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_fvarId_553_);
lean_dec_ref_known(v___x_539_, 1);
v___x_554_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_fst_519_, v_fvarId_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
lean_del_object(v___x_549_);
v___x_555_ = lean_box(0);
v___x_556_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v_fst_519_, v_fvarId_553_, v___x_555_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_544_);
lean_ctor_set(v___x_521_, 0, v___x_556_);
v___x_558_ = v___x_521_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_544_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_560_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_558_);
lean_ctor_set(v___x_516_, 0, v___x_526_);
v___x_560_ = v___x_516_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
v_a_508_ = v___x_560_;
goto v___jp_507_;
}
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_565_; 
lean_dec(v_fvarId_553_);
lean_dec_ref(v_val_501_);
v___x_563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0));
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_544_);
v___x_565_ = v___x_521_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_fst_519_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v___x_544_);
v___x_565_ = v_reuseFailAlloc_572_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_567_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_565_);
lean_ctor_set(v___x_516_, 0, v___x_563_);
v___x_567_ = v___x_516_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_565_);
v___x_567_ = v_reuseFailAlloc_571_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_569_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 0);
lean_ctor_set(v___x_549_, 0, v___x_567_);
v___x_569_ = v___x_549_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_575_; 
lean_dec(v___x_539_);
lean_dec_ref(v_val_501_);
v___x_573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0));
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_544_);
v___x_575_ = v___x_521_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_fst_519_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v___x_544_);
v___x_575_ = v_reuseFailAlloc_582_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_577_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_575_);
lean_ctor_set(v___x_516_, 0, v___x_573_);
v___x_577_ = v___x_516_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_575_);
v___x_577_ = v_reuseFailAlloc_581_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_579_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 0);
lean_ctor_set(v___x_549_, 0, v___x_577_);
v___x_579_ = v___x_549_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
else
{
lean_object* v___x_584_; 
lean_del_object(v___x_549_);
lean_dec(v___x_539_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_544_);
v___x_584_ = v___x_521_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_fst_519_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_544_);
v___x_584_ = v_reuseFailAlloc_588_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_584_);
lean_ctor_set(v___x_516_, 0, v___x_526_);
v___x_586_ = v___x_516_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v_a_508_ = v___x_586_;
goto v___jp_507_;
}
}
}
}
}
else
{
lean_object* v___x_590_; lean_object* v___x_592_; 
lean_dec(v___x_546_);
lean_dec(v___x_539_);
lean_dec_ref(v_val_501_);
v___x_590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0));
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_544_);
v___x_592_ = v___x_521_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_fst_519_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_544_);
v___x_592_ = v_reuseFailAlloc_597_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_594_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_592_);
lean_ctor_set(v___x_516_, 0, v___x_590_);
v___x_594_ = v___x_516_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v___x_592_);
v___x_594_ = v_reuseFailAlloc_596_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
}
}
}
}
}
}
}
v___jp_507_:
{
size_t v___x_509_; size_t v___x_510_; 
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_add(v_i_504_, v___x_509_);
v_i_504_ = v___x_510_;
v_b_505_ = v_a_508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___boxed(lean_object* v_val_606_, lean_object* v_as_607_, lean_object* v_sz_608_, lean_object* v_i_609_, lean_object* v_b_610_, lean_object* v___y_611_){
_start:
{
size_t v_sz_boxed_612_; size_t v_i_boxed_613_; lean_object* v_res_614_; 
v_sz_boxed_612_ = lean_unbox_usize(v_sz_608_);
lean_dec(v_sz_608_);
v_i_boxed_613_ = lean_unbox_usize(v_i_609_);
lean_dec(v_i_609_);
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_val_606_, v_as_607_, v_sz_boxed_612_, v_i_boxed_613_, v_b_610_);
lean_dec_ref(v_as_607_);
return v_res_614_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0(void){
_start:
{
lean_object* v___x_615_; lean_object* v_dummy_616_; 
v___x_615_ = lean_box(0);
v_dummy_616_ = l_Lean_Expr_sort___override(v___x_615_);
return v_dummy_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(lean_object* v_e_617_, lean_object* v_decl_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_fvars_624_; lean_object* v_mvarIdPending_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_693_; 
v_fvars_624_ = lean_ctor_get(v_decl_618_, 0);
v_mvarIdPending_625_ = lean_ctor_get(v_decl_618_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_decl_618_);
if (v_isSharedCheck_693_ == 0)
{
v___x_627_ = v_decl_618_;
v_isShared_628_ = v_isSharedCheck_693_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_mvarIdPending_625_);
lean_inc(v_fvars_624_);
lean_dec(v_decl_618_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_693_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_629_ = l_Lean_Expr_getAppNumArgs(v_e_617_);
v___x_630_ = lean_array_get_size(v_fvars_624_);
v___x_631_ = lean_nat_dec_eq(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v___x_629_);
lean_del_object(v___x_627_);
lean_dec(v_mvarIdPending_625_);
lean_dec_ref(v_fvars_624_);
lean_dec_ref(v_e_617_);
v___x_632_ = lean_box(v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_635_ = l_Lean_MVarId_findDecl_x3f___redArg(v_mvarIdPending_625_, v_a_620_);
lean_dec(v_mvarIdPending_625_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_684_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_684_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_684_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_684_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
if (lean_obj_tag(v_a_636_) == 1)
{
lean_object* v_val_640_; lean_object* v_dummy_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
lean_del_object(v___x_638_);
v_val_640_ = lean_ctor_get(v_a_636_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v_a_636_, 1);
v_dummy_641_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0, &l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0);
lean_inc(v___x_629_);
v___x_642_ = lean_mk_array(v___x_629_, v_dummy_641_);
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_sub(v___x_629_, v___x_643_);
lean_dec(v___x_629_);
v___x_645_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_617_, v___x_642_, v___x_644_);
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = lean_array_get_size(v___x_645_);
v___x_648_ = l_Array_toSubarray___redArg(v___x_645_, v___x_646_, v___x_647_);
v___x_649_ = lean_box(0);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v___x_648_);
lean_ctor_set(v___x_627_, 0, v___x_634_);
v___x_651_ = v___x_627_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v___x_648_);
v___x_651_ = v_reuseFailAlloc_678_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; size_t v_sz_653_; size_t v___x_654_; lean_object* v___x_655_; 
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_649_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v_sz_653_ = lean_array_size(v_fvars_624_);
v___x_654_ = ((size_t)0ULL);
v___x_655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_val_640_, v_fvars_624_, v_sz_653_, v___x_654_, v___x_652_);
lean_dec_ref(v_fvars_624_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_669_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_669_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_669_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_669_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v_fst_660_; 
v_fst_660_ = lean_ctor_get(v_a_656_, 0);
lean_inc(v_fst_660_);
lean_dec(v_a_656_);
if (lean_obj_tag(v_fst_660_) == 0)
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = lean_box(v___x_631_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_661_);
v___x_663_ = v___x_658_;
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
else
{
lean_object* v_val_665_; lean_object* v___x_667_; 
v_val_665_ = lean_ctor_get(v_fst_660_, 0);
lean_inc(v_val_665_);
lean_dec_ref_known(v_fst_660_, 1);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v_val_665_);
v___x_667_ = v___x_658_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_val_665_);
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
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
v_a_670_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_655_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_655_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
else
{
uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_682_; 
lean_dec(v_a_636_);
lean_dec(v___x_629_);
lean_del_object(v___x_627_);
lean_dec_ref(v_fvars_624_);
lean_dec_ref(v_e_617_);
v___x_679_ = 0;
v___x_680_ = lean_box(v___x_679_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_680_);
v___x_682_ = v___x_638_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_dec(v___x_629_);
lean_del_object(v___x_627_);
lean_dec_ref(v_fvars_624_);
lean_dec_ref(v_e_617_);
v_a_685_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_635_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_635_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___boxed(lean_object* v_e_694_, lean_object* v_decl_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(v_e_694_, v_decl_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
return v_res_701_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0(lean_object* v_00_u03b2_702_, lean_object* v_m_703_, lean_object* v_a_704_){
_start:
{
uint8_t v___x_705_; 
v___x_705_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_m_703_, v_a_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___boxed(lean_object* v_00_u03b2_706_, lean_object* v_m_707_, lean_object* v_a_708_){
_start:
{
uint8_t v_res_709_; lean_object* v_r_710_; 
v_res_709_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0(v_00_u03b2_706_, v_m_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_m_707_);
v_r_710_ = lean_box(v_res_709_);
return v_r_710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1(lean_object* v_00_u03b2_711_, lean_object* v_m_712_, lean_object* v_a_713_, lean_object* v_b_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v_m_712_, v_a_713_, v_b_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2(lean_object* v_val_716_, lean_object* v_as_717_, size_t v_sz_718_, size_t v_i_719_, lean_object* v_b_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_val_716_, v_as_717_, v_sz_718_, v_i_719_, v_b_720_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___boxed(lean_object* v_val_727_, lean_object* v_as_728_, lean_object* v_sz_729_, lean_object* v_i_730_, lean_object* v_b_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
size_t v_sz_boxed_737_; size_t v_i_boxed_738_; lean_object* v_res_739_; 
v_sz_boxed_737_ = lean_unbox_usize(v_sz_729_);
lean_dec(v_sz_729_);
v_i_boxed_738_ = lean_unbox_usize(v_i_730_);
lean_dec(v_i_730_);
v_res_739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2(v_val_727_, v_as_728_, v_sz_boxed_737_, v_i_boxed_738_, v_b_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec_ref(v_as_728_);
return v_res_739_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0(lean_object* v_00_u03b2_740_, lean_object* v_a_741_, lean_object* v_x_742_){
_start:
{
uint8_t v___x_743_; 
v___x_743_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_a_741_, v_x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_744_, lean_object* v_a_745_, lean_object* v_x_746_){
_start:
{
uint8_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0(v_00_u03b2_744_, v_a_745_, v_x_746_);
lean_dec(v_x_746_);
lean_dec(v_a_745_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2(lean_object* v_00_u03b2_749_, lean_object* v_data_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(v_data_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_752_, lean_object* v_i_753_, lean_object* v_source_754_, lean_object* v_target_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3___redArg(v_i_753_, v_source_754_, v_target_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_757_, lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5___redArg(v_x_758_, v_x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(lean_object* v_mvarId_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; lean_object* v_mctx_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_764_ = lean_st_ref_get(v___y_762_);
v_mctx_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc_ref(v_mctx_765_);
lean_dec(v___x_764_);
v___x_766_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_765_, v_mvarId_761_);
lean_dec_ref(v_mctx_765_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg___boxed(lean_object* v_mvarId_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarId_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec(v_mvarId_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0(lean_object* v_mvarId_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarId_772_, v___y_774_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___boxed(lean_object* v_mvarId_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0(v_mvarId_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v_mvarId_779_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(lean_object* v_e_786_, lean_object* v___y_787_){
_start:
{
uint8_t v___x_789_; 
v___x_789_ = l_Lean_Expr_hasMVar(v_e_786_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v_e_786_);
return v___x_790_;
}
else
{
lean_object* v___x_791_; lean_object* v_mctx_792_; lean_object* v___x_793_; lean_object* v_fst_794_; lean_object* v_snd_795_; lean_object* v___x_796_; lean_object* v_cache_797_; lean_object* v_zetaDeltaFVarIds_798_; lean_object* v_postponed_799_; lean_object* v_diag_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_809_; 
v___x_791_ = lean_st_ref_get(v___y_787_);
v_mctx_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc_ref(v_mctx_792_);
lean_dec(v___x_791_);
v___x_793_ = l_Lean_instantiateMVarsCore(v_mctx_792_, v_e_786_);
v_fst_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_fst_794_);
v_snd_795_ = lean_ctor_get(v___x_793_, 1);
lean_inc(v_snd_795_);
lean_dec_ref(v___x_793_);
v___x_796_ = lean_st_ref_take(v___y_787_);
v_cache_797_ = lean_ctor_get(v___x_796_, 1);
v_zetaDeltaFVarIds_798_ = lean_ctor_get(v___x_796_, 2);
v_postponed_799_ = lean_ctor_get(v___x_796_, 3);
v_diag_800_ = lean_ctor_get(v___x_796_, 4);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v___x_796_, 0);
lean_dec(v_unused_810_);
v___x_802_ = v___x_796_;
v_isShared_803_ = v_isSharedCheck_809_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_diag_800_);
lean_inc(v_postponed_799_);
lean_inc(v_zetaDeltaFVarIds_798_);
lean_inc(v_cache_797_);
lean_dec(v___x_796_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_809_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v_snd_795_);
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_snd_795_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_cache_797_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_zetaDeltaFVarIds_798_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v_postponed_799_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v_diag_800_);
v___x_805_ = v_reuseFailAlloc_808_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_st_ref_put(v___y_787_, v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_807_, 0, v_fst_794_);
return v___x_807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg___boxed(lean_object* v_e_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_e_811_, v___y_812_);
lean_dec(v___y_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1(lean_object* v_e_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_e_815_, v___y_817_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___boxed(lean_object* v_e_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1(v_e_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(lean_object* v_mvarId_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_832_; lean_object* v_mctx_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_832_ = lean_st_ref_get(v___y_830_);
v_mctx_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc_ref(v_mctx_833_);
lean_dec(v___x_832_);
v___x_834_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_833_, v_mvarId_829_);
lean_dec_ref(v_mctx_833_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg___boxed(lean_object* v_mvarId_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec(v_mvarId_836_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2(lean_object* v_mvarId_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_840_, v___y_842_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___boxed(lean_object* v_mvarId_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2(v_mvarId_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v_mvarId_847_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(lean_object* v_mvarIdPending_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarIdPending_854_, v_a_856_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_936_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_936_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_936_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_936_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
if (lean_obj_tag(v_a_861_) == 1)
{
lean_object* v_val_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v_val_865_ = lean_ctor_get(v_a_861_, 0);
lean_inc(v_val_865_);
lean_dec_ref_known(v_a_861_, 1);
v___x_866_ = l_Lean_Expr_getAppFn_x27(v_val_865_);
v___x_867_ = l_Lean_Expr_isMVar(v___x_866_);
lean_dec_ref(v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_869_; 
lean_dec(v_val_865_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v_mvarIdPending_854_);
v___x_869_ = v___x_863_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_mvarIdPending_854_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
else
{
lean_object* v___x_871_; 
lean_del_object(v___x_863_);
v___x_871_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_val_865_, v_a_856_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_924_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_924_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_924_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_924_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Expr_consumeMData(v_a_872_);
lean_dec(v_a_872_);
if (lean_obj_tag(v___x_876_) == 2)
{
lean_object* v_mvarId_877_; lean_object* v___x_879_; 
lean_dec(v_mvarIdPending_854_);
v_mvarId_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_mvarId_877_);
lean_dec_ref_known(v___x_876_, 1);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v_mvarId_877_);
v___x_879_ = v___x_874_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_mvarId_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
else
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Expr_getAppFn_x27(v___x_876_);
if (lean_obj_tag(v___x_881_) == 2)
{
lean_object* v_mvarId_882_; lean_object* v___x_883_; 
lean_del_object(v___x_874_);
v_mvarId_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_mvarId_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_882_, v_a_856_);
lean_dec(v_mvarId_882_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_912_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_912_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_912_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_912_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
if (lean_obj_tag(v_a_884_) == 1)
{
lean_object* v_val_888_; lean_object* v___x_889_; 
lean_del_object(v___x_886_);
v_val_888_ = lean_ctor_get(v_a_884_, 0);
lean_inc_n(v_val_888_, 2);
lean_dec_ref_known(v_a_884_, 1);
v___x_889_ = l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(v___x_876_, v_val_888_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_900_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_900_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_900_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_900_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
uint8_t v___x_894_; 
v___x_894_ = lean_unbox(v_a_890_);
lean_dec(v_a_890_);
if (v___x_894_ == 0)
{
lean_object* v___x_896_; 
lean_dec(v_val_888_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v_mvarIdPending_854_);
v___x_896_ = v___x_892_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_mvarIdPending_854_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
else
{
lean_object* v_mvarIdPending_898_; 
lean_del_object(v___x_892_);
lean_dec(v_mvarIdPending_854_);
v_mvarIdPending_898_ = lean_ctor_get(v_val_888_, 1);
lean_inc(v_mvarIdPending_898_);
lean_dec(v_val_888_);
v_mvarIdPending_854_ = v_mvarIdPending_898_;
goto _start;
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec(v_val_888_);
lean_dec(v_mvarIdPending_854_);
v_a_901_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_889_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_889_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
else
{
lean_object* v___x_910_; 
lean_dec(v_a_884_);
lean_dec_ref(v___x_876_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v_mvarIdPending_854_);
v___x_910_ = v___x_886_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_mvarIdPending_854_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v___x_876_);
lean_dec(v_mvarIdPending_854_);
v_a_913_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_883_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_883_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v___x_922_; 
lean_dec_ref(v___x_881_);
lean_dec_ref(v___x_876_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v_mvarIdPending_854_);
v___x_922_ = v___x_874_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_mvarIdPending_854_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v_mvarIdPending_854_);
v_a_925_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_871_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_871_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
else
{
lean_object* v___x_934_; 
lean_dec(v_a_861_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v_mvarIdPending_854_);
v___x_934_ = v___x_863_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_mvarIdPending_854_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_mvarIdPending_854_);
v_a_937_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_860_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_860_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending___boxed(lean_object* v_mvarIdPending_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(v_mvarIdPending_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(lean_object* v_n_953_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___closed__0));
v___x_955_ = lean_string_append(v___x_954_, v_n_953_);
v___x_956_ = lean_string_append(v___x_955_, v___x_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___boxed(lean_object* v_n_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v_n_957_);
lean_dec_ref(v_n_957_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString_spec__0(lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
if (lean_obj_tag(v_a_959_) == 0)
{
lean_object* v___x_961_; 
v___x_961_ = l_List_reverse___redArg(v_a_960_);
return v___x_961_;
}
else
{
lean_object* v_head_962_; lean_object* v_tail_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_982_; 
v_head_962_ = lean_ctor_get(v_a_959_, 0);
v_tail_963_ = lean_ctor_get(v_a_959_, 1);
v_isSharedCheck_982_ = !lean_is_exclusive(v_a_959_);
if (v_isSharedCheck_982_ == 0)
{
v___x_965_ = v_a_959_;
v_isShared_966_ = v_isSharedCheck_982_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_tail_963_);
lean_inc(v_head_962_);
lean_dec(v_a_959_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_982_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___y_968_; uint8_t v___x_973_; uint8_t v___x_974_; 
v___x_973_ = l_Lean_Name_hasMacroScopes(v_head_962_);
v___x_974_ = 1;
if (v___x_973_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = l_Lean_Name_toString(v_head_962_, v___x_974_);
v___x_976_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v___x_975_);
lean_dec_ref(v___x_975_);
v___y_968_ = v___x_976_;
goto v___jp_967_;
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_977_ = l_Lean_Name_eraseMacroScopes(v_head_962_);
lean_dec(v_head_962_);
v___x_978_ = l_Lean_Name_toString(v___x_977_, v___x_974_);
v___x_979_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0));
v___x_980_ = lean_string_append(v___x_978_, v___x_979_);
v___x_981_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v___x_980_);
lean_dec_ref(v___x_980_);
v___y_968_ = v___x_981_;
goto v___jp_967_;
}
v___jp_967_:
{
lean_object* v___x_970_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 1, v_a_960_);
lean_ctor_set(v___x_965_, 0, v___y_968_);
v___x_970_ = v___x_965_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___y_968_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_a_960_);
v___x_970_ = v_reuseFailAlloc_972_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
v_a_959_ = v_tail_963_;
v_a_960_ = v___x_970_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString(lean_object* v_ns_984_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_985_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0));
v___x_986_ = lean_box(0);
v___x_987_ = l_List_mapTR_loop___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString_spec__0(v_ns_984_, v___x_986_);
v___x_988_ = l_String_intercalate(v___x_985_, v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(lean_object* v_count_989_, lean_object* v_singular_990_, lean_object* v_plural_991_){
_start:
{
lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_992_ = lean_unsigned_to_nat(1u);
v___x_993_ = lean_nat_dec_eq(v_count_989_, v___x_992_);
if (v___x_993_ == 0)
{
lean_inc_ref(v_plural_991_);
return v_plural_991_;
}
else
{
lean_inc_ref(v_singular_990_);
return v_singular_990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1___boxed(lean_object* v_count_994_, lean_object* v_singular_995_, lean_object* v_plural_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v_count_994_, v_singular_995_, v_plural_996_);
lean_dec_ref(v_plural_996_);
lean_dec_ref(v_singular_995_);
lean_dec(v_count_994_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(lean_object* v___x_998_, lean_object* v_as_999_, size_t v_i_1000_, size_t v_stop_1001_, lean_object* v_b_1002_){
_start:
{
uint8_t v___x_1003_; 
v___x_1003_ = lean_usize_dec_eq(v_i_1000_, v_stop_1001_);
if (v___x_1003_ == 0)
{
size_t v___x_1004_; size_t v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = ((size_t)1ULL);
v___x_1005_ = lean_usize_sub(v_i_1000_, v___x_1004_);
v___x_1006_ = lean_array_uget_borrowed(v_as_999_, v___x_1005_);
if (lean_obj_tag(v___x_1006_) == 0)
{
v_i_1000_ = v___x_1005_;
goto _start;
}
else
{
lean_object* v_val_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v_val_1008_ = lean_ctor_get(v___x_1006_, 0);
v___x_1009_ = l_Lean_LocalDecl_fvarId(v_val_1008_);
v___x_1010_ = l_Lean_LocalContext_contains(v___x_998_, v___x_1009_);
lean_dec(v___x_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = l_Lean_LocalDecl_userName(v_val_1008_);
v___x_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v_b_1002_);
v_i_1000_ = v___x_1005_;
v_b_1002_ = v___x_1012_;
goto _start;
}
else
{
v_i_1000_ = v___x_1005_;
goto _start;
}
}
}
else
{
return v_b_1002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3___boxed(lean_object* v___x_1015_, lean_object* v_as_1016_, lean_object* v_i_1017_, lean_object* v_stop_1018_, lean_object* v_b_1019_){
_start:
{
size_t v_i_boxed_1020_; size_t v_stop_boxed_1021_; lean_object* v_res_1022_; 
v_i_boxed_1020_ = lean_unbox_usize(v_i_1017_);
lean_dec(v_i_1017_);
v_stop_boxed_1021_ = lean_unbox_usize(v_stop_1018_);
lean_dec(v_stop_1018_);
v_res_1022_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_1015_, v_as_1016_, v_i_boxed_1020_, v_stop_boxed_1021_, v_b_1019_);
lean_dec_ref(v_as_1016_);
lean_dec_ref(v___x_1015_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(lean_object* v___x_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_){
_start:
{
if (lean_obj_tag(v_x_1024_) == 0)
{
lean_object* v_cs_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v_cs_1026_ = lean_ctor_get(v_x_1024_, 0);
v___x_1027_ = lean_array_get_size(v_cs_1026_);
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = lean_nat_dec_lt(v___x_1028_, v___x_1027_);
if (v___x_1029_ == 0)
{
return v_x_1025_;
}
else
{
size_t v___x_1030_; size_t v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = lean_usize_of_nat(v___x_1027_);
v___x_1031_ = ((size_t)0ULL);
v___x_1032_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(v___x_1023_, v_cs_1026_, v___x_1030_, v___x_1031_, v_x_1025_);
return v___x_1032_;
}
}
else
{
lean_object* v_vs_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v_vs_1033_ = lean_ctor_get(v_x_1024_, 0);
v___x_1034_ = lean_array_get_size(v_vs_1033_);
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = lean_nat_dec_lt(v___x_1035_, v___x_1034_);
if (v___x_1036_ == 0)
{
return v_x_1025_;
}
else
{
size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = lean_usize_of_nat(v___x_1034_);
v___x_1038_ = ((size_t)0ULL);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_1023_, v_vs_1033_, v___x_1037_, v___x_1038_, v_x_1025_);
return v___x_1039_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(lean_object* v___x_1040_, lean_object* v_as_1041_, size_t v_i_1042_, size_t v_stop_1043_, lean_object* v_b_1044_){
_start:
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_usize_dec_eq(v_i_1042_, v_stop_1043_);
if (v___x_1045_ == 0)
{
size_t v___x_1046_; size_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1046_ = ((size_t)1ULL);
v___x_1047_ = lean_usize_sub(v_i_1042_, v___x_1046_);
v___x_1048_ = lean_array_uget_borrowed(v_as_1041_, v___x_1047_);
v___x_1049_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_1040_, v___x_1048_, v_b_1044_);
v_i_1042_ = v___x_1047_;
v_b_1044_ = v___x_1049_;
goto _start;
}
else
{
return v_b_1044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v___x_1051_, lean_object* v_as_1052_, lean_object* v_i_1053_, lean_object* v_stop_1054_, lean_object* v_b_1055_){
_start:
{
size_t v_i_boxed_1056_; size_t v_stop_boxed_1057_; lean_object* v_res_1058_; 
v_i_boxed_1056_ = lean_unbox_usize(v_i_1053_);
lean_dec(v_i_1053_);
v_stop_boxed_1057_ = lean_unbox_usize(v_stop_1054_);
lean_dec(v_stop_1054_);
v_res_1058_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(v___x_1051_, v_as_1052_, v_i_boxed_1056_, v_stop_boxed_1057_, v_b_1055_);
lean_dec_ref(v_as_1052_);
lean_dec_ref(v___x_1051_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2___boxed(lean_object* v___x_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_1059_, v_x_1060_, v_x_1061_);
lean_dec_ref(v_x_1060_);
lean_dec_ref(v___x_1059_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(lean_object* v___x_1063_, lean_object* v_t_1064_, lean_object* v_init_1065_){
_start:
{
lean_object* v_root_1066_; lean_object* v_tail_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_root_1066_ = lean_ctor_get(v_t_1064_, 0);
v_tail_1067_ = lean_ctor_get(v_t_1064_, 1);
v___x_1068_ = lean_array_get_size(v_tail_1067_);
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = lean_nat_dec_lt(v___x_1069_, v___x_1068_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
v___x_1071_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_1063_, v_root_1066_, v_init_1065_);
return v___x_1071_;
}
else
{
size_t v___x_1072_; size_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1072_ = lean_usize_of_nat(v___x_1068_);
v___x_1073_ = ((size_t)0ULL);
v___x_1074_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_1063_, v_tail_1067_, v___x_1072_, v___x_1073_, v_init_1065_);
v___x_1075_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_1063_, v_root_1066_, v___x_1074_);
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0___boxed(lean_object* v___x_1076_, lean_object* v_t_1077_, lean_object* v_init_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(v___x_1076_, v_t_1077_, v_init_1078_);
lean_dec_ref(v_t_1077_);
lean_dec_ref(v___x_1076_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(lean_object* v___x_1080_, lean_object* v_lctx_1081_, lean_object* v_init_1082_){
_start:
{
lean_object* v_decls_1083_; lean_object* v___x_1084_; 
v_decls_1083_ = lean_ctor_get(v_lctx_1081_, 1);
v___x_1084_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(v___x_1080_, v_decls_1083_, v_init_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0___boxed(lean_object* v___x_1085_, lean_object* v_lctx_1086_, lean_object* v_init_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(v___x_1085_, v_lctx_1086_, v_init_1087_);
lean_dec_ref(v_lctx_1086_);
lean_dec_ref(v___x_1085_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(lean_object* v_mdecl_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v_lctx_1097_; lean_object* v_lctx_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_lctx_1097_ = lean_ctor_get(v_a_1095_, 2);
v_lctx_1098_ = lean_ctor_get(v_mdecl_1094_, 1);
v___x_1099_ = lean_box(0);
v___x_1100_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(v_lctx_1097_, v_lctx_1098_, v___x_1099_);
v___x_1101_ = l_List_isEmpty___redArg(v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1102_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__0));
v___x_1103_ = l_List_lengthTR___redArg(v___x_1100_);
v___x_1104_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__1));
v___x_1105_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__2));
v___x_1106_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v___x_1103_, v___x_1104_, v___x_1105_);
lean_dec(v___x_1103_);
v___x_1107_ = lean_string_append(v___x_1102_, v___x_1106_);
lean_dec_ref(v___x_1106_);
v___x_1108_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__3));
v___x_1109_ = lean_string_append(v___x_1107_, v___x_1108_);
v___x_1110_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString(v___x_1100_);
v___x_1111_ = lean_string_append(v___x_1109_, v___x_1110_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec(v___x_1100_);
v___x_1113_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4));
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___boxed(lean_object* v_mdecl_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_mdecl_1115_, v_a_1116_);
lean_dec_ref(v_a_1116_);
lean_dec_ref(v_mdecl_1115_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars(lean_object* v_mdecl_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_mdecl_1119_, v_a_1120_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___boxed(lean_object* v_mdecl_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars(v_mdecl_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec_ref(v_mdecl_1126_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(lean_object* v_lctxInitIndices_1133_, lean_object* v_mdecl_1134_, lean_object* v_as_1135_, size_t v_i_1136_, size_t v_stop_1137_, lean_object* v_b_1138_){
_start:
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_usize_dec_eq(v_i_1136_, v_stop_1137_);
if (v___x_1139_ == 0)
{
size_t v___x_1140_; size_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = ((size_t)1ULL);
v___x_1141_ = lean_usize_sub(v_i_1136_, v___x_1140_);
v___x_1142_ = lean_array_uget_borrowed(v_as_1135_, v___x_1141_);
if (lean_obj_tag(v___x_1142_) == 0)
{
v_i_1136_ = v___x_1141_;
goto _start;
}
else
{
lean_object* v_val_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v_val_1144_ = lean_ctor_get(v___x_1142_, 0);
v___x_1145_ = l_Lean_LocalDecl_index(v_val_1144_);
v___x_1146_ = lean_nat_dec_le(v_lctxInitIndices_1133_, v___x_1145_);
lean_dec(v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v_lctx_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v_lctx_1147_ = lean_ctor_get(v_mdecl_1134_, 1);
v___x_1148_ = l_Lean_LocalDecl_fvarId(v_val_1144_);
v___x_1149_ = l_Lean_LocalContext_contains(v_lctx_1147_, v___x_1148_);
lean_dec(v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = l_Lean_LocalDecl_userName(v_val_1144_);
v___x_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set(v___x_1151_, 1, v_b_1138_);
v_i_1136_ = v___x_1141_;
v_b_1138_ = v___x_1151_;
goto _start;
}
else
{
v_i_1136_ = v___x_1141_;
goto _start;
}
}
else
{
v_i_1136_ = v___x_1141_;
goto _start;
}
}
}
else
{
return v_b_1138_;
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
lean_object* v_a_1346_; lean_object* v_lctx_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v_lctx_1347_ = lean_ctor_get(v_a_1346_, 1);
lean_inc_ref(v_lctx_1347_);
lean_dec(v_a_1346_);
v___x_1348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0));
v___x_1349_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_1347_, v___x_1328_, v___x_1348_);
lean_dec_ref(v_lctx_1347_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_inc(v___x_1344_);
v___x_1350_ = lean_array_push(v_b_1332_, v___x_1344_);
v_a_1339_ = v___x_1350_;
goto v___jp_1338_;
}
else
{
v_a_1339_ = v_b_1332_;
goto v___jp_1338_;
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v_b_1332_);
v_a_1351_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1345_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1345_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_b_1332_);
return v___x_1359_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___boxed(lean_object* v___x_1360_, lean_object* v_as_1361_, lean_object* v_i_1362_, lean_object* v_stop_1363_, lean_object* v_b_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
size_t v_i_boxed_1370_; size_t v_stop_boxed_1371_; lean_object* v_res_1372_; 
v_i_boxed_1370_ = lean_unbox_usize(v_i_1362_);
lean_dec(v_i_1362_);
v_stop_boxed_1371_ = lean_unbox_usize(v_stop_1363_);
lean_dec(v_stop_1363_);
v_res_1372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(v___x_1360_, v_as_1361_, v_i_boxed_1370_, v_stop_boxed_1371_, v_b_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec_ref(v_as_1361_);
lean_dec_ref(v___x_1360_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(lean_object* v_e_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_awaitingMVars_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_Meta_getMVarsNoDelayed(v_e_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v_a_1430_; lean_object* v___y_1435_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1427_, 1);
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = lean_array_get_size(v_a_1428_);
v___x_1447_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__4));
v___x_1448_ = lean_nat_dec_lt(v___x_1445_, v___x_1446_);
if (v___x_1448_ == 0)
{
v_a_1430_ = v___x_1447_;
goto v___jp_1429_;
}
else
{
lean_object* v_lctx_1449_; uint8_t v___x_1450_; 
v_lctx_1449_ = lean_ctor_get(v_a_1380_, 2);
v___x_1450_ = lean_nat_dec_le(v___x_1446_, v___x_1446_);
if (v___x_1450_ == 0)
{
if (v___x_1448_ == 0)
{
v_a_1430_ = v___x_1447_;
goto v___jp_1429_;
}
else
{
size_t v___x_1451_; size_t v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = ((size_t)0ULL);
v___x_1452_ = lean_usize_of_nat(v___x_1446_);
v___x_1453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(v_lctx_1449_, v_a_1428_, v___x_1451_, v___x_1452_, v___x_1447_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
v___y_1435_ = v___x_1453_;
goto v___jp_1434_;
}
}
else
{
size_t v___x_1454_; size_t v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = ((size_t)0ULL);
v___x_1455_ = lean_usize_of_nat(v___x_1446_);
v___x_1456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(v_lctx_1449_, v_a_1428_, v___x_1454_, v___x_1455_, v___x_1447_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
v___y_1435_ = v___x_1456_;
goto v___jp_1434_;
}
}
v___jp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1431_ = lean_array_get_size(v_a_1430_);
v___x_1432_ = lean_unsigned_to_nat(0u);
v___x_1433_ = lean_nat_dec_eq(v___x_1431_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_dec(v_a_1428_);
v_awaitingMVars_1386_ = v_a_1430_;
v___y_1387_ = v_a_1380_;
v___y_1388_ = v_a_1381_;
v___y_1389_ = v_a_1382_;
v___y_1390_ = v_a_1383_;
goto v___jp_1385_;
}
else
{
lean_dec_ref(v_a_1430_);
v_awaitingMVars_1386_ = v_a_1428_;
v___y_1387_ = v_a_1380_;
v___y_1388_ = v_a_1381_;
v___y_1389_ = v_a_1382_;
v___y_1390_ = v_a_1383_;
goto v___jp_1385_;
}
}
v___jp_1434_:
{
if (lean_obj_tag(v___y_1435_) == 0)
{
lean_object* v_a_1436_; 
v_a_1436_ = lean_ctor_get(v___y_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___y_1435_, 1);
v_a_1430_ = v_a_1436_;
goto v___jp_1429_;
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_a_1428_);
v_a_1437_ = lean_ctor_get(v___y_1435_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___y_1435_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___y_1435_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___y_1435_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
v_a_1457_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1427_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1427_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
v___jp_1385_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1391_ = lean_array_get_size(v_awaitingMVars_1386_);
v___x_1392_ = lean_unsigned_to_nat(0u);
v___x_1393_ = lean_nat_dec_eq(v___x_1391_, v___x_1392_);
if (v___x_1393_ == 0)
{
size_t v_sz_1394_; size_t v___x_1395_; lean_object* v___x_1396_; 
v_sz_1394_ = lean_array_size(v_awaitingMVars_1386_);
v___x_1395_ = ((size_t)0ULL);
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0(v_sz_1394_, v___x_1395_, v_awaitingMVars_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1416_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1416_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1416_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1401_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__0));
v___x_1402_ = lean_array_get_size(v_a_1397_);
v___x_1403_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__1));
v___x_1404_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__2));
v___x_1405_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v___x_1402_, v___x_1403_, v___x_1404_);
v___x_1406_ = lean_string_append(v___x_1401_, v___x_1405_);
lean_dec_ref(v___x_1405_);
v___x_1407_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__3));
v___x_1408_ = lean_string_append(v___x_1406_, v___x_1407_);
v___x_1409_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0));
v___x_1410_ = lean_array_to_list(v_a_1397_);
v___x_1411_ = l_String_intercalate(v___x_1409_, v___x_1410_);
v___x_1412_ = lean_string_append(v___x_1408_, v___x_1411_);
lean_dec_ref(v___x_1411_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1412_);
v___x_1414_ = v___x_1399_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
v_a_1417_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1396_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1396_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec_ref(v_awaitingMVars_1386_);
v___x_1425_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4));
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___boxed(lean_object* v_e_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_e_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(lean_object* v_mvarId_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v___x_1475_; lean_object* v_mctx_1476_; lean_object* v_decl_1477_; lean_object* v_depth_1478_; lean_object* v_depth_1479_; uint8_t v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1475_ = lean_st_ref_get(v___y_1473_);
v_mctx_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc_ref(v_mctx_1476_);
lean_dec(v___x_1475_);
v_decl_1477_ = l_Lean_MetavarContext_getDecl(v_mctx_1476_, v_mvarId_1472_);
v_depth_1478_ = lean_ctor_get(v_decl_1477_, 3);
lean_inc(v_depth_1478_);
lean_dec_ref(v_decl_1477_);
v_depth_1479_ = lean_ctor_get(v_mctx_1476_, 0);
lean_inc(v_depth_1479_);
lean_dec_ref(v_mctx_1476_);
v___x_1480_ = lean_nat_dec_eq(v_depth_1478_, v_depth_1479_);
lean_dec(v_depth_1479_);
lean_dec(v_depth_1478_);
v___x_1481_ = lean_box(v___x_1480_);
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg___boxed(lean_object* v_mvarId_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_1483_, v___y_1484_);
lean_dec(v___y_1484_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0(lean_object* v_mvarId_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_1487_, v___y_1489_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___boxed(lean_object* v_mvarId_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0(v_mvarId_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar(lean_object* v_mvarId_1514_, lean_object* v_lctxInitIndices_1515_, uint8_t v_fromDelayed_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_delayedExpl_1522_; lean_object* v___x_1523_; 
v_delayedExpl_1522_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__0));
v___x_1523_ = l_Lean_MVarId_findDecl_x3f___redArg(v_mvarId_1514_, v_a_1518_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1683_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1683_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1683_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
if (lean_obj_tag(v_a_1524_) == 1)
{
lean_object* v_val_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1678_; 
lean_del_object(v___x_1526_);
v_val_1528_ = lean_ctor_get(v_a_1524_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_a_1524_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1530_ = v_a_1524_;
v_isShared_1531_ = v_isSharedCheck_1678_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_val_1528_);
lean_dec(v_a_1524_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1678_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v_msg_1546_; lean_object* v___y_1547_; lean_object* v_msg_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; uint8_t v___y_1593_; lean_object* v_msg_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___x_1611_; lean_object* v_a_1612_; 
v___x_1611_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_1514_, v_a_1518_);
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref(v___x_1611_);
if (lean_obj_tag(v_a_1612_) == 1)
{
lean_object* v_val_1613_; lean_object* v_mvarIdPending_1614_; lean_object* v___x_1615_; 
lean_del_object(v___x_1530_);
lean_dec(v_val_1528_);
lean_dec(v_mvarId_1514_);
v_val_1613_ = lean_ctor_get(v_a_1612_, 0);
lean_inc(v_val_1613_);
lean_dec_ref_known(v_a_1612_, 1);
v_mvarIdPending_1614_ = lean_ctor_get(v_val_1613_, 1);
lean_inc(v_mvarIdPending_1614_);
lean_dec(v_val_1613_);
v___x_1615_ = l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(v_mvarIdPending_1614_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1617_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v___x_1617_ = l_Lean_MVarId_findDecl_x3f___redArg(v_a_1616_, v_a_1518_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1657_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1657_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1657_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
if (lean_obj_tag(v_a_1618_) == 1)
{
lean_object* v_val_1622_; lean_object* v_msg_1624_; lean_object* v___y_1625_; lean_object* v_a_1637_; lean_object* v___x_1649_; 
lean_del_object(v___x_1620_);
v_val_1622_ = lean_ctor_get(v_a_1618_, 0);
lean_inc(v_val_1622_);
lean_dec_ref_known(v_a_1618_, 1);
lean_inc(v_a_1616_);
v___x_1649_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(v_a_1616_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1651_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v___x_1651_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v_a_1650_);
lean_dec(v_a_1650_);
v_a_1637_ = v___x_1651_;
goto v___jp_1636_;
}
else
{
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1652_; 
v_a_1652_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1649_, 1);
v_a_1637_ = v_a_1652_;
goto v___jp_1636_;
}
else
{
lean_dec(v_val_1622_);
lean_dec(v_a_1616_);
return v___x_1649_;
}
}
v___jp_1623_:
{
lean_object* v___x_1626_; lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1635_; 
v___x_1626_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_val_1622_, v___y_1625_);
lean_dec(v_val_1622_);
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1629_ = v___x_1626_;
v_isShared_1630_ = v_isSharedCheck_1635_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1635_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1631_ = lean_string_append(v_msg_1624_, v_a_1627_);
lean_dec(v_a_1627_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1631_);
v___x_1633_ = v___x_1629_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
v___jp_1636_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_a_1644_; 
v___x_1638_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6));
v___x_1639_ = lean_string_append(v___x_1638_, v_a_1637_);
lean_dec_ref(v_a_1637_);
v___x_1640_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7));
v___x_1641_ = lean_string_append(v___x_1639_, v___x_1640_);
v___x_1642_ = lean_string_append(v___x_1641_, v_delayedExpl_1522_);
v___x_1643_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_a_1616_, v_a_1518_);
lean_dec(v_a_1616_);
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref(v___x_1643_);
if (lean_obj_tag(v_a_1644_) == 1)
{
lean_object* v_val_1645_; lean_object* v___x_1646_; 
v_val_1645_ = lean_ctor_get(v_a_1644_, 0);
lean_inc(v_val_1645_);
lean_dec_ref_known(v_a_1644_, 1);
v___x_1646_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_val_1645_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1648_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v___x_1646_, 1);
v___x_1648_ = lean_string_append(v___x_1642_, v_a_1647_);
lean_dec(v_a_1647_);
v_msg_1624_ = v___x_1648_;
v___y_1625_ = v_a_1517_;
goto v___jp_1623_;
}
else
{
lean_dec_ref(v___x_1642_);
lean_dec(v_val_1622_);
return v___x_1646_;
}
}
else
{
lean_dec(v_a_1644_);
v_msg_1624_ = v___x_1642_;
v___y_1625_ = v_a_1517_;
goto v___jp_1623_;
}
}
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1655_; 
lean_dec(v_a_1618_);
lean_dec(v_a_1616_);
v___x_1653_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__8));
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1653_);
v___x_1655_ = v___x_1620_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v_a_1616_);
v_a_1658_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1617_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1617_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v_a_1666_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1615_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1615_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
uint8_t v_kind_1674_; 
lean_dec(v_a_1612_);
v_kind_1674_ = lean_ctor_get_uint8(v_val_1528_, sizeof(void*)*7);
switch(v_kind_1674_)
{
case 0:
{
lean_object* v___x_1675_; 
v___x_1675_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__9));
v_msg_1597_ = v___x_1675_;
v___y_1598_ = v_a_1517_;
v___y_1599_ = v_a_1518_;
v___y_1600_ = v_a_1519_;
v___y_1601_ = v_a_1520_;
goto v___jp_1596_;
}
case 1:
{
lean_object* v___x_1676_; 
v___x_1676_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__10));
v_msg_1597_ = v___x_1676_;
v___y_1598_ = v_a_1517_;
v___y_1599_ = v_a_1518_;
v___y_1600_ = v_a_1519_;
v___y_1601_ = v_a_1520_;
goto v___jp_1596_;
}
default: 
{
lean_object* v___x_1677_; 
v___x_1677_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__11));
v_msg_1597_ = v___x_1677_;
v___y_1598_ = v_a_1517_;
v___y_1599_ = v_a_1518_;
v___y_1600_ = v_a_1519_;
v___y_1601_ = v_a_1520_;
goto v___jp_1596_;
}
}
}
v___jp_1532_:
{
lean_object* v___x_1535_; lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1544_; 
v___x_1535_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(v_lctxInitIndices_1515_, v_val_1528_, v___y_1534_);
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
v___jp_1545_:
{
if (v_fromDelayed_1516_ == 0)
{
v___y_1533_ = v_msg_1546_;
v___y_1534_ = v___y_1547_;
goto v___jp_1532_;
}
else
{
lean_object* v_lctx_1548_; lean_object* v_lctx_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v_lctx_1548_ = lean_ctor_get(v___y_1547_, 2);
v_lctx_1549_ = lean_ctor_get(v_val_1528_, 1);
v___x_1550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0));
v___x_1551_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_1549_, v_lctx_1548_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
v___x_1552_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_val_1528_, v___y_1547_);
lean_dec(v_val_1528_);
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_string_append(v_msg_1546_, v_a_1553_);
lean_dec(v_a_1553_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1557_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
else
{
v___y_1533_ = v_msg_1546_;
v___y_1534_ = v___y_1547_;
goto v___jp_1532_;
}
}
}
v___jp_1562_:
{
lean_object* v___x_1568_; lean_object* v_a_1569_; 
v___x_1568_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarId_1514_, v___y_1565_);
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref(v___x_1568_);
if (lean_obj_tag(v_a_1569_) == 1)
{
lean_dec(v_mvarId_1514_);
if (v_fromDelayed_1516_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec_ref_known(v_a_1569_, 1);
v___x_1570_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1));
v___x_1571_ = lean_string_append(v_msg_1563_, v___x_1570_);
v_msg_1546_ = v___x_1571_;
v___y_1547_ = v___y_1564_;
goto v___jp_1545_;
}
else
{
lean_object* v_val_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_val_1572_ = lean_ctor_get(v_a_1569_, 0);
lean_inc(v_val_1572_);
lean_dec_ref_known(v_a_1569_, 1);
v___x_1573_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2));
v___x_1574_ = lean_string_append(v_msg_1563_, v___x_1573_);
v___x_1575_ = lean_string_append(v___x_1574_, v_delayedExpl_1522_);
v___x_1576_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_val_1572_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1578_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1576_, 1);
v___x_1578_ = lean_string_append(v___x_1575_, v_a_1577_);
lean_dec(v_a_1577_);
v_msg_1546_ = v___x_1578_;
v___y_1547_ = v___y_1564_;
goto v___jp_1545_;
}
else
{
lean_dec_ref(v___x_1575_);
lean_dec(v_val_1528_);
return v___x_1576_;
}
}
}
else
{
lean_object* v___x_1579_; lean_object* v_a_1580_; uint8_t v___x_1581_; 
lean_dec(v_a_1569_);
v___x_1579_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_1514_, v___y_1565_);
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref(v___x_1579_);
v___x_1581_ = lean_unbox(v_a_1580_);
lean_dec(v_a_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3));
v___x_1583_ = lean_string_append(v_msg_1563_, v___x_1582_);
v_msg_1546_ = v___x_1583_;
v___y_1547_ = v___y_1564_;
goto v___jp_1545_;
}
else
{
if (v_fromDelayed_1516_ == 0)
{
v_msg_1546_ = v_msg_1563_;
v___y_1547_ = v___y_1564_;
goto v___jp_1545_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4));
v___x_1585_ = lean_string_append(v_msg_1563_, v___x_1584_);
v___x_1586_ = lean_string_append(v___x_1585_, v_delayedExpl_1522_);
v_msg_1546_ = v___x_1586_;
v___y_1547_ = v___y_1564_;
goto v___jp_1545_;
}
}
}
}
v___jp_1587_:
{
if (v___y_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5));
lean_inc_ref(v___y_1591_);
v___x_1595_ = lean_string_append(v___y_1591_, v___x_1594_);
v_msg_1563_ = v___x_1595_;
v___y_1564_ = v___y_1590_;
v___y_1565_ = v___y_1592_;
v___y_1566_ = v___y_1589_;
v___y_1567_ = v___y_1588_;
goto v___jp_1562_;
}
else
{
lean_inc_ref(v___y_1591_);
v_msg_1563_ = v___y_1591_;
v___y_1564_ = v___y_1590_;
v___y_1565_ = v___y_1592_;
v___y_1566_ = v___y_1589_;
v___y_1567_ = v___y_1588_;
goto v___jp_1562_;
}
}
v___jp_1596_:
{
lean_object* v___x_1602_; lean_object* v_userName_1603_; uint8_t v___x_1604_; 
v___x_1602_ = lean_st_ref_get(v___y_1599_);
v_userName_1603_ = lean_ctor_get(v_val_1528_, 0);
v___x_1604_ = l_Lean_Name_isAnonymous(v_userName_1603_);
if (v___x_1604_ == 0)
{
lean_object* v_mctx_1605_; lean_object* v___x_1607_; 
v_mctx_1605_ = lean_ctor_get(v___x_1602_, 0);
lean_inc_ref(v_mctx_1605_);
lean_dec(v___x_1602_);
lean_inc(v_mvarId_1514_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v_mvarId_1514_);
v___x_1607_ = v___x_1530_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_mvarId_1514_);
v___x_1607_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = l_Lean_MetavarContext_findUserName_x3f(v_mctx_1605_, v_userName_1603_);
lean_dec_ref(v_mctx_1605_);
v___x_1609_ = l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(v___x_1607_, v___x_1608_);
lean_dec(v___x_1608_);
lean_dec_ref(v___x_1607_);
v___y_1588_ = v___y_1601_;
v___y_1589_ = v___y_1600_;
v___y_1590_ = v___y_1598_;
v___y_1591_ = v_msg_1597_;
v___y_1592_ = v___y_1599_;
v___y_1593_ = v___x_1609_;
goto v___jp_1587_;
}
}
else
{
lean_dec(v___x_1602_);
lean_del_object(v___x_1530_);
v___y_1588_ = v___y_1601_;
v___y_1589_ = v___y_1600_;
v___y_1590_ = v___y_1598_;
v___y_1591_ = v_msg_1597_;
v___y_1592_ = v___y_1599_;
v___y_1593_ = v___x_1604_;
goto v___jp_1587_;
}
}
}
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
lean_dec(v_a_1524_);
lean_dec(v_mvarId_1514_);
v___x_1679_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__12));
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1679_);
v___x_1681_ = v___x_1526_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_dec(v_mvarId_1514_);
v_a_1684_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1523_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1523_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___boxed(lean_object* v_mvarId_1692_, lean_object* v_lctxInitIndices_1693_, lean_object* v_fromDelayed_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
uint8_t v_fromDelayed_boxed_1700_; lean_object* v_res_1701_; 
v_fromDelayed_boxed_1700_ = lean_unbox(v_fromDelayed_1694_);
v_res_1701_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar(v_mvarId_1692_, v_lctxInitIndices_1693_, v_fromDelayed_boxed_1700_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_lctxInitIndices_1693_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0(lean_object* v_mvarId_1702_, lean_object* v_lctxInitIndices_1703_, uint8_t v_fromDelayed_1704_, lean_object* v_ppCtx_1705_){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = lean_box(v_fromDelayed_1704_);
v___x_1708_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___boxed), 8, 3);
lean_closure_set(v___x_1708_, 0, v_mvarId_1702_);
lean_closure_set(v___x_1708_, 1, v_lctxInitIndices_1703_);
lean_closure_set(v___x_1708_, 2, v___x_1707_);
v___x_1709_ = l_Lean_PPContext_runMetaM___redArg(v_ppCtx_1705_, v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0___boxed(lean_object* v_mvarId_1710_, lean_object* v_lctxInitIndices_1711_, lean_object* v_fromDelayed_1712_, lean_object* v_ppCtx_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v_fromDelayed_boxed_1715_; lean_object* v_res_1716_; 
v_fromDelayed_boxed_1715_ = lean_unbox(v_fromDelayed_1712_);
v_res_1716_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0(v_mvarId_1710_, v_lctxInitIndices_1711_, v_fromDelayed_boxed_1715_, v_ppCtx_1713_);
lean_dec_ref(v_ppCtx_1713_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(lean_object* v_mvarId_1717_, uint8_t v_fromDelayed_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v_lctxInitIndices_1721_; lean_object* v___x_1722_; lean_object* v___f_1723_; lean_object* v___x_1724_; 
v_lctxInitIndices_1721_ = lean_ctor_get(v_a_1719_, 5);
v___x_1722_ = lean_box(v_fromDelayed_1718_);
lean_inc(v_lctxInitIndices_1721_);
v___f_1723_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1723_, 0, v_mvarId_1717_);
lean_closure_set(v___f_1723_, 1, v_lctxInitIndices_1721_);
lean_closure_set(v___f_1723_, 2, v___x_1722_);
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v___f_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___boxed(lean_object* v_mvarId_1725_, lean_object* v_fromDelayed_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
uint8_t v_fromDelayed_boxed_1729_; lean_object* v_res_1730_; 
v_fromDelayed_boxed_1729_ = lean_unbox(v_fromDelayed_1726_);
v_res_1730_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(v_mvarId_1725_, v_fromDelayed_boxed_1729_, v_a_1727_);
lean_dec_ref(v_a_1727_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar(lean_object* v_mvarId_1731_, uint8_t v_fromDelayed_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(v_mvarId_1731_, v_fromDelayed_1732_, v_a_1733_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___boxed(lean_object* v_mvarId_1741_, lean_object* v_fromDelayed_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
uint8_t v_fromDelayed_boxed_1750_; lean_object* v_res_1751_; 
v_fromDelayed_boxed_1750_ = lean_unbox(v_fromDelayed_1742_);
v_res_1751_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar(v_mvarId_1741_, v_fromDelayed_boxed_1750_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
lean_dec(v_a_1748_);
lean_dec_ref(v_a_1747_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
return v_res_1751_;
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
