// Lean compiler output
// Module: Lean.Elab.Tactic.Match
// Imports: public import Lean.Elab.Match public import Lean.Elab.Tactic.Induction
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTag___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rhs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__11;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(149, 22, 109, 211, 70, 26, 115, 13)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "case"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(216, 244, 120, 128, 139, 198, 139, 51)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caseArg"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__16_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(151, 119, 254, 229, 232, 21, 225, 201)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__19_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__19_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__20;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__22_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__22_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "withAnnotateState"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__26_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(27, 100, 151, 108, 10, 177, 75, 150)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "with_annotate_state"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__28_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "skip"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__29_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__29_value),LEAN_SCALAR_PTR_LITERAL(244, 42, 145, 170, 145, 147, 228, 105)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__31_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__31_value),LEAN_SCALAR_PTR_LITERAL(121, 5, 219, 45, 43, 52, 169, 192)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__32_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__0_value),((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__31_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__4_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalMatch___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalMatch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__0_value;
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__1 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__13;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "refine"};
static const lean_object* l_Lean_Elab_Tactic_evalMatch___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalMatch___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalMatch___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalMatch___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalMatch___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalMatch___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalMatch___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalMatch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalMatch___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalMatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 130, 130, 160, 131, 48, 178, 245)}};
static const lean_object* l_Lean_Elab_Tactic_evalMatch___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalMatch___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalMatch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "noImplicitLambda"};
static const lean_object* l_Lean_Elab_Tactic_evalMatch___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalMatch___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalMatch___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalMatch___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalMatch___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalMatch___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalMatch___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalMatch___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalMatch___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalMatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(138, 103, 178, 9, 238, 93, 41, 6)}};
static const lean_object* l_Lean_Elab_Tactic_evalMatch___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalMatch___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_evalMatch___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "no_implicit_lambda%"};
static const lean_object* l_Lean_Elab_Tactic_evalMatch___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalMatch___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__31_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 240, 216, 203, 28, 130, 220)}};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalMatch"};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 83, 146, 191, 89, 201, 129, 152)}};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(58) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__1_value),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)(((size_t)(13) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__4_value),((lean_object*)(((size_t)(13) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___boxed(lean_object*);
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__11(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__10));
v___x_22_ = l_String_toRawSubstring_x27(v___x_21_);
return v___x_22_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__20(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Array_mkArray0(lean_box(0));
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0(lean_object* v___x_72_, lean_object* v___x_73_, lean_object* v_alts_74_, lean_object* v_parentTag_75_, lean_object* v_as_76_, size_t v_sz_77_, size_t v_i_78_, lean_object* v_b_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = lean_usize_dec_lt(v_i_78_, v_sz_77_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; 
lean_dec(v_parentTag_75_);
lean_dec(v___x_73_);
lean_dec(v___x_72_);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v_b_79_);
lean_ctor_set(v___x_83_, 1, v___y_81_);
return v___x_83_;
}
else
{
lean_object* v_fst_84_; lean_object* v_snd_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_198_; 
v_fst_84_ = lean_ctor_get(v_b_79_, 0);
v_snd_85_ = lean_ctor_get(v_b_79_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v_b_79_);
if (v_isSharedCheck_198_ == 0)
{
v___x_87_ = v_b_79_;
v_isShared_88_ = v_isSharedCheck_198_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_snd_85_);
lean_inc(v_fst_84_);
lean_dec(v_b_79_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_198_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v_nextIdx_90_; lean_object* v_newCases_91_; lean_object* v_alt_92_; lean_object* v___y_93_; lean_object* v_fst_102_; lean_object* v_snd_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_197_; 
v_fst_102_ = lean_ctor_get(v_snd_85_, 0);
v_snd_103_ = lean_ctor_get(v_snd_85_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v_snd_85_);
if (v_isSharedCheck_197_ == 0)
{
v___x_105_ = v_snd_85_;
v_isShared_106_ = v_isSharedCheck_197_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_snd_103_);
lean_inc(v_fst_102_);
lean_dec(v_snd_85_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_197_;
goto v_resetjp_104_;
}
v___jp_89_:
{
lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_94_ = lean_array_push(v_fst_84_, v_alt_92_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 1, v_newCases_91_);
lean_ctor_set(v___x_87_, 0, v_nextIdx_90_);
v___x_96_ = v___x_87_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_nextIdx_90_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_newCases_91_);
v___x_96_ = v_reuseFailAlloc_101_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_97_; size_t v___x_98_; size_t v___x_99_; 
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_94_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = ((size_t)1ULL);
v___x_99_ = lean_usize_add(v_i_78_, v___x_98_);
v_i_78_ = v___x_99_;
v_b_79_ = v___x_97_;
v___y_81_ = v___y_93_;
goto _start;
}
}
v_resetjp_104_:
{
lean_object* v_nextIdx_107_; lean_object* v_a_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_nextIdx_107_ = lean_unsigned_to_nat(1u);
v_a_108_ = lean_array_uget_borrowed(v_as_76_, v_i_78_);
v___x_109_ = lean_mk_empty_array_with_capacity(v_nextIdx_107_);
lean_inc(v_a_108_);
v___x_110_ = lean_array_push(v___x_109_, v_a_108_);
v___x_111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__4));
v___x_112_ = lean_box(2);
v___x_113_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___x_111_);
lean_ctor_set(v___x_113_, 2, v___x_110_);
lean_inc(v___x_72_);
v___x_114_ = l_Lean_Syntax_setArg(v___x_72_, v_nextIdx_107_, v___x_113_);
v___x_115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6));
lean_inc(v___x_73_);
v___x_116_ = l_Lean_Syntax_isOfKind(v___x_73_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___y_119_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_117_ = lean_unsigned_to_nat(3u);
v___x_130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9));
lean_inc(v___x_73_);
v___x_131_ = l_Lean_Syntax_isOfKind(v___x_73_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v_macroScope_132_; lean_object* v_traceMsgs_133_; lean_object* v_expandedMacroDecls_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_191_; 
lean_del_object(v___x_105_);
v_macroScope_132_ = lean_ctor_get(v___y_81_, 0);
v_traceMsgs_133_ = lean_ctor_get(v___y_81_, 1);
v_expandedMacroDecls_134_ = lean_ctor_get(v___y_81_, 2);
v_isSharedCheck_191_ = !lean_is_exclusive(v___y_81_);
if (v_isSharedCheck_191_ == 0)
{
v___x_136_ = v___y_81_;
v_isShared_137_ = v_isSharedCheck_191_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_expandedMacroDecls_134_);
lean_inc(v_traceMsgs_133_);
lean_inc(v_macroScope_132_);
lean_dec(v___y_81_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_191_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v_quotContext_138_; lean_object* v_ref_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v_quotContext_138_ = lean_ctor_get(v___y_80_, 1);
v_ref_139_ = lean_ctor_get(v___y_80_, 5);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_nat_add(v_macroScope_132_, v_nextIdx_107_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_141_);
v___x_143_ = v___x_136_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_traceMsgs_133_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_expandedMacroDecls_134_);
v___x_143_ = v_reuseFailAlloc_190_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_144_ = l_Lean_SourceInfo_fromRef(v_ref_139_, v___x_131_);
v___x_145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__7));
lean_inc_n(v___x_144_, 15);
v___x_146_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__11);
v___x_148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__12));
lean_inc(v_quotContext_138_);
v___x_149_ = l_Lean_addMacroScope(v_quotContext_138_, v___x_148_, v_macroScope_132_);
v___x_150_ = lean_box(0);
v___x_151_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_151_, 0, v___x_144_);
lean_ctor_set(v___x_151_, 1, v___x_147_);
lean_ctor_set(v___x_151_, 2, v___x_149_);
lean_ctor_set(v___x_151_, 3, v___x_150_);
v___x_152_ = l_Lean_Syntax_node2(v___x_144_, v___x_115_, v___x_146_, v___x_151_);
v___x_153_ = l_Lean_Syntax_getArg(v___x_152_, v_nextIdx_107_);
v___x_154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__14));
v___x_155_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15));
v___x_156_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_144_);
lean_ctor_set(v___x_156_, 1, v___x_154_);
v___x_157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17));
v___x_158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__19));
v___x_159_ = l_Lean_Syntax_node1(v___x_144_, v___x_158_, v___x_153_);
v___x_160_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__20, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__20_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__20);
v___x_161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_161_, 0, v___x_144_);
lean_ctor_set(v___x_161_, 1, v___x_111_);
lean_ctor_set(v___x_161_, 2, v___x_160_);
lean_inc_ref(v___x_161_);
v___x_162_ = l_Lean_Syntax_node2(v___x_144_, v___x_157_, v___x_159_, v___x_161_);
v___x_163_ = l_Lean_Syntax_node1(v___x_144_, v___x_111_, v___x_162_);
v___x_164_ = lean_unsigned_to_nat(2u);
v___x_165_ = l_Lean_Syntax_getArg(v___x_114_, v___x_164_);
v___x_166_ = l_Lean_SourceInfo_fromRef(v___x_165_, v___x_82_);
v___x_167_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__21));
v___x_168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23));
v___x_170_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25));
v___x_171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27));
v___x_172_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__28));
v___x_173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_144_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = l_Lean_Syntax_getArg(v___x_114_, v___x_140_);
v___x_175_ = lean_mk_empty_array_with_capacity(v___x_164_);
v___x_176_ = lean_array_push(v___x_175_, v___x_174_);
v___x_177_ = lean_array_push(v___x_176_, v___x_165_);
v___x_178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_112_);
lean_ctor_set(v___x_178_, 1, v___x_111_);
lean_ctor_set(v___x_178_, 2, v___x_177_);
v___x_179_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__29));
v___x_180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30));
v___x_181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_144_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
v___x_182_ = l_Lean_Syntax_node1(v___x_144_, v___x_180_, v___x_181_);
v___x_183_ = l_Lean_Syntax_node3(v___x_144_, v___x_171_, v___x_173_, v___x_178_, v___x_182_);
lean_inc(v___x_73_);
v___x_184_ = l_Lean_Syntax_node3(v___x_144_, v___x_111_, v___x_183_, v___x_161_, v___x_73_);
v___x_185_ = l_Lean_Syntax_node1(v___x_144_, v___x_170_, v___x_184_);
v___x_186_ = l_Lean_Syntax_node1(v___x_144_, v___x_169_, v___x_185_);
v___x_187_ = l_Lean_Syntax_node4(v___x_144_, v___x_155_, v___x_156_, v___x_163_, v___x_168_, v___x_186_);
v___x_188_ = lean_array_push(v_snd_103_, v___x_187_);
v___x_189_ = l_Lean_Syntax_setArg(v___x_114_, v___x_117_, v___x_152_);
v_nextIdx_90_ = v_fst_102_;
v_newCases_91_ = v___x_188_;
v_alt_92_ = v___x_189_;
v___y_93_ = v___x_143_;
goto v___jp_89_;
}
}
}
else
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_array_get_size(v_alts_74_);
v___x_193_ = lean_nat_dec_lt(v_nextIdx_107_, v___x_192_);
if (v___x_193_ == 0)
{
lean_inc(v_parentTag_75_);
v___y_119_ = v_parentTag_75_;
goto v___jp_118_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__32));
lean_inc(v_fst_102_);
v___x_195_ = lean_name_append_index_after(v___x_194_, v_fst_102_);
lean_inc(v_parentTag_75_);
v___x_196_ = l_Lean_Name_append(v_parentTag_75_, v___x_195_);
v___y_119_ = v___x_196_;
goto v___jp_118_;
}
}
v___jp_118_:
{
lean_object* v_ref_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
v_ref_120_ = lean_ctor_get(v___y_80_, 5);
v___x_121_ = l_Lean_mkIdentFrom(v___x_73_, v___y_119_, v___x_116_);
v___x_122_ = l_Lean_SourceInfo_fromRef(v_ref_120_, v___x_116_);
v___x_123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__7));
lean_inc(v___x_122_);
if (v_isShared_106_ == 0)
{
lean_ctor_set_tag(v___x_105_, 2);
lean_ctor_set(v___x_105_, 1, v___x_123_);
lean_ctor_set(v___x_105_, 0, v___x_122_);
v___x_125_ = v___x_105_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_123_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = l_Lean_Syntax_node2(v___x_122_, v___x_115_, v___x_125_, v___x_121_);
v___x_127_ = lean_nat_add(v_fst_102_, v_nextIdx_107_);
lean_dec(v_fst_102_);
v___x_128_ = l_Lean_Syntax_setArg(v___x_114_, v___x_117_, v___x_126_);
v_nextIdx_90_ = v___x_127_;
v_newCases_91_ = v_snd_103_;
v_alt_92_ = v___x_128_;
v___y_93_ = v___y_81_;
goto v___jp_89_;
}
}
}
else
{
lean_del_object(v___x_105_);
v_nextIdx_90_ = v_fst_102_;
v_newCases_91_ = v_snd_103_;
v_alt_92_ = v___x_114_;
v___y_93_ = v___y_81_;
goto v___jp_89_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___boxed(lean_object* v___x_199_, lean_object* v___x_200_, lean_object* v_alts_201_, lean_object* v_parentTag_202_, lean_object* v_as_203_, lean_object* v_sz_204_, lean_object* v_i_205_, lean_object* v_b_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
size_t v_sz_boxed_209_; size_t v_i_boxed_210_; lean_object* v_res_211_; 
v_sz_boxed_209_ = lean_unbox_usize(v_sz_204_);
lean_dec(v_sz_204_);
v_i_boxed_210_ = lean_unbox_usize(v_i_205_);
lean_dec(v_i_205_);
v_res_211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0(v___x_199_, v___x_200_, v_alts_201_, v_parentTag_202_, v_as_203_, v_sz_boxed_209_, v_i_boxed_210_, v_b_206_, v___y_207_, v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec_ref(v_as_203_);
lean_dec_ref(v_alts_201_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1(lean_object* v_alts_218_, lean_object* v_parentTag_219_, lean_object* v_as_220_, size_t v_sz_221_, size_t v_i_222_, lean_object* v_b_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
uint8_t v___x_226_; 
v___x_226_ = lean_usize_dec_lt(v_i_222_, v_sz_221_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; 
lean_dec(v_parentTag_219_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v_b_223_);
lean_ctor_set(v___x_227_, 1, v___y_225_);
return v___x_227_;
}
else
{
lean_object* v_snd_228_; lean_object* v_fst_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_280_; 
v_snd_228_ = lean_ctor_get(v_b_223_, 1);
v_fst_229_ = lean_ctor_get(v_b_223_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v_b_223_);
if (v_isSharedCheck_280_ == 0)
{
v___x_231_ = v_b_223_;
v_isShared_232_ = v_isSharedCheck_280_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_snd_228_);
lean_inc(v_fst_229_);
lean_dec(v_b_223_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_280_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v_fst_233_; lean_object* v_snd_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_279_; 
v_fst_233_ = lean_ctor_get(v_snd_228_, 0);
v_snd_234_ = lean_ctor_get(v_snd_228_, 1);
v_isSharedCheck_279_ = !lean_is_exclusive(v_snd_228_);
if (v_isSharedCheck_279_ == 0)
{
v___x_236_ = v_snd_228_;
v_isShared_237_ = v_isSharedCheck_279_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_snd_234_);
lean_inc(v_fst_233_);
lean_dec(v_snd_228_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_279_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v_nextIdx_238_; lean_object* v_a_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v_nextIdx_238_ = lean_unsigned_to_nat(1u);
v_a_239_ = lean_array_uget_borrowed(v_as_220_, v_i_222_);
v___x_240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1));
lean_inc(v_a_239_);
v___x_241_ = l_Lean_Syntax_setKind(v_a_239_, v___x_240_);
v___x_242_ = lean_unsigned_to_nat(3u);
v___x_243_ = l_Lean_Syntax_getArg(v___x_241_, v___x_242_);
v___x_244_ = l_Lean_Syntax_getArg(v___x_241_, v_nextIdx_238_);
v___x_245_ = l_Lean_Syntax_getSepArgs(v___x_244_);
lean_dec(v___x_244_);
if (v_isShared_237_ == 0)
{
v___x_247_ = v___x_236_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_fst_233_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_snd_234_);
v___x_247_ = v_reuseFailAlloc_278_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_249_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 1, v___x_247_);
v___x_249_ = v___x_231_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_fst_229_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_247_);
v___x_249_ = v_reuseFailAlloc_277_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
size_t v_sz_250_; size_t v___x_251_; lean_object* v___x_252_; 
v_sz_250_ = lean_array_size(v___x_245_);
v___x_251_ = ((size_t)0ULL);
lean_inc(v_parentTag_219_);
v___x_252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0(v___x_241_, v___x_243_, v_alts_218_, v_parentTag_219_, v___x_245_, v_sz_250_, v___x_251_, v___x_249_, v___y_224_, v___y_225_);
lean_dec_ref(v___x_245_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v_snd_254_; lean_object* v_a_255_; lean_object* v_fst_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_275_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
v_snd_254_ = lean_ctor_get(v_a_253_, 1);
lean_inc(v_snd_254_);
v_a_255_ = lean_ctor_get(v___x_252_, 1);
lean_inc(v_a_255_);
lean_dec_ref_known(v___x_252_, 2);
v_fst_256_ = lean_ctor_get(v_a_253_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v_a_253_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v_a_253_, 1);
lean_dec(v_unused_276_);
v___x_258_ = v_a_253_;
v_isShared_259_ = v_isSharedCheck_275_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_fst_256_);
lean_dec(v_a_253_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_275_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v_fst_260_; lean_object* v_snd_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_274_; 
v_fst_260_ = lean_ctor_get(v_snd_254_, 0);
v_snd_261_ = lean_ctor_get(v_snd_254_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_snd_254_);
if (v_isSharedCheck_274_ == 0)
{
v___x_263_ = v_snd_254_;
v_isShared_264_ = v_isSharedCheck_274_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_snd_261_);
lean_inc(v_fst_260_);
lean_dec(v_snd_254_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_274_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_fst_260_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_snd_261_);
v___x_266_ = v_reuseFailAlloc_273_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_268_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v___x_266_);
v___x_268_ = v___x_258_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_fst_256_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v___x_266_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
size_t v___x_269_; size_t v___x_270_; 
v___x_269_ = ((size_t)1ULL);
v___x_270_ = lean_usize_add(v_i_222_, v___x_269_);
v_i_222_ = v___x_270_;
v_b_223_ = v___x_268_;
v___y_225_ = v_a_255_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_parentTag_219_);
return v___x_252_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___boxed(lean_object* v_alts_281_, lean_object* v_parentTag_282_, lean_object* v_as_283_, lean_object* v_sz_284_, lean_object* v_i_285_, lean_object* v_b_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
size_t v_sz_boxed_289_; size_t v_i_boxed_290_; lean_object* v_res_291_; 
v_sz_boxed_289_ = lean_unbox_usize(v_sz_284_);
lean_dec(v_sz_284_);
v_i_boxed_290_ = lean_unbox_usize(v_i_285_);
lean_dec(v_i_285_);
v_res_291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1(v_alts_281_, v_parentTag_282_, v_as_283_, v_sz_boxed_289_, v_i_boxed_290_, v_b_286_, v___y_287_, v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec_ref(v_as_283_);
lean_dec_ref(v_alts_281_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm(lean_object* v_parentTag_311_, lean_object* v_matchTac_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_315_; lean_object* v_matchAlts_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_alts_319_; lean_object* v_nextIdx_320_; lean_object* v___x_321_; size_t v_sz_322_; size_t v___x_323_; lean_object* v___x_324_; 
v___x_315_ = lean_unsigned_to_nat(5u);
v_matchAlts_316_ = l_Lean_Syntax_getArg(v_matchTac_312_, v___x_315_);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = l_Lean_Syntax_getArg(v_matchAlts_316_, v___x_317_);
lean_dec(v_matchAlts_316_);
v_alts_319_ = l_Lean_Syntax_getArgs(v___x_318_);
lean_dec(v___x_318_);
v_nextIdx_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__2));
v_sz_322_ = lean_array_size(v_alts_319_);
v___x_323_ = ((size_t)0ULL);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1(v_alts_319_, v_parentTag_311_, v_alts_319_, v_sz_322_, v___x_323_, v___x_321_, v_a_313_, v_a_314_);
lean_dec_ref(v_alts_319_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v_snd_326_; lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_354_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
v_snd_326_ = lean_ctor_get(v_a_325_, 1);
lean_inc(v_snd_326_);
v_a_327_ = lean_ctor_get(v___x_324_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v___x_324_, 0);
lean_dec(v_unused_355_);
v___x_329_ = v___x_324_;
v_isShared_330_ = v_isSharedCheck_354_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_324_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_354_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v_fst_331_; lean_object* v_snd_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_352_; 
v_fst_331_ = lean_ctor_get(v_a_325_, 0);
lean_inc(v_fst_331_);
lean_dec(v_a_325_);
v_snd_332_ = lean_ctor_get(v_snd_326_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_snd_326_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; 
v_unused_353_ = lean_ctor_get(v_snd_326_, 0);
lean_dec(v_unused_353_);
v___x_334_ = v_snd_326_;
v_isShared_335_ = v_isSharedCheck_352_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_snd_332_);
lean_dec(v_snd_326_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_352_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3));
v___x_337_ = l_Lean_Syntax_setKind(v_matchTac_312_, v___x_336_);
v___x_338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5));
v___x_339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__4));
v___x_340_ = lean_box(2);
v___x_341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
lean_ctor_set(v___x_341_, 2, v_fst_331_);
v___x_342_ = lean_mk_empty_array_with_capacity(v_nextIdx_320_);
v___x_343_ = lean_array_push(v___x_342_, v___x_341_);
v___x_344_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_344_, 0, v___x_340_);
lean_ctor_set(v___x_344_, 1, v___x_338_);
lean_ctor_set(v___x_344_, 2, v___x_343_);
v___x_345_ = l_Lean_Syntax_setArg(v___x_337_, v___x_315_, v___x_344_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_345_);
v___x_347_ = v___x_334_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_snd_332_);
v___x_347_ = v_reuseFailAlloc_351_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_349_; 
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_347_);
v___x_349_ = v___x_329_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_a_327_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
else
{
lean_object* v_a_356_; lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_matchTac_312_);
v_a_356_ = lean_ctor_get(v___x_324_, 0);
v_a_357_ = lean_ctor_get(v___x_324_, 1);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_324_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_inc(v_a_356_);
lean_dec(v___x_324_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_356_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___boxed(lean_object* v_parentTag_365_, lean_object* v_matchTac_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm(v_parentTag_365_, v_matchTac_366_, v_a_367_, v_a_368_);
lean_dec_ref(v_a_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalMatch___lam__0(lean_object* v_stx_370_, lean_object* v___x_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_declName_x3f_381_; lean_object* v_macroStack_382_; uint8_t v_mayPostpone_383_; uint8_t v_errToSorry_384_; lean_object* v_autoBoundImplicitContext_385_; lean_object* v_autoBoundImplicitForbidden_386_; lean_object* v_sectionVars_387_; lean_object* v_sectionFVars_388_; uint8_t v_implicitLambda_389_; uint8_t v_heedElabAsElim_390_; uint8_t v_isNoncomputableSection_391_; uint8_t v_isMetaSection_392_; uint8_t v_ignoreTCFailures_393_; uint8_t v_inPattern_394_; lean_object* v_tacSnap_x3f_395_; uint8_t v_saveRecAppSyntax_396_; uint8_t v_holesAsSyntheticOpaque_397_; uint8_t v_checkDeprecated_398_; lean_object* v_fixedTermElabs_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_declName_x3f_381_ = lean_ctor_get(v___y_374_, 0);
v_macroStack_382_ = lean_ctor_get(v___y_374_, 1);
v_mayPostpone_383_ = lean_ctor_get_uint8(v___y_374_, sizeof(void*)*8);
v_errToSorry_384_ = lean_ctor_get_uint8(v___y_374_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_385_ = lean_ctor_get(v___y_374_, 2);
v_autoBoundImplicitForbidden_386_ = lean_ctor_get(v___y_374_, 3);
v_sectionVars_387_ = lean_ctor_get(v___y_374_, 4);
v_sectionFVars_388_ = lean_ctor_get(v___y_374_, 5);
v_implicitLambda_389_ = lean_ctor_get_uint8(v___y_374_, sizeof(void*)*8 + 2);
v_heedElabAsElim_390_ = lean_ctor_get_uint8(v___y_374_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_391_ = lean_ctor_get_uint8(v___y_374_, sizeof(void*)*8 + 4);
v_isMetaSection_392_ = lean_ctor_get_uint8(v___y_374_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_393_ = lean_ctor_get_uint8(v___y_374_, sizeof(void*)*8 + 6);
v_inPattern_394_ = lean_ctor_get_uint8(v___y_374_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_395_ = lean_ctor_get(v___y_374_, 6);
v_saveRecAppSyntax_396_ = lean_ctor_get_uint8(v___y_374_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_397_ = lean_ctor_get_uint8(v___y_374_, sizeof(void*)*8 + 9);
v_checkDeprecated_398_ = lean_ctor_get_uint8(v___y_374_, sizeof(void*)*8 + 10);
v_fixedTermElabs_399_ = lean_ctor_get(v___y_374_, 7);
lean_inc(v___x_371_);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_stx_370_);
lean_ctor_set(v___x_400_, 1, v___x_371_);
lean_inc(v_macroStack_382_);
v___x_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v_macroStack_382_);
lean_inc_ref(v_fixedTermElabs_399_);
lean_inc(v_tacSnap_x3f_395_);
lean_inc(v_sectionFVars_388_);
lean_inc(v_sectionVars_387_);
lean_inc_ref(v_autoBoundImplicitForbidden_386_);
lean_inc(v_autoBoundImplicitContext_385_);
lean_inc(v_declName_x3f_381_);
v___x_402_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_402_, 0, v_declName_x3f_381_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
lean_ctor_set(v___x_402_, 2, v_autoBoundImplicitContext_385_);
lean_ctor_set(v___x_402_, 3, v_autoBoundImplicitForbidden_386_);
lean_ctor_set(v___x_402_, 4, v_sectionVars_387_);
lean_ctor_set(v___x_402_, 5, v_sectionFVars_388_);
lean_ctor_set(v___x_402_, 6, v_tacSnap_x3f_395_);
lean_ctor_set(v___x_402_, 7, v_fixedTermElabs_399_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*8, v_mayPostpone_383_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*8 + 1, v_errToSorry_384_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*8 + 2, v_implicitLambda_389_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*8 + 3, v_heedElabAsElim_390_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*8 + 4, v_isNoncomputableSection_391_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*8 + 5, v_isMetaSection_392_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*8 + 6, v_ignoreTCFailures_393_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*8 + 7, v_inPattern_394_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_396_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_397_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*8 + 10, v_checkDeprecated_398_);
v___x_403_ = l_Lean_Elab_Tactic_evalTactic(v___x_371_, v___y_372_, v___y_373_, v___x_402_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec_ref_known(v___x_402_, 8);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalMatch___lam__0___boxed(lean_object* v_stx_404_, lean_object* v___x_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Elab_Tactic_evalMatch___lam__0(v_stx_404_, v___x_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___redArg(lean_object* v_x_416_, lean_object* v___y_417_){
_start:
{
if (lean_obj_tag(v_x_416_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_419_; 
v_a_418_ = lean_ctor_get(v_x_416_, 0);
lean_inc(v_a_418_);
v___x_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_419_, 0, v_a_418_);
lean_ctor_set(v___x_419_, 1, v___y_417_);
return v___x_419_;
}
else
{
lean_object* v_a_420_; lean_object* v___x_421_; 
v_a_420_ = lean_ctor_get(v_x_416_, 0);
lean_inc(v_a_420_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_a_420_);
lean_ctor_set(v___x_421_, 1, v___y_417_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___redArg___boxed(lean_object* v_x_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___redArg(v_x_422_, v___y_423_);
lean_dec_ref(v_x_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__0(lean_object* v_env_425_, lean_object* v_stx_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_425_, v_stx_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
if (lean_obj_tag(v_a_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_439_; 
v_a_431_ = lean_ctor_get(v___x_429_, 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; 
v_unused_440_ = lean_ctor_get(v___x_429_, 0);
lean_dec(v_unused_440_);
v___x_433_ = v___x_429_;
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_429_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = lean_box(0);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_a_431_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_object* v_val_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_469_; 
v_val_441_ = lean_ctor_get(v_a_430_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v_a_430_);
if (v_isSharedCheck_469_ == 0)
{
v___x_443_ = v_a_430_;
v_isShared_444_ = v_isSharedCheck_469_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_val_441_);
lean_dec(v_a_430_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_469_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_snd_445_; 
v_snd_445_ = lean_ctor_get(v_val_441_, 1);
lean_inc(v_snd_445_);
lean_dec(v_val_441_);
if (lean_obj_tag(v_snd_445_) == 0)
{
lean_object* v_a_446_; lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
lean_del_object(v___x_443_);
v_a_446_ = lean_ctor_get(v___x_429_, 1);
lean_inc(v_a_446_);
lean_dec_ref_known(v___x_429_, 2);
v_a_447_ = lean_ctor_get(v_snd_445_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v_snd_445_);
if (v_isSharedCheck_455_ == 0)
{
v___x_449_ = v_snd_445_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v_snd_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_454_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; 
v___x_453_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___redArg(v___x_452_, v_a_446_);
lean_dec_ref(v___x_452_);
return v___x_453_;
}
}
}
else
{
lean_object* v_a_456_; lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_468_; 
v_a_456_ = lean_ctor_get(v___x_429_, 1);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_429_, 2);
v_a_457_ = lean_ctor_get(v_snd_445_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v_snd_445_);
if (v_isSharedCheck_468_ == 0)
{
v___x_459_ = v_snd_445_;
v_isShared_460_ = v_isSharedCheck_468_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v_snd_445_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_468_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v_a_457_);
v___x_462_ = v___x_443_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_467_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_464_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_462_);
v___x_464_ = v___x_459_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_466_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; 
v___x_465_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___redArg(v___x_464_, v_a_456_);
lean_dec_ref(v___x_464_);
return v___x_465_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_470_; lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_a_470_ = lean_ctor_get(v___x_429_, 0);
v_a_471_ = lean_ctor_get(v___x_429_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_429_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_inc(v_a_470_);
lean_dec(v___x_429_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_470_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__0___boxed(lean_object* v_env_479_, lean_object* v_stx_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__0(v_env_479_, v_stx_480_, v___y_481_, v___y_482_);
lean_dec_ref(v___y_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__3(lean_object* v_currNamespace_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v_currNamespace_484_);
lean_ctor_set(v___x_487_, 1, v___y_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__3(v_currNamespace_488_, v___y_489_, v___y_490_);
lean_dec_ref(v___y_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__4(lean_object* v_env_492_, lean_object* v_options_493_, lean_object* v_currNamespace_494_, lean_object* v_openDecls_495_, lean_object* v_n_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = l_Lean_ResolveName_resolveGlobalName(v_env_492_, v_options_493_, v_currNamespace_494_, v_openDecls_495_, v_n_496_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v___y_498_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__4___boxed(lean_object* v_env_501_, lean_object* v_options_502_, lean_object* v_currNamespace_503_, lean_object* v_openDecls_504_, lean_object* v_n_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__4(v_env_501_, v_options_502_, v_currNamespace_503_, v_openDecls_504_, v_n_505_, v___y_506_, v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec_ref(v_options_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__1(lean_object* v_env_509_, lean_object* v_declName_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
uint8_t v___x_513_; lean_object* v_env_514_; lean_object* v___x_515_; uint8_t v___x_516_; uint8_t v___x_517_; 
v___x_513_ = 0;
v_env_514_ = l_Lean_Environment_setExporting(v_env_509_, v___x_513_);
lean_inc(v_declName_510_);
v___x_515_ = l_Lean_mkPrivateName(v_env_514_, v_declName_510_);
v___x_516_ = 1;
lean_inc_ref(v_env_514_);
v___x_517_ = l_Lean_Environment_contains(v_env_514_, v___x_515_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_518_ = l_Lean_privateToUserName(v_declName_510_);
v___x_519_ = l_Lean_Environment_contains(v_env_514_, v___x_518_, v___x_516_);
v___x_520_ = lean_box(v___x_519_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v___y_512_);
return v___x_521_;
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec_ref(v_env_514_);
lean_dec(v_declName_510_);
v___x_522_ = lean_box(v___x_517_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v___y_512_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__1___boxed(lean_object* v_env_524_, lean_object* v_declName_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__1(v_env_524_, v_declName_525_, v___y_526_, v___y_527_);
lean_dec_ref(v___y_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0_spec__1(lean_object* v_msgData_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; lean_object* v_env_536_; lean_object* v___x_537_; lean_object* v_mctx_538_; lean_object* v_lctx_539_; lean_object* v_options_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_535_ = lean_st_ref_get(v___y_533_);
v_env_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc_ref(v_env_536_);
lean_dec(v___x_535_);
v___x_537_ = lean_st_ref_get(v___y_531_);
v_mctx_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc_ref(v_mctx_538_);
lean_dec(v___x_537_);
v_lctx_539_ = lean_ctor_get(v___y_530_, 2);
v_options_540_ = lean_ctor_get(v___y_532_, 2);
lean_inc_ref(v_options_540_);
lean_inc_ref(v_lctx_539_);
v___x_541_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_541_, 0, v_env_536_);
lean_ctor_set(v___x_541_, 1, v_mctx_538_);
lean_ctor_set(v___x_541_, 2, v_lctx_539_);
lean_ctor_set(v___x_541_, 3, v_options_540_);
v___x_542_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v_msgData_529_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0_spec__1(v_msgData_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_550_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_551_; double v___x_552_; 
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = lean_float_of_nat(v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg(lean_object* v_cls_556_, lean_object* v_msg_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_ref_563_; lean_object* v___x_564_; lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_609_; 
v_ref_563_ = lean_ctor_get(v___y_560_, 5);
v___x_564_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0_spec__1(v_msg_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_609_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_609_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_609_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v_traceState_570_; lean_object* v_env_571_; lean_object* v_nextMacroScope_572_; lean_object* v_ngen_573_; lean_object* v_auxDeclNGen_574_; lean_object* v_cache_575_; lean_object* v_messages_576_; lean_object* v_infoState_577_; lean_object* v_snapshotTasks_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_608_; 
v___x_569_ = lean_st_ref_take(v___y_561_);
v_traceState_570_ = lean_ctor_get(v___x_569_, 4);
v_env_571_ = lean_ctor_get(v___x_569_, 0);
v_nextMacroScope_572_ = lean_ctor_get(v___x_569_, 1);
v_ngen_573_ = lean_ctor_get(v___x_569_, 2);
v_auxDeclNGen_574_ = lean_ctor_get(v___x_569_, 3);
v_cache_575_ = lean_ctor_get(v___x_569_, 5);
v_messages_576_ = lean_ctor_get(v___x_569_, 6);
v_infoState_577_ = lean_ctor_get(v___x_569_, 7);
v_snapshotTasks_578_ = lean_ctor_get(v___x_569_, 8);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_608_ == 0)
{
v___x_580_ = v___x_569_;
v_isShared_581_ = v_isSharedCheck_608_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_snapshotTasks_578_);
lean_inc(v_infoState_577_);
lean_inc(v_messages_576_);
lean_inc(v_cache_575_);
lean_inc(v_traceState_570_);
lean_inc(v_auxDeclNGen_574_);
lean_inc(v_ngen_573_);
lean_inc(v_nextMacroScope_572_);
lean_inc(v_env_571_);
lean_dec(v___x_569_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_608_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
uint64_t v_tid_582_; lean_object* v_traces_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_607_; 
v_tid_582_ = lean_ctor_get_uint64(v_traceState_570_, sizeof(void*)*1);
v_traces_583_ = lean_ctor_get(v_traceState_570_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v_traceState_570_);
if (v_isSharedCheck_607_ == 0)
{
v___x_585_ = v_traceState_570_;
v_isShared_586_ = v_isSharedCheck_607_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_traces_583_);
lean_dec(v_traceState_570_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_607_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; double v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_587_ = lean_box(0);
v___x_588_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__0);
v___x_589_ = 0;
v___x_590_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__1));
v___x_591_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_591_, 0, v_cls_556_);
lean_ctor_set(v___x_591_, 1, v___x_587_);
lean_ctor_set(v___x_591_, 2, v___x_590_);
lean_ctor_set_float(v___x_591_, sizeof(void*)*3, v___x_588_);
lean_ctor_set_float(v___x_591_, sizeof(void*)*3 + 8, v___x_588_);
lean_ctor_set_uint8(v___x_591_, sizeof(void*)*3 + 16, v___x_589_);
v___x_592_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__2));
v___x_593_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v_a_565_);
lean_ctor_set(v___x_593_, 2, v___x_592_);
lean_inc(v_ref_563_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v_ref_563_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = l_Lean_PersistentArray_push___redArg(v_traces_583_, v___x_594_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_595_);
v___x_597_ = v___x_585_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_595_);
lean_ctor_set_uint64(v_reuseFailAlloc_606_, sizeof(void*)*1, v_tid_582_);
v___x_597_ = v_reuseFailAlloc_606_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_599_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 4, v___x_597_);
v___x_599_ = v___x_580_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_env_571_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_nextMacroScope_572_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_ngen_573_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_auxDeclNGen_574_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_605_, 5, v_cache_575_);
lean_ctor_set(v_reuseFailAlloc_605_, 6, v_messages_576_);
lean_ctor_set(v_reuseFailAlloc_605_, 7, v_infoState_577_);
lean_ctor_set(v_reuseFailAlloc_605_, 8, v_snapshotTasks_578_);
v___x_599_ = v_reuseFailAlloc_605_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_600_ = lean_st_ref_put(v___y_561_, v___x_599_);
v___x_601_ = lean_box(0);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_601_);
v___x_603_ = v___x_567_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___boxed(lean_object* v_cls_610_, lean_object* v_msg_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg(v_cls_610_, v_msg_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4(lean_object* v_as_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
if (lean_obj_tag(v_as_621_) == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_box(0);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
else
{
lean_object* v_options_633_; uint8_t v_hasTrace_634_; 
v_options_633_ = lean_ctor_get(v___y_628_, 2);
v_hasTrace_634_ = lean_ctor_get_uint8(v_options_633_, sizeof(void*)*1);
if (v_hasTrace_634_ == 0)
{
lean_object* v_tail_635_; 
v_tail_635_ = lean_ctor_get(v_as_621_, 1);
lean_inc(v_tail_635_);
lean_dec_ref_known(v_as_621_, 2);
v_as_621_ = v_tail_635_;
goto _start;
}
else
{
lean_object* v_head_637_; lean_object* v_tail_638_; lean_object* v_fst_639_; lean_object* v_snd_640_; lean_object* v_inheritedTraceOptions_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_head_637_ = lean_ctor_get(v_as_621_, 0);
lean_inc(v_head_637_);
v_tail_638_ = lean_ctor_get(v_as_621_, 1);
lean_inc(v_tail_638_);
lean_dec_ref_known(v_as_621_, 2);
v_fst_639_ = lean_ctor_get(v_head_637_, 0);
lean_inc_n(v_fst_639_, 2);
v_snd_640_ = lean_ctor_get(v_head_637_, 1);
lean_inc(v_snd_640_);
lean_dec(v_head_637_);
v_inheritedTraceOptions_641_ = lean_ctor_get(v___y_628_, 13);
v___x_642_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__1));
v___x_643_ = l_Lean_Name_append(v___x_642_, v_fst_639_);
v___x_644_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_641_, v_options_633_, v___x_643_);
lean_dec(v___x_643_);
if (v___x_644_ == 0)
{
lean_dec(v_snd_640_);
lean_dec(v_fst_639_);
v_as_621_ = v_tail_638_;
goto _start;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_646_, 0, v_snd_640_);
v___x_647_ = l_Lean_MessageData_ofFormat(v___x_646_);
v___x_648_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg(v_fst_639_, v___x_647_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_dec_ref_known(v___x_648_, 1);
v_as_621_ = v_tail_638_;
goto _start;
}
else
{
lean_dec(v_tail_638_);
return v___x_648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___boxed(lean_object* v_as_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4(v_as_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18_spec__21___redArg(lean_object* v_m_661_, lean_object* v_query_662_, lean_object* v_x_663_, lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
lean_object* v_zero_666_; uint8_t v_isZero_667_; 
v_zero_666_ = lean_unsigned_to_nat(0u);
v_isZero_667_ = lean_nat_dec_eq(v_x_664_, v_zero_666_);
if (v_isZero_667_ == 1)
{
lean_dec(v_x_665_);
lean_dec(v_x_664_);
if (lean_obj_tag(v_x_663_) == 0)
{
lean_object* v___x_668_; 
v___x_668_ = lean_box(2);
return v___x_668_;
}
else
{
lean_object* v_val_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
v_val_669_ = lean_ctor_get(v_x_663_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v_x_663_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_val_669_);
lean_dec(v_x_663_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_val_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
else
{
lean_object* v_keyArray_677_; lean_object* v_valueArray_678_; lean_object* v___x_679_; uint8_t v_isSome_680_; 
v_keyArray_677_ = lean_ctor_get(v_m_661_, 1);
v_valueArray_678_ = lean_ctor_get(v_m_661_, 2);
v___x_679_ = lean_array_fget_borrowed(v_keyArray_677_, v_x_665_);
v_isSome_680_ = lean_noption_is_some(v___x_679_);
if (v_isSome_680_ == 0)
{
lean_dec(v_x_664_);
if (lean_obj_tag(v_x_663_) == 0)
{
lean_object* v___x_681_; 
v___x_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_681_, 0, v_x_665_);
return v___x_681_;
}
else
{
lean_object* v_val_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v_x_665_);
v_val_682_ = lean_ctor_get(v_x_663_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v_x_663_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_val_682_);
lean_dec(v_x_663_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_val_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v_one_690_; lean_object* v_n_691_; lean_object* v___y_693_; 
v_one_690_ = lean_unsigned_to_nat(1u);
v_n_691_ = lean_nat_sub(v_x_664_, v_one_690_);
lean_dec(v_x_664_);
if (v_isSome_680_ == 0)
{
goto v___jp_699_;
}
else
{
lean_object* v___x_701_; uint8_t v_isSome_702_; 
v___x_701_ = lean_array_fget_borrowed(v_valueArray_678_, v_x_665_);
v_isSome_702_ = lean_noption_is_some(v___x_701_);
if (v_isSome_702_ == 0)
{
goto v___jp_699_;
}
else
{
lean_object* v_val_703_; uint8_t v___x_704_; 
lean_inc(v___x_679_);
v_val_703_ = lean_noption_get(v___x_679_);
v___x_704_ = lean_name_eq(v_val_703_, v_query_662_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
lean_dec(v_val_703_);
v___x_705_ = lean_array_get_size(v_keyArray_677_);
v___x_706_ = lean_nat_add(v_x_665_, v_one_690_);
lean_dec(v_x_665_);
v___x_707_ = lean_nat_dec_lt(v___x_706_, v___x_705_);
if (v___x_707_ == 0)
{
lean_dec(v___x_706_);
v_x_664_ = v_n_691_;
v_x_665_ = v_zero_666_;
goto _start;
}
else
{
v_x_664_ = v_n_691_;
v_x_665_ = v___x_706_;
goto _start;
}
}
else
{
lean_object* v_val_710_; lean_object* v___x_711_; 
lean_dec(v_n_691_);
lean_dec(v_x_663_);
lean_inc(v___x_701_);
v_val_710_ = lean_noption_get(v___x_701_);
v___x_711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_711_, 0, v_x_665_);
lean_ctor_set(v___x_711_, 1, v_val_703_);
lean_ctor_set(v___x_711_, 2, v_val_710_);
return v___x_711_;
}
}
}
v___jp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_694_ = lean_array_get_size(v_keyArray_677_);
v___x_695_ = lean_nat_add(v_x_665_, v_one_690_);
lean_dec(v_x_665_);
v___x_696_ = lean_nat_dec_lt(v___x_695_, v___x_694_);
if (v___x_696_ == 0)
{
lean_dec(v___x_695_);
v_x_663_ = v___y_693_;
v_x_664_ = v_n_691_;
v_x_665_ = v_zero_666_;
goto _start;
}
else
{
v_x_663_ = v___y_693_;
v_x_664_ = v_n_691_;
v_x_665_ = v___x_695_;
goto _start;
}
}
v___jp_699_:
{
if (lean_obj_tag(v_x_663_) == 0)
{
lean_object* v___x_700_; 
lean_inc(v_x_665_);
v___x_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_700_, 0, v_x_665_);
v___y_693_ = v___x_700_;
goto v___jp_692_;
}
else
{
v___y_693_ = v_x_663_;
goto v___jp_692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18_spec__21___redArg___boxed(lean_object* v_m_712_, lean_object* v_query_713_, lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_x_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18_spec__21___redArg(v_m_712_, v_query_713_, v_x_714_, v_x_715_, v_x_716_);
lean_dec(v_query_713_);
lean_dec_ref(v_m_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18___redArg(lean_object* v_m_718_, lean_object* v_query_719_){
_start:
{
lean_object* v_keyArray_720_; lean_object* v___x_721_; uint64_t v___y_723_; 
v_keyArray_720_ = lean_ctor_get(v_m_718_, 1);
v___x_721_ = lean_array_get_size(v_keyArray_720_);
if (lean_obj_tag(v_query_719_) == 0)
{
uint64_t v___x_738_; 
v___x_738_ = 1723ULL;
v___y_723_ = v___x_738_;
goto v___jp_722_;
}
else
{
uint64_t v_hash_739_; 
v_hash_739_ = lean_ctor_get_uint64(v_query_719_, sizeof(void*)*2);
v___y_723_ = v_hash_739_;
goto v___jp_722_;
}
v___jp_722_:
{
uint64_t v___x_724_; uint64_t v___x_725_; uint64_t v_fold_726_; uint64_t v___x_727_; uint64_t v___x_728_; uint64_t v___x_729_; size_t v___x_730_; size_t v___x_731_; size_t v___x_732_; size_t v___x_733_; size_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_724_ = 32ULL;
v___x_725_ = lean_uint64_shift_right(v___y_723_, v___x_724_);
v_fold_726_ = lean_uint64_xor(v___y_723_, v___x_725_);
v___x_727_ = 16ULL;
v___x_728_ = lean_uint64_shift_right(v_fold_726_, v___x_727_);
v___x_729_ = lean_uint64_xor(v_fold_726_, v___x_728_);
v___x_730_ = lean_uint64_to_usize(v___x_729_);
v___x_731_ = lean_usize_of_nat(v___x_721_);
v___x_732_ = ((size_t)1ULL);
v___x_733_ = lean_usize_sub(v___x_731_, v___x_732_);
v___x_734_ = lean_usize_land(v___x_730_, v___x_733_);
v___x_735_ = lean_usize_to_nat(v___x_734_);
v___x_736_ = lean_box(0);
v___x_737_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18_spec__21___redArg(v_m_718_, v_query_719_, v___x_736_, v___x_721_, v___x_735_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18___redArg___boxed(lean_object* v_m_740_, lean_object* v_query_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18___redArg(v_m_740_, v_query_741_);
lean_dec(v_query_741_);
lean_dec_ref(v_m_740_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___redArg(lean_object* v_m_743_, lean_object* v_query_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18___redArg(v_m_743_, v_query_744_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_index_746_; lean_object* v_key_747_; lean_object* v_value_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
v_index_746_ = lean_ctor_get(v___x_745_, 0);
v_key_747_ = lean_ctor_get(v___x_745_, 1);
v_value_748_ = lean_ctor_get(v___x_745_, 2);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_745_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_value_748_);
lean_inc(v_key_747_);
lean_inc(v_index_746_);
lean_dec(v___x_745_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_index_746_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_key_747_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_value_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
else
{
lean_object* v___x_756_; 
lean_dec(v___x_745_);
v___x_756_ = lean_box(1);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___redArg___boxed(lean_object* v_m_757_, lean_object* v_query_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___redArg(v_m_757_, v_query_758_);
lean_dec(v_query_758_);
lean_dec_ref(v_m_757_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg(lean_object* v_m_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___redArg(v_m_760_, v_a_761_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_value_763_; lean_object* v___x_764_; 
v_value_763_ = lean_ctor_get(v___x_762_, 2);
lean_inc(v_value_763_);
lean_dec_ref_known(v___x_762_, 3);
v___x_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_764_, 0, v_value_763_);
return v___x_764_;
}
else
{
lean_object* v___x_765_; 
v___x_765_ = lean_box(0);
return v___x_765_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_m_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg(v_m_766_, v_a_767_);
lean_dec(v_a_767_);
lean_dec_ref(v_m_766_);
return v_res_768_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___redArg(lean_object* v_keys_769_, lean_object* v_i_770_, lean_object* v_k_771_){
_start:
{
lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_772_ = lean_array_get_size(v_keys_769_);
v___x_773_ = lean_nat_dec_lt(v_i_770_, v___x_772_);
if (v___x_773_ == 0)
{
lean_dec(v_i_770_);
return v___x_773_;
}
else
{
lean_object* v_k_x27_774_; uint8_t v___x_775_; 
v_k_x27_774_ = lean_array_fget_borrowed(v_keys_769_, v_i_770_);
v___x_775_ = l_Lean_instBEqExtraModUse_beq(v_k_771_, v_k_x27_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_unsigned_to_nat(1u);
v___x_777_ = lean_nat_add(v_i_770_, v___x_776_);
lean_dec(v_i_770_);
v_i_770_ = v___x_777_;
goto _start;
}
else
{
lean_dec(v_i_770_);
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___redArg___boxed(lean_object* v_keys_779_, lean_object* v_i_780_, lean_object* v_k_781_){
_start:
{
uint8_t v_res_782_; lean_object* v_r_783_; 
v_res_782_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___redArg(v_keys_779_, v_i_780_, v_k_781_);
lean_dec_ref(v_k_781_);
lean_dec_ref(v_keys_779_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg(lean_object* v_x_784_, size_t v_x_785_, lean_object* v_x_786_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
lean_object* v_es_787_; lean_object* v___x_788_; size_t v___x_789_; size_t v___x_790_; lean_object* v_j_791_; lean_object* v___x_792_; 
v_es_787_ = lean_ctor_get(v_x_784_, 0);
v___x_788_ = lean_box(2);
v___x_789_ = ((size_t)31ULL);
v___x_790_ = lean_usize_land(v_x_785_, v___x_789_);
v_j_791_ = lean_usize_to_nat(v___x_790_);
v___x_792_ = lean_array_get_borrowed(v___x_788_, v_es_787_, v_j_791_);
lean_dec(v_j_791_);
switch(lean_obj_tag(v___x_792_))
{
case 0:
{
lean_object* v_key_793_; uint8_t v___x_794_; 
v_key_793_ = lean_ctor_get(v___x_792_, 0);
v___x_794_ = l_Lean_instBEqExtraModUse_beq(v_x_786_, v_key_793_);
return v___x_794_;
}
case 1:
{
lean_object* v_node_795_; size_t v___x_796_; size_t v___x_797_; 
v_node_795_ = lean_ctor_get(v___x_792_, 0);
v___x_796_ = ((size_t)5ULL);
v___x_797_ = lean_usize_shift_right(v_x_785_, v___x_796_);
v_x_784_ = v_node_795_;
v_x_785_ = v___x_797_;
goto _start;
}
default: 
{
uint8_t v___x_799_; 
v___x_799_ = 0;
return v___x_799_;
}
}
}
else
{
lean_object* v_ks_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_ks_800_ = lean_ctor_get(v_x_784_, 0);
v___x_801_ = lean_unsigned_to_nat(0u);
v___x_802_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___redArg(v_ks_800_, v___x_801_, v_x_786_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___boxed(lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
size_t v_x_25039__boxed_806_; uint8_t v_res_807_; lean_object* v_r_808_; 
v_x_25039__boxed_806_ = lean_unbox_usize(v_x_804_);
lean_dec(v_x_804_);
v_res_807_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg(v_x_803_, v_x_25039__boxed_806_, v_x_805_);
lean_dec_ref(v_x_805_);
lean_dec_ref(v_x_803_);
v_r_808_ = lean_box(v_res_807_);
return v_r_808_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___redArg(lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
uint64_t v___x_811_; size_t v___x_812_; uint8_t v___x_813_; 
v___x_811_ = l_Lean_instHashableExtraModUse_hash(v_x_810_);
v___x_812_ = lean_uint64_to_usize(v___x_811_);
v___x_813_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg(v_x_809_, v___x_812_, v_x_810_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
uint8_t v_res_816_; lean_object* v_r_817_; 
v_res_816_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___redArg(v_x_814_, v_x_815_);
lean_dec_ref(v_x_815_);
lean_dec_ref(v_x_814_);
v_r_817_ = lean_box(v_res_816_);
return v_r_817_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__1));
v___x_821_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__0));
v___x_822_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_821_, v___x_820_);
return v___x_822_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_823_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__3);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4);
v___x_829_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
lean_ctor_set(v___x_829_, 2, v___x_828_);
lean_ctor_set(v___x_829_, 3, v___x_828_);
lean_ctor_set(v___x_829_, 4, v___x_828_);
lean_ctor_set(v___x_829_, 5, v___x_828_);
return v___x_829_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__10(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__9));
v___x_835_ = l_Lean_stringToMessageData(v___x_834_);
return v___x_835_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__11));
v___x_838_ = l_Lean_stringToMessageData(v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__13(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__1));
v___x_840_ = l_Lean_stringToMessageData(v___x_839_);
return v___x_840_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v_cls_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_cls_841_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__8));
v___x_842_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__1));
v___x_843_ = l_Lean_Name_append(v___x_842_, v_cls_841_);
return v___x_843_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__16(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__15));
v___x_846_ = l_Lean_stringToMessageData(v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__18(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__17));
v___x_849_ = l_Lean_stringToMessageData(v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4(lean_object* v_mod_854_, uint8_t v_isMeta_855_, lean_object* v_hint_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; lean_object* v_env_867_; uint8_t v_isExporting_868_; lean_object* v___x_869_; lean_object* v_env_870_; lean_object* v___x_871_; lean_object* v_entry_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_866_ = lean_st_ref_get(v___y_864_);
v_env_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc_ref(v_env_867_);
lean_dec(v___x_866_);
v_isExporting_868_ = lean_ctor_get_uint8(v_env_867_, sizeof(void*)*8);
lean_dec_ref(v_env_867_);
v___x_869_ = lean_st_ref_get(v___y_864_);
v_env_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc_ref(v_env_870_);
lean_dec(v___x_869_);
v___x_871_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__2);
lean_inc(v_mod_854_);
v_entry_872_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_872_, 0, v_mod_854_);
lean_ctor_set_uint8(v_entry_872_, sizeof(void*)*1, v_isExporting_868_);
lean_ctor_set_uint8(v_entry_872_, sizeof(void*)*1 + 1, v_isMeta_855_);
v___x_873_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_874_ = lean_box(1);
v___x_875_ = lean_box(0);
v___x_918_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_871_, v___x_873_, v_env_870_, v___x_874_, v___x_875_);
v___x_919_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___redArg(v___x_918_, v_entry_872_);
lean_dec(v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v_options_920_; uint8_t v_hasTrace_921_; 
v_options_920_ = lean_ctor_get(v___y_863_, 2);
v_hasTrace_921_ = lean_ctor_get_uint8(v_options_920_, sizeof(void*)*1);
if (v_hasTrace_921_ == 0)
{
lean_dec(v_hint_856_);
lean_dec(v_mod_854_);
v___y_877_ = v___y_862_;
v___y_878_ = v___y_864_;
goto v___jp_876_;
}
else
{
lean_object* v_inheritedTraceOptions_922_; lean_object* v_cls_923_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_inheritedTraceOptions_922_ = lean_ctor_get(v___y_863_, 13);
v_cls_923_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__8));
v___x_943_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__14);
v___x_944_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_922_, v_options_920_, v___x_943_);
if (v___x_944_ == 0)
{
lean_dec(v_hint_856_);
lean_dec(v_mod_854_);
v___y_877_ = v___y_862_;
v___y_878_ = v___y_864_;
goto v___jp_876_;
}
else
{
lean_object* v___x_945_; lean_object* v___y_947_; 
v___x_945_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__16);
if (v_isExporting_868_ == 0)
{
lean_object* v___x_954_; 
v___x_954_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__21));
v___y_947_ = v___x_954_;
goto v___jp_946_;
}
else
{
lean_object* v___x_955_; 
v___x_955_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__22));
v___y_947_ = v___x_955_;
goto v___jp_946_;
}
v___jp_946_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
lean_inc_ref(v___y_947_);
v___x_948_ = l_Lean_stringToMessageData(v___y_947_);
v___x_949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_945_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__18);
v___x_951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
if (v_isMeta_855_ == 0)
{
lean_object* v___x_952_; 
v___x_952_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__19));
v___y_930_ = v___x_951_;
v___y_931_ = v___x_952_;
goto v___jp_929_;
}
else
{
lean_object* v___x_953_; 
v___x_953_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__20));
v___y_930_ = v___x_951_;
v___y_931_ = v___x_953_;
goto v___jp_929_;
}
}
}
v___jp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___y_925_);
lean_ctor_set(v___x_927_, 1, v___y_926_);
v___x_928_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg(v_cls_923_, v___x_927_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_dec_ref_known(v___x_928_, 1);
v___y_877_ = v___y_862_;
v___y_878_ = v___y_864_;
goto v___jp_876_;
}
else
{
lean_dec_ref_known(v_entry_872_, 1);
return v___x_928_;
}
}
v___jp_929_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
lean_inc_ref(v___y_931_);
v___x_932_ = l_Lean_stringToMessageData(v___y_931_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___y_930_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__10);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = l_Lean_MessageData_ofName(v_mod_854_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_Name_isAnonymous(v_hint_856_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__12);
v___x_940_ = l_Lean_MessageData_ofName(v_hint_856_);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___y_925_ = v___x_937_;
v___y_926_ = v___x_941_;
goto v___jp_924_;
}
else
{
lean_object* v___x_942_; 
lean_dec(v_hint_856_);
v___x_942_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__13);
v___y_925_ = v___x_937_;
v___y_926_ = v___x_942_;
goto v___jp_924_;
}
}
}
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec_ref_known(v_entry_872_, 1);
lean_dec(v_hint_856_);
lean_dec(v_mod_854_);
v___x_956_ = lean_box(0);
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
return v___x_957_;
}
v___jp_876_:
{
lean_object* v___x_879_; lean_object* v_toEnvExtension_880_; lean_object* v_env_881_; lean_object* v_nextMacroScope_882_; lean_object* v_ngen_883_; lean_object* v_auxDeclNGen_884_; lean_object* v_traceState_885_; lean_object* v_messages_886_; lean_object* v_infoState_887_; lean_object* v_snapshotTasks_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_916_; 
v___x_879_ = lean_st_ref_take(v___y_878_);
v_toEnvExtension_880_ = lean_ctor_get(v___x_873_, 0);
v_env_881_ = lean_ctor_get(v___x_879_, 0);
v_nextMacroScope_882_ = lean_ctor_get(v___x_879_, 1);
v_ngen_883_ = lean_ctor_get(v___x_879_, 2);
v_auxDeclNGen_884_ = lean_ctor_get(v___x_879_, 3);
v_traceState_885_ = lean_ctor_get(v___x_879_, 4);
v_messages_886_ = lean_ctor_get(v___x_879_, 6);
v_infoState_887_ = lean_ctor_get(v___x_879_, 7);
v_snapshotTasks_888_ = lean_ctor_get(v___x_879_, 8);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v___x_879_, 5);
lean_dec(v_unused_917_);
v___x_890_ = v___x_879_;
v_isShared_891_ = v_isSharedCheck_916_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_snapshotTasks_888_);
lean_inc(v_infoState_887_);
lean_inc(v_messages_886_);
lean_inc(v_traceState_885_);
lean_inc(v_auxDeclNGen_884_);
lean_inc(v_ngen_883_);
lean_inc(v_nextMacroScope_882_);
lean_inc(v_env_881_);
lean_dec(v___x_879_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_916_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_asyncMode_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v_asyncMode_892_ = lean_ctor_get(v_toEnvExtension_880_, 2);
v___x_893_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_873_, v_env_881_, v_entry_872_, v_asyncMode_892_, v___x_875_);
v___x_894_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__5);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 5, v___x_894_);
lean_ctor_set(v___x_890_, 0, v___x_893_);
v___x_896_ = v___x_890_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_nextMacroScope_882_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_ngen_883_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v_auxDeclNGen_884_);
lean_ctor_set(v_reuseFailAlloc_915_, 4, v_traceState_885_);
lean_ctor_set(v_reuseFailAlloc_915_, 5, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_915_, 6, v_messages_886_);
lean_ctor_set(v_reuseFailAlloc_915_, 7, v_infoState_887_);
lean_ctor_set(v_reuseFailAlloc_915_, 8, v_snapshotTasks_888_);
v___x_896_ = v_reuseFailAlloc_915_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v_mctx_899_; lean_object* v_zetaDeltaFVarIds_900_; lean_object* v_postponed_901_; lean_object* v_diag_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_913_; 
v___x_897_ = lean_st_ref_put(v___y_878_, v___x_896_);
v___x_898_ = lean_st_ref_take(v___y_877_);
v_mctx_899_ = lean_ctor_get(v___x_898_, 0);
v_zetaDeltaFVarIds_900_ = lean_ctor_get(v___x_898_, 2);
v_postponed_901_ = lean_ctor_get(v___x_898_, 3);
v_diag_902_ = lean_ctor_get(v___x_898_, 4);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; 
v_unused_914_ = lean_ctor_get(v___x_898_, 1);
lean_dec(v_unused_914_);
v___x_904_ = v___x_898_;
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_diag_902_);
lean_inc(v_postponed_901_);
lean_inc(v_zetaDeltaFVarIds_900_);
lean_inc(v_mctx_899_);
lean_dec(v___x_898_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_906_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__6);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v___x_906_);
v___x_908_ = v___x_904_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_mctx_899_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_zetaDeltaFVarIds_900_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v_postponed_901_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v_diag_902_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_st_ref_put(v___y_877_, v___x_908_);
v___x_910_ = lean_box(0);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___boxed(lean_object* v_mod_958_, lean_object* v_isMeta_959_, lean_object* v_hint_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
uint8_t v_isMeta_boxed_970_; lean_object* v_res_971_; 
v_isMeta_boxed_970_ = lean_unbox(v_isMeta_959_);
v_res_971_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4(v_mod_958_, v_isMeta_boxed_970_, v_hint_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__5(lean_object* v___x_972_, lean_object* v_declName_973_, lean_object* v_as_974_, size_t v_sz_975_, size_t v_i_976_, lean_object* v_b_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
uint8_t v___x_987_; 
v___x_987_ = lean_usize_dec_lt(v_i_976_, v_sz_975_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
lean_dec(v_declName_973_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v_b_977_);
return v___x_988_;
}
else
{
lean_object* v___x_989_; lean_object* v_modules_990_; lean_object* v___x_991_; lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v_toImport_994_; lean_object* v_module_995_; uint8_t v___x_996_; lean_object* v___x_997_; 
v___x_989_ = l_Lean_Environment_header(v___x_972_);
v_modules_990_ = lean_ctor_get(v___x_989_, 3);
lean_inc_ref(v_modules_990_);
lean_dec_ref(v___x_989_);
v___x_991_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_992_ = lean_array_uget_borrowed(v_as_974_, v_i_976_);
v___x_993_ = lean_array_get(v___x_991_, v_modules_990_, v_a_992_);
lean_dec_ref(v_modules_990_);
v_toImport_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc_ref(v_toImport_994_);
lean_dec(v___x_993_);
v_module_995_ = lean_ctor_get(v_toImport_994_, 0);
lean_inc(v_module_995_);
lean_dec_ref(v_toImport_994_);
v___x_996_ = 0;
lean_inc(v_declName_973_);
v___x_997_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4(v_module_995_, v___x_996_, v_declName_973_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_998_; size_t v___x_999_; size_t v___x_1000_; 
lean_dec_ref_known(v___x_997_, 1);
v___x_998_ = lean_box(0);
v___x_999_ = ((size_t)1ULL);
v___x_1000_ = lean_usize_add(v_i_976_, v___x_999_);
v_i_976_ = v___x_1000_;
v_b_977_ = v___x_998_;
goto _start;
}
else
{
lean_dec(v_declName_973_);
return v___x_997_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__5___boxed(lean_object* v___x_1002_, lean_object* v_declName_1003_, lean_object* v_as_1004_, lean_object* v_sz_1005_, lean_object* v_i_1006_, lean_object* v_b_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
size_t v_sz_boxed_1017_; size_t v_i_boxed_1018_; lean_object* v_res_1019_; 
v_sz_boxed_1017_ = lean_unbox_usize(v_sz_1005_);
lean_dec(v_sz_1005_);
v_i_boxed_1018_ = lean_unbox_usize(v_i_1006_);
lean_dec(v_i_1006_);
v_res_1019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__5(v___x_1002_, v_declName_1003_, v_as_1004_, v_sz_boxed_1017_, v_i_boxed_1018_, v_b_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec_ref(v_as_1004_);
lean_dec_ref(v___x_1002_);
return v_res_1019_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__1));
v___x_1023_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__0));
v___x_1024_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1023_, v___x_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2(lean_object* v_declName_1027_, uint8_t v_isMeta_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; lean_object* v_env_1042_; lean_object* v___y_1044_; lean_object* v___x_1057_; 
v___x_1038_ = lean_st_ref_get(v___y_1036_);
v_env_1042_ = lean_ctor_get(v___x_1038_, 0);
lean_inc_ref(v_env_1042_);
lean_dec(v___x_1038_);
v___x_1057_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1042_, v_declName_1027_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_dec_ref(v_env_1042_);
lean_dec(v_declName_1027_);
goto v___jp_1039_;
}
else
{
lean_object* v_val_1058_; lean_object* v___x_1059_; lean_object* v_modules_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_val_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v___x_1057_, 1);
v___x_1059_ = l_Lean_Environment_header(v_env_1042_);
v_modules_1060_ = lean_ctor_get(v___x_1059_, 3);
lean_inc_ref(v_modules_1060_);
lean_dec_ref(v___x_1059_);
v___x_1061_ = lean_array_get_size(v_modules_1060_);
v___x_1062_ = lean_nat_dec_lt(v_val_1058_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_dec_ref(v_modules_1060_);
lean_dec(v_val_1058_);
lean_dec_ref(v_env_1042_);
lean_dec(v_declName_1027_);
goto v___jp_1039_;
}
else
{
lean_object* v___x_1063_; lean_object* v_env_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___y_1068_; 
v___x_1063_ = lean_st_ref_get(v___y_1036_);
v_env_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc_ref(v_env_1064_);
lean_dec(v___x_1063_);
v___x_1065_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__2);
v___x_1066_ = lean_array_fget(v_modules_1060_, v_val_1058_);
lean_dec(v_val_1058_);
lean_dec_ref(v_modules_1060_);
if (v_isMeta_1028_ == 0)
{
lean_dec_ref(v_env_1064_);
v___y_1068_ = v_isMeta_1028_;
goto v___jp_1067_;
}
else
{
uint8_t v___x_1079_; 
lean_inc(v_declName_1027_);
v___x_1079_ = l_Lean_isMarkedMeta(v_env_1064_, v_declName_1027_);
if (v___x_1079_ == 0)
{
v___y_1068_ = v_isMeta_1028_;
goto v___jp_1067_;
}
else
{
uint8_t v___x_1080_; 
v___x_1080_ = 0;
v___y_1068_ = v___x_1080_;
goto v___jp_1067_;
}
}
v___jp_1067_:
{
lean_object* v_toImport_1069_; lean_object* v_module_1070_; lean_object* v___x_1071_; 
v_toImport_1069_ = lean_ctor_get(v___x_1066_, 0);
lean_inc_ref(v_toImport_1069_);
lean_dec(v___x_1066_);
v_module_1070_ = lean_ctor_get(v_toImport_1069_, 0);
lean_inc(v_module_1070_);
lean_dec_ref(v_toImport_1069_);
lean_inc(v_declName_1027_);
v___x_1071_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4(v_module_1070_, v___y_1068_, v_declName_1027_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec_ref_known(v___x_1071_, 1);
v___x_1072_ = l_Lean_indirectModUseExt;
v___x_1073_ = lean_box(1);
v___x_1074_ = lean_box(0);
lean_inc_ref(v_env_1042_);
v___x_1075_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1065_, v___x_1072_, v_env_1042_, v___x_1073_, v___x_1074_);
v___x_1076_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg(v___x_1075_, v_declName_1027_);
lean_dec(v___x_1075_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__3));
v___y_1044_ = v___x_1077_;
goto v___jp_1043_;
}
else
{
lean_object* v_val_1078_; 
v_val_1078_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_val_1078_);
lean_dec_ref_known(v___x_1076_, 1);
v___y_1044_ = v_val_1078_;
goto v___jp_1043_;
}
}
else
{
lean_dec_ref(v_env_1042_);
lean_dec(v_declName_1027_);
return v___x_1071_;
}
}
}
}
v___jp_1039_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
v___jp_1043_:
{
lean_object* v___x_1045_; size_t v_sz_1046_; size_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1045_ = lean_box(0);
v_sz_1046_ = lean_array_size(v___y_1044_);
v___x_1047_ = ((size_t)0ULL);
v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__5(v_env_1042_, v_declName_1027_, v___y_1044_, v_sz_1046_, v___x_1047_, v___x_1045_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec_ref(v___y_1044_);
lean_dec_ref(v_env_1042_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; 
v_unused_1056_ = lean_ctor_get(v___x_1048_, 0);
lean_dec(v_unused_1056_);
v___x_1050_ = v___x_1048_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_dec(v___x_1048_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1045_);
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1045_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
else
{
return v___x_1048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___boxed(lean_object* v_declName_1081_, lean_object* v_isMeta_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
uint8_t v_isMeta_boxed_1092_; lean_object* v_res_1093_; 
v_isMeta_boxed_1092_ = lean_unbox(v_isMeta_1082_);
v_res_1093_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2(v_declName_1081_, v_isMeta_boxed_1092_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___redArg(lean_object* v_as_x27_1094_, lean_object* v_b_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
if (lean_obj_tag(v_as_x27_1094_) == 0)
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v_b_1095_);
return v___x_1105_;
}
else
{
lean_object* v_head_1106_; lean_object* v_tail_1107_; uint8_t v___x_1108_; lean_object* v___x_1109_; 
v_head_1106_ = lean_ctor_get(v_as_x27_1094_, 0);
v_tail_1107_ = lean_ctor_get(v_as_x27_1094_, 1);
v___x_1108_ = 1;
lean_inc(v_head_1106_);
v___x_1109_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2(v_head_1106_, v___x_1108_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v___x_1110_; 
lean_dec_ref_known(v___x_1109_, 1);
v___x_1110_ = lean_box(0);
v_as_x27_1094_ = v_tail_1107_;
v_b_1095_ = v___x_1110_;
goto _start;
}
else
{
return v___x_1109_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1112_, lean_object* v_b_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___redArg(v_as_x27_1112_, v_b_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v_as_x27_1112_);
return v_res_1123_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = lean_box(0);
v___x_1125_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v___x_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg(){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___closed__0);
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___boxed(lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg();
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___redArg(lean_object* v_msg_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_ref_1138_; lean_object* v___x_1139_; lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1148_; 
v_ref_1138_ = lean_ctor_get(v___y_1135_, 5);
v___x_1139_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0_spec__1(v_msg_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1148_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1148_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
lean_inc(v_ref_1138_);
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_ref_1138_);
lean_ctor_set(v___x_1144_, 1, v_a_1140_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set_tag(v___x_1142_, 1);
lean_ctor_set(v___x_1142_, 0, v___x_1144_);
v___x_1146_ = v___x_1142_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___redArg___boxed(lean_object* v_msg_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___redArg(v_msg_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___redArg(lean_object* v_ref_1156_, lean_object* v_msg_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_fileName_1167_; lean_object* v_fileMap_1168_; lean_object* v_options_1169_; lean_object* v_currRecDepth_1170_; lean_object* v_maxRecDepth_1171_; lean_object* v_ref_1172_; lean_object* v_currNamespace_1173_; lean_object* v_openDecls_1174_; lean_object* v_initHeartbeats_1175_; lean_object* v_maxHeartbeats_1176_; lean_object* v_quotContext_1177_; lean_object* v_currMacroScope_1178_; uint8_t v_diag_1179_; lean_object* v_cancelTk_x3f_1180_; uint8_t v_suppressElabErrors_1181_; lean_object* v_inheritedTraceOptions_1182_; lean_object* v_ref_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_fileName_1167_ = lean_ctor_get(v___y_1164_, 0);
v_fileMap_1168_ = lean_ctor_get(v___y_1164_, 1);
v_options_1169_ = lean_ctor_get(v___y_1164_, 2);
v_currRecDepth_1170_ = lean_ctor_get(v___y_1164_, 3);
v_maxRecDepth_1171_ = lean_ctor_get(v___y_1164_, 4);
v_ref_1172_ = lean_ctor_get(v___y_1164_, 5);
v_currNamespace_1173_ = lean_ctor_get(v___y_1164_, 6);
v_openDecls_1174_ = lean_ctor_get(v___y_1164_, 7);
v_initHeartbeats_1175_ = lean_ctor_get(v___y_1164_, 8);
v_maxHeartbeats_1176_ = lean_ctor_get(v___y_1164_, 9);
v_quotContext_1177_ = lean_ctor_get(v___y_1164_, 10);
v_currMacroScope_1178_ = lean_ctor_get(v___y_1164_, 11);
v_diag_1179_ = lean_ctor_get_uint8(v___y_1164_, sizeof(void*)*14);
v_cancelTk_x3f_1180_ = lean_ctor_get(v___y_1164_, 12);
v_suppressElabErrors_1181_ = lean_ctor_get_uint8(v___y_1164_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1182_ = lean_ctor_get(v___y_1164_, 13);
v_ref_1183_ = l_Lean_replaceRef(v_ref_1156_, v_ref_1172_);
lean_inc_ref(v_inheritedTraceOptions_1182_);
lean_inc(v_cancelTk_x3f_1180_);
lean_inc(v_currMacroScope_1178_);
lean_inc(v_quotContext_1177_);
lean_inc(v_maxHeartbeats_1176_);
lean_inc(v_initHeartbeats_1175_);
lean_inc(v_openDecls_1174_);
lean_inc(v_currNamespace_1173_);
lean_inc(v_maxRecDepth_1171_);
lean_inc(v_currRecDepth_1170_);
lean_inc_ref(v_options_1169_);
lean_inc_ref(v_fileMap_1168_);
lean_inc_ref(v_fileName_1167_);
v___x_1184_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1184_, 0, v_fileName_1167_);
lean_ctor_set(v___x_1184_, 1, v_fileMap_1168_);
lean_ctor_set(v___x_1184_, 2, v_options_1169_);
lean_ctor_set(v___x_1184_, 3, v_currRecDepth_1170_);
lean_ctor_set(v___x_1184_, 4, v_maxRecDepth_1171_);
lean_ctor_set(v___x_1184_, 5, v_ref_1183_);
lean_ctor_set(v___x_1184_, 6, v_currNamespace_1173_);
lean_ctor_set(v___x_1184_, 7, v_openDecls_1174_);
lean_ctor_set(v___x_1184_, 8, v_initHeartbeats_1175_);
lean_ctor_set(v___x_1184_, 9, v_maxHeartbeats_1176_);
lean_ctor_set(v___x_1184_, 10, v_quotContext_1177_);
lean_ctor_set(v___x_1184_, 11, v_currMacroScope_1178_);
lean_ctor_set(v___x_1184_, 12, v_cancelTk_x3f_1180_);
lean_ctor_set(v___x_1184_, 13, v_inheritedTraceOptions_1182_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*14, v_diag_1179_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*14 + 1, v_suppressElabErrors_1181_);
v___x_1185_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___redArg(v_msg_1157_, v___y_1162_, v___y_1163_, v___x_1184_, v___y_1165_);
lean_dec_ref_known(v___x_1184_, 14);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1186_, lean_object* v_msg_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___redArg(v_ref_1186_, v_msg_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v_ref_1186_);
return v_res_1197_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = l_Lean_maxRecDepthErrorMessage;
v___x_1204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__3);
v___x_1206_ = l_Lean_MessageData_ofFormat(v___x_1205_);
return v___x_1206_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__4);
v___x_1208_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__2));
v___x_1209_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg(lean_object* v_ref_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__5);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v_ref_1210_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___boxed(lean_object* v_ref_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg(v_ref_1215_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__2(lean_object* v_env_1218_, lean_object* v_currNamespace_1219_, lean_object* v_openDecls_1220_, lean_object* v_n_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = l_Lean_ResolveName_resolveNamespace(v_env_1218_, v_currNamespace_1219_, v_openDecls_1220_, v_n_1221_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v___y_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__2___boxed(lean_object* v_env_1226_, lean_object* v_currNamespace_1227_, lean_object* v_openDecls_1228_, lean_object* v_n_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__2(v_env_1226_, v_currNamespace_1227_, v_openDecls_1228_, v_n_1229_, v___y_1230_, v___y_1231_);
lean_dec_ref(v___y_1230_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg(lean_object* v_x_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; lean_object* v_env_1245_; lean_object* v_options_1246_; lean_object* v_currRecDepth_1247_; lean_object* v_maxRecDepth_1248_; lean_object* v_ref_1249_; lean_object* v_currNamespace_1250_; lean_object* v_openDecls_1251_; lean_object* v_quotContext_1252_; lean_object* v_currMacroScope_1253_; lean_object* v___x_1254_; lean_object* v_nextMacroScope_1255_; lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v_methods_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1244_ = lean_st_ref_get(v___y_1242_);
v_env_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc_ref_n(v_env_1245_, 4);
lean_dec(v___x_1244_);
v_options_1246_ = lean_ctor_get(v___y_1241_, 2);
v_currRecDepth_1247_ = lean_ctor_get(v___y_1241_, 3);
v_maxRecDepth_1248_ = lean_ctor_get(v___y_1241_, 4);
v_ref_1249_ = lean_ctor_get(v___y_1241_, 5);
v_currNamespace_1250_ = lean_ctor_get(v___y_1241_, 6);
v_openDecls_1251_ = lean_ctor_get(v___y_1241_, 7);
v_quotContext_1252_ = lean_ctor_get(v___y_1241_, 10);
v_currMacroScope_1253_ = lean_ctor_get(v___y_1241_, 11);
v___x_1254_ = lean_st_ref_get(v___y_1242_);
v_nextMacroScope_1255_ = lean_ctor_get(v___x_1254_, 1);
lean_inc(v_nextMacroScope_1255_);
lean_dec(v___x_1254_);
v___f_1256_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1256_, 0, v_env_1245_);
v___f_1257_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1257_, 0, v_env_1245_);
lean_inc_n(v_openDecls_1251_, 2);
lean_inc_n(v_currNamespace_1250_, 3);
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1258_, 0, v_env_1245_);
lean_closure_set(v___f_1258_, 1, v_currNamespace_1250_);
lean_closure_set(v___f_1258_, 2, v_openDecls_1251_);
v___f_1259_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1259_, 0, v_currNamespace_1250_);
lean_inc_ref(v_options_1246_);
v___f_1260_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1260_, 0, v_env_1245_);
lean_closure_set(v___f_1260_, 1, v_options_1246_);
lean_closure_set(v___f_1260_, 2, v_currNamespace_1250_);
lean_closure_set(v___f_1260_, 3, v_openDecls_1251_);
v_methods_1261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1261_, 0, v___f_1256_);
lean_ctor_set(v_methods_1261_, 1, v___f_1259_);
lean_ctor_set(v_methods_1261_, 2, v___f_1257_);
lean_ctor_set(v_methods_1261_, 3, v___f_1258_);
lean_ctor_set(v_methods_1261_, 4, v___f_1260_);
lean_inc(v_ref_1249_);
lean_inc(v_maxRecDepth_1248_);
lean_inc(v_currRecDepth_1247_);
lean_inc(v_currMacroScope_1253_);
lean_inc(v_quotContext_1252_);
v___x_1262_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1262_, 0, v_methods_1261_);
lean_ctor_set(v___x_1262_, 1, v_quotContext_1252_);
lean_ctor_set(v___x_1262_, 2, v_currMacroScope_1253_);
lean_ctor_set(v___x_1262_, 3, v_currRecDepth_1247_);
lean_ctor_set(v___x_1262_, 4, v_maxRecDepth_1248_);
lean_ctor_set(v___x_1262_, 5, v_ref_1249_);
v___x_1263_ = lean_box(0);
v___x_1264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1264_, 0, v_nextMacroScope_1255_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
lean_ctor_set(v___x_1264_, 2, v___x_1263_);
v___x_1265_ = lean_apply_2(v_x_1234_, v___x_1262_, v___x_1264_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v_a_1267_; lean_object* v_macroScope_1268_; lean_object* v_traceMsgs_1269_; lean_object* v_expandedMacroDecls_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 1);
lean_inc(v_a_1266_);
v_a_1267_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1265_, 2);
v_macroScope_1268_ = lean_ctor_get(v_a_1266_, 0);
lean_inc(v_macroScope_1268_);
v_traceMsgs_1269_ = lean_ctor_get(v_a_1266_, 1);
lean_inc(v_traceMsgs_1269_);
v_expandedMacroDecls_1270_ = lean_ctor_get(v_a_1266_, 2);
lean_inc(v_expandedMacroDecls_1270_);
lean_dec(v_a_1266_);
v___x_1271_ = lean_box(0);
v___x_1272_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___redArg(v_expandedMacroDecls_1270_, v___x_1271_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v_expandedMacroDecls_1270_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v___x_1273_; lean_object* v_env_1274_; lean_object* v_ngen_1275_; lean_object* v_auxDeclNGen_1276_; lean_object* v_traceState_1277_; lean_object* v_cache_1278_; lean_object* v_messages_1279_; lean_object* v_infoState_1280_; lean_object* v_snapshotTasks_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref_known(v___x_1272_, 1);
v___x_1273_ = lean_st_ref_take(v___y_1242_);
v_env_1274_ = lean_ctor_get(v___x_1273_, 0);
v_ngen_1275_ = lean_ctor_get(v___x_1273_, 2);
v_auxDeclNGen_1276_ = lean_ctor_get(v___x_1273_, 3);
v_traceState_1277_ = lean_ctor_get(v___x_1273_, 4);
v_cache_1278_ = lean_ctor_get(v___x_1273_, 5);
v_messages_1279_ = lean_ctor_get(v___x_1273_, 6);
v_infoState_1280_ = lean_ctor_get(v___x_1273_, 7);
v_snapshotTasks_1281_ = lean_ctor_get(v___x_1273_, 8);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1307_ == 0)
{
lean_object* v_unused_1308_; 
v_unused_1308_ = lean_ctor_get(v___x_1273_, 1);
lean_dec(v_unused_1308_);
v___x_1283_ = v___x_1273_;
v_isShared_1284_ = v_isSharedCheck_1307_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_snapshotTasks_1281_);
lean_inc(v_infoState_1280_);
lean_inc(v_messages_1279_);
lean_inc(v_cache_1278_);
lean_inc(v_traceState_1277_);
lean_inc(v_auxDeclNGen_1276_);
lean_inc(v_ngen_1275_);
lean_inc(v_env_1274_);
lean_dec(v___x_1273_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1307_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 1, v_macroScope_1268_);
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_env_1274_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_macroScope_1268_);
lean_ctor_set(v_reuseFailAlloc_1306_, 2, v_ngen_1275_);
lean_ctor_set(v_reuseFailAlloc_1306_, 3, v_auxDeclNGen_1276_);
lean_ctor_set(v_reuseFailAlloc_1306_, 4, v_traceState_1277_);
lean_ctor_set(v_reuseFailAlloc_1306_, 5, v_cache_1278_);
lean_ctor_set(v_reuseFailAlloc_1306_, 6, v_messages_1279_);
lean_ctor_set(v_reuseFailAlloc_1306_, 7, v_infoState_1280_);
lean_ctor_set(v_reuseFailAlloc_1306_, 8, v_snapshotTasks_1281_);
v___x_1286_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = lean_st_ref_put(v___y_1242_, v___x_1286_);
v___x_1288_ = l_List_reverse___redArg(v_traceMsgs_1269_);
v___x_1289_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4(v___x_1288_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1296_ == 0)
{
lean_object* v_unused_1297_; 
v_unused_1297_ = lean_ctor_get(v___x_1289_, 0);
lean_dec(v_unused_1297_);
v___x_1291_ = v___x_1289_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_dec(v___x_1289_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v_a_1267_);
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1267_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_a_1267_);
v_a_1298_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1289_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1289_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v_traceMsgs_1269_);
lean_dec(v_macroScope_1268_);
lean_dec(v_a_1267_);
v_a_1309_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1272_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1272_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
else
{
lean_object* v_a_1317_; 
v_a_1317_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1265_, 2);
if (lean_obj_tag(v_a_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v_a_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v_a_1318_ = lean_ctor_get(v_a_1317_, 0);
lean_inc(v_a_1318_);
v_a_1319_ = lean_ctor_get(v_a_1317_, 1);
lean_inc_ref(v_a_1319_);
lean_dec_ref_known(v_a_1317_, 2);
v___x_1320_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___closed__0));
v___x_1321_ = lean_string_dec_eq(v_a_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1322_, 0, v_a_1319_);
v___x_1323_ = l_Lean_MessageData_ofFormat(v___x_1322_);
v___x_1324_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___redArg(v_a_1318_, v___x_1323_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v_a_1318_);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; 
lean_dec_ref(v_a_1319_);
v___x_1325_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg(v_a_1318_);
return v___x_1325_;
}
}
else
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg();
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___boxed(lean_object* v_x_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg(v_x_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg___lam__0(lean_object* v_stx_1338_, lean_object* v_output_1339_, lean_object* v_trees_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_lctx_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_lctx_1350_ = lean_ctor_get(v___y_1345_, 2);
lean_inc_ref(v_lctx_1350_);
v___x_1351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1351_, 0, v_lctx_1350_);
lean_ctor_set(v___x_1351_, 1, v_stx_1338_);
lean_ctor_set(v___x_1351_, 2, v_output_1339_);
v___x_1352_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
v___x_1353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v_trees_1340_);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg___lam__0___boxed(lean_object* v_stx_1355_, lean_object* v_output_1356_, lean_object* v_trees_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg___lam__0(v_stx_1355_, v_output_1356_, v_trees_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___lam__0(lean_object* v___y_1368_, lean_object* v_mkInfoTree_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v_a_1377_, lean_object* v_a_x3f_1378_){
_start:
{
lean_object* v___x_1380_; lean_object* v_infoState_1381_; lean_object* v_trees_1382_; lean_object* v___x_1383_; 
v___x_1380_ = lean_st_ref_get(v___y_1368_);
v_infoState_1381_ = lean_ctor_get(v___x_1380_, 7);
lean_inc_ref(v_infoState_1381_);
lean_dec(v___x_1380_);
v_trees_1382_ = lean_ctor_get(v_infoState_1381_, 2);
lean_inc_ref(v_trees_1382_);
lean_dec_ref(v_infoState_1381_);
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
lean_inc(v___y_1373_);
lean_inc_ref(v___y_1372_);
lean_inc(v___y_1371_);
lean_inc_ref(v___y_1370_);
v___x_1383_ = lean_apply_10(v_mkInfoTree_1369_, v_trees_1382_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1368_, lean_box(0));
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1422_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1422_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1422_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v_infoState_1389_; lean_object* v_env_1390_; lean_object* v_nextMacroScope_1391_; lean_object* v_ngen_1392_; lean_object* v_auxDeclNGen_1393_; lean_object* v_traceState_1394_; lean_object* v_cache_1395_; lean_object* v_messages_1396_; lean_object* v_snapshotTasks_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1421_; 
v___x_1388_ = lean_st_ref_take(v___y_1368_);
v_infoState_1389_ = lean_ctor_get(v___x_1388_, 7);
v_env_1390_ = lean_ctor_get(v___x_1388_, 0);
v_nextMacroScope_1391_ = lean_ctor_get(v___x_1388_, 1);
v_ngen_1392_ = lean_ctor_get(v___x_1388_, 2);
v_auxDeclNGen_1393_ = lean_ctor_get(v___x_1388_, 3);
v_traceState_1394_ = lean_ctor_get(v___x_1388_, 4);
v_cache_1395_ = lean_ctor_get(v___x_1388_, 5);
v_messages_1396_ = lean_ctor_get(v___x_1388_, 6);
v_snapshotTasks_1397_ = lean_ctor_get(v___x_1388_, 8);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1399_ = v___x_1388_;
v_isShared_1400_ = v_isSharedCheck_1421_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_snapshotTasks_1397_);
lean_inc(v_infoState_1389_);
lean_inc(v_messages_1396_);
lean_inc(v_cache_1395_);
lean_inc(v_traceState_1394_);
lean_inc(v_auxDeclNGen_1393_);
lean_inc(v_ngen_1392_);
lean_inc(v_nextMacroScope_1391_);
lean_inc(v_env_1390_);
lean_dec(v___x_1388_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1421_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
uint8_t v_enabled_1401_; lean_object* v_assignment_1402_; lean_object* v_lazyAssignment_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1419_; 
v_enabled_1401_ = lean_ctor_get_uint8(v_infoState_1389_, sizeof(void*)*3);
v_assignment_1402_ = lean_ctor_get(v_infoState_1389_, 0);
v_lazyAssignment_1403_ = lean_ctor_get(v_infoState_1389_, 1);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_infoState_1389_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; 
v_unused_1420_ = lean_ctor_get(v_infoState_1389_, 2);
lean_dec(v_unused_1420_);
v___x_1405_ = v_infoState_1389_;
v_isShared_1406_ = v_isSharedCheck_1419_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_lazyAssignment_1403_);
lean_inc(v_assignment_1402_);
lean_dec(v_infoState_1389_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1419_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1407_ = l_Lean_PersistentArray_push___redArg(v_a_1377_, v_a_1384_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 2, v___x_1407_);
v___x_1409_ = v___x_1405_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_assignment_1402_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_lazyAssignment_1403_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v___x_1407_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*3, v_enabled_1401_);
v___x_1409_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1411_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 7, v___x_1409_);
v___x_1411_ = v___x_1399_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_env_1390_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_nextMacroScope_1391_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_ngen_1392_);
lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_auxDeclNGen_1393_);
lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_traceState_1394_);
lean_ctor_set(v_reuseFailAlloc_1417_, 5, v_cache_1395_);
lean_ctor_set(v_reuseFailAlloc_1417_, 6, v_messages_1396_);
lean_ctor_set(v_reuseFailAlloc_1417_, 7, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1417_, 8, v_snapshotTasks_1397_);
v___x_1411_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1412_ = lean_st_ref_put(v___y_1368_, v___x_1411_);
v___x_1413_ = lean_box(0);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1413_);
v___x_1415_ = v___x_1386_;
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
}
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec_ref(v_a_1377_);
v_a_1423_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1383_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1383_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___lam__0___boxed(lean_object* v___y_1431_, lean_object* v_mkInfoTree_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v_a_1440_, lean_object* v_a_x3f_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___lam__0(v___y_1431_, v_mkInfoTree_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v_a_1440_, v_a_x3f_1441_);
lean_dec(v_a_x3f_1441_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1431_);
return v_res_1443_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1444_ = lean_unsigned_to_nat(32u);
v___x_1445_ = lean_mk_empty_array_with_capacity(v___x_1444_);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__1(void){
_start:
{
size_t v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1447_ = ((size_t)5ULL);
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = lean_unsigned_to_nat(32u);
v___x_1450_ = lean_mk_empty_array_with_capacity(v___x_1449_);
v___x_1451_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__0);
v___x_1452_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
lean_ctor_set(v___x_1452_, 1, v___x_1450_);
lean_ctor_set(v___x_1452_, 2, v___x_1448_);
lean_ctor_set(v___x_1452_, 3, v___x_1448_);
lean_ctor_set_usize(v___x_1452_, 4, v___x_1447_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg(lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; lean_object* v_infoState_1456_; lean_object* v_trees_1457_; lean_object* v___x_1458_; lean_object* v_infoState_1459_; lean_object* v_env_1460_; lean_object* v_nextMacroScope_1461_; lean_object* v_ngen_1462_; lean_object* v_auxDeclNGen_1463_; lean_object* v_traceState_1464_; lean_object* v_cache_1465_; lean_object* v_messages_1466_; lean_object* v_snapshotTasks_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1488_; 
v___x_1455_ = lean_st_ref_get(v___y_1453_);
v_infoState_1456_ = lean_ctor_get(v___x_1455_, 7);
lean_inc_ref(v_infoState_1456_);
lean_dec(v___x_1455_);
v_trees_1457_ = lean_ctor_get(v_infoState_1456_, 2);
lean_inc_ref(v_trees_1457_);
lean_dec_ref(v_infoState_1456_);
v___x_1458_ = lean_st_ref_take(v___y_1453_);
v_infoState_1459_ = lean_ctor_get(v___x_1458_, 7);
v_env_1460_ = lean_ctor_get(v___x_1458_, 0);
v_nextMacroScope_1461_ = lean_ctor_get(v___x_1458_, 1);
v_ngen_1462_ = lean_ctor_get(v___x_1458_, 2);
v_auxDeclNGen_1463_ = lean_ctor_get(v___x_1458_, 3);
v_traceState_1464_ = lean_ctor_get(v___x_1458_, 4);
v_cache_1465_ = lean_ctor_get(v___x_1458_, 5);
v_messages_1466_ = lean_ctor_get(v___x_1458_, 6);
v_snapshotTasks_1467_ = lean_ctor_get(v___x_1458_, 8);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1469_ = v___x_1458_;
v_isShared_1470_ = v_isSharedCheck_1488_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_snapshotTasks_1467_);
lean_inc(v_infoState_1459_);
lean_inc(v_messages_1466_);
lean_inc(v_cache_1465_);
lean_inc(v_traceState_1464_);
lean_inc(v_auxDeclNGen_1463_);
lean_inc(v_ngen_1462_);
lean_inc(v_nextMacroScope_1461_);
lean_inc(v_env_1460_);
lean_dec(v___x_1458_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1488_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
uint8_t v_enabled_1471_; lean_object* v_assignment_1472_; lean_object* v_lazyAssignment_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1486_; 
v_enabled_1471_ = lean_ctor_get_uint8(v_infoState_1459_, sizeof(void*)*3);
v_assignment_1472_ = lean_ctor_get(v_infoState_1459_, 0);
v_lazyAssignment_1473_ = lean_ctor_get(v_infoState_1459_, 1);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_infoState_1459_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v_infoState_1459_, 2);
lean_dec(v_unused_1487_);
v___x_1475_ = v_infoState_1459_;
v_isShared_1476_ = v_isSharedCheck_1486_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_lazyAssignment_1473_);
lean_inc(v_assignment_1472_);
lean_dec(v_infoState_1459_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1486_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1477_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__1);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 2, v___x_1477_);
v___x_1479_ = v___x_1475_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_assignment_1472_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_lazyAssignment_1473_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v___x_1477_);
lean_ctor_set_uint8(v_reuseFailAlloc_1485_, sizeof(void*)*3, v_enabled_1471_);
v___x_1479_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1481_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 7, v___x_1479_);
v___x_1481_ = v___x_1469_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_env_1460_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_nextMacroScope_1461_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_ngen_1462_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_auxDeclNGen_1463_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v_traceState_1464_);
lean_ctor_set(v_reuseFailAlloc_1484_, 5, v_cache_1465_);
lean_ctor_set(v_reuseFailAlloc_1484_, 6, v_messages_1466_);
lean_ctor_set(v_reuseFailAlloc_1484_, 7, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1484_, 8, v_snapshotTasks_1467_);
v___x_1481_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_st_ref_put(v___y_1453_, v___x_1481_);
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v_trees_1457_);
return v___x_1483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___boxed(lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg(v___y_1489_);
lean_dec(v___y_1489_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg(lean_object* v_x_1492_, lean_object* v_mkInfoTree_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; lean_object* v_infoState_1504_; uint8_t v_enabled_1505_; 
v___x_1503_ = lean_st_ref_get(v___y_1501_);
v_infoState_1504_ = lean_ctor_get(v___x_1503_, 7);
lean_inc_ref(v_infoState_1504_);
lean_dec(v___x_1503_);
v_enabled_1505_ = lean_ctor_get_uint8(v_infoState_1504_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1504_);
if (v_enabled_1505_ == 0)
{
lean_object* v___x_1506_; 
lean_dec_ref(v_mkInfoTree_1493_);
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
lean_inc(v___y_1497_);
lean_inc_ref(v___y_1496_);
lean_inc(v___y_1495_);
lean_inc_ref(v___y_1494_);
v___x_1506_ = lean_apply_9(v_x_1492_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, lean_box(0));
return v___x_1506_;
}
else
{
lean_object* v___x_1507_; lean_object* v_a_1508_; lean_object* v_r_1509_; 
v___x_1507_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg(v___y_1501_);
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref(v___x_1507_);
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
lean_inc(v___y_1497_);
lean_inc_ref(v___y_1496_);
lean_inc(v___y_1495_);
lean_inc_ref(v___y_1494_);
v_r_1509_ = lean_apply_9(v_x_1492_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, lean_box(0));
if (lean_obj_tag(v_r_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1534_; 
v_a_1510_ = lean_ctor_get(v_r_1509_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_r_1509_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1512_ = v_r_1509_;
v_isShared_1513_ = v_isSharedCheck_1534_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v_r_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1534_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
lean_inc(v_a_1510_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set_tag(v___x_1512_, 1);
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___lam__0(v___y_1501_, v_mkInfoTree_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v_a_1508_, v___x_1515_);
lean_dec_ref(v___x_1515_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1523_ == 0)
{
lean_object* v_unused_1524_; 
v_unused_1524_ = lean_ctor_get(v___x_1516_, 0);
lean_dec(v_unused_1524_);
v___x_1518_ = v___x_1516_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_dec(v___x_1516_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v_a_1510_);
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1510_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_a_1510_);
v_a_1525_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1516_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1516_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_a_1535_ = lean_ctor_get(v_r_1509_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v_r_1509_, 1);
v___x_1536_ = lean_box(0);
v___x_1537_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___lam__0(v___y_1501_, v_mkInfoTree_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v_a_1508_, v___x_1536_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v___x_1537_, 0);
lean_dec(v_unused_1545_);
v___x_1539_ = v___x_1537_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_dec(v___x_1537_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 1);
lean_ctor_set(v___x_1539_, 0, v_a_1535_);
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1535_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_a_1535_);
v_a_1546_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1537_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1537_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___boxed(lean_object* v_x_1554_, lean_object* v_mkInfoTree_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg(v_x_1554_, v_mkInfoTree_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg(lean_object* v_stx_1566_, lean_object* v_output_1567_, lean_object* v_x_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___f_1578_; lean_object* v___x_1579_; 
v___f_1578_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1578_, 0, v_stx_1566_);
lean_closure_set(v___f_1578_, 1, v_output_1567_);
v___x_1579_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg(v_x_1568_, v___f_1578_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg___boxed(lean_object* v_stx_1580_, lean_object* v_output_1581_, lean_object* v_x_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg(v_stx_1580_, v_output_1581_, v_x_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalMatch(lean_object* v_stx_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_Elab_Tactic_getMainTag___redArg(v_a_1608_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
lean_inc(v_stx_1606_);
v___x_1618_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___boxed), 4, 2);
lean_closure_set(v___x_1618_, 0, v_a_1617_);
lean_closure_set(v___x_1618_, 1, v_stx_1606_);
v___x_1619_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg(v___x_1618_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v_fst_1621_; lean_object* v_snd_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1648_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v_fst_1621_ = lean_ctor_get(v_a_1620_, 0);
v_snd_1622_ = lean_ctor_get(v_a_1620_, 1);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_a_1620_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1624_ = v_a_1620_;
v_isShared_1625_ = v_isSharedCheck_1648_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_snd_1622_);
lean_inc(v_fst_1621_);
lean_dec(v_a_1620_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1648_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v_ref_1626_; uint8_t v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v_ref_1626_ = lean_ctor_get(v_a_1613_, 5);
v___x_1627_ = 0;
v___x_1628_ = l_Lean_SourceInfo_fromRef(v_ref_1626_, v___x_1627_);
v___x_1629_ = ((lean_object*)(l_Lean_Elab_Tactic_evalMatch___closed__0));
v___x_1630_ = ((lean_object*)(l_Lean_Elab_Tactic_evalMatch___closed__1));
lean_inc(v___x_1628_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set_tag(v___x_1624_, 2);
lean_ctor_set(v___x_1624_, 1, v___x_1629_);
lean_ctor_set(v___x_1624_, 0, v___x_1628_);
v___x_1632_ = v___x_1624_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v___x_1629_);
v___x_1632_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___f_1645_; lean_object* v___x_1646_; 
v___x_1633_ = ((lean_object*)(l_Lean_Elab_Tactic_evalMatch___closed__3));
v___x_1634_ = ((lean_object*)(l_Lean_Elab_Tactic_evalMatch___closed__4));
lean_inc_n(v___x_1628_, 2);
v___x_1635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1628_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l_Lean_Syntax_node2(v___x_1628_, v___x_1633_, v___x_1635_, v_fst_1621_);
v___x_1637_ = l_Lean_Syntax_node2(v___x_1628_, v___x_1630_, v___x_1632_, v___x_1636_);
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = lean_mk_empty_array_with_capacity(v___x_1638_);
v___x_1640_ = lean_array_push(v___x_1639_, v___x_1637_);
v___x_1641_ = l_Array_append___redArg(v___x_1640_, v_snd_1622_);
lean_dec(v_snd_1622_);
v___x_1642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__4));
v___x_1643_ = lean_box(2);
v___x_1644_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v___x_1642_);
lean_ctor_set(v___x_1644_, 2, v___x_1641_);
lean_inc_ref(v___x_1644_);
lean_inc(v_stx_1606_);
v___f_1645_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalMatch___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1645_, 0, v_stx_1606_);
lean_closure_set(v___f_1645_, 1, v___x_1644_);
v___x_1646_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg(v_stx_1606_, v___x_1644_, v___f_1645_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1646_;
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_stx_1606_);
v_a_1649_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1619_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1619_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec(v_stx_1606_);
v_a_1657_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1616_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1616_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalMatch___boxed(lean_object* v_stx_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_Elab_Tactic_evalMatch(v_stx_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1(lean_object* v_00_u03b1_1676_, lean_object* v_x_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___redArg(v_x_1677_, v___y_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1681_, lean_object* v_x_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1(v_00_u03b1_1681_, v_x_1682_, v___y_1683_, v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec_ref(v_x_1682_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6(lean_object* v_00_u03b1_1686_, lean_object* v_ref_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg(v_ref_1687_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___boxed(lean_object* v_00_u03b1_1698_, lean_object* v_ref_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6(v_00_u03b1_1698_, v_ref_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7(lean_object* v_00_u03b1_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg();
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___boxed(lean_object* v_00_u03b1_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7(v_00_u03b1_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0(lean_object* v_00_u03b1_1732_, lean_object* v_x_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg(v_x_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___boxed(lean_object* v_00_u03b1_1744_, lean_object* v_x_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0(v_00_u03b1_1744_, v_x_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1(lean_object* v_00_u03b1_1756_, lean_object* v_stx_1757_, lean_object* v_output_1758_, lean_object* v_x_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg(v_stx_1757_, v_output_1758_, v_x_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___boxed(lean_object* v_00_u03b1_1770_, lean_object* v_stx_1771_, lean_object* v_output_1772_, lean_object* v_x_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1(v_00_u03b1_1770_, v_stx_1771_, v_output_1772_, v_x_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0(lean_object* v_cls_1784_, lean_object* v_msg_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg(v_cls_1784_, v_msg_1785_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___boxed(lean_object* v_cls_1796_, lean_object* v_msg_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0(v_cls_1796_, v_msg_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3(lean_object* v_as_1808_, lean_object* v_as_x27_1809_, lean_object* v_b_1810_, lean_object* v_a_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___redArg(v_as_x27_1809_, v_b_1810_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___boxed(lean_object* v_as_1822_, lean_object* v_as_x27_1823_, lean_object* v_b_1824_, lean_object* v_a_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3(v_as_1822_, v_as_x27_1823_, v_b_1824_, v_a_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_as_x27_1823_);
lean_dec(v_as_1822_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5(lean_object* v_00_u03b1_1836_, lean_object* v_ref_1837_, lean_object* v_msg_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___redArg(v_ref_1837_, v_msg_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1849_, lean_object* v_ref_1850_, lean_object* v_msg_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5(v_00_u03b1_1849_, v_ref_1850_, v_msg_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v_ref_1850_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15(lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg(v___y_1869_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___boxed(lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15(v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9(lean_object* v_00_u03b1_1882_, lean_object* v_x_1883_, lean_object* v_mkInfoTree_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg(v_x_1883_, v_mkInfoTree_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___boxed(lean_object* v_00_u03b1_1895_, lean_object* v_x_1896_, lean_object* v_mkInfoTree_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9(v_00_u03b1_1895_, v_x_1896_, v_mkInfoTree_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1908_, lean_object* v_m_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg(v_m_1909_, v_a_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1912_, lean_object* v_m_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6(v_00_u03b2_1912_, v_m_1913_, v_a_1914_);
lean_dec(v_a_1914_);
lean_dec_ref(v_m_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10(lean_object* v_00_u03b1_1916_, lean_object* v_msg_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___redArg(v_msg_1917_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___boxed(lean_object* v_00_u03b1_1928_, lean_object* v_msg_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10(v_00_u03b1_1928_, v_msg_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
return v_res_1939_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_1940_, lean_object* v_x_1941_, lean_object* v_x_1942_){
_start:
{
uint8_t v___x_1943_; 
v___x_1943_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___redArg(v_x_1941_, v_x_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1944_, lean_object* v_x_1945_, lean_object* v_x_1946_){
_start:
{
uint8_t v_res_1947_; lean_object* v_r_1948_; 
v_res_1947_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8(v_00_u03b2_1944_, v_x_1945_, v_x_1946_);
lean_dec_ref(v_x_1946_);
lean_dec_ref(v_x_1945_);
v_r_1948_ = lean_box(v_res_1947_);
return v_r_1948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11(lean_object* v_00_u03b2_1949_, lean_object* v_m_1950_, lean_object* v_query_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___redArg(v_m_1950_, v_query_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___boxed(lean_object* v_00_u03b2_1953_, lean_object* v_m_1954_, lean_object* v_query_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11(v_00_u03b2_1953_, v_m_1954_, v_query_1955_);
lean_dec(v_query_1955_);
lean_dec_ref(v_m_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14(lean_object* v_00_u03b2_1957_, lean_object* v_x_1958_, size_t v_x_1959_, lean_object* v_x_1960_){
_start:
{
uint8_t v___x_1961_; 
v___x_1961_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg(v_x_1958_, v_x_1959_, v_x_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_, lean_object* v_x_1965_){
_start:
{
size_t v_x_26734__boxed_1966_; uint8_t v_res_1967_; lean_object* v_r_1968_; 
v_x_26734__boxed_1966_ = lean_unbox_usize(v_x_1964_);
lean_dec(v_x_1964_);
v_res_1967_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14(v_00_u03b2_1962_, v_x_1963_, v_x_26734__boxed_1966_, v_x_1965_);
lean_dec_ref(v_x_1965_);
lean_dec_ref(v_x_1963_);
v_r_1968_ = lean_box(v_res_1967_);
return v_r_1968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18(lean_object* v_00_u03b2_1969_, lean_object* v_m_1970_, lean_object* v_query_1971_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18___redArg(v_m_1970_, v_query_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18___boxed(lean_object* v_00_u03b2_1973_, lean_object* v_m_1974_, lean_object* v_query_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18(v_00_u03b2_1973_, v_m_1974_, v_query_1975_);
lean_dec(v_query_1975_);
lean_dec_ref(v_m_1974_);
return v_res_1976_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18(lean_object* v_00_u03b2_1977_, lean_object* v_keys_1978_, lean_object* v_vals_1979_, lean_object* v_heq_1980_, lean_object* v_i_1981_, lean_object* v_k_1982_){
_start:
{
uint8_t v___x_1983_; 
v___x_1983_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___redArg(v_keys_1978_, v_i_1981_, v_k_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___boxed(lean_object* v_00_u03b2_1984_, lean_object* v_keys_1985_, lean_object* v_vals_1986_, lean_object* v_heq_1987_, lean_object* v_i_1988_, lean_object* v_k_1989_){
_start:
{
uint8_t v_res_1990_; lean_object* v_r_1991_; 
v_res_1990_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18(v_00_u03b2_1984_, v_keys_1985_, v_vals_1986_, v_heq_1987_, v_i_1988_, v_k_1989_);
lean_dec_ref(v_k_1989_);
lean_dec_ref(v_vals_1986_);
lean_dec_ref(v_keys_1985_);
v_r_1991_ = lean_box(v_res_1990_);
return v_r_1991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18_spec__21(lean_object* v_00_u03b2_1992_, lean_object* v_m_1993_, lean_object* v_query_1994_, lean_object* v_x_1995_, lean_object* v_x_1996_, lean_object* v_x_1997_, lean_object* v_x_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18_spec__21___redArg(v_m_1993_, v_query_1994_, v_x_1995_, v_x_1996_, v_x_1997_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18_spec__21___boxed(lean_object* v_00_u03b2_2000_, lean_object* v_m_2001_, lean_object* v_query_2002_, lean_object* v_x_2003_, lean_object* v_x_2004_, lean_object* v_x_2005_, lean_object* v_x_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11_spec__18_spec__21(v_00_u03b2_2000_, v_m_2001_, v_query_2002_, v_x_2003_, v_x_2004_, v_x_2005_, v_x_2006_);
lean_dec(v_query_2002_);
lean_dec_ref(v_m_2001_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1(){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2021_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2022_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0));
v___x_2023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3));
v___x_2024_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalMatch___boxed), 10, 0);
v___x_2025_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2021_, v___x_2022_, v___x_2023_, v___x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___boxed(lean_object* v_a_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1();
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3(){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3));
v___x_2055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__6));
v___x_2056_ = l_Lean_addBuiltinDeclarationRanges(v___x_2054_, v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___boxed(lean_object* v_a_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3();
return v_res_2058_;
}
}
lean_object* runtime_initialize_Lean_Elab_Match(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Induction(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Match(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Match(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Induction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Match(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Match(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Induction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Match(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Match(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Induction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Match(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Match(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Match(builtin);
}
#ifdef __cplusplus
}
#endif
