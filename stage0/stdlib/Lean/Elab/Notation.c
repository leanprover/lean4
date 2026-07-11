// Lean compiler output
// Module: Lean.Elab.Notation
// Imports: public import Lean.Elab.Syntax public import Lean.Elab.AuxDef public import Lean.Elab.BuiltinNotation
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_strLitToPattern___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object*);
lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_topDown(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
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
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Macro_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Command_visibility_ofAttrKind(lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_isLocalAttrKind(lean_object*);
extern lean_object* l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSyntax(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_evalOptPrio___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0 = (const lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1 = (const lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2 = (const lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3 = (const lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inherit_doc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(83, 8, 69, 42, 53, 230, 51, 166)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_addInheritDocDefault___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_addInheritDocDefault___closed__0 = (const lean_object*)&l_Lean_Elab_Command_addInheritDocDefault___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_addInheritDocDefault___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_addInheritDocDefault___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Command_addInheritDocDefault___closed__1 = (const lean_object*)&l_Lean_Elab_Command_addInheritDocDefault___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_addInheritDocDefault___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Command_addInheritDocDefault___closed__2 = (const lean_object*)&l_Lean_Elab_Command_addInheritDocDefault___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addInheritDocDefault(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cat"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1_value),LEAN_SCALAR_PTR_LITERAL(95, 91, 11, 245, 227, 176, 7, 196)}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "precedence"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 243, 176, 51, 48, 112, 202, 160)}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6_value;
static const lean_array_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "identPrec"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9_value),LEAN_SCALAR_PTR_LITERAL(251, 25, 252, 182, 120, 175, 78, 126)}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unicodeAtom"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13_value),LEAN_SCALAR_PTR_LITERAL(29, 147, 94, 13, 45, 35, 101, 109)}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "atom"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15_value),LEAN_SCALAR_PTR_LITERAL(144, 22, 146, 169, 39, 242, 124, 88)}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_removeParentheses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Elab_Command_removeParentheses___closed__0 = (const lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Lean_Elab_Command_removeParentheses___closed__1 = (const lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_removeParentheses___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_Elab_Command_removeParentheses___closed__2 = (const lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__2_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean_Elab_Command_removeParentheses___closed__3 = (const lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_removeParentheses___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Elab_Command_removeParentheses___closed__4 = (const lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_removeParentheses___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__4_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Elab_Command_removeParentheses___closed__5 = (const lean_object*)&l_Lean_Elab_Command_removeParentheses___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0;
LEAN_EXPORT uint8_t l_Lean_Elab_Command_hasDuplicateAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "antiquot"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__0 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 107, 218, 203, 20, 35, 251, 156)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__1 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__2 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__3 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Command_mkUnexpander___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__4;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__3_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__5 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "antiquotName"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__6 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__6_value),LEAN_SCALAR_PTR_LITERAL(67, 48, 35, 197, 163, 216, 250, 79)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__7 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__8 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__9 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__9_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__10 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__11 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__11_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__12 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__13 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "app_unexpander"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__14 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Command_mkUnexpander___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__15;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__14_value),LEAN_SCALAR_PTR_LITERAL(173, 94, 177, 152, 198, 163, 81, 20)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__16 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__16_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__17 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__17_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "unexpand"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__18 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Command_mkUnexpander___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__19;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__18_value),LEAN_SCALAR_PTR_LITERAL(42, 154, 37, 229, 99, 64, 199, 76)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__20 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.PrettyPrinter.Unexpander"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__21 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Command_mkUnexpander___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__22;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__23 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__23_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Unexpander"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__24 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__23_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__24_value),LEAN_SCALAR_PTR_LITERAL(127, 37, 73, 100, 13, 145, 76, 255)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__25 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__25_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__26 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__26_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__27 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__27_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__27_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__28 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__28_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__29 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__29_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__29_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__30 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__30_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__31 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__31_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__31_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__32 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__32_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__33 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__33_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__34 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__34_value),LEAN_SCALAR_PTR_LITERAL(145, 163, 173, 41, 168, 168, 65, 81)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__35 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__35_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`("};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__36 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__36_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__37 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__37_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__38 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__38_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "withRef"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__39 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__39_value;
static lean_once_cell_t l_Lean_Elab_Command_mkUnexpander___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__40;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__39_value),LEAN_SCALAR_PTR_LITERAL(193, 74, 233, 14, 30, 198, 157, 185)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__41 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__41_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__42_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__39_value),LEAN_SCALAR_PTR_LITERAL(128, 176, 237, 189, 54, 129, 101, 238)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__42 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__42_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__43 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__43_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__43_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__44 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__44_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__45 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__45_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "throw"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__46 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__46_value;
static lean_once_cell_t l_Lean_Elab_Command_mkUnexpander___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__47;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__46_value),LEAN_SCALAR_PTR_LITERAL(60, 81, 80, 209, 187, 239, 255, 113)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__48 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__48_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MonadExcept"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__49 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__49_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__49_value),LEAN_SCALAR_PTR_LITERAL(162, 154, 253, 120, 110, 153, 103, 113)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__50_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__46_value),LEAN_SCALAR_PTR_LITERAL(121, 11, 61, 69, 62, 207, 229, 53)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__50 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__50_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__51 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__51_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__51_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__52 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__52_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__53 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__53_value;
static const lean_string_object l_Lean_Elab_Command_mkUnexpander___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__54 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__54_value;
static lean_once_cell_t l_Lean_Elab_Command_mkUnexpander___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__55;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__56_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__56_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__56 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__56_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__56_value)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__57 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__57_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__58_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__58_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__58 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__58_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__58_value)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__59 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__59_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__60_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__60_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__60 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__60_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__60_value)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__61 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__61_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__62_value_aux_0),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 144, 98, 72, 115, 31, 20, 74)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__62 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__62_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__62_value)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__63 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__63_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__63_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__64 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__64_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__61_value),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__64_value)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__65 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__65_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__59_value),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__65_value)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__66 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__66_value;
static const lean_ctor_object l_Lean_Elab_Command_mkUnexpander___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__57_value),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__66_value)}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__67 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__67_value;
static const lean_array_object l_Lean_Elab_Command_mkUnexpander___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_mkUnexpander___closed__68 = (const lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__68_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "notation"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 34, 53, 7, 182, 20, 8, 182)}};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "macro_rules"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__2_value),LEAN_SCALAR_PTR_LITERAL(125, 80, 75, 5, 165, 87, 197, 1)}};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "precheckedQuot"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__6_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__9_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__12_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabNotation___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabNotation___closed__14_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Command_elabNotation___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_Command_elabNotation___boxed__const__1 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabNotation"};
static const lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 81, 117, 114, 113, 220, 215, 248)}};
static const lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(lean_object* v_id_1_, lean_object* v_as_2_, size_t v_i_3_, size_t v_stop_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_eq(v_i_3_, v_stop_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_6_ = lean_array_uget_borrowed(v_as_2_, v_i_3_);
v___x_7_ = l_Lean_Syntax_getId(v___x_6_);
v___x_8_ = l_Lean_TSyntax_getId(v_id_1_);
v___x_9_ = lean_name_eq(v___x_7_, v___x_8_);
lean_dec(v___x_8_);
lean_dec(v___x_7_);
if (v___x_9_ == 0)
{
size_t v___x_10_; size_t v___x_11_; 
v___x_10_ = ((size_t)1ULL);
v___x_11_ = lean_usize_add(v_i_3_, v___x_10_);
v_i_3_ = v___x_11_;
goto _start;
}
else
{
return v___x_9_;
}
}
else
{
uint8_t v___x_13_; 
v___x_13_ = 0;
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1___boxed(lean_object* v_id_14_, lean_object* v_as_15_, lean_object* v_i_16_, lean_object* v_stop_17_){
_start:
{
size_t v_i_boxed_18_; size_t v_stop_boxed_19_; uint8_t v_res_20_; lean_object* v_r_21_; 
v_i_boxed_18_ = lean_unbox_usize(v_i_16_);
lean_dec(v_i_16_);
v_stop_boxed_19_ = lean_unbox_usize(v_stop_17_);
lean_dec(v_stop_17_);
v_res_20_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(v_id_14_, v_as_15_, v_i_boxed_18_, v_stop_boxed_19_);
lean_dec_ref(v_as_15_);
lean_dec(v_id_14_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(lean_object* v_vars_28_, lean_object* v_x_29_){
_start:
{
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_x_29_);
v___x_31_ = l_Lean_Syntax_isOfKind(v_x_29_, v___x_30_);
if (v___x_31_ == 0)
{
if (lean_obj_tag(v_x_29_) == 1)
{
lean_object* v_info_32_; lean_object* v_kind_33_; lean_object* v_args_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_44_; 
v_info_32_ = lean_ctor_get(v_x_29_, 0);
v_kind_33_ = lean_ctor_get(v_x_29_, 1);
v_args_34_ = lean_ctor_get(v_x_29_, 2);
v_isSharedCheck_44_ = !lean_is_exclusive(v_x_29_);
if (v_isSharedCheck_44_ == 0)
{
v___x_36_ = v_x_29_;
v_isShared_37_ = v_isSharedCheck_44_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_args_34_);
lean_inc(v_kind_33_);
lean_inc(v_info_32_);
lean_dec(v_x_29_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_44_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
size_t v_sz_38_; size_t v___x_39_; lean_object* v___x_40_; lean_object* v___x_42_; 
v_sz_38_ = lean_array_size(v_args_34_);
v___x_39_ = ((size_t)0ULL);
v___x_40_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(v_vars_28_, v_sz_38_, v___x_39_, v_args_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 2, v___x_40_);
v___x_42_ = v___x_36_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_info_32_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v_kind_33_);
lean_ctor_set(v_reuseFailAlloc_43_, 2, v___x_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
else
{
return v_x_29_;
}
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_array_get_size(v_vars_28_);
v___x_47_ = lean_nat_dec_lt(v___x_45_, v___x_46_);
if (v___x_47_ == 0)
{
return v_x_29_;
}
else
{
if (v___x_47_ == 0)
{
return v_x_29_;
}
else
{
size_t v___x_48_; size_t v___x_49_; uint8_t v___x_50_; 
v___x_48_ = ((size_t)0ULL);
v___x_49_ = lean_usize_of_nat(v___x_46_);
v___x_50_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(v_x_29_, v_vars_28_, v___x_48_, v___x_49_);
if (v___x_50_ == 0)
{
return v_x_29_;
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
v___x_52_ = lean_box(0);
v___x_53_ = l_Lean_Syntax_mkAntiquotNode(v___x_51_, v_x_29_, v___x_45_, v___x_52_, v___x_31_);
return v___x_53_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(lean_object* v_vars_54_, size_t v_sz_55_, size_t v_i_56_, lean_object* v_bs_57_){
_start:
{
uint8_t v___x_58_; 
v___x_58_ = lean_usize_dec_lt(v_i_56_, v_sz_55_);
if (v___x_58_ == 0)
{
return v_bs_57_;
}
else
{
lean_object* v_v_59_; lean_object* v___x_60_; lean_object* v_bs_x27_61_; lean_object* v___x_62_; size_t v___x_63_; size_t v___x_64_; lean_object* v___x_65_; 
v_v_59_ = lean_array_uget(v_bs_57_, v_i_56_);
v___x_60_ = lean_unsigned_to_nat(0u);
v_bs_x27_61_ = lean_array_uset(v_bs_57_, v_i_56_, v___x_60_);
v___x_62_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(v_vars_54_, v_v_59_);
v___x_63_ = ((size_t)1ULL);
v___x_64_ = lean_usize_add(v_i_56_, v___x_63_);
v___x_65_ = lean_array_uset(v_bs_x27_61_, v_i_56_, v___x_62_);
v_i_56_ = v___x_64_;
v_bs_57_ = v___x_65_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0___boxed(lean_object* v_vars_67_, lean_object* v_sz_68_, lean_object* v_i_69_, lean_object* v_bs_70_){
_start:
{
size_t v_sz_boxed_71_; size_t v_i_boxed_72_; lean_object* v_res_73_; 
v_sz_boxed_71_ = lean_unbox_usize(v_sz_68_);
lean_dec(v_sz_68_);
v_i_boxed_72_ = lean_unbox_usize(v_i_69_);
lean_dec(v_i_69_);
v_res_73_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(v_vars_67_, v_sz_boxed_71_, v_i_boxed_72_, v_bs_70_);
lean_dec_ref(v_vars_67_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___boxed(lean_object* v_vars_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(v_vars_74_, v_x_75_);
lean_dec_ref(v_vars_74_);
return v_res_76_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14(void){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Array_mkArray0(lean_box(0));
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(uint8_t v___x_106_, lean_object* v___x_107_, size_t v_sz_108_, size_t v_i_109_, lean_object* v_bs_110_){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = lean_usize_dec_lt(v_i_109_, v_sz_108_);
if (v___x_111_ == 0)
{
lean_dec(v___x_107_);
return v_bs_110_;
}
else
{
lean_object* v___x_112_; lean_object* v_v_113_; lean_object* v___x_114_; lean_object* v_bs_x27_115_; lean_object* v___y_117_; uint8_t v___x_122_; 
v___x_112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
v_v_113_ = lean_array_uget(v_bs_110_, v_i_109_);
v___x_114_ = lean_unsigned_to_nat(0u);
v_bs_x27_115_ = lean_array_uset(v_bs_110_, v_i_109_, v___x_114_);
lean_inc(v_v_113_);
v___x_122_ = l_Lean_Syntax_isOfKind(v_v_113_, v___x_112_);
if (v___x_122_ == 0)
{
v___y_117_ = v_v_113_;
goto v___jp_116_;
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = l_Lean_Syntax_getArg(v_v_113_, v___x_114_);
v___x_124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(v___x_123_);
v___x_125_ = l_Lean_Syntax_isOfKind(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_dec(v___x_123_);
v___y_117_ = v_v_113_;
goto v___jp_116_;
}
else
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = l_Lean_Syntax_getArg(v___x_123_, v___x_114_);
lean_dec(v___x_123_);
v___x_127_ = l_Lean_Syntax_matchesNull(v___x_126_, v___x_114_);
if (v___x_127_ == 0)
{
v___y_117_ = v_v_113_;
goto v___jp_116_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = l_Lean_Syntax_getArg(v_v_113_, v___x_128_);
v___x_130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
lean_inc(v___x_129_);
v___x_131_ = l_Lean_Syntax_isOfKind(v___x_129_, v___x_130_);
if (v___x_131_ == 0)
{
lean_dec(v___x_129_);
v___y_117_ = v_v_113_;
goto v___jp_116_;
}
else
{
lean_object* v___x_132_; lean_object* v_attr_133_; uint8_t v___x_134_; 
v___x_132_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
v_attr_133_ = l_Lean_Syntax_getArg(v___x_129_, v___x_114_);
lean_inc(v_attr_133_);
v___x_134_ = l_Lean_Syntax_isOfKind(v_attr_133_, v___x_132_);
if (v___x_134_ == 0)
{
lean_dec(v_attr_133_);
lean_dec(v___x_129_);
v___y_117_ = v_v_113_;
goto v___jp_116_;
}
else
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = l_Lean_Syntax_getArg(v___x_129_, v___x_128_);
lean_dec(v___x_129_);
v___x_136_ = l_Lean_Syntax_matchesNull(v___x_135_, v___x_114_);
if (v___x_136_ == 0)
{
lean_dec(v_attr_133_);
v___y_117_ = v_v_113_;
goto v___jp_116_;
}
else
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_137_ = l_Lean_TSyntax_getId(v_attr_133_);
v___x_138_ = l_Lean_Name_eraseMacroScopes(v___x_137_);
lean_dec(v___x_137_);
v___x_139_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11));
v___x_140_ = lean_name_eq(v___x_138_, v___x_139_);
lean_dec(v___x_138_);
if (v___x_140_ == 0)
{
lean_dec(v_attr_133_);
v___y_117_ = v_v_113_;
goto v___jp_116_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_v_113_);
v___x_141_ = lean_box(0);
v___x_142_ = l_Lean_SourceInfo_fromRef(v___x_141_, v___x_106_);
v___x_143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_144_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
lean_inc_n(v___x_142_, 4);
v___x_145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_142_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
lean_ctor_set(v___x_145_, 2, v___x_144_);
v___x_146_ = l_Lean_Syntax_node1(v___x_142_, v___x_124_, v___x_145_);
lean_inc(v___x_107_);
v___x_147_ = l_Lean_Syntax_node1(v___x_142_, v___x_143_, v___x_107_);
v___x_148_ = l_Lean_Syntax_node2(v___x_142_, v___x_130_, v_attr_133_, v___x_147_);
v___x_149_ = l_Lean_Syntax_node2(v___x_142_, v___x_112_, v___x_146_, v___x_148_);
v___y_117_ = v___x_149_;
goto v___jp_116_;
}
}
}
}
}
}
}
v___jp_116_:
{
size_t v___x_118_; size_t v___x_119_; lean_object* v___x_120_; 
v___x_118_ = ((size_t)1ULL);
v___x_119_ = lean_usize_add(v_i_109_, v___x_118_);
v___x_120_ = lean_array_uset(v_bs_x27_115_, v_i_109_, v___y_117_);
v_i_109_ = v___x_119_;
v_bs_110_ = v___x_120_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___boxed(lean_object* v___x_150_, lean_object* v___x_151_, lean_object* v_sz_152_, lean_object* v_i_153_, lean_object* v_bs_154_){
_start:
{
uint8_t v___x_10694__boxed_155_; size_t v_sz_boxed_156_; size_t v_i_boxed_157_; lean_object* v_res_158_; 
v___x_10694__boxed_155_ = lean_unbox(v___x_150_);
v_sz_boxed_156_ = lean_unbox_usize(v_sz_152_);
lean_dec(v_sz_152_);
v_i_boxed_157_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_res_158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(v___x_10694__boxed_155_, v___x_151_, v_sz_boxed_156_, v_i_boxed_157_, v_bs_154_);
return v_res_158_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0(void){
_start:
{
uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = 0;
v___x_160_ = lean_box(0);
v___x_161_ = l_Lean_SourceInfo_fromRef(v___x_160_, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_162_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
v___x_163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_164_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0);
v___x_165_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_163_);
lean_ctor_set(v___x_165_, 2, v___x_162_);
return v___x_165_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_166_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1);
v___x_167_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
v___x_168_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0);
v___x_169_ = l_Lean_Syntax_node1(v___x_168_, v___x_167_, v___x_166_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(lean_object* v___x_170_, size_t v_sz_171_, size_t v_i_172_, lean_object* v_bs_173_){
_start:
{
uint8_t v___x_174_; 
v___x_174_ = lean_usize_dec_lt(v_i_172_, v_sz_171_);
if (v___x_174_ == 0)
{
lean_dec(v___x_170_);
return v_bs_173_;
}
else
{
lean_object* v___x_175_; lean_object* v_v_176_; lean_object* v___x_177_; lean_object* v_bs_x27_178_; lean_object* v___y_180_; uint8_t v___x_185_; 
v___x_175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
v_v_176_ = lean_array_uget(v_bs_173_, v_i_172_);
v___x_177_ = lean_unsigned_to_nat(0u);
v_bs_x27_178_ = lean_array_uset(v_bs_173_, v_i_172_, v___x_177_);
lean_inc(v_v_176_);
v___x_185_ = l_Lean_Syntax_isOfKind(v_v_176_, v___x_175_);
if (v___x_185_ == 0)
{
v___y_180_ = v_v_176_;
goto v___jp_179_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_186_ = l_Lean_Syntax_getArg(v_v_176_, v___x_177_);
v___x_187_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(v___x_186_);
v___x_188_ = l_Lean_Syntax_isOfKind(v___x_186_, v___x_187_);
if (v___x_188_ == 0)
{
lean_dec(v___x_186_);
v___y_180_ = v_v_176_;
goto v___jp_179_;
}
else
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = l_Lean_Syntax_getArg(v___x_186_, v___x_177_);
lean_dec(v___x_186_);
v___x_190_ = l_Lean_Syntax_matchesNull(v___x_189_, v___x_177_);
if (v___x_190_ == 0)
{
v___y_180_ = v_v_176_;
goto v___jp_179_;
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = l_Lean_Syntax_getArg(v_v_176_, v___x_191_);
v___x_193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
lean_inc(v___x_192_);
v___x_194_ = l_Lean_Syntax_isOfKind(v___x_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_dec(v___x_192_);
v___y_180_ = v_v_176_;
goto v___jp_179_;
}
else
{
lean_object* v___x_195_; lean_object* v_attr_196_; uint8_t v___x_197_; 
v___x_195_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
v_attr_196_ = l_Lean_Syntax_getArg(v___x_192_, v___x_177_);
lean_inc(v_attr_196_);
v___x_197_ = l_Lean_Syntax_isOfKind(v_attr_196_, v___x_195_);
if (v___x_197_ == 0)
{
lean_dec(v_attr_196_);
lean_dec(v___x_192_);
v___y_180_ = v_v_176_;
goto v___jp_179_;
}
else
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = l_Lean_Syntax_getArg(v___x_192_, v___x_191_);
lean_dec(v___x_192_);
v___x_199_ = l_Lean_Syntax_matchesNull(v___x_198_, v___x_177_);
if (v___x_199_ == 0)
{
lean_dec(v_attr_196_);
v___y_180_ = v_v_176_;
goto v___jp_179_;
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_200_ = l_Lean_TSyntax_getId(v_attr_196_);
v___x_201_ = l_Lean_Name_eraseMacroScopes(v___x_200_);
lean_dec(v___x_200_);
v___x_202_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11));
v___x_203_ = lean_name_eq(v___x_201_, v___x_202_);
lean_dec(v___x_201_);
if (v___x_203_ == 0)
{
lean_dec(v_attr_196_);
v___y_180_ = v_v_176_;
goto v___jp_179_;
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec(v_v_176_);
v___x_204_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0);
v___x_205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_206_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2);
lean_inc(v___x_170_);
v___x_207_ = l_Lean_Syntax_node1(v___x_204_, v___x_205_, v___x_170_);
v___x_208_ = l_Lean_Syntax_node2(v___x_204_, v___x_193_, v_attr_196_, v___x_207_);
v___x_209_ = l_Lean_Syntax_node2(v___x_204_, v___x_175_, v___x_206_, v___x_208_);
v___y_180_ = v___x_209_;
goto v___jp_179_;
}
}
}
}
}
}
}
v___jp_179_:
{
size_t v___x_181_; size_t v___x_182_; lean_object* v___x_183_; 
v___x_181_ = ((size_t)1ULL);
v___x_182_ = lean_usize_add(v_i_172_, v___x_181_);
v___x_183_ = lean_array_uset(v_bs_x27_178_, v_i_172_, v___y_180_);
v_i_172_ = v___x_182_;
v_bs_173_ = v___x_183_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___boxed(lean_object* v___x_210_, lean_object* v_sz_211_, lean_object* v_i_212_, lean_object* v_bs_213_){
_start:
{
size_t v_sz_boxed_214_; size_t v_i_boxed_215_; lean_object* v_res_216_; 
v_sz_boxed_214_ = lean_unbox_usize(v_sz_211_);
lean_dec(v_sz_211_);
v_i_boxed_215_ = lean_unbox_usize(v_i_212_);
lean_dec(v_i_212_);
v_res_216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(v___x_210_, v_sz_boxed_214_, v_i_boxed_215_, v_bs_213_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addInheritDocDefault(lean_object* v_rhs_224_, lean_object* v_attrs_x3f_225_){
_start:
{
if (lean_obj_tag(v_attrs_x3f_225_) == 0)
{
lean_dec(v_rhs_224_);
return v_attrs_x3f_225_;
}
else
{
lean_object* v_val_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_val_226_ = lean_ctor_get(v_attrs_x3f_225_, 0);
v___x_227_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
lean_inc(v_rhs_224_);
v___x_228_ = l_Lean_Syntax_isOfKind(v_rhs_224_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_229_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_rhs_224_);
v___x_230_ = l_Lean_Syntax_isOfKind(v_rhs_224_, v___x_229_);
if (v___x_230_ == 0)
{
lean_dec(v_rhs_224_);
return v_attrs_x3f_225_;
}
else
{
lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_243_; 
lean_inc(v_val_226_);
v_isSharedCheck_243_ = !lean_is_exclusive(v_attrs_x3f_225_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v_attrs_x3f_225_, 0);
lean_dec(v_unused_244_);
v___x_232_ = v_attrs_x3f_225_;
v_isShared_233_ = v_isSharedCheck_243_;
goto v_resetjp_231_;
}
else
{
lean_dec(v_attrs_x3f_225_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_243_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_235_; size_t v_sz_236_; size_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_234_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__2));
v___x_235_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_226_);
lean_dec(v_val_226_);
v_sz_236_ = lean_array_size(v___x_235_);
v___x_237_ = ((size_t)0ULL);
v___x_238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(v___x_228_, v_rhs_224_, v_sz_236_, v___x_237_, v___x_235_);
v___x_239_ = l_Lean_Syntax_SepArray_ofElems(v___x_234_, v___x_238_);
lean_dec_ref(v___x_238_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_239_);
v___x_241_ = v___x_232_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = l_Lean_Syntax_getArg(v_rhs_224_, v___x_245_);
lean_dec(v_rhs_224_);
v___x_247_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v___x_246_);
v___x_248_ = l_Lean_Syntax_isOfKind(v___x_246_, v___x_247_);
if (v___x_248_ == 0)
{
lean_dec(v___x_246_);
return v_attrs_x3f_225_;
}
else
{
lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_261_; 
lean_inc(v_val_226_);
v_isSharedCheck_261_ = !lean_is_exclusive(v_attrs_x3f_225_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; 
v_unused_262_ = lean_ctor_get(v_attrs_x3f_225_, 0);
lean_dec(v_unused_262_);
v___x_250_ = v_attrs_x3f_225_;
v_isShared_251_ = v_isSharedCheck_261_;
goto v_resetjp_249_;
}
else
{
lean_dec(v_attrs_x3f_225_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_261_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_253_; size_t v_sz_254_; size_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_252_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__2));
v___x_253_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_226_);
lean_dec(v_val_226_);
v_sz_254_ = lean_array_size(v___x_253_);
v___x_255_ = ((size_t)0ULL);
v___x_256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(v___x_246_, v_sz_254_, v___x_255_, v___x_253_);
v___x_257_ = l_Lean_Syntax_SepArray_ofElems(v___x_252_, v___x_256_);
lean_dec_ref(v___x_256_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_257_);
v___x_259_ = v___x_250_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2));
v___x_271_ = l_String_toRawSubstring_x27(v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(lean_object* v_x_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v_prec_x3f_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
lean_inc(v_x_302_);
v___x_342_ = l_Lean_Syntax_isOfKind(v_x_302_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12));
lean_inc(v_x_302_);
v___x_344_ = l_Lean_Syntax_isOfKind(v_x_302_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
lean_inc(v_x_302_);
v___x_346_ = l_Lean_Syntax_isOfKind(v_x_302_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_dec(v_x_302_);
v___x_347_ = l_Lean_Macro_throwUnsupported___redArg(v_a_304_);
return v___x_347_;
}
else
{
lean_object* v___x_348_; 
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v_x_302_);
lean_ctor_set(v___x_348_, 1, v_a_304_);
return v___x_348_;
}
}
else
{
lean_object* v_ref_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_ref_349_ = lean_ctor_get(v_a_303_, 5);
v___x_350_ = l_Lean_SourceInfo_fromRef(v_ref_349_, v___x_342_);
v___x_351_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16));
v___x_352_ = l_Lean_Syntax_node1(v___x_350_, v___x_351_, v_x_302_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v_a_304_);
return v___x_353_;
}
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = l_Lean_Syntax_getArg(v_x_302_, v___x_354_);
v___x_356_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
v___x_357_ = l_Lean_Syntax_isOfKind(v___x_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
lean_inc(v_x_302_);
v___x_359_ = l_Lean_Syntax_isOfKind(v_x_302_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
lean_dec(v_x_302_);
v___x_360_ = l_Lean_Macro_throwUnsupported___redArg(v_a_304_);
return v___x_360_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_x_302_);
lean_ctor_set(v___x_361_, 1, v_a_304_);
return v___x_361_;
}
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = l_Lean_Syntax_getArg(v_x_302_, v___x_362_);
v___x_364_ = l_Lean_Syntax_isNone(v___x_363_);
if (v___x_364_ == 0)
{
uint8_t v___x_365_; 
lean_inc(v___x_363_);
v___x_365_ = l_Lean_Syntax_matchesNull(v___x_363_, v___x_362_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; uint8_t v___x_367_; 
lean_dec(v___x_363_);
v___x_366_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
lean_inc(v_x_302_);
v___x_367_ = l_Lean_Syntax_isOfKind(v_x_302_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
lean_dec(v_x_302_);
v___x_368_ = l_Lean_Macro_throwUnsupported___redArg(v_a_304_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; 
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_x_302_);
lean_ctor_set(v___x_369_, 1, v_a_304_);
return v___x_369_;
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_370_ = l_Lean_Syntax_getArg(v___x_363_, v___x_354_);
lean_dec(v___x_363_);
v___x_371_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
lean_inc(v___x_370_);
v___x_372_ = l_Lean_Syntax_isOfKind(v___x_370_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; uint8_t v___x_374_; 
lean_dec(v___x_370_);
v___x_373_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
lean_inc(v_x_302_);
v___x_374_ = l_Lean_Syntax_isOfKind(v_x_302_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; 
lean_dec(v_x_302_);
v___x_375_ = l_Lean_Macro_throwUnsupported___redArg(v_a_304_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; 
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v_x_302_);
lean_ctor_set(v___x_376_, 1, v_a_304_);
return v___x_376_;
}
}
else
{
lean_object* v_prec_x3f_377_; lean_object* v___x_378_; 
lean_dec(v_x_302_);
v_prec_x3f_377_ = l_Lean_Syntax_getArg(v___x_370_, v___x_362_);
lean_dec(v___x_370_);
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v_prec_x3f_377_);
v_prec_x3f_318_ = v___x_378_;
v___y_319_ = v_a_303_;
v___y_320_ = v_a_304_;
goto v___jp_317_;
}
}
}
else
{
lean_object* v___x_379_; 
lean_dec(v___x_363_);
lean_dec(v_x_302_);
v___x_379_ = lean_box(0);
v_prec_x3f_318_ = v___x_379_;
v___y_319_ = v_a_303_;
v___y_320_ = v_a_304_;
goto v___jp_317_;
}
}
}
v___jp_305_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_inc_ref(v___y_311_);
v___x_313_ = l_Array_append___redArg(v___y_311_, v___y_312_);
lean_dec_ref(v___y_312_);
lean_inc(v___y_306_);
lean_inc(v___y_309_);
v___x_314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_314_, 0, v___y_309_);
lean_ctor_set(v___x_314_, 1, v___y_306_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
lean_inc(v___y_307_);
v___x_315_ = l_Lean_Syntax_node2(v___y_309_, v___y_307_, v___y_310_, v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___y_308_);
return v___x_316_;
}
v___jp_317_:
{
lean_object* v_quotContext_321_; lean_object* v_currMacroScope_322_; lean_object* v_ref_323_; uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_quotContext_321_ = lean_ctor_get(v___y_319_, 1);
v_currMacroScope_322_ = lean_ctor_get(v___y_319_, 2);
v_ref_323_ = lean_ctor_get(v___y_319_, 5);
v___x_324_ = 0;
v___x_325_ = l_Lean_SourceInfo_fromRef(v_ref_323_, v___x_324_);
v___x_326_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2));
v___x_327_ = lean_obj_once(&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3, &l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3_once, _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3);
v___x_328_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
lean_inc(v_currMacroScope_322_);
lean_inc(v_quotContext_321_);
v___x_329_ = l_Lean_addMacroScope(v_quotContext_321_, v___x_328_, v_currMacroScope_322_);
v___x_330_ = lean_box(0);
lean_inc(v___x_325_);
v___x_331_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_331_, 0, v___x_325_);
lean_ctor_set(v___x_331_, 1, v___x_327_);
lean_ctor_set(v___x_331_, 2, v___x_329_);
lean_ctor_set(v___x_331_, 3, v___x_330_);
v___x_332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_333_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
if (lean_obj_tag(v_prec_x3f_318_) == 1)
{
lean_object* v_val_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_val_334_ = lean_ctor_get(v_prec_x3f_318_, 0);
lean_inc(v_val_334_);
lean_dec_ref_known(v_prec_x3f_318_, 1);
v___x_335_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
v___x_336_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc_n(v___x_325_, 2);
v___x_337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_325_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = l_Lean_Syntax_node2(v___x_325_, v___x_335_, v___x_337_, v_val_334_);
v___x_339_ = l_Array_mkArray1___redArg(v___x_338_);
v___y_306_ = v___x_332_;
v___y_307_ = v___x_326_;
v___y_308_ = v___y_320_;
v___y_309_ = v___x_325_;
v___y_310_ = v___x_331_;
v___y_311_ = v___x_333_;
v___y_312_ = v___x_339_;
goto v___jp_305_;
}
else
{
lean_object* v___x_340_; 
lean_dec(v_prec_x3f_318_);
v___x_340_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_306_ = v___x_332_;
v___y_307_ = v___x_326_;
v___y_308_ = v___y_320_;
v___y_309_ = v___x_325_;
v___y_310_ = v___x_331_;
v___y_311_ = v___x_333_;
v___y_312_ = v___x_340_;
goto v___jp_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___boxed(lean_object* v_x_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(v_x_380_, v_a_381_, v_a_382_);
lean_dec_ref(v_a_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(lean_object* v_stx_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_k_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
lean_inc(v_stx_384_);
v_k_386_ = l_Lean_Syntax_getKind(v_stx_384_);
v___x_387_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
v___x_388_ = lean_name_eq(v_k_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12));
v___x_390_ = lean_name_eq(v_k_386_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
v___x_392_ = lean_name_eq(v_k_386_, v___x_391_);
lean_dec(v_k_386_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
lean_dec(v_stx_384_);
v___x_393_ = l_Lean_Macro_throwUnsupported___redArg(v_a_385_);
return v___x_393_;
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; uint8_t v_preserveForPP_397_; 
v___x_394_ = lean_unsigned_to_nat(4u);
v___x_395_ = l_Lean_Syntax_getArg(v_stx_384_, v___x_394_);
v___x_396_ = l_Lean_Syntax_isNone(v___x_395_);
lean_dec(v___x_395_);
v_preserveForPP_397_ = lean_bool_not(v___x_396_);
if (v_preserveForPP_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = l_Lean_Syntax_getArg(v_stx_384_, v___x_398_);
lean_dec(v_stx_384_);
v___x_400_ = l_Lean_Elab_Command_strLitToPattern___redArg(v___x_399_, v_a_385_);
lean_dec(v___x_399_);
return v___x_400_;
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_401_ = lean_unsigned_to_nat(3u);
v___x_402_ = l_Lean_Syntax_getArg(v_stx_384_, v___x_401_);
lean_dec(v_stx_384_);
v___x_403_ = l_Lean_Elab_Command_strLitToPattern___redArg(v___x_402_, v_a_385_);
lean_dec(v___x_402_);
return v___x_403_;
}
}
}
else
{
lean_object* v___x_404_; 
lean_dec(v_k_386_);
v___x_404_ = l_Lean_Elab_Command_strLitToPattern___redArg(v_stx_384_, v_a_385_);
lean_dec(v_stx_384_);
return v___x_404_;
}
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec(v_k_386_);
v___x_405_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = l_Lean_Syntax_getArg(v_stx_384_, v___x_406_);
lean_dec(v_stx_384_);
v___x_408_ = lean_box(0);
v___x_409_ = l_Lean_Syntax_mkAntiquotNode(v___x_405_, v___x_407_, v___x_406_, v___x_408_, v___x_388_);
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v_a_385_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern(lean_object* v_stx_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(v_stx_411_, v_a_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___boxed(lean_object* v_stx_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Elab_Command_expandNotationItemIntoPattern(v_stx_415_, v_a_416_, v_a_417_);
lean_dec_ref(v_a_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux(lean_object* v_parens_419_, lean_object* v_body_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Syntax_getHeadInfo(v_parens_419_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_leading_422_; lean_object* v___x_423_; 
v_leading_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc_ref(v_leading_422_);
lean_dec_ref_known(v___x_421_, 4);
v___x_423_ = l_Lean_Syntax_getHeadInfo(v_body_420_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_pos_424_; lean_object* v_trailing_425_; lean_object* v_endPos_426_; lean_object* v___x_427_; 
v_pos_424_ = lean_ctor_get(v___x_423_, 1);
lean_inc(v_pos_424_);
v_trailing_425_ = lean_ctor_get(v___x_423_, 2);
lean_inc_ref(v_trailing_425_);
v_endPos_426_ = lean_ctor_get(v___x_423_, 3);
lean_inc(v_endPos_426_);
lean_dec_ref_known(v___x_423_, 4);
v___x_427_ = l_Lean_Syntax_getTailInfo(v_body_420_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_leading_428_; lean_object* v_pos_429_; lean_object* v_endPos_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_451_; 
v_leading_428_ = lean_ctor_get(v___x_427_, 0);
v_pos_429_ = lean_ctor_get(v___x_427_, 1);
v_endPos_430_ = lean_ctor_get(v___x_427_, 3);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; 
v_unused_452_ = lean_ctor_get(v___x_427_, 2);
lean_dec(v_unused_452_);
v___x_432_ = v___x_427_;
v_isShared_433_ = v_isSharedCheck_451_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_endPos_430_);
lean_inc(v_pos_429_);
lean_inc(v_leading_428_);
lean_dec(v___x_427_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_451_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Syntax_getTailInfo(v_parens_419_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_trailing_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_447_; 
v_trailing_435_ = lean_ctor_get(v___x_434_, 2);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; 
v_unused_448_ = lean_ctor_get(v___x_434_, 3);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v___x_434_, 1);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v___x_434_, 0);
lean_dec(v_unused_450_);
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_447_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_trailing_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_447_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 3, v_endPos_426_);
lean_ctor_set(v___x_437_, 2, v_trailing_425_);
lean_ctor_set(v___x_437_, 1, v_pos_424_);
lean_ctor_set(v___x_437_, 0, v_leading_422_);
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_leading_422_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_pos_424_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_trailing_425_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_endPos_426_);
v___x_440_ = v_reuseFailAlloc_446_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = l_Lean_Syntax_setHeadInfo(v_body_420_, v___x_440_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 2, v_trailing_435_);
v___x_443_ = v___x_432_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_leading_428_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_pos_429_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_trailing_435_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v_endPos_430_);
v___x_443_ = v_reuseFailAlloc_445_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Syntax_setTailInfo(v___x_441_, v___x_443_);
return v___x_444_;
}
}
}
}
else
{
lean_dec(v___x_434_);
lean_del_object(v___x_432_);
lean_dec(v_endPos_430_);
lean_dec(v_pos_429_);
lean_dec_ref(v_leading_428_);
lean_dec(v_endPos_426_);
lean_dec_ref(v_trailing_425_);
lean_dec(v_pos_424_);
lean_dec_ref(v_leading_422_);
return v_body_420_;
}
}
}
else
{
lean_dec(v___x_427_);
lean_dec(v_endPos_426_);
lean_dec_ref(v_trailing_425_);
lean_dec(v_pos_424_);
lean_dec_ref(v_leading_422_);
return v_body_420_;
}
}
else
{
lean_dec(v___x_423_);
lean_dec_ref(v_leading_422_);
return v_body_420_;
}
}
else
{
lean_dec(v___x_421_);
return v_body_420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux___boxed(lean_object* v_parens_453_, lean_object* v_body_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Elab_Command_removeParenthesesAux(v_parens_453_, v_body_454_);
lean_dec(v_parens_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses(lean_object* v_stx_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__1));
lean_inc(v_stx_471_);
v___x_475_ = l_Lean_Syntax_isOfKind(v_stx_471_, v___x_474_);
if (v___x_475_ == 0)
{
if (lean_obj_tag(v_stx_471_) == 1)
{
lean_object* v_info_476_; lean_object* v_kind_477_; lean_object* v_args_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_506_; 
v_info_476_ = lean_ctor_get(v_stx_471_, 0);
v_kind_477_ = lean_ctor_get(v_stx_471_, 1);
v_args_478_ = lean_ctor_get(v_stx_471_, 2);
v_isSharedCheck_506_ = !lean_is_exclusive(v_stx_471_);
if (v_isSharedCheck_506_ == 0)
{
v___x_480_ = v_stx_471_;
v_isShared_481_ = v_isSharedCheck_506_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_args_478_);
lean_inc(v_kind_477_);
lean_inc(v_info_476_);
lean_dec(v_stx_471_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_506_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
size_t v_sz_482_; size_t v___x_483_; lean_object* v___x_484_; 
v_sz_482_ = lean_array_size(v_args_478_);
v___x_483_ = ((size_t)0ULL);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_482_, v___x_483_, v_args_478_, v_a_472_, v_a_473_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_496_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_a_486_ = lean_ctor_get(v___x_484_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_496_ == 0)
{
v___x_488_ = v___x_484_;
v_isShared_489_ = v_isSharedCheck_496_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_496_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 2, v_a_485_);
v___x_491_ = v___x_480_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_info_476_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_kind_477_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_a_485_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_491_);
v___x_493_ = v___x_488_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_a_486_);
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
lean_object* v_a_497_; lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_del_object(v___x_480_);
lean_dec(v_kind_477_);
lean_dec(v_info_476_);
v_a_497_ = lean_ctor_get(v___x_484_, 0);
v_a_498_ = lean_ctor_get(v___x_484_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_484_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_inc(v_a_497_);
lean_dec(v___x_484_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_497_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
else
{
lean_object* v___x_507_; 
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_stx_471_);
lean_ctor_set(v___x_507_, 1, v_a_473_);
return v___x_507_;
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = l_Lean_Syntax_getArg(v_stx_471_, v___x_508_);
v___x_510_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__3));
lean_inc(v___x_509_);
v___x_511_ = l_Lean_Syntax_isOfKind(v___x_509_, v___x_510_);
if (v___x_511_ == 0)
{
lean_dec(v___x_509_);
if (lean_obj_tag(v_stx_471_) == 1)
{
lean_object* v_info_512_; lean_object* v_kind_513_; lean_object* v_args_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_542_; 
v_info_512_ = lean_ctor_get(v_stx_471_, 0);
v_kind_513_ = lean_ctor_get(v_stx_471_, 1);
v_args_514_ = lean_ctor_get(v_stx_471_, 2);
v_isSharedCheck_542_ = !lean_is_exclusive(v_stx_471_);
if (v_isSharedCheck_542_ == 0)
{
v___x_516_ = v_stx_471_;
v_isShared_517_ = v_isSharedCheck_542_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_args_514_);
lean_inc(v_kind_513_);
lean_inc(v_info_512_);
lean_dec(v_stx_471_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_542_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
size_t v_sz_518_; size_t v___x_519_; lean_object* v___x_520_; 
v_sz_518_ = lean_array_size(v_args_514_);
v___x_519_ = ((size_t)0ULL);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_518_, v___x_519_, v_args_514_, v_a_472_, v_a_473_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_532_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_a_522_ = lean_ctor_get(v___x_520_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_532_ == 0)
{
v___x_524_ = v___x_520_;
v_isShared_525_ = v_isSharedCheck_532_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_532_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 2, v_a_521_);
v___x_527_ = v___x_516_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_info_512_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_kind_513_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_a_521_);
v___x_527_ = v_reuseFailAlloc_531_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_529_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_527_);
v___x_529_ = v___x_524_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_a_522_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_del_object(v___x_516_);
lean_dec(v_kind_513_);
lean_dec(v_info_512_);
v_a_533_ = lean_ctor_get(v___x_520_, 0);
v_a_534_ = lean_ctor_get(v___x_520_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_520_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_inc(v_a_533_);
lean_dec(v___x_520_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_533_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
else
{
lean_object* v___x_543_; 
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v_stx_471_);
lean_ctor_set(v___x_543_, 1, v_a_473_);
return v___x_543_;
}
}
else
{
lean_object* v___x_544_; lean_object* v_h_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_544_ = lean_unsigned_to_nat(1u);
v_h_545_ = l_Lean_Syntax_getArg(v___x_509_, v___x_544_);
lean_dec(v___x_509_);
v___x_546_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__5));
lean_inc(v_h_545_);
v___x_547_ = l_Lean_Syntax_isOfKind(v_h_545_, v___x_546_);
if (v___x_547_ == 0)
{
lean_dec(v_h_545_);
if (lean_obj_tag(v_stx_471_) == 1)
{
lean_object* v_info_548_; lean_object* v_kind_549_; lean_object* v_args_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_578_; 
v_info_548_ = lean_ctor_get(v_stx_471_, 0);
v_kind_549_ = lean_ctor_get(v_stx_471_, 1);
v_args_550_ = lean_ctor_get(v_stx_471_, 2);
v_isSharedCheck_578_ = !lean_is_exclusive(v_stx_471_);
if (v_isSharedCheck_578_ == 0)
{
v___x_552_ = v_stx_471_;
v_isShared_553_ = v_isSharedCheck_578_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_args_550_);
lean_inc(v_kind_549_);
lean_inc(v_info_548_);
lean_dec(v_stx_471_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_578_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
size_t v_sz_554_; size_t v___x_555_; lean_object* v___x_556_; 
v_sz_554_ = lean_array_size(v_args_550_);
v___x_555_ = ((size_t)0ULL);
v___x_556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_554_, v___x_555_, v_args_550_, v_a_472_, v_a_473_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_568_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_a_558_ = lean_ctor_get(v___x_556_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_568_ == 0)
{
v___x_560_ = v___x_556_;
v_isShared_561_ = v_isSharedCheck_568_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_568_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 2, v_a_557_);
v___x_563_ = v___x_552_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_info_548_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_kind_549_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_a_557_);
v___x_563_ = v_reuseFailAlloc_567_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_565_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_563_);
v___x_565_ = v___x_560_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_a_558_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v_a_569_; lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_del_object(v___x_552_);
lean_dec(v_kind_549_);
lean_dec(v_info_548_);
v_a_569_ = lean_ctor_get(v___x_556_, 0);
v_a_570_ = lean_ctor_get(v___x_556_, 1);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_556_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_inc(v_a_569_);
lean_dec(v___x_556_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_569_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
else
{
lean_object* v___x_579_; 
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_stx_471_);
lean_ctor_set(v___x_579_, 1, v_a_473_);
return v___x_579_;
}
}
else
{
lean_object* v_e_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_e_580_ = l_Lean_Syntax_getArg(v_stx_471_, v___x_544_);
v___x_581_ = l_Lean_TSyntax_getHygieneInfo(v_h_545_);
lean_dec(v_h_545_);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_inc(v_e_580_);
v___x_583_ = l_Lean_Elab_Term_expandCDot_x3f(v_e_580_, v___x_582_, v_a_472_, v_a_473_);
lean_dec_ref_known(v___x_582_, 1);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v_a_585_; lean_object* v___y_587_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
v_a_585_ = lean_ctor_get(v___x_583_, 1);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_583_, 2);
if (lean_obj_tag(v_a_584_) == 0)
{
v___y_587_ = v_e_580_;
goto v___jp_586_;
}
else
{
lean_object* v_val_599_; 
lean_dec(v_e_580_);
v_val_599_ = lean_ctor_get(v_a_584_, 0);
lean_inc(v_val_599_);
lean_dec_ref_known(v_a_584_, 1);
v___y_587_ = v_val_599_;
goto v___jp_586_;
}
v___jp_586_:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Elab_Command_removeParentheses(v___y_587_, v_a_472_, v_a_585_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_598_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v_a_590_ = lean_ctor_get(v___x_588_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_598_ == 0)
{
v___x_592_ = v___x_588_;
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = l_Lean_Elab_Command_removeParenthesesAux(v_stx_471_, v_a_589_);
lean_dec(v_stx_471_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_a_590_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
else
{
lean_dec(v_stx_471_);
return v___x_588_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec(v_e_580_);
lean_dec(v_stx_471_);
v_a_600_ = lean_ctor_get(v___x_583_, 0);
v_a_601_ = lean_ctor_get(v___x_583_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_583_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_inc(v_a_600_);
lean_dec(v___x_583_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_600_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(size_t v_sz_609_, size_t v_i_610_, lean_object* v_bs_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
uint8_t v___x_614_; 
v___x_614_ = lean_usize_dec_lt(v_i_610_, v_sz_609_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v_bs_611_);
lean_ctor_set(v___x_615_, 1, v___y_613_);
return v___x_615_;
}
else
{
lean_object* v_v_616_; lean_object* v___x_617_; 
v_v_616_ = lean_array_uget_borrowed(v_bs_611_, v_i_610_);
lean_inc(v_v_616_);
v___x_617_ = l_Lean_Elab_Command_removeParentheses(v_v_616_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v_a_619_; lean_object* v___x_620_; lean_object* v_bs_x27_621_; size_t v___x_622_; size_t v___x_623_; lean_object* v___x_624_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
v_a_619_ = lean_ctor_get(v___x_617_, 1);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_617_, 2);
v___x_620_ = lean_unsigned_to_nat(0u);
v_bs_x27_621_ = lean_array_uset(v_bs_611_, v_i_610_, v___x_620_);
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_610_, v___x_622_);
v___x_624_ = lean_array_uset(v_bs_x27_621_, v_i_610_, v_a_618_);
v_i_610_ = v___x_623_;
v_bs_611_ = v___x_624_;
v___y_613_ = v_a_619_;
goto _start;
}
else
{
lean_object* v_a_626_; lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec_ref(v_bs_611_);
v_a_626_ = lean_ctor_get(v___x_617_, 0);
v_a_627_ = lean_ctor_get(v___x_617_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_617_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_inc(v_a_626_);
lean_dec(v___x_617_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_626_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0___boxed(lean_object* v_sz_635_, lean_object* v_i_636_, lean_object* v_bs_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
size_t v_sz_boxed_640_; size_t v_i_boxed_641_; lean_object* v_res_642_; 
v_sz_boxed_640_ = lean_unbox_usize(v_sz_635_);
lean_dec(v_sz_635_);
v_i_boxed_641_ = lean_unbox_usize(v_i_636_);
lean_dec(v_i_636_);
v_res_642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_boxed_640_, v_i_boxed_641_, v_bs_637_, v___y_638_, v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses___boxed(lean_object* v_stx_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Elab_Command_removeParentheses(v_stx_643_, v_a_644_, v_a_645_);
lean_dec_ref(v_a_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(lean_object* v___x_650_, uint8_t v_firstChoiceOnly_651_, lean_object* v_stx_652_, lean_object* v_b_653_){
_start:
{
lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_667_; lean_object* v_a_668_; lean_object* v_snd_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_702_; 
v_snd_678_ = lean_ctor_get(v_b_653_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_b_653_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; 
v_unused_703_ = lean_ctor_get(v_b_653_, 0);
lean_dec(v_unused_703_);
v___x_680_ = v_b_653_;
v_isShared_681_ = v_isSharedCheck_702_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_snd_678_);
lean_dec(v_b_653_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_702_;
goto v_resetjp_679_;
}
v___jp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; size_t v_sz_659_; size_t v___x_660_; lean_object* v___x_661_; lean_object* v_fst_662_; 
v___x_657_ = lean_box(0);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___y_656_);
v_sz_659_ = lean_array_size(v___y_655_);
v___x_660_ = ((size_t)0ULL);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v___x_650_, v_firstChoiceOnly_651_, v___y_655_, v_sz_659_, v___x_660_, v___x_658_);
v_fst_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_fst_662_);
if (lean_obj_tag(v_fst_662_) == 0)
{
lean_object* v_snd_663_; lean_object* v___x_664_; 
v_snd_663_ = lean_ctor_get(v___x_661_, 1);
lean_inc(v_snd_663_);
lean_dec_ref(v___x_661_);
v___x_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_664_, 0, v_snd_663_);
return v___x_664_;
}
else
{
lean_object* v_val_665_; 
lean_dec_ref(v___x_661_);
v_val_665_ = lean_ctor_get(v_fst_662_, 0);
lean_inc(v_val_665_);
lean_dec_ref_known(v_fst_662_, 1);
return v_val_665_;
}
}
v___jp_666_:
{
if (lean_obj_tag(v_stx_652_) == 1)
{
lean_dec_ref(v___y_667_);
if (v_firstChoiceOnly_651_ == 0)
{
lean_object* v_args_669_; 
v_args_669_ = lean_ctor_get(v_stx_652_, 2);
v___y_655_ = v_args_669_;
v___y_656_ = v_a_668_;
goto v___jp_654_;
}
else
{
lean_object* v_kind_670_; lean_object* v_args_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_kind_670_ = lean_ctor_get(v_stx_652_, 1);
v_args_671_ = lean_ctor_get(v_stx_652_, 2);
v___x_672_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1));
v___x_673_ = lean_name_eq(v_kind_670_, v___x_672_);
if (v___x_673_ == 0)
{
v___y_655_ = v_args_671_;
v___y_656_ = v_a_668_;
goto v___jp_654_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_box(0);
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_array_get_borrowed(v___x_674_, v_args_671_, v___x_675_);
v_stx_652_ = v___x_676_;
v_b_653_ = v_a_668_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_a_668_);
return v___y_667_;
}
}
v_resetjp_679_:
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = lean_box(0);
v___x_683_ = l_Lean_Syntax_isAntiquot(v_stx_652_);
if (v___x_683_ == 0)
{
lean_object* v___x_685_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_682_);
v___x_685_ = v___x_680_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_snd_678_);
v___x_685_ = v_reuseFailAlloc_687_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; 
lean_inc_ref(v___x_685_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
v___y_667_ = v___x_686_;
v_a_668_ = v___x_685_;
goto v___jp_666_;
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_688_ = l_Lean_Syntax_getAntiquotTerm(v_stx_652_);
v___x_689_ = l_Lean_Syntax_getId(v___x_688_);
lean_dec(v___x_688_);
v___x_690_ = l_Lean_NameSet_contains(v_snd_678_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = l_Lean_NameSet_insert(v_snd_678_, v___x_689_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_691_);
lean_ctor_set(v___x_680_, 0, v___x_682_);
v___x_693_ = v___x_680_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_691_);
v___x_693_ = v_reuseFailAlloc_695_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; 
lean_inc_ref(v___x_693_);
v___x_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
v___y_667_ = v___x_694_;
v_a_668_ = v___x_693_;
goto v___jp_666_;
}
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
lean_dec(v___x_689_);
v___x_696_ = lean_box(v___x_690_);
v___x_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_697_);
v___x_699_ = v___x_680_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_snd_678_);
v___x_699_ = v_reuseFailAlloc_701_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; 
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(lean_object* v___x_704_, uint8_t v_firstChoiceOnly_705_, lean_object* v_as_706_, size_t v_sz_707_, size_t v_i_708_, lean_object* v_b_709_){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = lean_usize_dec_lt(v_i_708_, v_sz_707_);
if (v___x_710_ == 0)
{
return v_b_709_;
}
else
{
lean_object* v_snd_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_729_; 
v_snd_711_ = lean_ctor_get(v_b_709_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v_b_709_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; 
v_unused_730_ = lean_ctor_get(v_b_709_, 0);
lean_dec(v_unused_730_);
v___x_713_ = v_b_709_;
v_isShared_714_ = v_isSharedCheck_729_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_snd_711_);
lean_dec(v_b_709_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_729_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_a_715_; lean_object* v___x_716_; 
v_a_715_ = lean_array_uget_borrowed(v_as_706_, v_i_708_);
lean_inc(v_snd_711_);
v___x_716_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_704_, v_firstChoiceOnly_705_, v_a_715_, v_snd_711_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_717_);
v___x_719_ = v___x_713_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_snd_711_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
lean_dec(v_snd_711_);
v_a_721_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_716_, 1);
v___x_722_ = lean_box(0);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v_a_721_);
lean_ctor_set(v___x_713_, 0, v___x_722_);
v___x_724_ = v___x_713_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_a_721_);
v___x_724_ = v_reuseFailAlloc_728_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
size_t v___x_725_; size_t v___x_726_; 
v___x_725_ = ((size_t)1ULL);
v___x_726_ = lean_usize_add(v_i_708_, v___x_725_);
v_i_708_ = v___x_726_;
v_b_709_ = v___x_724_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0___boxed(lean_object* v___x_731_, lean_object* v_firstChoiceOnly_732_, lean_object* v_as_733_, lean_object* v_sz_734_, lean_object* v_i_735_, lean_object* v_b_736_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_737_; size_t v_sz_boxed_738_; size_t v_i_boxed_739_; lean_object* v_res_740_; 
v_firstChoiceOnly_boxed_737_ = lean_unbox(v_firstChoiceOnly_732_);
v_sz_boxed_738_ = lean_unbox_usize(v_sz_734_);
lean_dec(v_sz_734_);
v_i_boxed_739_ = lean_unbox_usize(v_i_735_);
lean_dec(v_i_735_);
v_res_740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v___x_731_, v_firstChoiceOnly_boxed_737_, v_as_733_, v_sz_boxed_738_, v_i_boxed_739_, v_b_736_);
lean_dec_ref(v_as_733_);
lean_dec_ref(v___x_731_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___boxed(lean_object* v___x_741_, lean_object* v_firstChoiceOnly_742_, lean_object* v_stx_743_, lean_object* v_b_744_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_745_; lean_object* v_res_746_; 
v_firstChoiceOnly_boxed_745_ = lean_unbox(v_firstChoiceOnly_742_);
v_res_746_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_741_, v_firstChoiceOnly_boxed_745_, v_stx_743_, v_b_744_);
lean_dec(v_stx_743_);
lean_dec_ref(v___x_741_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(lean_object* v_as_747_, size_t v_sz_748_, size_t v_i_749_, lean_object* v_b_750_){
_start:
{
uint8_t v___x_751_; 
v___x_751_ = lean_usize_dec_lt(v_i_749_, v_sz_748_);
if (v___x_751_ == 0)
{
return v_b_750_;
}
else
{
lean_object* v_snd_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_790_; 
v_snd_752_ = lean_ctor_get(v_b_750_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_b_750_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v_b_750_, 0);
lean_dec(v_unused_791_);
v___x_754_ = v_b_750_;
v_isShared_755_ = v_isSharedCheck_790_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_snd_752_);
lean_dec(v_b_750_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_790_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_a_756_; lean_object* v___x_757_; uint8_t v_firstChoiceOnly_758_; lean_object* v_stx_759_; lean_object* v___x_760_; lean_object* v___y_762_; lean_object* v___x_786_; 
v_a_756_ = lean_array_uget_borrowed(v_as_747_, v_i_749_);
lean_inc(v_a_756_);
v___x_757_ = l_Lean_Syntax_topDown(v_a_756_, v___x_751_);
v_firstChoiceOnly_758_ = lean_ctor_get_uint8(v___x_757_, sizeof(void*)*1);
v_stx_759_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_stx_759_);
lean_dec_ref(v___x_757_);
v___x_760_ = lean_box(0);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_760_);
v___x_786_ = v___x_754_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_snd_752_);
v___x_786_ = v_reuseFailAlloc_789_;
goto v_reusejp_785_;
}
v___jp_761_:
{
lean_object* v_fst_763_; 
v_fst_763_ = lean_ctor_get(v___y_762_, 0);
if (lean_obj_tag(v_fst_763_) == 0)
{
lean_object* v_snd_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_774_; 
v_snd_764_ = lean_ctor_get(v___y_762_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v___y_762_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v___y_762_, 0);
lean_dec(v_unused_775_);
v___x_766_ = v___y_762_;
v_isShared_767_ = v_isSharedCheck_774_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_snd_764_);
lean_dec(v___y_762_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_774_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_760_);
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_snd_764_);
v___x_769_ = v_reuseFailAlloc_773_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
size_t v___x_770_; size_t v___x_771_; 
v___x_770_ = ((size_t)1ULL);
v___x_771_ = lean_usize_add(v_i_749_, v___x_770_);
v_i_749_ = v___x_771_;
v_b_750_ = v___x_769_;
goto _start;
}
}
}
else
{
lean_object* v_snd_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_inc_ref(v_fst_763_);
v_snd_776_ = lean_ctor_get(v___y_762_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v___y_762_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v___y_762_, 0);
lean_dec(v_unused_784_);
v___x_778_ = v___y_762_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_snd_776_);
lean_dec(v___y_762_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_fst_763_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_snd_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
v_reusejp_785_:
{
lean_object* v___x_787_; lean_object* v_a_788_; 
lean_inc_ref(v___x_786_);
v___x_787_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_786_, v_firstChoiceOnly_758_, v_stx_759_, v___x_786_);
lean_dec(v_stx_759_);
lean_dec_ref(v___x_786_);
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref(v___x_787_);
v___y_762_ = v_a_788_;
goto v___jp_761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1___boxed(lean_object* v_as_792_, lean_object* v_sz_793_, lean_object* v_i_794_, lean_object* v_b_795_){
_start:
{
size_t v_sz_boxed_796_; size_t v_i_boxed_797_; lean_object* v_res_798_; 
v_sz_boxed_796_ = lean_unbox_usize(v_sz_793_);
lean_dec(v_sz_793_);
v_i_boxed_797_ = lean_unbox_usize(v_i_794_);
lean_dec(v_i_794_);
v_res_798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(v_as_792_, v_sz_boxed_796_, v_i_boxed_797_, v_b_795_);
lean_dec_ref(v_as_792_);
return v_res_798_;
}
}
static lean_object* _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0(void){
_start:
{
lean_object* v_seen_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_seen_799_ = l_Lean_NameSet_empty;
v___x_800_ = lean_box(0);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v_seen_799_);
return v___x_801_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_hasDuplicateAntiquot(lean_object* v_stxs_802_){
_start:
{
lean_object* v___x_803_; size_t v_sz_804_; size_t v___x_805_; lean_object* v___x_806_; lean_object* v_fst_807_; 
v___x_803_ = lean_obj_once(&l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0, &l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0_once, _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0);
v_sz_804_ = lean_array_size(v_stxs_802_);
v___x_805_ = ((size_t)0ULL);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(v_stxs_802_, v_sz_804_, v___x_805_, v___x_803_);
v_fst_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_fst_807_);
lean_dec_ref(v___x_806_);
if (lean_obj_tag(v_fst_807_) == 0)
{
uint8_t v___x_808_; 
v___x_808_ = 0;
return v___x_808_;
}
else
{
lean_object* v_val_809_; uint8_t v___x_810_; 
v_val_809_ = lean_ctor_get(v_fst_807_, 0);
lean_inc(v_val_809_);
lean_dec_ref_known(v_fst_807_, 1);
v___x_810_ = lean_unbox(v_val_809_);
lean_dec(v_val_809_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___boxed(lean_object* v_stxs_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_Lean_Elab_Command_hasDuplicateAntiquot(v_stxs_811_);
lean_dec_ref(v_stxs_811_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__4(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__3));
v___x_821_ = l_String_toRawSubstring_x27(v___x_820_);
return v___x_821_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__15(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__14));
v___x_843_ = l_String_toRawSubstring_x27(v___x_842_);
return v___x_843_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__19(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__18));
v___x_849_ = l_String_toRawSubstring_x27(v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__22(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__21));
v___x_854_ = l_String_toRawSubstring_x27(v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__40(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__39));
v___x_892_ = l_String_toRawSubstring_x27(v___x_891_);
return v___x_892_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__47(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__46));
v___x_907_ = l_String_toRawSubstring_x27(v___x_906_);
return v___x_907_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__55(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_923_ = l_String_toRawSubstring_x27(v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander(lean_object* v_attrKind_961_, lean_object* v_pat_962_, lean_object* v_qrhs_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___y_967_; lean_object* v_fst_971_; lean_object* v_snd_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
lean_inc(v_qrhs_963_);
v___x_1170_ = l_Lean_Syntax_isOfKind(v_qrhs_963_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_qrhs_963_);
v___x_1172_ = l_Lean_Syntax_isOfKind(v_qrhs_963_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec(v_qrhs_963_);
lean_dec(v_pat_962_);
lean_dec(v_attrKind_961_);
v___x_1173_ = lean_box(0);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v_a_965_);
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; 
v___x_1175_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__68));
v_fst_971_ = v_qrhs_963_;
v_snd_972_ = v___x_1175_;
v___y_973_ = v_a_964_;
v___y_974_ = v_a_965_;
goto v___jp_970_;
}
}
else
{
lean_object* v___x_1176_; lean_object* v_c_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1176_ = lean_unsigned_to_nat(0u);
v_c_1177_ = l_Lean_Syntax_getArg(v_qrhs_963_, v___x_1176_);
v___x_1178_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_c_1177_);
v___x_1179_ = l_Lean_Syntax_isOfKind(v_c_1177_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_dec(v_c_1177_);
lean_dec(v_qrhs_963_);
lean_dec(v_pat_962_);
lean_dec(v_attrKind_961_);
v___x_1180_ = lean_box(0);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v_a_965_);
return v___x_1181_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_args_1184_; 
v___x_1182_ = lean_unsigned_to_nat(1u);
v___x_1183_ = l_Lean_Syntax_getArg(v_qrhs_963_, v___x_1182_);
lean_dec(v_qrhs_963_);
v_args_1184_ = l_Lean_Syntax_getArgs(v___x_1183_);
lean_dec(v___x_1183_);
v_fst_971_ = v_c_1177_;
v_snd_972_ = v_args_1184_;
v___y_973_ = v_a_964_;
v___y_974_ = v_a_965_;
goto v___jp_970_;
}
}
v___jp_966_:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_box(0);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___y_967_);
return v___x_969_;
}
v___jp_970_:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = l_Lean_TSyntax_getId(v_fst_971_);
lean_dec(v_fst_971_);
v___x_976_ = l_Lean_Macro_resolveGlobalName(v___x_975_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
if (lean_obj_tag(v_a_977_) == 1)
{
lean_object* v_head_978_; lean_object* v_snd_979_; 
v_head_978_ = lean_ctor_get(v_a_977_, 0);
lean_inc(v_head_978_);
v_snd_979_ = lean_ctor_get(v_head_978_, 1);
lean_inc(v_snd_979_);
if (lean_obj_tag(v_snd_979_) == 0)
{
lean_object* v_tail_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1156_; 
v_tail_980_ = lean_ctor_get(v_a_977_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_a_977_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; 
v_unused_1157_ = lean_ctor_get(v_a_977_, 0);
lean_dec(v_unused_1157_);
v___x_982_ = v_a_977_;
v_isShared_983_ = v_isSharedCheck_1156_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_tail_980_);
lean_dec(v_a_977_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1156_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
if (lean_obj_tag(v_tail_980_) == 0)
{
lean_object* v_a_984_; lean_object* v_fst_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1153_; 
v_a_984_ = lean_ctor_get(v___x_976_, 1);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_976_, 2);
v_fst_985_ = lean_ctor_get(v_head_978_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_head_978_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v_head_978_, 1);
lean_dec(v_unused_1154_);
v___x_987_ = v_head_978_;
v_isShared_988_ = v_isSharedCheck_1153_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_fst_985_);
lean_dec(v_head_978_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1153_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
size_t v_sz_989_; size_t v___x_990_; lean_object* v___x_991_; 
v_sz_989_ = lean_array_size(v_snd_972_);
v___x_990_ = ((size_t)0ULL);
v___x_991_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_989_, v___x_990_, v_snd_972_, v___y_973_, v_a_984_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1143_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_a_993_ = lean_ctor_get(v___x_991_, 1);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_995_ = v___x_991_;
v_isShared_996_ = v_isSharedCheck_1143_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1143_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
uint8_t v___x_997_; uint8_t v___x_998_; 
v___x_997_ = l_Lean_Elab_Command_hasDuplicateAntiquot(v_a_992_);
v___x_998_ = lean_bool_not(v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_dec(v_a_992_);
lean_del_object(v___x_987_);
lean_dec(v_fst_985_);
lean_del_object(v___x_982_);
lean_dec(v_pat_962_);
lean_dec(v_attrKind_961_);
v___x_999_ = lean_box(0);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_999_);
v___x_1001_ = v___x_995_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_a_993_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
else
{
lean_object* v_quotContext_1003_; lean_object* v_currMacroScope_1004_; lean_object* v_ref_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v_quotContext_1003_ = lean_ctor_get(v___y_973_, 1);
v_currMacroScope_1004_ = lean_ctor_get(v___y_973_, 2);
v_ref_1005_ = lean_ctor_get(v___y_973_, 5);
v___x_1006_ = 0;
v___x_1007_ = l_Lean_SourceInfo_fromRef(v_ref_1005_, v___x_1006_);
v___x_1008_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0));
v___x_1009_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__1));
v___x_1010_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__2));
lean_inc(v___x_1007_);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 2);
lean_ctor_set(v___x_987_, 1, v___x_1010_);
lean_ctor_set(v___x_987_, 0, v___x_1007_);
v___x_1012_ = v___x_987_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_1014_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
lean_inc_n(v___x_1007_, 18);
v___x_1015_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1007_);
lean_ctor_set(v___x_1015_, 1, v___x_1013_);
lean_ctor_set(v___x_1015_, 2, v___x_1014_);
v___x_1016_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__4, &l_Lean_Elab_Command_mkUnexpander___closed__4_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__4);
v___x_1017_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__5));
lean_inc_n(v_currMacroScope_1004_, 4);
lean_inc_n(v_quotContext_1003_, 4);
v___x_1018_ = l_Lean_addMacroScope(v_quotContext_1003_, v___x_1017_, v_currMacroScope_1004_);
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1007_);
lean_ctor_set(v___x_1020_, 1, v___x_1016_);
lean_ctor_set(v___x_1020_, 2, v___x_1018_);
lean_ctor_set(v___x_1020_, 3, v___x_1019_);
v___x_1021_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__7));
v___x_1022_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
v___x_1023_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1007_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1007_);
lean_ctor_set(v___x_1024_, 1, v___x_1008_);
lean_inc_ref(v___x_1023_);
v___x_1025_ = l_Lean_Syntax_node2(v___x_1007_, v___x_1021_, v___x_1023_, v___x_1024_);
lean_inc_ref(v___x_1020_);
lean_inc_ref(v___x_1015_);
v___x_1026_ = l_Lean_Syntax_node4(v___x_1007_, v___x_1009_, v___x_1012_, v___x_1015_, v___x_1020_, v___x_1025_);
v___x_1027_ = l_Lean_Syntax_mkApp(v___x_1026_, v_a_992_);
lean_inc(v_attrKind_961_);
v___x_1028_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_961_);
v___x_1029_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__9));
v___x_1030_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__10));
v___x_1031_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
v___x_1032_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
v___x_1033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1007_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
v___x_1035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
v___x_1036_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__15, &l_Lean_Elab_Command_mkUnexpander___closed__15_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__15);
v___x_1037_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__16));
v___x_1038_ = l_Lean_addMacroScope(v_quotContext_1003_, v___x_1037_, v_currMacroScope_1004_);
v___x_1039_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1007_);
lean_ctor_set(v___x_1039_, 1, v___x_1036_);
lean_ctor_set(v___x_1039_, 2, v___x_1038_);
lean_ctor_set(v___x_1039_, 3, v___x_1019_);
v___x_1040_ = l_Lean_mkIdent(v_fst_985_);
lean_inc(v___x_1040_);
v___x_1041_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1013_, v___x_1040_);
v___x_1042_ = l_Lean_Syntax_node2(v___x_1007_, v___x_1035_, v___x_1039_, v___x_1041_);
v___x_1043_ = l_Lean_Syntax_node2(v___x_1007_, v___x_1034_, v_attrKind_961_, v___x_1042_);
v___x_1044_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1013_, v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
v___x_1046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1007_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = l_Lean_Syntax_node3(v___x_1007_, v___x_1031_, v___x_1033_, v___x_1044_, v___x_1046_);
v___x_1048_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1013_, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1007_);
lean_ctor_set(v___x_1049_, 1, v___x_1029_);
v___x_1050_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__19, &l_Lean_Elab_Command_mkUnexpander___closed__19_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__19);
v___x_1051_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__20));
v___x_1052_ = l_Lean_addMacroScope(v_quotContext_1003_, v___x_1051_, v_currMacroScope_1004_);
v___x_1053_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1007_);
lean_ctor_set(v___x_1053_, 1, v___x_1050_);
lean_ctor_set(v___x_1053_, 2, v___x_1052_);
lean_ctor_set(v___x_1053_, 3, v___x_1019_);
v___x_1054_ = l_Lean_Syntax_node2(v___x_1007_, v___x_1013_, v___x_1053_, v___x_1040_);
v___x_1055_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__22, &l_Lean_Elab_Command_mkUnexpander___closed__22_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__22);
v___x_1056_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__25));
v___x_1057_ = l_Lean_addMacroScope(v_quotContext_1003_, v___x_1056_, v_currMacroScope_1004_);
v___x_1058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v_snd_979_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___x_1019_);
lean_ctor_set(v___x_982_, 0, v___x_1058_);
v___x_1060_ = v___x_982_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v___x_1019_);
v___x_1060_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_inc_n(v___x_1007_, 31);
v___x_1061_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1007_);
lean_ctor_set(v___x_1061_, 1, v___x_1055_);
lean_ctor_set(v___x_1061_, 2, v___x_1057_);
lean_ctor_set(v___x_1061_, 3, v___x_1060_);
v___x_1062_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_1063_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1007_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__27));
v___x_1065_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__28));
v___x_1066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1007_);
lean_ctor_set(v___x_1066_, 1, v___x_1064_);
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__30));
v___x_1068_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__32));
v___x_1069_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
v___x_1070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1007_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__35));
v___x_1072_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
v___x_1073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1007_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_1075_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1007_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
lean_inc_ref_n(v___x_1075_, 2);
lean_inc_ref(v___x_1073_);
v___x_1076_ = l_Lean_Syntax_node3(v___x_1007_, v___x_1071_, v___x_1073_, v___x_1027_, v___x_1075_);
v___x_1077_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1013_, v___x_1076_);
v___x_1078_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1013_, v___x_1077_);
v___x_1079_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
v___x_1080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1007_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
v___x_1082_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__40, &l_Lean_Elab_Command_mkUnexpander___closed__40_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__40);
v___x_1083_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__41));
lean_inc_n(v_currMacroScope_1004_, 3);
lean_inc_n(v_quotContext_1003_, 3);
v___x_1084_ = l_Lean_addMacroScope(v_quotContext_1003_, v___x_1083_, v_currMacroScope_1004_);
v___x_1085_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__42));
v___x_1086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v_snd_979_);
v___x_1087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v___x_1019_);
v___x_1088_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1007_);
lean_ctor_set(v___x_1088_, 1, v___x_1082_);
lean_ctor_set(v___x_1088_, 2, v___x_1084_);
lean_ctor_set(v___x_1088_, 3, v___x_1087_);
v___x_1089_ = l_Lean_Syntax_node3(v___x_1007_, v___x_1071_, v___x_1073_, v_pat_962_, v___x_1075_);
v___x_1090_ = l_Lean_Syntax_node2(v___x_1007_, v___x_1013_, v___x_1020_, v___x_1089_);
v___x_1091_ = l_Lean_Syntax_node2(v___x_1007_, v___x_1081_, v___x_1088_, v___x_1090_);
lean_inc_ref(v___x_1080_);
lean_inc_ref(v___x_1070_);
v___x_1092_ = l_Lean_Syntax_node4(v___x_1007_, v___x_1068_, v___x_1070_, v___x_1078_, v___x_1080_, v___x_1091_);
v___x_1093_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__44));
v___x_1094_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__45));
v___x_1095_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1007_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1093_, v___x_1095_);
v___x_1097_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1013_, v___x_1096_);
v___x_1098_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1013_, v___x_1097_);
v___x_1099_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__47, &l_Lean_Elab_Command_mkUnexpander___closed__47_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__47);
v___x_1100_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__48));
v___x_1101_ = l_Lean_addMacroScope(v_quotContext_1003_, v___x_1100_, v_currMacroScope_1004_);
v___x_1102_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__50));
v___x_1103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v_snd_979_);
v___x_1104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v___x_1019_);
v___x_1105_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1007_);
lean_ctor_set(v___x_1105_, 1, v___x_1099_);
lean_ctor_set(v___x_1105_, 2, v___x_1101_);
lean_ctor_set(v___x_1105_, 3, v___x_1104_);
v___x_1106_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__52));
v___x_1107_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__3));
v___x_1108_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
v___x_1109_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1007_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__5));
v___x_1111_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__55, &l_Lean_Elab_Command_mkUnexpander___closed__55_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__55);
v___x_1112_ = lean_box(0);
v___x_1113_ = l_Lean_addMacroScope(v_quotContext_1003_, v___x_1112_, v_currMacroScope_1004_);
v___x_1114_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__67));
v___x_1115_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1007_);
lean_ctor_set(v___x_1115_, 1, v___x_1111_);
lean_ctor_set(v___x_1115_, 2, v___x_1113_);
lean_ctor_set(v___x_1115_, 3, v___x_1114_);
v___x_1116_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1110_, v___x_1115_);
v___x_1117_ = l_Lean_Syntax_node2(v___x_1007_, v___x_1107_, v___x_1109_, v___x_1116_);
lean_inc_ref(v___x_1015_);
v___x_1118_ = l_Lean_Syntax_node3(v___x_1007_, v___x_1106_, v___x_1117_, v___x_1015_, v___x_1075_);
v___x_1119_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1013_, v___x_1118_);
v___x_1120_ = l_Lean_Syntax_node2(v___x_1007_, v___x_1081_, v___x_1105_, v___x_1119_);
v___x_1121_ = l_Lean_Syntax_node4(v___x_1007_, v___x_1068_, v___x_1070_, v___x_1098_, v___x_1080_, v___x_1120_);
v___x_1122_ = l_Lean_Syntax_node2(v___x_1007_, v___x_1013_, v___x_1092_, v___x_1121_);
v___x_1123_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1067_, v___x_1122_);
v___x_1124_ = l_Lean_Syntax_node2(v___x_1007_, v___x_1065_, v___x_1066_, v___x_1123_);
v___x_1125_ = lean_unsigned_to_nat(9u);
v___x_1126_ = lean_mk_empty_array_with_capacity(v___x_1125_);
v___x_1127_ = lean_array_push(v___x_1126_, v___x_1015_);
v___x_1128_ = lean_array_push(v___x_1127_, v___x_1048_);
v___x_1129_ = lean_array_push(v___x_1128_, v___x_1028_);
v___x_1130_ = lean_array_push(v___x_1129_, v___x_1049_);
v___x_1131_ = lean_array_push(v___x_1130_, v___x_1054_);
v___x_1132_ = lean_array_push(v___x_1131_, v___x_1023_);
v___x_1133_ = lean_array_push(v___x_1132_, v___x_1061_);
v___x_1134_ = lean_array_push(v___x_1133_, v___x_1063_);
v___x_1135_ = lean_array_push(v___x_1134_, v___x_1124_);
v___x_1136_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1007_);
lean_ctor_set(v___x_1136_, 1, v___x_1030_);
lean_ctor_set(v___x_1136_, 2, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1137_);
v___x_1139_ = v___x_995_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_a_993_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_del_object(v___x_987_);
lean_dec(v_fst_985_);
lean_del_object(v___x_982_);
lean_dec(v_pat_962_);
lean_dec(v_attrKind_961_);
v_a_1144_ = lean_ctor_get(v___x_991_, 0);
v_a_1145_ = lean_ctor_get(v___x_991_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_991_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_inc(v_a_1144_);
lean_dec(v___x_991_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1144_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
else
{
lean_object* v_a_1155_; 
lean_del_object(v___x_982_);
lean_dec(v_tail_980_);
lean_dec(v_head_978_);
lean_dec_ref(v_snd_972_);
lean_dec(v_pat_962_);
lean_dec(v_attrKind_961_);
v_a_1155_ = lean_ctor_get(v___x_976_, 1);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_976_, 2);
v___y_967_ = v_a_1155_;
goto v___jp_966_;
}
}
}
else
{
lean_object* v_a_1158_; 
lean_dec(v_snd_979_);
lean_dec_ref_known(v_a_977_, 2);
lean_dec(v_head_978_);
lean_dec_ref(v_snd_972_);
lean_dec(v_pat_962_);
lean_dec(v_attrKind_961_);
v_a_1158_ = lean_ctor_get(v___x_976_, 1);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_976_, 2);
v___y_967_ = v_a_1158_;
goto v___jp_966_;
}
}
else
{
lean_object* v_a_1159_; 
lean_dec(v_a_977_);
lean_dec_ref(v_snd_972_);
lean_dec(v_pat_962_);
lean_dec(v_attrKind_961_);
v_a_1159_ = lean_ctor_get(v___x_976_, 1);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_976_, 2);
v___y_967_ = v_a_1159_;
goto v___jp_966_;
}
}
else
{
lean_object* v_a_1160_; lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v_snd_972_);
lean_dec(v_pat_962_);
lean_dec(v_attrKind_961_);
v_a_1160_ = lean_ctor_get(v___x_976_, 0);
v_a_1161_ = lean_ctor_get(v___x_976_, 1);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_976_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_inc(v_a_1160_);
lean_dec(v___x_976_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1160_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander___boxed(lean_object* v_attrKind_1185_, lean_object* v_pat_1186_, lean_object* v_qrhs_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_Elab_Command_mkUnexpander(v_attrKind_1185_, v_pat_1186_, v_qrhs_1187_, v_a_1188_, v_a_1189_);
lean_dec_ref(v_a_1188_);
return v_res_1190_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___x_1191_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg(){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0);
v___x_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___boxed(lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(lean_object* v_00_u03b1_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___boxed(lean_object* v_00_u03b1_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(v_00_u03b1_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; lean_object* v_env_1212_; lean_object* v___x_1213_; lean_object* v_mainModule_1214_; lean_object* v___x_1215_; 
v___x_1211_ = lean_st_ref_get(v___y_1209_);
v_env_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc_ref(v_env_1212_);
lean_dec(v___x_1211_);
v___x_1213_ = l_Lean_Environment_header(v_env_1212_);
lean_dec_ref(v_env_1212_);
v_mainModule_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_mainModule_1214_);
lean_dec_ref(v___x_1213_);
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v_mainModule_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg___boxed(lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_1216_);
lean_dec(v___y_1216_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___boxed(lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___lam__0(lean_object* v___x_1227_, lean_object* v_sc_1228_){
_start:
{
lean_object* v_header_1229_; lean_object* v_currNamespace_1230_; lean_object* v_openDecls_1231_; lean_object* v_levelNames_1232_; lean_object* v_varDecls_1233_; lean_object* v_varUIds_1234_; lean_object* v_includedVars_1235_; lean_object* v_omittedVars_1236_; uint8_t v_isNoncomputable_1237_; uint8_t v_isPublic_1238_; uint8_t v_isMeta_1239_; lean_object* v_attrs_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v_header_1229_ = lean_ctor_get(v_sc_1228_, 0);
v_currNamespace_1230_ = lean_ctor_get(v_sc_1228_, 2);
v_openDecls_1231_ = lean_ctor_get(v_sc_1228_, 3);
v_levelNames_1232_ = lean_ctor_get(v_sc_1228_, 4);
v_varDecls_1233_ = lean_ctor_get(v_sc_1228_, 5);
v_varUIds_1234_ = lean_ctor_get(v_sc_1228_, 6);
v_includedVars_1235_ = lean_ctor_get(v_sc_1228_, 7);
v_omittedVars_1236_ = lean_ctor_get(v_sc_1228_, 8);
v_isNoncomputable_1237_ = lean_ctor_get_uint8(v_sc_1228_, sizeof(void*)*10);
v_isPublic_1238_ = lean_ctor_get_uint8(v_sc_1228_, sizeof(void*)*10 + 1);
v_isMeta_1239_ = lean_ctor_get_uint8(v_sc_1228_, sizeof(void*)*10 + 2);
v_attrs_1240_ = lean_ctor_get(v_sc_1228_, 9);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_sc_1228_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v_sc_1228_, 1);
lean_dec(v_unused_1248_);
v___x_1242_ = v_sc_1228_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_attrs_1240_);
lean_inc(v_omittedVars_1236_);
lean_inc(v_includedVars_1235_);
lean_inc(v_varUIds_1234_);
lean_inc(v_varDecls_1233_);
lean_inc(v_levelNames_1232_);
lean_inc(v_openDecls_1231_);
lean_inc(v_currNamespace_1230_);
lean_inc(v_header_1229_);
lean_dec(v_sc_1228_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___x_1227_);
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_header_1229_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_currNamespace_1230_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_openDecls_1231_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_levelNames_1232_);
lean_ctor_set(v_reuseFailAlloc_1246_, 5, v_varDecls_1233_);
lean_ctor_set(v_reuseFailAlloc_1246_, 6, v_varUIds_1234_);
lean_ctor_set(v_reuseFailAlloc_1246_, 7, v_includedVars_1235_);
lean_ctor_set(v_reuseFailAlloc_1246_, 8, v_omittedVars_1236_);
lean_ctor_set(v_reuseFailAlloc_1246_, 9, v_attrs_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, sizeof(void*)*10, v_isNoncomputable_1237_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, sizeof(void*)*10 + 1, v_isPublic_1238_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, sizeof(void*)*10 + 2, v_isMeta_1239_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(size_t v_sz_1249_, size_t v_i_1250_, lean_object* v_bs_1251_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_usize_dec_lt(v_i_1250_, v_sz_1249_);
if (v___x_1252_ == 0)
{
return v_bs_1251_;
}
else
{
lean_object* v_v_1253_; lean_object* v___x_1254_; lean_object* v_bs_x27_1255_; size_t v___x_1256_; size_t v___x_1257_; lean_object* v___x_1258_; 
v_v_1253_ = lean_array_uget(v_bs_1251_, v_i_1250_);
v___x_1254_ = lean_unsigned_to_nat(0u);
v_bs_x27_1255_ = lean_array_uset(v_bs_1251_, v_i_1250_, v___x_1254_);
v___x_1256_ = ((size_t)1ULL);
v___x_1257_ = lean_usize_add(v_i_1250_, v___x_1256_);
v___x_1258_ = lean_array_uset(v_bs_x27_1255_, v_i_1250_, v_v_1253_);
v_i_1250_ = v___x_1257_;
v_bs_1251_ = v___x_1258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3___boxed(lean_object* v_sz_1260_, lean_object* v_i_1261_, lean_object* v_bs_1262_){
_start:
{
size_t v_sz_boxed_1263_; size_t v_i_boxed_1264_; lean_object* v_res_1265_; 
v_sz_boxed_1263_ = lean_unbox_usize(v_sz_1260_);
lean_dec(v_sz_1260_);
v_i_boxed_1264_ = lean_unbox_usize(v_i_1261_);
lean_dec(v_i_1261_);
v_res_1265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_boxed_1263_, v_i_boxed_1264_, v_bs_1262_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(lean_object* v_o_1269_, lean_object* v_k_1270_, uint8_t v_v_1271_){
_start:
{
lean_object* v_map_1272_; uint8_t v_hasTrace_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1287_; 
v_map_1272_ = lean_ctor_get(v_o_1269_, 0);
v_hasTrace_1273_ = lean_ctor_get_uint8(v_o_1269_, sizeof(void*)*1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_o_1269_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1275_ = v_o_1269_;
v_isShared_1276_ = v_isSharedCheck_1287_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_map_1272_);
lean_dec(v_o_1269_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1287_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1277_, 0, v_v_1271_);
lean_inc(v_k_1270_);
v___x_1278_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1270_, v___x_1277_, v_map_1272_);
if (v_hasTrace_1273_ == 0)
{
lean_object* v___x_1279_; uint8_t v___x_1280_; lean_object* v___x_1282_; 
v___x_1279_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
v___x_1280_ = l_Lean_Name_isPrefixOf(v___x_1279_, v_k_1270_);
lean_dec(v_k_1270_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1278_);
v___x_1282_ = v___x_1275_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1278_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_ctor_set_uint8(v___x_1282_, sizeof(void*)*1, v___x_1280_);
return v___x_1282_;
}
}
else
{
lean_object* v___x_1285_; 
lean_dec(v_k_1270_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1278_);
v___x_1285_ = v___x_1275_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1278_);
lean_ctor_set_uint8(v_reuseFailAlloc_1286_, sizeof(void*)*1, v_hasTrace_1273_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___boxed(lean_object* v_o_1288_, lean_object* v_k_1289_, lean_object* v_v_1290_){
_start:
{
uint8_t v_v_boxed_1291_; lean_object* v_res_1292_; 
v_v_boxed_1291_ = lean_unbox(v_v_1290_);
v_res_1292_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(v_o_1288_, v_k_1289_, v_v_boxed_1291_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(lean_object* v_opts_1293_, lean_object* v_opt_1294_, uint8_t v_val_1295_){
_start:
{
lean_object* v_name_1296_; lean_object* v___x_1297_; 
v_name_1296_ = lean_ctor_get(v_opt_1294_, 0);
lean_inc(v_name_1296_);
lean_dec_ref(v_opt_1294_);
v___x_1297_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(v_opts_1293_, v_name_1296_, v_val_1295_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6___boxed(lean_object* v_opts_1298_, lean_object* v_opt_1299_, lean_object* v_val_1300_){
_start:
{
uint8_t v_val_boxed_1301_; lean_object* v_res_1302_; 
v_val_boxed_1301_ = lean_unbox(v_val_1300_);
v_res_1302_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_1298_, v_opt_1299_, v_val_boxed_1301_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(size_t v_sz_1303_, size_t v_i_1304_, lean_object* v_bs_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
uint8_t v___x_1308_; 
v___x_1308_ = lean_usize_dec_lt(v_i_1304_, v_sz_1303_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v_bs_1305_);
lean_ctor_set(v___x_1309_, 1, v___y_1307_);
return v___x_1309_;
}
else
{
lean_object* v_v_1310_; lean_object* v___x_1311_; 
v_v_1310_ = lean_array_uget_borrowed(v_bs_1305_, v_i_1304_);
lean_inc(v_v_1310_);
v___x_1311_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(v_v_1310_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v_a_1313_; lean_object* v___x_1314_; lean_object* v_bs_x27_1315_; size_t v___x_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
v_a_1313_ = lean_ctor_get(v___x_1311_, 1);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1311_, 2);
v___x_1314_ = lean_unsigned_to_nat(0u);
v_bs_x27_1315_ = lean_array_uset(v_bs_1305_, v_i_1304_, v___x_1314_);
v___x_1316_ = ((size_t)1ULL);
v___x_1317_ = lean_usize_add(v_i_1304_, v___x_1316_);
v___x_1318_ = lean_array_uset(v_bs_x27_1315_, v_i_1304_, v_a_1312_);
v_i_1304_ = v___x_1317_;
v_bs_1305_ = v___x_1318_;
v___y_1307_ = v_a_1313_;
goto _start;
}
else
{
lean_object* v_a_1320_; lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v_bs_1305_);
v_a_1320_ = lean_ctor_get(v___x_1311_, 0);
v_a_1321_ = lean_ctor_get(v___x_1311_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1311_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_inc(v_a_1320_);
lean_dec(v___x_1311_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1320_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed(lean_object* v_sz_1329_, lean_object* v_i_1330_, lean_object* v_bs_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
size_t v_sz_boxed_1334_; size_t v_i_boxed_1335_; lean_object* v_res_1336_; 
v_sz_boxed_1334_ = lean_unbox_usize(v_sz_1329_);
lean_dec(v_sz_1329_);
v_i_boxed_1335_ = lean_unbox_usize(v_i_1330_);
lean_dec(v_i_1330_);
v_res_1336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(v_sz_boxed_1334_, v_i_boxed_1335_, v_bs_1331_, v___y_1332_, v___y_1333_);
lean_dec_ref(v___y_1332_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(size_t v_sz_1337_, size_t v_i_1338_, lean_object* v_bs_1339_){
_start:
{
uint8_t v___x_1340_; 
v___x_1340_ = lean_usize_dec_lt(v_i_1338_, v_sz_1337_);
if (v___x_1340_ == 0)
{
return v_bs_1339_;
}
else
{
lean_object* v___x_1341_; lean_object* v_v_1342_; lean_object* v_bs_x27_1343_; lean_object* v___x_1344_; size_t v___x_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
v___x_1341_ = lean_unsigned_to_nat(0u);
v_v_1342_ = lean_array_uget(v_bs_1339_, v_i_1338_);
v_bs_x27_1343_ = lean_array_uset(v_bs_1339_, v_i_1338_, v___x_1341_);
v___x_1344_ = l_Lean_Syntax_getArg(v_v_1342_, v___x_1341_);
lean_dec(v_v_1342_);
v___x_1345_ = ((size_t)1ULL);
v___x_1346_ = lean_usize_add(v_i_1338_, v___x_1345_);
v___x_1347_ = lean_array_uset(v_bs_x27_1343_, v_i_1338_, v___x_1344_);
v_i_1338_ = v___x_1346_;
v_bs_1339_ = v___x_1347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed(lean_object* v_sz_1349_, lean_object* v_i_1350_, lean_object* v_bs_1351_){
_start:
{
size_t v_sz_boxed_1352_; size_t v_i_boxed_1353_; lean_object* v_res_1354_; 
v_sz_boxed_1352_ = lean_unbox_usize(v_sz_1349_);
lean_dec(v_sz_1349_);
v_i_boxed_1353_ = lean_unbox_usize(v_i_1350_);
lean_dec(v_i_1350_);
v_res_1354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_boxed_1352_, v_i_boxed_1353_, v_bs_1351_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(size_t v_sz_1355_, size_t v_i_1356_, lean_object* v_bs_1357_, lean_object* v___y_1358_){
_start:
{
uint8_t v___x_1359_; 
v___x_1359_ = lean_usize_dec_lt(v_i_1356_, v_sz_1355_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v_bs_1357_);
lean_ctor_set(v___x_1360_, 1, v___y_1358_);
return v___x_1360_;
}
else
{
lean_object* v_v_1361_; lean_object* v___x_1362_; 
v_v_1361_ = lean_array_uget_borrowed(v_bs_1357_, v_i_1356_);
lean_inc(v_v_1361_);
v___x_1362_ = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(v_v_1361_, v___y_1358_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v_a_1364_; lean_object* v___x_1365_; lean_object* v_bs_x27_1366_; size_t v___x_1367_; size_t v___x_1368_; lean_object* v___x_1369_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
v_a_1364_ = lean_ctor_get(v___x_1362_, 1);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1362_, 2);
v___x_1365_ = lean_unsigned_to_nat(0u);
v_bs_x27_1366_ = lean_array_uset(v_bs_1357_, v_i_1356_, v___x_1365_);
v___x_1367_ = ((size_t)1ULL);
v___x_1368_ = lean_usize_add(v_i_1356_, v___x_1367_);
v___x_1369_ = lean_array_uset(v_bs_x27_1366_, v_i_1356_, v_a_1363_);
v_i_1356_ = v___x_1368_;
v_bs_1357_ = v___x_1369_;
v___y_1358_ = v_a_1364_;
goto _start;
}
else
{
lean_object* v_a_1371_; lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec_ref(v_bs_1357_);
v_a_1371_ = lean_ctor_get(v___x_1362_, 0);
v_a_1372_ = lean_ctor_get(v___x_1362_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1362_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_inc(v_a_1371_);
lean_dec(v___x_1362_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1371_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg___boxed(lean_object* v_sz_1380_, lean_object* v_i_1381_, lean_object* v_bs_1382_, lean_object* v___y_1383_){
_start:
{
size_t v_sz_boxed_1384_; size_t v_i_boxed_1385_; lean_object* v_res_1386_; 
v_sz_boxed_1384_ = lean_unbox_usize(v_sz_1380_);
lean_dec(v_sz_1380_);
v_i_boxed_1385_ = lean_unbox_usize(v_i_1381_);
lean_dec(v_i_1381_);
v_res_1386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(v_sz_boxed_1384_, v_i_boxed_1385_, v_bs_1382_, v___y_1383_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(size_t v_sz_1387_, size_t v_i_1388_, lean_object* v_bs_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(v_sz_1387_, v_i_1388_, v_bs_1389_, v___y_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed(lean_object* v_sz_1393_, lean_object* v_i_1394_, lean_object* v_bs_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
size_t v_sz_boxed_1398_; size_t v_i_boxed_1399_; lean_object* v_res_1400_; 
v_sz_boxed_1398_ = lean_unbox_usize(v_sz_1393_);
lean_dec(v_sz_1393_);
v_i_boxed_1399_ = lean_unbox_usize(v_i_1394_);
lean_dec(v_i_1394_);
v_res_1400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(v_sz_boxed_1398_, v_i_boxed_1399_, v_bs_1395_, v___y_1396_, v___y_1397_);
lean_dec_ref(v___y_1396_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(lean_object* v_env_1401_, lean_object* v_currNamespace_1402_, lean_object* v_openDecls_1403_, lean_object* v_n_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = l_Lean_ResolveName_resolveNamespace(v_env_1401_, v_currNamespace_1402_, v_openDecls_1403_, v_n_1404_);
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
lean_ctor_set(v___x_1408_, 1, v___y_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed(lean_object* v_env_1409_, lean_object* v_currNamespace_1410_, lean_object* v_openDecls_1411_, lean_object* v_n_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(v_env_1409_, v_currNamespace_1410_, v_openDecls_1411_, v_n_1412_, v___y_1413_, v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1415_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1416_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
lean_ctor_set(v___x_1421_, 2, v___x_1420_);
lean_ctor_set(v___x_1421_, 3, v___x_1420_);
lean_ctor_set(v___x_1421_, 4, v___x_1419_);
lean_ctor_set(v___x_1421_, 5, v___x_1419_);
lean_ctor_set(v___x_1421_, 6, v___x_1419_);
lean_ctor_set(v___x_1421_, 7, v___x_1419_);
lean_ctor_set(v___x_1421_, 8, v___x_1419_);
lean_ctor_set(v___x_1421_, 9, v___x_1419_);
return v___x_1421_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_unsigned_to_nat(32u);
v___x_1423_ = lean_mk_empty_array_with_capacity(v___x_1422_);
v___x_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
return v___x_1424_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4(void){
_start:
{
size_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1425_ = ((size_t)5ULL);
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = lean_unsigned_to_nat(32u);
v___x_1428_ = lean_mk_empty_array_with_capacity(v___x_1427_);
v___x_1429_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3);
v___x_1430_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1428_);
lean_ctor_set(v___x_1430_, 2, v___x_1426_);
lean_ctor_set(v___x_1430_, 3, v___x_1426_);
lean_ctor_set_usize(v___x_1430_, 4, v___x_1425_);
return v___x_1430_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1431_ = lean_box(1);
v___x_1432_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4);
v___x_1433_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_1434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v___x_1432_);
lean_ctor_set(v___x_1434_, 2, v___x_1431_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; lean_object* v_env_1439_; lean_object* v___x_1440_; lean_object* v_scopes_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v_opts_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1438_ = lean_st_ref_get(v___y_1436_);
v_env_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc_ref(v_env_1439_);
lean_dec(v___x_1438_);
v___x_1440_ = lean_st_ref_get(v___y_1436_);
v_scopes_1441_ = lean_ctor_get(v___x_1440_, 2);
lean_inc(v_scopes_1441_);
lean_dec(v___x_1440_);
v___x_1442_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1443_ = l_List_head_x21___redArg(v___x_1442_, v_scopes_1441_);
lean_dec(v_scopes_1441_);
v_opts_1444_ = lean_ctor_get(v___x_1443_, 1);
lean_inc_ref(v_opts_1444_);
lean_dec(v___x_1443_);
v___x_1445_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_1446_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5);
v___x_1447_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1447_, 0, v_env_1439_);
lean_ctor_set(v___x_1447_, 1, v___x_1445_);
lean_ctor_set(v___x_1447_, 2, v___x_1446_);
lean_ctor_set(v___x_1447_, 3, v_opts_1444_);
v___x_1448_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
lean_ctor_set(v___x_1448_, 1, v_msgData_1435_);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msgData_1450_, v___y_1451_);
lean_dec(v___y_1451_);
return v_res_1453_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1454_; double v___x_1455_; 
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_float_of_nat(v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(lean_object* v_cls_1458_, lean_object* v_msg_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_Elab_Command_getRef___redArg(v___y_1460_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1512_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msg_1459_, v___y_1461_);
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1512_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1512_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v_traceState_1471_; lean_object* v_env_1472_; lean_object* v_messages_1473_; lean_object* v_scopes_1474_; lean_object* v_usedQuotCtxts_1475_; lean_object* v_nextMacroScope_1476_; lean_object* v_maxRecDepth_1477_; lean_object* v_ngen_1478_; lean_object* v_auxDeclNGen_1479_; lean_object* v_infoState_1480_; lean_object* v_snapshotTasks_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1511_; 
v___x_1470_ = lean_st_ref_take(v___y_1461_);
v_traceState_1471_ = lean_ctor_get(v___x_1470_, 9);
v_env_1472_ = lean_ctor_get(v___x_1470_, 0);
v_messages_1473_ = lean_ctor_get(v___x_1470_, 1);
v_scopes_1474_ = lean_ctor_get(v___x_1470_, 2);
v_usedQuotCtxts_1475_ = lean_ctor_get(v___x_1470_, 3);
v_nextMacroScope_1476_ = lean_ctor_get(v___x_1470_, 4);
v_maxRecDepth_1477_ = lean_ctor_get(v___x_1470_, 5);
v_ngen_1478_ = lean_ctor_get(v___x_1470_, 6);
v_auxDeclNGen_1479_ = lean_ctor_get(v___x_1470_, 7);
v_infoState_1480_ = lean_ctor_get(v___x_1470_, 8);
v_snapshotTasks_1481_ = lean_ctor_get(v___x_1470_, 10);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1483_ = v___x_1470_;
v_isShared_1484_ = v_isSharedCheck_1511_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_snapshotTasks_1481_);
lean_inc(v_traceState_1471_);
lean_inc(v_infoState_1480_);
lean_inc(v_auxDeclNGen_1479_);
lean_inc(v_ngen_1478_);
lean_inc(v_maxRecDepth_1477_);
lean_inc(v_nextMacroScope_1476_);
lean_inc(v_usedQuotCtxts_1475_);
lean_inc(v_scopes_1474_);
lean_inc(v_messages_1473_);
lean_inc(v_env_1472_);
lean_dec(v___x_1470_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1511_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
uint64_t v_tid_1485_; lean_object* v_traces_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1510_; 
v_tid_1485_ = lean_ctor_get_uint64(v_traceState_1471_, sizeof(void*)*1);
v_traces_1486_ = lean_ctor_get(v_traceState_1471_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_traceState_1471_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1488_ = v_traceState_1471_;
v_isShared_1489_ = v_isSharedCheck_1510_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_traces_1486_);
lean_dec(v_traceState_1471_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1510_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; double v___x_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1490_ = lean_box(0);
v___x_1491_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0);
v___x_1492_ = 0;
v___x_1493_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1494_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1494_, 0, v_cls_1458_);
lean_ctor_set(v___x_1494_, 1, v___x_1490_);
lean_ctor_set(v___x_1494_, 2, v___x_1493_);
lean_ctor_set_float(v___x_1494_, sizeof(void*)*3, v___x_1491_);
lean_ctor_set_float(v___x_1494_, sizeof(void*)*3 + 8, v___x_1491_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*3 + 16, v___x_1492_);
v___x_1495_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__1));
v___x_1496_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set(v___x_1496_, 1, v_a_1466_);
lean_ctor_set(v___x_1496_, 2, v___x_1495_);
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v_a_1464_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = l_Lean_PersistentArray_push___redArg(v_traces_1486_, v___x_1497_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1498_);
v___x_1500_ = v___x_1488_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1498_);
lean_ctor_set_uint64(v_reuseFailAlloc_1509_, sizeof(void*)*1, v_tid_1485_);
v___x_1500_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1502_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 9, v___x_1500_);
v___x_1502_ = v___x_1483_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_env_1472_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_messages_1473_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_scopes_1474_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_usedQuotCtxts_1475_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_nextMacroScope_1476_);
lean_ctor_set(v_reuseFailAlloc_1508_, 5, v_maxRecDepth_1477_);
lean_ctor_set(v_reuseFailAlloc_1508_, 6, v_ngen_1478_);
lean_ctor_set(v_reuseFailAlloc_1508_, 7, v_auxDeclNGen_1479_);
lean_ctor_set(v_reuseFailAlloc_1508_, 8, v_infoState_1480_);
lean_ctor_set(v_reuseFailAlloc_1508_, 9, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1508_, 10, v_snapshotTasks_1481_);
v___x_1502_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1503_ = lean_st_ref_set(v___y_1461_, v___x_1502_);
v___x_1504_ = lean_box(0);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1504_);
v___x_1506_ = v___x_1468_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref(v_msg_1459_);
lean_dec(v_cls_1458_);
v_a_1513_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1463_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1463_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___boxed(lean_object* v_cls_1521_, lean_object* v_msg_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_1521_, v_msg_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(lean_object* v_as_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
if (lean_obj_tag(v_as_1527_) == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = lean_box(0);
v___x_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
return v___x_1532_;
}
else
{
lean_object* v_head_1533_; lean_object* v_tail_1534_; lean_object* v_fst_1535_; lean_object* v_snd_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v_scopes_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v_opts_1543_; uint8_t v_hasTrace_1544_; 
v_head_1533_ = lean_ctor_get(v_as_1527_, 0);
lean_inc(v_head_1533_);
v_tail_1534_ = lean_ctor_get(v_as_1527_, 1);
lean_inc(v_tail_1534_);
lean_dec_ref_known(v_as_1527_, 2);
v_fst_1535_ = lean_ctor_get(v_head_1533_, 0);
lean_inc(v_fst_1535_);
v_snd_1536_ = lean_ctor_get(v_head_1533_, 1);
lean_inc(v_snd_1536_);
lean_dec(v_head_1533_);
v___x_1537_ = l_Lean_inheritedTraceOptions;
v___x_1538_ = lean_st_ref_get(v___x_1537_);
v___x_1539_ = lean_st_ref_get(v___y_1529_);
v_scopes_1540_ = lean_ctor_get(v___x_1539_, 2);
lean_inc(v_scopes_1540_);
lean_dec(v___x_1539_);
v___x_1541_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1542_ = l_List_head_x21___redArg(v___x_1541_, v_scopes_1540_);
lean_dec(v_scopes_1540_);
v_opts_1543_ = lean_ctor_get(v___x_1542_, 1);
lean_inc_ref(v_opts_1543_);
lean_dec(v___x_1542_);
v_hasTrace_1544_ = lean_ctor_get_uint8(v_opts_1543_, sizeof(void*)*1);
if (v_hasTrace_1544_ == 0)
{
lean_dec_ref(v_opts_1543_);
lean_dec(v___x_1538_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
v_as_1527_ = v_tail_1534_;
goto _start;
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
lean_inc(v_fst_1535_);
v___x_1547_ = l_Lean_Name_append(v___x_1546_, v_fst_1535_);
v___x_1548_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1538_, v_opts_1543_, v___x_1547_);
lean_dec(v___x_1547_);
lean_dec_ref(v_opts_1543_);
lean_dec(v___x_1538_);
if (v___x_1548_ == 0)
{
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
v_as_1527_ = v_tail_1534_;
goto _start;
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1550_, 0, v_snd_1536_);
v___x_1551_ = l_Lean_MessageData_ofFormat(v___x_1550_);
v___x_1552_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_fst_1535_, v___x_1551_, v___y_1528_, v___y_1529_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_dec_ref_known(v___x_1552_, 1);
v_as_1527_ = v_tail_1534_;
goto _start;
}
else
{
lean_dec(v_tail_1534_);
return v___x_1552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___boxed(lean_object* v_as_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v_as_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(lean_object* v_currNamespace_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_currNamespace_1559_);
lean_ctor_set(v___x_1562_, 1, v___y_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(v_currNamespace_1563_, v___y_1564_, v___y_1565_);
lean_dec_ref(v___y_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(lean_object* v_env_1567_, lean_object* v_opts_1568_, lean_object* v_currNamespace_1569_, lean_object* v_openDecls_1570_, lean_object* v_n_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = l_Lean_ResolveName_resolveGlobalName(v_env_1567_, v_opts_1568_, v_currNamespace_1569_, v_openDecls_1570_, v_n_1571_);
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v___y_1573_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed(lean_object* v_env_1576_, lean_object* v_opts_1577_, lean_object* v_currNamespace_1578_, lean_object* v_openDecls_1579_, lean_object* v_n_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(v_env_1576_, v_opts_1577_, v_currNamespace_1578_, v_openDecls_1579_, v_n_1580_, v___y_1581_, v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec_ref(v_opts_1577_);
return v_res_1583_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_box(1);
v___x_1585_ = l_Lean_MessageData_ofFormat(v___x_1584_);
return v___x_1585_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__2));
v___x_1590_ = l_Lean_MessageData_ofFormat(v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(lean_object* v_x_1591_, lean_object* v_x_1592_){
_start:
{
if (lean_obj_tag(v_x_1592_) == 0)
{
return v_x_1591_;
}
else
{
lean_object* v_head_1593_; lean_object* v_tail_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1616_; 
v_head_1593_ = lean_ctor_get(v_x_1592_, 0);
v_tail_1594_ = lean_ctor_get(v_x_1592_, 1);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1596_ = v_x_1592_;
v_isShared_1597_ = v_isSharedCheck_1616_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_tail_1594_);
lean_inc(v_head_1593_);
lean_dec(v_x_1592_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1616_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_before_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1614_; 
v_before_1598_ = lean_ctor_get(v_head_1593_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_head_1593_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; 
v_unused_1615_ = lean_ctor_get(v_head_1593_, 1);
lean_dec(v_unused_1615_);
v___x_1600_ = v_head_1593_;
v_isShared_1601_ = v_isSharedCheck_1614_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_before_1598_);
lean_dec(v_head_1593_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1614_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1602_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0);
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 7);
lean_ctor_set(v___x_1600_, 1, v___x_1602_);
lean_ctor_set(v___x_1600_, 0, v_x_1591_);
v___x_1604_ = v___x_1600_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_x_1591_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3);
if (v_isShared_1597_ == 0)
{
lean_ctor_set_tag(v___x_1596_, 7);
lean_ctor_set(v___x_1596_, 1, v___x_1605_);
lean_ctor_set(v___x_1596_, 0, v___x_1604_);
v___x_1607_ = v___x_1596_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1608_ = l_Lean_MessageData_ofSyntax(v_before_1598_);
v___x_1609_ = l_Lean_indentD(v___x_1608_);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1607_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v_x_1591_ = v___x_1610_;
v_x_1592_ = v_tail_1594_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(lean_object* v_opts_1617_, lean_object* v_opt_1618_){
_start:
{
lean_object* v_name_1619_; lean_object* v_defValue_1620_; lean_object* v_map_1621_; lean_object* v___x_1622_; 
v_name_1619_ = lean_ctor_get(v_opt_1618_, 0);
v_defValue_1620_ = lean_ctor_get(v_opt_1618_, 1);
v_map_1621_ = lean_ctor_get(v_opts_1617_, 0);
v___x_1622_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1621_, v_name_1619_);
if (lean_obj_tag(v___x_1622_) == 0)
{
uint8_t v___x_1623_; 
v___x_1623_ = lean_unbox(v_defValue_1620_);
return v___x_1623_;
}
else
{
lean_object* v_val_1624_; 
v_val_1624_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_val_1624_);
lean_dec_ref_known(v___x_1622_, 1);
if (lean_obj_tag(v_val_1624_) == 1)
{
uint8_t v_v_1625_; 
v_v_1625_ = lean_ctor_get_uint8(v_val_1624_, 0);
lean_dec_ref_known(v_val_1624_, 0);
return v_v_1625_;
}
else
{
uint8_t v___x_1626_; 
lean_dec(v_val_1624_);
v___x_1626_ = lean_unbox(v_defValue_1620_);
return v___x_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25___boxed(lean_object* v_opts_1627_, lean_object* v_opt_1628_){
_start:
{
uint8_t v_res_1629_; lean_object* v_r_1630_; 
v_res_1629_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(v_opts_1627_, v_opt_1628_);
lean_dec_ref(v_opt_1628_);
lean_dec_ref(v_opts_1627_);
v_r_1630_ = lean_box(v_res_1629_);
return v_r_1630_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__1));
v___x_1635_ = l_Lean_MessageData_ofFormat(v___x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(lean_object* v_msgData_1636_, lean_object* v_macroStack_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v_scopes_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_opts_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; uint8_t v___x_1647_; 
v___x_1640_ = lean_st_ref_get(v___y_1638_);
v_scopes_1641_ = lean_ctor_get(v___x_1640_, 2);
lean_inc(v_scopes_1641_);
lean_dec(v___x_1640_);
v___x_1642_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1643_ = l_List_head_x21___redArg(v___x_1642_, v_scopes_1641_);
lean_dec(v_scopes_1641_);
v_opts_1644_ = lean_ctor_get(v___x_1643_, 1);
lean_inc_ref(v_opts_1644_);
lean_dec(v___x_1643_);
v___x_1645_ = l_Lean_Elab_pp_macroStack;
v___x_1646_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(v_opts_1644_, v___x_1645_);
lean_dec_ref(v_opts_1644_);
v___x_1647_ = lean_bool_not(v___x_1646_);
if (v___x_1647_ == 0)
{
if (lean_obj_tag(v_macroStack_1637_) == 0)
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v_msgData_1636_);
return v___x_1648_;
}
else
{
lean_object* v_head_1649_; lean_object* v_after_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1665_; 
v_head_1649_ = lean_ctor_get(v_macroStack_1637_, 0);
lean_inc(v_head_1649_);
v_after_1650_ = lean_ctor_get(v_head_1649_, 1);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_head_1649_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v_head_1649_, 0);
lean_dec(v_unused_1666_);
v___x_1652_ = v_head_1649_;
v_isShared_1653_ = v_isSharedCheck_1665_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_after_1650_);
lean_dec(v_head_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1665_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0);
if (v_isShared_1653_ == 0)
{
lean_ctor_set_tag(v___x_1652_, 7);
lean_ctor_set(v___x_1652_, 1, v___x_1654_);
lean_ctor_set(v___x_1652_, 0, v_msgData_1636_);
v___x_1656_ = v___x_1652_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_msgData_1636_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v_msgData_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1657_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2);
v___x_1658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = l_Lean_MessageData_ofSyntax(v_after_1650_);
v___x_1660_ = l_Lean_indentD(v___x_1659_);
v_msgData_1661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1661_, 0, v___x_1658_);
lean_ctor_set(v_msgData_1661_, 1, v___x_1660_);
v___x_1662_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(v_msgData_1661_, v_macroStack_1637_);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
}
}
}
else
{
lean_object* v___x_1667_; 
lean_dec(v_macroStack_1637_);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v_msgData_1636_);
return v___x_1667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___boxed(lean_object* v_msgData_1668_, lean_object* v_macroStack_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_msgData_1668_, v_macroStack_1669_, v___y_1670_);
lean_dec(v___y_1670_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(lean_object* v_msg_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Elab_Command_getRef___redArg(v___y_1674_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v_macroStack_1679_; lean_object* v___x_1680_; lean_object* v_a_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1692_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref_known(v___x_1677_, 1);
v_macroStack_1679_ = lean_ctor_get(v___y_1674_, 4);
v___x_1680_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msg_1673_, v___y_1675_);
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref(v___x_1680_);
v___x_1682_ = l_Lean_Elab_getBetterRef(v_a_1678_, v_macroStack_1679_);
lean_dec(v_a_1678_);
lean_inc(v_macroStack_1679_);
v___x_1683_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_a_1681_, v_macroStack_1679_, v___y_1675_);
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1682_);
lean_ctor_set(v___x_1688_, 1, v_a_1684_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set_tag(v___x_1686_, 1);
lean_ctor_set(v___x_1686_, 0, v___x_1688_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec_ref(v_msg_1673_);
v_a_1693_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1677_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1677_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg___boxed(lean_object* v_msg_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(lean_object* v_ref_1706_, lean_object* v_msg_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Elab_Command_getRef___redArg(v___y_1708_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v_fileName_1713_; lean_object* v_fileMap_1714_; lean_object* v_currRecDepth_1715_; lean_object* v_cmdPos_1716_; lean_object* v_macroStack_1717_; lean_object* v_quotContext_x3f_1718_; lean_object* v_currMacroScope_1719_; lean_object* v_snap_x3f_1720_; lean_object* v_cancelTk_x3f_1721_; uint8_t v_suppressElabErrors_1722_; lean_object* v_ref_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
lean_dec_ref_known(v___x_1711_, 1);
v_fileName_1713_ = lean_ctor_get(v___y_1708_, 0);
v_fileMap_1714_ = lean_ctor_get(v___y_1708_, 1);
v_currRecDepth_1715_ = lean_ctor_get(v___y_1708_, 2);
v_cmdPos_1716_ = lean_ctor_get(v___y_1708_, 3);
v_macroStack_1717_ = lean_ctor_get(v___y_1708_, 4);
v_quotContext_x3f_1718_ = lean_ctor_get(v___y_1708_, 5);
v_currMacroScope_1719_ = lean_ctor_get(v___y_1708_, 6);
v_snap_x3f_1720_ = lean_ctor_get(v___y_1708_, 8);
v_cancelTk_x3f_1721_ = lean_ctor_get(v___y_1708_, 9);
v_suppressElabErrors_1722_ = lean_ctor_get_uint8(v___y_1708_, sizeof(void*)*10);
v_ref_1723_ = l_Lean_replaceRef(v_ref_1706_, v_a_1712_);
lean_dec(v_a_1712_);
lean_inc(v_cancelTk_x3f_1721_);
lean_inc(v_snap_x3f_1720_);
lean_inc(v_currMacroScope_1719_);
lean_inc(v_quotContext_x3f_1718_);
lean_inc(v_macroStack_1717_);
lean_inc(v_cmdPos_1716_);
lean_inc(v_currRecDepth_1715_);
lean_inc_ref(v_fileMap_1714_);
lean_inc_ref(v_fileName_1713_);
v___x_1724_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1724_, 0, v_fileName_1713_);
lean_ctor_set(v___x_1724_, 1, v_fileMap_1714_);
lean_ctor_set(v___x_1724_, 2, v_currRecDepth_1715_);
lean_ctor_set(v___x_1724_, 3, v_cmdPos_1716_);
lean_ctor_set(v___x_1724_, 4, v_macroStack_1717_);
lean_ctor_set(v___x_1724_, 5, v_quotContext_x3f_1718_);
lean_ctor_set(v___x_1724_, 6, v_currMacroScope_1719_);
lean_ctor_set(v___x_1724_, 7, v_ref_1723_);
lean_ctor_set(v___x_1724_, 8, v_snap_x3f_1720_);
lean_ctor_set(v___x_1724_, 9, v_cancelTk_x3f_1721_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*10, v_suppressElabErrors_1722_);
v___x_1725_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_1707_, v___x_1724_, v___y_1709_);
lean_dec_ref_known(v___x_1724_, 10);
return v___x_1725_;
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec_ref(v_msg_1707_);
v_a_1726_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1711_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1711_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg___boxed(lean_object* v_ref_1734_, lean_object* v_msg_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_ref_1734_, v_msg_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v_ref_1734_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(lean_object* v_env_1740_, lean_object* v_declName_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
uint8_t v___x_1744_; lean_object* v_env_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; uint8_t v___x_1748_; 
v___x_1744_ = 0;
v_env_1745_ = l_Lean_Environment_setExporting(v_env_1740_, v___x_1744_);
lean_inc(v_declName_1741_);
v___x_1746_ = l_Lean_mkPrivateName(v_env_1745_, v_declName_1741_);
v___x_1747_ = 1;
lean_inc_ref(v_env_1745_);
v___x_1748_ = l_Lean_Environment_contains(v_env_1745_, v___x_1746_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1749_ = l_Lean_privateToUserName(v_declName_1741_);
v___x_1750_ = l_Lean_Environment_contains(v_env_1745_, v___x_1749_, v___x_1747_);
v___x_1751_ = lean_box(v___x_1750_);
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
lean_ctor_set(v___x_1752_, 1, v___y_1743_);
return v___x_1752_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec_ref(v_env_1745_);
lean_dec(v_declName_1741_);
v___x_1753_ = lean_box(v___x_1748_);
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set(v___x_1754_, 1, v___y_1743_);
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed(lean_object* v_env_1755_, lean_object* v_declName_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(v_env_1755_, v_declName_1756_, v___y_1757_, v___y_1758_);
lean_dec_ref(v___y_1757_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(lean_object* v_x_1760_, lean_object* v___y_1761_){
_start:
{
if (lean_obj_tag(v_x_1760_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; 
v_a_1762_ = lean_ctor_get(v_x_1760_, 0);
lean_inc(v_a_1762_);
v___x_1763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1763_, 0, v_a_1762_);
lean_ctor_set(v___x_1763_, 1, v___y_1761_);
return v___x_1763_;
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1765_; 
v_a_1764_ = lean_ctor_get(v_x_1760_, 0);
lean_inc(v_a_1764_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v_a_1764_);
lean_ctor_set(v___x_1765_, 1, v___y_1761_);
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg___boxed(lean_object* v_x_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v_x_1766_, v___y_1767_);
lean_dec_ref(v_x_1766_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(lean_object* v_env_1769_, lean_object* v_stx_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1769_, v_stx_1770_, v___y_1771_, v___y_1772_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
if (lean_obj_tag(v_a_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1783_; 
v_a_1775_ = lean_ctor_get(v___x_1773_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1783_ == 0)
{
lean_object* v_unused_1784_; 
v_unused_1784_ = lean_ctor_get(v___x_1773_, 0);
lean_dec(v_unused_1784_);
v___x_1777_ = v___x_1773_;
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1773_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = lean_box(0);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1779_);
v___x_1781_ = v___x_1777_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_a_1775_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v_val_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1813_; 
v_val_1785_ = lean_ctor_get(v_a_1774_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_a_1774_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1787_ = v_a_1774_;
v_isShared_1788_ = v_isSharedCheck_1813_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_val_1785_);
lean_dec(v_a_1774_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1813_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v_snd_1789_; 
v_snd_1789_ = lean_ctor_get(v_val_1785_, 1);
lean_inc(v_snd_1789_);
lean_dec(v_val_1785_);
if (lean_obj_tag(v_snd_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1799_; 
lean_del_object(v___x_1787_);
v_a_1790_ = lean_ctor_get(v___x_1773_, 1);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1773_, 2);
v_a_1791_ = lean_ctor_get(v_snd_1789_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_snd_1789_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1793_ = v_snd_1789_;
v_isShared_1794_ = v_isSharedCheck_1799_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v_snd_1789_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1799_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v___x_1796_, v_a_1790_);
lean_dec_ref(v___x_1796_);
return v___x_1797_;
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1812_; 
v_a_1800_ = lean_ctor_get(v___x_1773_, 1);
lean_inc(v_a_1800_);
lean_dec_ref_known(v___x_1773_, 2);
v_a_1801_ = lean_ctor_get(v_snd_1789_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_snd_1789_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1803_ = v_snd_1789_;
v_isShared_1804_ = v_isSharedCheck_1812_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v_snd_1789_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1812_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v_a_1801_);
v___x_1806_ = v___x_1787_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1808_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1806_);
v___x_1808_ = v___x_1803_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v___x_1808_, v_a_1800_);
lean_dec_ref(v___x_1808_);
return v___x_1809_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
v_a_1814_ = lean_ctor_get(v___x_1773_, 0);
v_a_1815_ = lean_ctor_get(v___x_1773_, 1);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1773_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_inc(v_a_1814_);
lean_dec(v___x_1773_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1814_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed(lean_object* v_env_1823_, lean_object* v_stx_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(v_env_1823_, v_stx_1824_, v___y_1825_, v___y_1826_);
lean_dec_ref(v___y_1825_);
return v_res_1827_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = l_Lean_maxRecDepthErrorMessage;
v___x_1834_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3);
v___x_1836_ = l_Lean_MessageData_ofFormat(v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4);
v___x_1838_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2));
v___x_1839_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set(v___x_1839_, 1, v___x_1837_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(lean_object* v_ref_1840_){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_ref_1840_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___boxed(lean_object* v_ref_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_1845_);
return v_res_1847_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(lean_object* v_keys_1848_, lean_object* v_i_1849_, lean_object* v_k_1850_){
_start:
{
lean_object* v___x_1851_; uint8_t v___x_1852_; 
v___x_1851_ = lean_array_get_size(v_keys_1848_);
v___x_1852_ = lean_nat_dec_lt(v_i_1849_, v___x_1851_);
if (v___x_1852_ == 0)
{
lean_dec(v_i_1849_);
return v___x_1852_;
}
else
{
lean_object* v_k_x27_1853_; uint8_t v___x_1854_; 
v_k_x27_1853_ = lean_array_fget_borrowed(v_keys_1848_, v_i_1849_);
v___x_1854_ = l_Lean_instBEqExtraModUse_beq(v_k_1850_, v_k_x27_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_unsigned_to_nat(1u);
v___x_1856_ = lean_nat_add(v_i_1849_, v___x_1855_);
lean_dec(v_i_1849_);
v_i_1849_ = v___x_1856_;
goto _start;
}
else
{
lean_dec(v_i_1849_);
return v___x_1854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg___boxed(lean_object* v_keys_1858_, lean_object* v_i_1859_, lean_object* v_k_1860_){
_start:
{
uint8_t v_res_1861_; lean_object* v_r_1862_; 
v_res_1861_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_1858_, v_i_1859_, v_k_1860_);
lean_dec_ref(v_k_1860_);
lean_dec_ref(v_keys_1858_);
v_r_1862_ = lean_box(v_res_1861_);
return v_r_1862_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(lean_object* v_x_1863_, size_t v_x_1864_, lean_object* v_x_1865_){
_start:
{
if (lean_obj_tag(v_x_1863_) == 0)
{
lean_object* v_es_1866_; lean_object* v___x_1867_; size_t v___x_1868_; size_t v___x_1869_; lean_object* v_j_1870_; lean_object* v___x_1871_; 
v_es_1866_ = lean_ctor_get(v_x_1863_, 0);
v___x_1867_ = lean_box(2);
v___x_1868_ = ((size_t)31ULL);
v___x_1869_ = lean_usize_land(v_x_1864_, v___x_1868_);
v_j_1870_ = lean_usize_to_nat(v___x_1869_);
v___x_1871_ = lean_array_get_borrowed(v___x_1867_, v_es_1866_, v_j_1870_);
lean_dec(v_j_1870_);
switch(lean_obj_tag(v___x_1871_))
{
case 0:
{
lean_object* v_key_1872_; uint8_t v___x_1873_; 
v_key_1872_ = lean_ctor_get(v___x_1871_, 0);
v___x_1873_ = l_Lean_instBEqExtraModUse_beq(v_x_1865_, v_key_1872_);
return v___x_1873_;
}
case 1:
{
lean_object* v_node_1874_; size_t v___x_1875_; size_t v___x_1876_; 
v_node_1874_ = lean_ctor_get(v___x_1871_, 0);
v___x_1875_ = ((size_t)5ULL);
v___x_1876_ = lean_usize_shift_right(v_x_1864_, v___x_1875_);
v_x_1863_ = v_node_1874_;
v_x_1864_ = v___x_1876_;
goto _start;
}
default: 
{
uint8_t v___x_1878_; 
v___x_1878_ = 0;
return v___x_1878_;
}
}
}
else
{
lean_object* v_ks_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v_ks_1879_ = lean_ctor_get(v_x_1863_, 0);
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_ks_1879_, v___x_1880_, v_x_1865_);
return v___x_1881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___boxed(lean_object* v_x_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
size_t v_x_23540__boxed_1885_; uint8_t v_res_1886_; lean_object* v_r_1887_; 
v_x_23540__boxed_1885_ = lean_unbox_usize(v_x_1883_);
lean_dec(v_x_1883_);
v_res_1886_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_1882_, v_x_23540__boxed_1885_, v_x_1884_);
lean_dec_ref(v_x_1884_);
lean_dec_ref(v_x_1882_);
v_r_1887_ = lean_box(v_res_1886_);
return v_r_1887_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
uint64_t v___x_1890_; size_t v___x_1891_; uint8_t v___x_1892_; 
v___x_1890_ = l_Lean_instHashableExtraModUse_hash(v_x_1889_);
v___x_1891_ = lean_uint64_to_usize(v___x_1890_);
v___x_1892_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_1888_, v___x_1891_, v_x_1889_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg___boxed(lean_object* v_x_1893_, lean_object* v_x_1894_){
_start:
{
uint8_t v_res_1895_; lean_object* v_r_1896_; 
v_res_1895_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_1893_, v_x_1894_);
lean_dec_ref(v_x_1894_);
lean_dec_ref(v_x_1893_);
v_r_1896_ = lean_box(v_res_1895_);
return v_r_1896_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1));
v___x_1900_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0));
v___x_1901_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1900_, v___x_1899_);
return v___x_1901_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5));
v___x_1907_ = l_Lean_stringToMessageData(v___x_1906_);
return v___x_1907_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7));
v___x_1910_ = l_Lean_stringToMessageData(v___x_1909_);
return v___x_1910_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9(void){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1912_ = l_Lean_stringToMessageData(v___x_1911_);
return v___x_1912_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10(void){
_start:
{
lean_object* v_cls_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v_cls_1913_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4));
v___x_1914_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
v___x_1915_ = l_Lean_Name_append(v___x_1914_, v_cls_1913_);
return v___x_1915_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11));
v___x_1918_ = l_Lean_stringToMessageData(v___x_1917_);
return v___x_1918_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13));
v___x_1921_ = l_Lean_stringToMessageData(v___x_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(lean_object* v_mod_1926_, uint8_t v_isMeta_1927_, lean_object* v_hint_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; lean_object* v_env_1933_; uint8_t v_isExporting_1934_; lean_object* v___x_1935_; lean_object* v_env_1936_; lean_object* v___x_1937_; lean_object* v_entry_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___y_1943_; lean_object* v___x_1969_; uint8_t v___x_1970_; uint8_t v___x_1971_; 
v___x_1932_ = lean_st_ref_get(v___y_1930_);
v_env_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc_ref(v_env_1933_);
lean_dec(v___x_1932_);
v_isExporting_1934_ = lean_ctor_get_uint8(v_env_1933_, sizeof(void*)*8);
lean_dec_ref(v_env_1933_);
v___x_1935_ = lean_st_ref_get(v___y_1930_);
v_env_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc_ref(v_env_1936_);
lean_dec(v___x_1935_);
v___x_1937_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2);
lean_inc(v_mod_1926_);
v_entry_1938_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1938_, 0, v_mod_1926_);
lean_ctor_set_uint8(v_entry_1938_, sizeof(void*)*1, v_isExporting_1934_);
lean_ctor_set_uint8(v_entry_1938_, sizeof(void*)*1 + 1, v_isMeta_1927_);
v___x_1939_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1940_ = lean_box(1);
v___x_1941_ = lean_box(0);
v___x_1969_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1937_, v___x_1939_, v_env_1936_, v___x_1940_, v___x_1941_);
v___x_1970_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v___x_1969_, v_entry_1938_);
lean_dec(v___x_1969_);
v___x_1971_ = lean_bool_not(v___x_1970_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_dec_ref_known(v_entry_1938_, 1);
lean_dec(v_hint_1928_);
lean_dec(v_mod_1926_);
v___x_1972_ = lean_box(0);
v___x_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
return v___x_1973_;
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v_scopes_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v_opts_1980_; uint8_t v_hasTrace_1981_; 
v___x_1974_ = l_Lean_inheritedTraceOptions;
v___x_1975_ = lean_st_ref_get(v___x_1974_);
v___x_1976_ = lean_st_ref_get(v___y_1930_);
v_scopes_1977_ = lean_ctor_get(v___x_1976_, 2);
lean_inc(v_scopes_1977_);
lean_dec(v___x_1976_);
v___x_1978_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1979_ = l_List_head_x21___redArg(v___x_1978_, v_scopes_1977_);
lean_dec(v_scopes_1977_);
v_opts_1980_ = lean_ctor_get(v___x_1979_, 1);
lean_inc_ref(v_opts_1980_);
lean_dec(v___x_1979_);
v_hasTrace_1981_ = lean_ctor_get_uint8(v_opts_1980_, sizeof(void*)*1);
if (v_hasTrace_1981_ == 0)
{
lean_dec_ref(v_opts_1980_);
lean_dec(v___x_1975_);
lean_dec(v_hint_1928_);
lean_dec(v_mod_1926_);
v___y_1943_ = v___y_1930_;
goto v___jp_1942_;
}
else
{
lean_object* v_cls_1982_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v_cls_1982_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4));
v___x_2002_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10);
v___x_2003_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1975_, v_opts_1980_, v___x_2002_);
lean_dec_ref(v_opts_1980_);
lean_dec(v___x_1975_);
if (v___x_2003_ == 0)
{
lean_dec(v_hint_1928_);
lean_dec(v_mod_1926_);
v___y_1943_ = v___y_1930_;
goto v___jp_1942_;
}
else
{
lean_object* v___x_2004_; lean_object* v___y_2006_; 
v___x_2004_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12);
if (v_isExporting_1934_ == 0)
{
lean_object* v___x_2013_; 
v___x_2013_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__17));
v___y_2006_ = v___x_2013_;
goto v___jp_2005_;
}
else
{
lean_object* v___x_2014_; 
v___x_2014_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__18));
v___y_2006_ = v___x_2014_;
goto v___jp_2005_;
}
v___jp_2005_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_inc_ref(v___y_2006_);
v___x_2007_ = l_Lean_stringToMessageData(v___y_2006_);
v___x_2008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2004_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14);
v___x_2010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2008_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
if (v_isMeta_1927_ == 0)
{
lean_object* v___x_2011_; 
v___x_2011_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15));
v___y_1989_ = v___x_2010_;
v___y_1990_ = v___x_2011_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2012_; 
v___x_2012_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16));
v___y_1989_ = v___x_2010_;
v___y_1990_ = v___x_2012_;
goto v___jp_1988_;
}
}
}
v___jp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___y_1984_);
lean_ctor_set(v___x_1986_, 1, v___y_1985_);
v___x_1987_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_1982_, v___x_1986_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_dec_ref_known(v___x_1987_, 1);
v___y_1943_ = v___y_1930_;
goto v___jp_1942_;
}
else
{
lean_dec_ref_known(v_entry_1938_, 1);
return v___x_1987_;
}
}
v___jp_1988_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
lean_inc_ref(v___y_1990_);
v___x_1991_ = l_Lean_stringToMessageData(v___y_1990_);
v___x_1992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___y_1989_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6);
v___x_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = l_Lean_MessageData_ofName(v_mod_1926_);
v___x_1996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1994_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = l_Lean_Name_isAnonymous(v_hint_1928_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8);
v___x_1999_ = l_Lean_MessageData_ofName(v_hint_1928_);
v___x_2000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1998_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
v___y_1984_ = v___x_1996_;
v___y_1985_ = v___x_2000_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2001_; 
lean_dec(v_hint_1928_);
v___x_2001_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9);
v___y_1984_ = v___x_1996_;
v___y_1985_ = v___x_2001_;
goto v___jp_1983_;
}
}
}
}
v___jp_1942_:
{
lean_object* v___x_1944_; lean_object* v_toEnvExtension_1945_; lean_object* v_env_1946_; lean_object* v_messages_1947_; lean_object* v_scopes_1948_; lean_object* v_usedQuotCtxts_1949_; lean_object* v_nextMacroScope_1950_; lean_object* v_maxRecDepth_1951_; lean_object* v_ngen_1952_; lean_object* v_auxDeclNGen_1953_; lean_object* v_infoState_1954_; lean_object* v_traceState_1955_; lean_object* v_snapshotTasks_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1968_; 
v___x_1944_ = lean_st_ref_take(v___y_1943_);
v_toEnvExtension_1945_ = lean_ctor_get(v___x_1939_, 0);
v_env_1946_ = lean_ctor_get(v___x_1944_, 0);
v_messages_1947_ = lean_ctor_get(v___x_1944_, 1);
v_scopes_1948_ = lean_ctor_get(v___x_1944_, 2);
v_usedQuotCtxts_1949_ = lean_ctor_get(v___x_1944_, 3);
v_nextMacroScope_1950_ = lean_ctor_get(v___x_1944_, 4);
v_maxRecDepth_1951_ = lean_ctor_get(v___x_1944_, 5);
v_ngen_1952_ = lean_ctor_get(v___x_1944_, 6);
v_auxDeclNGen_1953_ = lean_ctor_get(v___x_1944_, 7);
v_infoState_1954_ = lean_ctor_get(v___x_1944_, 8);
v_traceState_1955_ = lean_ctor_get(v___x_1944_, 9);
v_snapshotTasks_1956_ = lean_ctor_get(v___x_1944_, 10);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1958_ = v___x_1944_;
v_isShared_1959_ = v_isSharedCheck_1968_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_snapshotTasks_1956_);
lean_inc(v_traceState_1955_);
lean_inc(v_infoState_1954_);
lean_inc(v_auxDeclNGen_1953_);
lean_inc(v_ngen_1952_);
lean_inc(v_maxRecDepth_1951_);
lean_inc(v_nextMacroScope_1950_);
lean_inc(v_usedQuotCtxts_1949_);
lean_inc(v_scopes_1948_);
lean_inc(v_messages_1947_);
lean_inc(v_env_1946_);
lean_dec(v___x_1944_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1968_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v_asyncMode_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; 
v_asyncMode_1960_ = lean_ctor_get(v_toEnvExtension_1945_, 2);
v___x_1961_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1939_, v_env_1946_, v_entry_1938_, v_asyncMode_1960_, v___x_1941_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1961_);
v___x_1963_ = v___x_1958_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_messages_1947_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_scopes_1948_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v_usedQuotCtxts_1949_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v_nextMacroScope_1950_);
lean_ctor_set(v_reuseFailAlloc_1967_, 5, v_maxRecDepth_1951_);
lean_ctor_set(v_reuseFailAlloc_1967_, 6, v_ngen_1952_);
lean_ctor_set(v_reuseFailAlloc_1967_, 7, v_auxDeclNGen_1953_);
lean_ctor_set(v_reuseFailAlloc_1967_, 8, v_infoState_1954_);
lean_ctor_set(v_reuseFailAlloc_1967_, 9, v_traceState_1955_);
lean_ctor_set(v_reuseFailAlloc_1967_, 10, v_snapshotTasks_1956_);
v___x_1963_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1964_ = lean_st_ref_set(v___y_1943_, v___x_1963_);
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___boxed(lean_object* v_mod_2015_, lean_object* v_isMeta_2016_, lean_object* v_hint_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
uint8_t v_isMeta_boxed_2021_; lean_object* v_res_2022_; 
v_isMeta_boxed_2021_ = lean_unbox(v_isMeta_2016_);
v_res_2022_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_mod_2015_, v_isMeta_boxed_2021_, v_hint_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(lean_object* v___x_2023_, lean_object* v_declName_2024_, lean_object* v_as_2025_, size_t v_sz_2026_, size_t v_i_2027_, lean_object* v_b_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
uint8_t v___x_2032_; 
v___x_2032_ = lean_usize_dec_lt(v_i_2027_, v_sz_2026_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; 
lean_dec(v_declName_2024_);
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v_b_2028_);
return v___x_2033_;
}
else
{
lean_object* v___x_2034_; lean_object* v_modules_2035_; lean_object* v___x_2036_; lean_object* v_a_2037_; lean_object* v___x_2038_; lean_object* v_toImport_2039_; lean_object* v_module_2040_; uint8_t v___x_2041_; lean_object* v___x_2042_; 
v___x_2034_ = l_Lean_Environment_header(v___x_2023_);
v_modules_2035_ = lean_ctor_get(v___x_2034_, 3);
lean_inc_ref(v_modules_2035_);
lean_dec_ref(v___x_2034_);
v___x_2036_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2037_ = lean_array_uget_borrowed(v_as_2025_, v_i_2027_);
v___x_2038_ = lean_array_get(v___x_2036_, v_modules_2035_, v_a_2037_);
lean_dec_ref(v_modules_2035_);
v_toImport_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc_ref(v_toImport_2039_);
lean_dec(v___x_2038_);
v_module_2040_ = lean_ctor_get(v_toImport_2039_, 0);
lean_inc(v_module_2040_);
lean_dec_ref(v_toImport_2039_);
v___x_2041_ = 0;
lean_inc(v_declName_2024_);
v___x_2042_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_module_2040_, v___x_2041_, v_declName_2024_, v___y_2029_, v___y_2030_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v___x_2043_; size_t v___x_2044_; size_t v___x_2045_; 
lean_dec_ref_known(v___x_2042_, 1);
v___x_2043_ = lean_box(0);
v___x_2044_ = ((size_t)1ULL);
v___x_2045_ = lean_usize_add(v_i_2027_, v___x_2044_);
v_i_2027_ = v___x_2045_;
v_b_2028_ = v___x_2043_;
goto _start;
}
else
{
lean_dec(v_declName_2024_);
return v___x_2042_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7___boxed(lean_object* v___x_2047_, lean_object* v_declName_2048_, lean_object* v_as_2049_, lean_object* v_sz_2050_, lean_object* v_i_2051_, lean_object* v_b_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
size_t v_sz_boxed_2056_; size_t v_i_boxed_2057_; lean_object* v_res_2058_; 
v_sz_boxed_2056_ = lean_unbox_usize(v_sz_2050_);
lean_dec(v_sz_2050_);
v_i_boxed_2057_ = lean_unbox_usize(v_i_2051_);
lean_dec(v_i_2051_);
v_res_2058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v___x_2047_, v_declName_2048_, v_as_2049_, v_sz_boxed_2056_, v_i_boxed_2057_, v_b_2052_, v___y_2053_, v___y_2054_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec_ref(v_as_2049_);
lean_dec_ref(v___x_2047_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(lean_object* v_a_2059_, lean_object* v_x_2060_){
_start:
{
if (lean_obj_tag(v_x_2060_) == 0)
{
lean_object* v___x_2061_; 
v___x_2061_ = lean_box(0);
return v___x_2061_;
}
else
{
lean_object* v_key_2062_; lean_object* v_value_2063_; lean_object* v_tail_2064_; uint8_t v___x_2065_; 
v_key_2062_ = lean_ctor_get(v_x_2060_, 0);
v_value_2063_ = lean_ctor_get(v_x_2060_, 1);
v_tail_2064_ = lean_ctor_get(v_x_2060_, 2);
v___x_2065_ = lean_name_eq(v_key_2062_, v_a_2059_);
if (v___x_2065_ == 0)
{
v_x_2060_ = v_tail_2064_;
goto _start;
}
else
{
lean_object* v___x_2067_; 
lean_inc(v_value_2063_);
v___x_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2067_, 0, v_value_2063_);
return v___x_2067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg___boxed(lean_object* v_a_2068_, lean_object* v_x_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_2068_, v_x_2069_);
lean_dec(v_x_2069_);
lean_dec(v_a_2068_);
return v_res_2070_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2071_; uint64_t v___x_2072_; 
v___x_2071_ = lean_unsigned_to_nat(1723u);
v___x_2072_ = lean_uint64_of_nat(v___x_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(lean_object* v_m_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_buckets_2075_; lean_object* v___x_2076_; uint64_t v___y_2078_; 
v_buckets_2075_ = lean_ctor_get(v_m_2073_, 1);
v___x_2076_ = lean_array_get_size(v_buckets_2075_);
if (lean_obj_tag(v_a_2074_) == 0)
{
uint64_t v___x_2092_; 
v___x_2092_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0);
v___y_2078_ = v___x_2092_;
goto v___jp_2077_;
}
else
{
uint64_t v_hash_2093_; 
v_hash_2093_ = lean_ctor_get_uint64(v_a_2074_, sizeof(void*)*2);
v___y_2078_ = v_hash_2093_;
goto v___jp_2077_;
}
v___jp_2077_:
{
uint64_t v___x_2079_; uint64_t v___x_2080_; uint64_t v_fold_2081_; uint64_t v___x_2082_; uint64_t v___x_2083_; uint64_t v___x_2084_; size_t v___x_2085_; size_t v___x_2086_; size_t v___x_2087_; size_t v___x_2088_; size_t v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2079_ = 32ULL;
v___x_2080_ = lean_uint64_shift_right(v___y_2078_, v___x_2079_);
v_fold_2081_ = lean_uint64_xor(v___y_2078_, v___x_2080_);
v___x_2082_ = 16ULL;
v___x_2083_ = lean_uint64_shift_right(v_fold_2081_, v___x_2082_);
v___x_2084_ = lean_uint64_xor(v_fold_2081_, v___x_2083_);
v___x_2085_ = lean_uint64_to_usize(v___x_2084_);
v___x_2086_ = lean_usize_of_nat(v___x_2076_);
v___x_2087_ = ((size_t)1ULL);
v___x_2088_ = lean_usize_sub(v___x_2086_, v___x_2087_);
v___x_2089_ = lean_usize_land(v___x_2085_, v___x_2088_);
v___x_2090_ = lean_array_uget_borrowed(v_buckets_2075_, v___x_2089_);
v___x_2091_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_2074_, v___x_2090_);
return v___x_2091_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_m_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v_m_2094_, v_a_2095_);
lean_dec(v_a_2095_);
lean_dec_ref(v_m_2094_);
return v_res_2096_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2099_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1));
v___x_2100_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0));
v___x_2101_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2100_, v___x_2099_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(lean_object* v_declName_2104_, uint8_t v_isMeta_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2109_; lean_object* v_env_2113_; lean_object* v___y_2115_; lean_object* v___x_2128_; 
v___x_2109_ = lean_st_ref_get(v___y_2107_);
v_env_2113_ = lean_ctor_get(v___x_2109_, 0);
lean_inc_ref(v_env_2113_);
lean_dec(v___x_2109_);
v___x_2128_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2113_, v_declName_2104_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_dec_ref(v_env_2113_);
lean_dec(v_declName_2104_);
goto v___jp_2110_;
}
else
{
lean_object* v_val_2129_; lean_object* v___x_2130_; lean_object* v_modules_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
v_val_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_val_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v___x_2130_ = l_Lean_Environment_header(v_env_2113_);
v_modules_2131_ = lean_ctor_get(v___x_2130_, 3);
lean_inc_ref(v_modules_2131_);
lean_dec_ref(v___x_2130_);
v___x_2132_ = lean_array_get_size(v_modules_2131_);
v___x_2133_ = lean_nat_dec_lt(v_val_2129_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_dec_ref(v_modules_2131_);
lean_dec(v_val_2129_);
lean_dec_ref(v_env_2113_);
lean_dec(v_declName_2104_);
goto v___jp_2110_;
}
else
{
lean_object* v___x_2134_; lean_object* v_env_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___y_2139_; 
v___x_2134_ = lean_st_ref_get(v___y_2107_);
v_env_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc_ref(v_env_2135_);
lean_dec(v___x_2134_);
v___x_2136_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2);
v___x_2137_ = lean_array_fget(v_modules_2131_, v_val_2129_);
lean_dec(v_val_2129_);
lean_dec_ref(v_modules_2131_);
if (v_isMeta_2105_ == 0)
{
lean_dec_ref(v_env_2135_);
v___y_2139_ = v_isMeta_2105_;
goto v___jp_2138_;
}
else
{
uint8_t v___x_2150_; uint8_t v___x_2151_; 
lean_inc(v_declName_2104_);
v___x_2150_ = l_Lean_isMarkedMeta(v_env_2135_, v_declName_2104_);
v___x_2151_ = lean_bool_not(v___x_2150_);
v___y_2139_ = v___x_2151_;
goto v___jp_2138_;
}
v___jp_2138_:
{
lean_object* v_toImport_2140_; lean_object* v_module_2141_; lean_object* v___x_2142_; 
v_toImport_2140_ = lean_ctor_get(v___x_2137_, 0);
lean_inc_ref(v_toImport_2140_);
lean_dec(v___x_2137_);
v_module_2141_ = lean_ctor_get(v_toImport_2140_, 0);
lean_inc(v_module_2141_);
lean_dec_ref(v_toImport_2140_);
lean_inc(v_declName_2104_);
v___x_2142_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_module_2141_, v___y_2139_, v_declName_2104_, v___y_2106_, v___y_2107_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
lean_dec_ref_known(v___x_2142_, 1);
v___x_2143_ = l_Lean_indirectModUseExt;
v___x_2144_ = lean_box(1);
v___x_2145_ = lean_box(0);
lean_inc_ref(v_env_2113_);
v___x_2146_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2136_, v___x_2143_, v_env_2113_, v___x_2144_, v___x_2145_);
v___x_2147_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v___x_2146_, v_declName_2104_);
lean_dec(v___x_2146_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v___x_2148_; 
v___x_2148_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__3));
v___y_2115_ = v___x_2148_;
goto v___jp_2114_;
}
else
{
lean_object* v_val_2149_; 
v_val_2149_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_val_2149_);
lean_dec_ref_known(v___x_2147_, 1);
v___y_2115_ = v_val_2149_;
goto v___jp_2114_;
}
}
else
{
lean_dec_ref(v_env_2113_);
lean_dec(v_declName_2104_);
return v___x_2142_;
}
}
}
}
v___jp_2110_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_box(0);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
return v___x_2112_;
}
v___jp_2114_:
{
lean_object* v___x_2116_; size_t v_sz_2117_; size_t v___x_2118_; lean_object* v___x_2119_; 
v___x_2116_ = lean_box(0);
v_sz_2117_ = lean_array_size(v___y_2115_);
v___x_2118_ = ((size_t)0ULL);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v_env_2113_, v_declName_2104_, v___y_2115_, v_sz_2117_, v___x_2118_, v___x_2116_, v___y_2106_, v___y_2107_);
lean_dec_ref(v___y_2115_);
lean_dec_ref(v_env_2113_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2126_ == 0)
{
lean_object* v_unused_2127_; 
v_unused_2127_ = lean_ctor_get(v___x_2119_, 0);
lean_dec(v_unused_2127_);
v___x_2121_ = v___x_2119_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_dec(v___x_2119_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2116_);
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2116_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
else
{
return v___x_2119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___boxed(lean_object* v_declName_2152_, lean_object* v_isMeta_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
uint8_t v_isMeta_boxed_2157_; lean_object* v_res_2158_; 
v_isMeta_boxed_2157_ = lean_unbox(v_isMeta_2153_);
v_res_2158_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_declName_2152_, v_isMeta_boxed_2157_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(lean_object* v_as_x27_2159_, lean_object* v_b_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
if (lean_obj_tag(v_as_x27_2159_) == 0)
{
lean_object* v___x_2164_; 
v___x_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2164_, 0, v_b_2160_);
return v___x_2164_;
}
else
{
lean_object* v_head_2165_; lean_object* v_tail_2166_; uint8_t v___x_2167_; lean_object* v___x_2168_; 
v_head_2165_ = lean_ctor_get(v_as_x27_2159_, 0);
v_tail_2166_ = lean_ctor_get(v_as_x27_2159_, 1);
v___x_2167_ = 1;
lean_inc(v_head_2165_);
v___x_2168_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_head_2165_, v___x_2167_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v___x_2169_; 
lean_dec_ref_known(v___x_2168_, 1);
v___x_2169_ = lean_box(0);
v_as_x27_2159_ = v_tail_2166_;
v_b_2160_ = v___x_2169_;
goto _start;
}
else
{
return v___x_2168_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2171_, lean_object* v_b_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_2171_, v_b_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v_as_x27_2171_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(lean_object* v_x_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___x_2182_; lean_object* v_env_2183_; lean_object* v___x_2184_; lean_object* v_scopes_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v_opts_2188_; lean_object* v___x_2189_; 
v___x_2182_ = lean_st_ref_get(v___y_2180_);
v_env_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc_ref(v_env_2183_);
lean_dec(v___x_2182_);
v___x_2184_ = lean_st_ref_get(v___y_2180_);
v_scopes_2185_ = lean_ctor_get(v___x_2184_, 2);
lean_inc(v_scopes_2185_);
lean_dec(v___x_2184_);
v___x_2186_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2187_ = l_List_head_x21___redArg(v___x_2186_, v_scopes_2185_);
lean_dec(v_scopes_2185_);
v_opts_2188_ = lean_ctor_get(v___x_2187_, 1);
lean_inc_ref(v_opts_2188_);
lean_dec(v___x_2187_);
v___x_2189_ = l_Lean_Elab_Command_getScope___redArg(v___y_2180_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v_currNamespace_2191_; lean_object* v___x_2192_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v_currNamespace_2191_ = lean_ctor_get(v_a_2190_, 2);
lean_inc(v_currNamespace_2191_);
lean_dec(v_a_2190_);
v___x_2192_ = l_Lean_Elab_Command_getScope___redArg(v___y_2180_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v_openDecls_2194_; lean_object* v___x_2195_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v_openDecls_2194_ = lean_ctor_get(v_a_2193_, 3);
lean_inc(v_openDecls_2194_);
lean_dec(v_a_2193_);
v___x_2195_ = l_Lean_Elab_Command_getRef___redArg(v___y_2179_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2197_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
v___x_2197_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2179_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v_currRecDepth_2199_; lean_object* v_quotContext_x3f_2200_; lean_object* v___f_2201_; lean_object* v___f_2202_; lean_object* v___f_2203_; lean_object* v___f_2204_; lean_object* v___f_2205_; lean_object* v_methods_2206_; lean_object* v_a_2208_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2197_, 1);
v_currRecDepth_2199_ = lean_ctor_get(v___y_2179_, 2);
v_quotContext_x3f_2200_ = lean_ctor_get(v___y_2179_, 5);
lean_inc_ref_n(v_env_2183_, 3);
v___f_2201_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2201_, 0, v_env_2183_);
v___f_2202_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2202_, 0, v_env_2183_);
lean_inc_n(v_currNamespace_2191_, 2);
v___f_2203_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2203_, 0, v_currNamespace_2191_);
lean_inc(v_openDecls_2194_);
v___f_2204_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2204_, 0, v_env_2183_);
lean_closure_set(v___f_2204_, 1, v_currNamespace_2191_);
lean_closure_set(v___f_2204_, 2, v_openDecls_2194_);
v___f_2205_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2205_, 0, v_env_2183_);
lean_closure_set(v___f_2205_, 1, v_opts_2188_);
lean_closure_set(v___f_2205_, 2, v_currNamespace_2191_);
lean_closure_set(v___f_2205_, 3, v_openDecls_2194_);
v_methods_2206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2206_, 0, v___f_2202_);
lean_ctor_set(v_methods_2206_, 1, v___f_2203_);
lean_ctor_set(v_methods_2206_, 2, v___f_2201_);
lean_ctor_set(v_methods_2206_, 3, v___f_2204_);
lean_ctor_set(v_methods_2206_, 4, v___f_2205_);
if (lean_obj_tag(v_quotContext_x3f_2200_) == 0)
{
lean_object* v___x_2280_; lean_object* v_a_2281_; 
v___x_2280_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2180_);
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref(v___x_2280_);
v_a_2208_ = v_a_2281_;
goto v___jp_2207_;
}
else
{
lean_object* v_val_2282_; 
v_val_2282_ = lean_ctor_get(v_quotContext_x3f_2200_, 0);
lean_inc(v_val_2282_);
v_a_2208_ = v_val_2282_;
goto v___jp_2207_;
}
v___jp_2207_:
{
lean_object* v___x_2209_; lean_object* v_maxRecDepth_2210_; lean_object* v___x_2211_; lean_object* v_nextMacroScope_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2209_ = lean_st_ref_get(v___y_2180_);
v_maxRecDepth_2210_ = lean_ctor_get(v___x_2209_, 5);
lean_inc(v_maxRecDepth_2210_);
lean_dec(v___x_2209_);
v___x_2211_ = lean_st_ref_get(v___y_2180_);
v_nextMacroScope_2212_ = lean_ctor_get(v___x_2211_, 4);
lean_inc(v_nextMacroScope_2212_);
lean_dec(v___x_2211_);
lean_inc(v_currRecDepth_2199_);
v___x_2213_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2213_, 0, v_methods_2206_);
lean_ctor_set(v___x_2213_, 1, v_a_2208_);
lean_ctor_set(v___x_2213_, 2, v_a_2198_);
lean_ctor_set(v___x_2213_, 3, v_currRecDepth_2199_);
lean_ctor_set(v___x_2213_, 4, v_maxRecDepth_2210_);
lean_ctor_set(v___x_2213_, 5, v_a_2196_);
v___x_2214_ = lean_box(0);
v___x_2215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2215_, 0, v_nextMacroScope_2212_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
lean_ctor_set(v___x_2215_, 2, v___x_2214_);
v___x_2216_ = lean_apply_2(v_x_2178_, v___x_2213_, v___x_2215_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v_a_2218_; lean_object* v_macroScope_2219_; lean_object* v_traceMsgs_2220_; lean_object* v_expandedMacroDecls_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 1);
lean_inc(v_a_2217_);
v_a_2218_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2216_, 2);
v_macroScope_2219_ = lean_ctor_get(v_a_2217_, 0);
lean_inc(v_macroScope_2219_);
v_traceMsgs_2220_ = lean_ctor_get(v_a_2217_, 1);
lean_inc(v_traceMsgs_2220_);
v_expandedMacroDecls_2221_ = lean_ctor_get(v_a_2217_, 2);
lean_inc(v_expandedMacroDecls_2221_);
lean_dec(v_a_2217_);
v___x_2222_ = lean_box(0);
v___x_2223_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_expandedMacroDecls_2221_, v___x_2222_, v___y_2179_, v___y_2180_);
lean_dec(v_expandedMacroDecls_2221_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v___x_2224_; lean_object* v_env_2225_; lean_object* v_messages_2226_; lean_object* v_scopes_2227_; lean_object* v_usedQuotCtxts_2228_; lean_object* v_maxRecDepth_2229_; lean_object* v_ngen_2230_; lean_object* v_auxDeclNGen_2231_; lean_object* v_infoState_2232_; lean_object* v_traceState_2233_; lean_object* v_snapshotTasks_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2260_; 
lean_dec_ref_known(v___x_2223_, 1);
v___x_2224_ = lean_st_ref_take(v___y_2180_);
v_env_2225_ = lean_ctor_get(v___x_2224_, 0);
v_messages_2226_ = lean_ctor_get(v___x_2224_, 1);
v_scopes_2227_ = lean_ctor_get(v___x_2224_, 2);
v_usedQuotCtxts_2228_ = lean_ctor_get(v___x_2224_, 3);
v_maxRecDepth_2229_ = lean_ctor_get(v___x_2224_, 5);
v_ngen_2230_ = lean_ctor_get(v___x_2224_, 6);
v_auxDeclNGen_2231_ = lean_ctor_get(v___x_2224_, 7);
v_infoState_2232_ = lean_ctor_get(v___x_2224_, 8);
v_traceState_2233_ = lean_ctor_get(v___x_2224_, 9);
v_snapshotTasks_2234_ = lean_ctor_get(v___x_2224_, 10);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2260_ == 0)
{
lean_object* v_unused_2261_; 
v_unused_2261_ = lean_ctor_get(v___x_2224_, 4);
lean_dec(v_unused_2261_);
v___x_2236_ = v___x_2224_;
v_isShared_2237_ = v_isSharedCheck_2260_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_snapshotTasks_2234_);
lean_inc(v_traceState_2233_);
lean_inc(v_infoState_2232_);
lean_inc(v_auxDeclNGen_2231_);
lean_inc(v_ngen_2230_);
lean_inc(v_maxRecDepth_2229_);
lean_inc(v_usedQuotCtxts_2228_);
lean_inc(v_scopes_2227_);
lean_inc(v_messages_2226_);
lean_inc(v_env_2225_);
lean_dec(v___x_2224_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2260_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 4, v_macroScope_2219_);
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_env_2225_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_messages_2226_);
lean_ctor_set(v_reuseFailAlloc_2259_, 2, v_scopes_2227_);
lean_ctor_set(v_reuseFailAlloc_2259_, 3, v_usedQuotCtxts_2228_);
lean_ctor_set(v_reuseFailAlloc_2259_, 4, v_macroScope_2219_);
lean_ctor_set(v_reuseFailAlloc_2259_, 5, v_maxRecDepth_2229_);
lean_ctor_set(v_reuseFailAlloc_2259_, 6, v_ngen_2230_);
lean_ctor_set(v_reuseFailAlloc_2259_, 7, v_auxDeclNGen_2231_);
lean_ctor_set(v_reuseFailAlloc_2259_, 8, v_infoState_2232_);
lean_ctor_set(v_reuseFailAlloc_2259_, 9, v_traceState_2233_);
lean_ctor_set(v_reuseFailAlloc_2259_, 10, v_snapshotTasks_2234_);
v___x_2239_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2240_ = lean_st_ref_set(v___y_2180_, v___x_2239_);
v___x_2241_ = l_List_reverse___redArg(v_traceMsgs_2220_);
v___x_2242_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v___x_2241_, v___y_2179_, v___y_2180_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2249_ == 0)
{
lean_object* v_unused_2250_; 
v_unused_2250_ = lean_ctor_get(v___x_2242_, 0);
lean_dec(v_unused_2250_);
v___x_2244_ = v___x_2242_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_dec(v___x_2242_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v_a_2218_);
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2218_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v_a_2218_);
v_a_2251_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2242_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2242_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v_traceMsgs_2220_);
lean_dec(v_macroScope_2219_);
lean_dec(v_a_2218_);
v_a_2262_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2223_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2223_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
lean_object* v_a_2270_; 
v_a_2270_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2216_, 2);
if (lean_obj_tag(v_a_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v_a_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_a_2271_ = lean_ctor_get(v_a_2270_, 0);
lean_inc(v_a_2271_);
v_a_2272_ = lean_ctor_get(v_a_2270_, 1);
lean_inc_ref(v_a_2272_);
lean_dec_ref_known(v_a_2270_, 2);
v___x_2273_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0));
v___x_2274_ = lean_string_dec_eq(v_a_2272_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2275_, 0, v_a_2272_);
v___x_2276_ = l_Lean_MessageData_ofFormat(v___x_2275_);
v___x_2277_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_a_2271_, v___x_2276_, v___y_2179_, v___y_2180_);
lean_dec(v_a_2271_);
return v___x_2277_;
}
else
{
lean_object* v___x_2278_; 
lean_dec_ref(v_a_2272_);
v___x_2278_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_a_2271_);
return v___x_2278_;
}
}
else
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2279_;
}
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec(v_a_2196_);
lean_dec(v_openDecls_2194_);
lean_dec(v_currNamespace_2191_);
lean_dec_ref(v_opts_2188_);
lean_dec_ref(v_env_2183_);
lean_dec_ref(v_x_2178_);
v_a_2283_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2197_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2197_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_openDecls_2194_);
lean_dec(v_currNamespace_2191_);
lean_dec_ref(v_opts_2188_);
lean_dec_ref(v_env_2183_);
lean_dec_ref(v_x_2178_);
v_a_2291_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2195_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2195_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_currNamespace_2191_);
lean_dec_ref(v_opts_2188_);
lean_dec_ref(v_env_2183_);
lean_dec_ref(v_x_2178_);
v_a_2299_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2192_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2192_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref(v_opts_2188_);
lean_dec_ref(v_env_2183_);
lean_dec_ref(v_x_2178_);
v_a_2307_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2189_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2189_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___boxed(lean_object* v_x_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(lean_object* v_as_2320_, size_t v_i_2321_, size_t v_stop_2322_, lean_object* v_b_2323_){
_start:
{
lean_object* v___y_2325_; uint8_t v___x_2329_; 
v___x_2329_ = lean_usize_dec_eq(v_i_2321_, v_stop_2322_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
v___x_2330_ = lean_array_uget_borrowed(v_as_2320_, v_i_2321_);
lean_inc(v___x_2330_);
v___x_2331_ = l_Lean_Syntax_getKind(v___x_2330_);
v___x_2332_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
v___x_2333_ = lean_name_eq(v___x_2331_, v___x_2332_);
lean_dec(v___x_2331_);
if (v___x_2333_ == 0)
{
v___y_2325_ = v_b_2323_;
goto v___jp_2324_;
}
else
{
lean_object* v___x_2334_; 
lean_inc(v___x_2330_);
v___x_2334_ = lean_array_push(v_b_2323_, v___x_2330_);
v___y_2325_ = v___x_2334_;
goto v___jp_2324_;
}
}
else
{
return v_b_2323_;
}
v___jp_2324_:
{
size_t v___x_2326_; size_t v___x_2327_; 
v___x_2326_ = ((size_t)1ULL);
v___x_2327_ = lean_usize_add(v_i_2321_, v___x_2326_);
v_i_2321_ = v___x_2327_;
v_b_2323_ = v___y_2325_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8___boxed(lean_object* v_as_2335_, lean_object* v_i_2336_, lean_object* v_stop_2337_, lean_object* v_b_2338_){
_start:
{
size_t v_i_boxed_2339_; size_t v_stop_boxed_2340_; lean_object* v_res_2341_; 
v_i_boxed_2339_ = lean_unbox_usize(v_i_2336_);
lean_dec(v_i_2336_);
v_stop_boxed_2340_ = lean_unbox_usize(v_stop_2337_);
lean_dec(v_stop_2337_);
v_res_2341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v_as_2335_, v_i_boxed_2339_, v_stop_boxed_2340_, v_b_2338_);
lean_dec_ref(v_as_2335_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation(lean_object* v_x_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; size_t v___y_2478_; uint8_t v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; 
v___x_2415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0));
v___x_2416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1));
v___x_2417_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
lean_inc(v_x_2384_);
v___x_2418_ = l_Lean_Syntax_isOfKind(v_x_2384_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2527_; 
lean_dec(v_x_2384_);
v___x_2527_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2527_;
}
else
{
lean_object* v___x_2528_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; uint8_t v___y_2539_; size_t v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; size_t v___y_2614_; uint8_t v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; uint8_t v___y_2649_; size_t v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; uint8_t v___y_2680_; size_t v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; uint8_t v___y_2713_; size_t v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v_prio_x3f_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v_name_x3f_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v_prec_x3f_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v_attrs_x3f_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v_doc_x3f_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___x_2883_; uint8_t v___x_2884_; 
v___x_2528_ = lean_unsigned_to_nat(0u);
v___x_2883_ = l_Lean_Syntax_getArg(v_x_2384_, v___x_2528_);
v___x_2884_ = l_Lean_Syntax_isNone(v___x_2883_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; uint8_t v___x_2886_; 
v___x_2885_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2883_);
v___x_2886_ = l_Lean_Syntax_matchesNull(v___x_2883_, v___x_2885_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; 
lean_dec(v___x_2883_);
lean_dec(v_x_2384_);
v___x_2887_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2887_;
}
else
{
lean_object* v_doc_x3f_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v_doc_x3f_2888_ = l_Lean_Syntax_getArg(v___x_2883_, v___x_2528_);
lean_dec(v___x_2883_);
v___x_2889_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__15));
lean_inc(v_doc_x3f_2888_);
v___x_2890_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2888_, v___x_2889_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; 
lean_dec(v_doc_x3f_2888_);
lean_dec(v_x_2384_);
v___x_2891_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2891_;
}
else
{
lean_object* v___x_2892_; 
v___x_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2892_, 0, v_doc_x3f_2888_);
v_doc_x3f_2867_ = v___x_2892_;
v___y_2868_ = v_a_2385_;
v___y_2869_ = v_a_2386_;
goto v___jp_2866_;
}
}
}
else
{
lean_object* v___x_2893_; 
lean_dec(v___x_2883_);
v___x_2893_ = lean_box(0);
v_doc_x3f_2867_ = v___x_2893_;
v___y_2868_ = v_a_2385_;
v___y_2869_ = v_a_2386_;
goto v___jp_2866_;
}
v___jp_2529_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; size_t v_sz_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_inc_ref_n(v___y_2545_, 2);
v___x_2550_ = l_Array_append___redArg(v___y_2545_, v___y_2549_);
lean_dec_ref(v___y_2549_);
lean_inc_n(v___y_2548_, 3);
lean_inc_n(v___y_2535_, 9);
v___x_2551_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2551_, 0, v___y_2535_);
lean_ctor_set(v___x_2551_, 1, v___y_2548_);
lean_ctor_set(v___x_2551_, 2, v___x_2550_);
v___x_2552_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
v___x_2553_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
v___x_2554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___y_2535_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__8));
v___x_2556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___y_2535_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_2558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___y_2535_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = l_Nat_reprFast(v___y_2541_);
v___x_2560_ = lean_box(2);
v___x_2561_ = l_Lean_Syntax_mkNumLit(v___x_2559_, v___x_2560_);
v___x_2562_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_2563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___y_2535_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = l_Lean_Syntax_node5(v___y_2535_, v___x_2552_, v___x_2554_, v___x_2556_, v___x_2558_, v___x_2561_, v___x_2563_);
v___x_2565_ = l_Lean_Syntax_node1(v___y_2535_, v___y_2548_, v___x_2564_);
v_sz_2566_ = lean_array_size(v___y_2534_);
v___x_2567_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_2566_, v___y_2540_, v___y_2534_);
v___x_2568_ = l_Array_append___redArg(v___y_2545_, v___x_2567_);
lean_dec_ref(v___x_2567_);
v___x_2569_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2569_, 0, v___y_2535_);
lean_ctor_set(v___x_2569_, 1, v___y_2548_);
lean_ctor_set(v___x_2569_, 2, v___x_2568_);
v___x_2570_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
v___x_2571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___y_2535_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = lean_unsigned_to_nat(10u);
v___x_2573_ = lean_mk_empty_array_with_capacity(v___x_2572_);
v___x_2574_ = lean_array_push(v___x_2573_, v___y_2530_);
v___x_2575_ = lean_array_push(v___x_2574_, v___y_2538_);
lean_inc(v___y_2546_);
v___x_2576_ = lean_array_push(v___x_2575_, v___y_2546_);
v___x_2577_ = lean_array_push(v___x_2576_, v___y_2531_);
v___x_2578_ = lean_array_push(v___x_2577_, v___y_2544_);
v___x_2579_ = lean_array_push(v___x_2578_, v___x_2551_);
v___x_2580_ = lean_array_push(v___x_2579_, v___x_2565_);
v___x_2581_ = lean_array_push(v___x_2580_, v___x_2569_);
v___x_2582_ = lean_array_push(v___x_2581_, v___x_2571_);
v___x_2583_ = lean_array_push(v___x_2582_, v___y_2532_);
lean_inc(v___y_2536_);
v___x_2584_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2584_, 0, v___y_2535_);
lean_ctor_set(v___x_2584_, 1, v___y_2536_);
lean_ctor_set(v___x_2584_, 2, v___x_2583_);
v___x_2585_ = l_Lean_Elab_Command_elabSyntax(v___x_2584_, v___y_2537_, v___y_2533_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref_known(v___x_2585_, 1);
v___x_2587_ = lean_array_get_size(v___y_2542_);
v___x_2588_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__68));
v___x_2589_ = lean_nat_dec_lt(v___x_2528_, v___x_2587_);
if (v___x_2589_ == 0)
{
v___y_2473_ = v___y_2533_;
v___y_2474_ = v_a_2586_;
v___y_2475_ = v___x_2560_;
v___y_2476_ = v___x_2562_;
v___y_2477_ = v___y_2537_;
v___y_2478_ = v___y_2540_;
v___y_2479_ = v___y_2539_;
v___y_2480_ = v___y_2542_;
v___y_2481_ = v___y_2543_;
v___y_2482_ = v___y_2545_;
v___y_2483_ = v___y_2546_;
v___y_2484_ = v___y_2548_;
v___y_2485_ = v___y_2547_;
v___y_2486_ = v___x_2588_;
goto v___jp_2472_;
}
else
{
uint8_t v___x_2590_; 
v___x_2590_ = lean_nat_dec_le(v___x_2587_, v___x_2587_);
if (v___x_2590_ == 0)
{
if (v___x_2589_ == 0)
{
v___y_2473_ = v___y_2533_;
v___y_2474_ = v_a_2586_;
v___y_2475_ = v___x_2560_;
v___y_2476_ = v___x_2562_;
v___y_2477_ = v___y_2537_;
v___y_2478_ = v___y_2540_;
v___y_2479_ = v___y_2539_;
v___y_2480_ = v___y_2542_;
v___y_2481_ = v___y_2543_;
v___y_2482_ = v___y_2545_;
v___y_2483_ = v___y_2546_;
v___y_2484_ = v___y_2548_;
v___y_2485_ = v___y_2547_;
v___y_2486_ = v___x_2588_;
goto v___jp_2472_;
}
else
{
size_t v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_usize_of_nat(v___x_2587_);
v___x_2592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2542_, v___y_2540_, v___x_2591_, v___x_2588_);
v___y_2473_ = v___y_2533_;
v___y_2474_ = v_a_2586_;
v___y_2475_ = v___x_2560_;
v___y_2476_ = v___x_2562_;
v___y_2477_ = v___y_2537_;
v___y_2478_ = v___y_2540_;
v___y_2479_ = v___y_2539_;
v___y_2480_ = v___y_2542_;
v___y_2481_ = v___y_2543_;
v___y_2482_ = v___y_2545_;
v___y_2483_ = v___y_2546_;
v___y_2484_ = v___y_2548_;
v___y_2485_ = v___y_2547_;
v___y_2486_ = v___x_2592_;
goto v___jp_2472_;
}
}
else
{
size_t v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_usize_of_nat(v___x_2587_);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2542_, v___y_2540_, v___x_2593_, v___x_2588_);
v___y_2473_ = v___y_2533_;
v___y_2474_ = v_a_2586_;
v___y_2475_ = v___x_2560_;
v___y_2476_ = v___x_2562_;
v___y_2477_ = v___y_2537_;
v___y_2478_ = v___y_2540_;
v___y_2479_ = v___y_2539_;
v___y_2480_ = v___y_2542_;
v___y_2481_ = v___y_2543_;
v___y_2482_ = v___y_2545_;
v___y_2483_ = v___y_2546_;
v___y_2484_ = v___y_2548_;
v___y_2485_ = v___y_2547_;
v___y_2486_ = v___x_2594_;
goto v___jp_2472_;
}
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2542_);
v_a_2595_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2585_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2585_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
v___jp_2603_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
lean_inc_ref(v___y_2619_);
v___x_2624_ = l_Array_append___redArg(v___y_2619_, v___y_2623_);
lean_dec_ref(v___y_2623_);
lean_inc(v___y_2622_);
lean_inc(v___y_2609_);
v___x_2625_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2625_, 0, v___y_2609_);
lean_ctor_set(v___x_2625_, 1, v___y_2622_);
lean_ctor_set(v___x_2625_, 2, v___x_2624_);
if (lean_obj_tag(v___y_2612_) == 1)
{
lean_object* v_val_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v_val_2626_ = lean_ctor_get(v___y_2612_, 0);
lean_inc(v_val_2626_);
lean_dec_ref_known(v___y_2612_, 1);
v___x_2627_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
v___x_2628_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc_n(v___y_2609_, 5);
v___x_2629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___y_2609_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___x_2630_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__11));
v___x_2631_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___y_2609_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_2633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___y_2609_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_2635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___y_2609_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = l_Lean_Syntax_node5(v___y_2609_, v___x_2627_, v___x_2629_, v___x_2631_, v___x_2633_, v_val_2626_, v___x_2635_);
v___x_2637_ = l_Array_mkArray1___redArg(v___x_2636_);
v___y_2530_ = v___y_2604_;
v___y_2531_ = v___y_2605_;
v___y_2532_ = v___y_2606_;
v___y_2533_ = v___y_2607_;
v___y_2534_ = v___y_2608_;
v___y_2535_ = v___y_2609_;
v___y_2536_ = v___y_2610_;
v___y_2537_ = v___y_2611_;
v___y_2538_ = v___y_2613_;
v___y_2539_ = v___y_2615_;
v___y_2540_ = v___y_2614_;
v___y_2541_ = v___y_2616_;
v___y_2542_ = v___y_2617_;
v___y_2543_ = v___y_2618_;
v___y_2544_ = v___x_2625_;
v___y_2545_ = v___y_2619_;
v___y_2546_ = v___y_2620_;
v___y_2547_ = v___y_2621_;
v___y_2548_ = v___y_2622_;
v___y_2549_ = v___x_2637_;
goto v___jp_2529_;
}
else
{
lean_object* v___x_2638_; 
lean_dec(v___y_2612_);
v___x_2638_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2530_ = v___y_2604_;
v___y_2531_ = v___y_2605_;
v___y_2532_ = v___y_2606_;
v___y_2533_ = v___y_2607_;
v___y_2534_ = v___y_2608_;
v___y_2535_ = v___y_2609_;
v___y_2536_ = v___y_2610_;
v___y_2537_ = v___y_2611_;
v___y_2538_ = v___y_2613_;
v___y_2539_ = v___y_2615_;
v___y_2540_ = v___y_2614_;
v___y_2541_ = v___y_2616_;
v___y_2542_ = v___y_2617_;
v___y_2543_ = v___y_2618_;
v___y_2544_ = v___x_2625_;
v___y_2545_ = v___y_2619_;
v___y_2546_ = v___y_2620_;
v___y_2547_ = v___y_2621_;
v___y_2548_ = v___y_2622_;
v___y_2549_ = v___x_2638_;
goto v___jp_2529_;
}
}
v___jp_2639_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
lean_inc_ref(v___y_2655_);
v___x_2660_ = l_Array_append___redArg(v___y_2655_, v___y_2659_);
lean_dec_ref(v___y_2659_);
lean_inc(v___y_2658_);
lean_inc_n(v___y_2644_, 2);
v___x_2661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2661_, 0, v___y_2644_);
lean_ctor_set(v___x_2661_, 1, v___y_2658_);
lean_ctor_set(v___x_2661_, 2, v___x_2660_);
lean_inc_ref(v___y_2646_);
v___x_2662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___y_2644_);
lean_ctor_set(v___x_2662_, 1, v___y_2646_);
if (lean_obj_tag(v___y_2654_) == 1)
{
lean_object* v_val_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v_val_2663_ = lean_ctor_get(v___y_2654_, 0);
lean_inc(v_val_2663_);
lean_dec_ref_known(v___y_2654_, 1);
v___x_2664_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
v___x_2665_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc_n(v___y_2644_, 2);
v___x_2666_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___y_2644_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = l_Lean_Syntax_node2(v___y_2644_, v___x_2664_, v___x_2666_, v_val_2663_);
v___x_2668_ = l_Array_mkArray1___redArg(v___x_2667_);
v___y_2604_ = v___y_2640_;
v___y_2605_ = v___x_2662_;
v___y_2606_ = v___y_2641_;
v___y_2607_ = v___y_2642_;
v___y_2608_ = v___y_2643_;
v___y_2609_ = v___y_2644_;
v___y_2610_ = v___y_2645_;
v___y_2611_ = v___y_2647_;
v___y_2612_ = v___y_2648_;
v___y_2613_ = v___x_2661_;
v___y_2614_ = v___y_2650_;
v___y_2615_ = v___y_2649_;
v___y_2616_ = v___y_2651_;
v___y_2617_ = v___y_2652_;
v___y_2618_ = v___y_2653_;
v___y_2619_ = v___y_2655_;
v___y_2620_ = v___y_2656_;
v___y_2621_ = v___y_2657_;
v___y_2622_ = v___y_2658_;
v___y_2623_ = v___x_2668_;
goto v___jp_2603_;
}
else
{
lean_object* v___x_2669_; 
lean_dec(v___y_2654_);
v___x_2669_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2604_ = v___y_2640_;
v___y_2605_ = v___x_2662_;
v___y_2606_ = v___y_2641_;
v___y_2607_ = v___y_2642_;
v___y_2608_ = v___y_2643_;
v___y_2609_ = v___y_2644_;
v___y_2610_ = v___y_2645_;
v___y_2611_ = v___y_2647_;
v___y_2612_ = v___y_2648_;
v___y_2613_ = v___x_2661_;
v___y_2614_ = v___y_2650_;
v___y_2615_ = v___y_2649_;
v___y_2616_ = v___y_2651_;
v___y_2617_ = v___y_2652_;
v___y_2618_ = v___y_2653_;
v___y_2619_ = v___y_2655_;
v___y_2620_ = v___y_2656_;
v___y_2621_ = v___y_2657_;
v___y_2622_ = v___y_2658_;
v___y_2623_ = v___x_2669_;
goto v___jp_2603_;
}
}
v___jp_2670_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_inc_ref(v___y_2686_);
v___x_2691_ = l_Array_append___redArg(v___y_2686_, v___y_2690_);
lean_dec_ref(v___y_2690_);
lean_inc(v___y_2689_);
lean_inc(v___y_2675_);
v___x_2692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2692_, 0, v___y_2675_);
lean_ctor_set(v___x_2692_, 1, v___y_2689_);
lean_ctor_set(v___x_2692_, 2, v___x_2691_);
if (lean_obj_tag(v___y_2672_) == 1)
{
lean_object* v_val_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v_val_2693_ = lean_ctor_get(v___y_2672_, 0);
lean_inc(v_val_2693_);
lean_dec_ref_known(v___y_2672_, 1);
v___x_2694_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__11));
lean_inc_ref(v___y_2684_);
v___x_2695_ = l_Lean_Name_mkStr4(v___x_2415_, v___x_2416_, v___y_2684_, v___x_2694_);
v___x_2696_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc_n(v___y_2675_, 4);
v___x_2697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___y_2675_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
lean_inc_ref(v___y_2686_);
v___x_2698_ = l_Array_append___redArg(v___y_2686_, v_val_2693_);
lean_dec(v_val_2693_);
lean_inc(v___y_2689_);
v___x_2699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2699_, 0, v___y_2675_);
lean_ctor_set(v___x_2699_, 1, v___y_2689_);
lean_ctor_set(v___x_2699_, 2, v___x_2698_);
v___x_2700_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
v___x_2701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___y_2675_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = l_Lean_Syntax_node3(v___y_2675_, v___x_2695_, v___x_2697_, v___x_2699_, v___x_2701_);
v___x_2703_ = l_Array_mkArray1___redArg(v___x_2702_);
v___y_2640_ = v___x_2692_;
v___y_2641_ = v___y_2671_;
v___y_2642_ = v___y_2673_;
v___y_2643_ = v___y_2674_;
v___y_2644_ = v___y_2675_;
v___y_2645_ = v___y_2676_;
v___y_2646_ = v___y_2677_;
v___y_2647_ = v___y_2678_;
v___y_2648_ = v___y_2679_;
v___y_2649_ = v___y_2680_;
v___y_2650_ = v___y_2681_;
v___y_2651_ = v___y_2682_;
v___y_2652_ = v___y_2683_;
v___y_2653_ = v___y_2684_;
v___y_2654_ = v___y_2685_;
v___y_2655_ = v___y_2686_;
v___y_2656_ = v___y_2687_;
v___y_2657_ = v___y_2688_;
v___y_2658_ = v___y_2689_;
v___y_2659_ = v___x_2703_;
goto v___jp_2639_;
}
else
{
lean_object* v___x_2704_; 
lean_dec(v___y_2672_);
v___x_2704_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2640_ = v___x_2692_;
v___y_2641_ = v___y_2671_;
v___y_2642_ = v___y_2673_;
v___y_2643_ = v___y_2674_;
v___y_2644_ = v___y_2675_;
v___y_2645_ = v___y_2676_;
v___y_2646_ = v___y_2677_;
v___y_2647_ = v___y_2678_;
v___y_2648_ = v___y_2679_;
v___y_2649_ = v___y_2680_;
v___y_2650_ = v___y_2681_;
v___y_2651_ = v___y_2682_;
v___y_2652_ = v___y_2683_;
v___y_2653_ = v___y_2684_;
v___y_2654_ = v___y_2685_;
v___y_2655_ = v___y_2686_;
v___y_2656_ = v___y_2687_;
v___y_2657_ = v___y_2688_;
v___y_2658_ = v___y_2689_;
v___y_2659_ = v___x_2704_;
goto v___jp_2639_;
}
}
v___jp_2705_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2722_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__12));
v___x_2723_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__13));
v___x_2724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_2725_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
if (lean_obj_tag(v___y_2716_) == 1)
{
lean_object* v_val_2726_; lean_object* v___x_2727_; 
v_val_2726_ = lean_ctor_get(v___y_2716_, 0);
lean_inc(v_val_2726_);
lean_dec_ref_known(v___y_2716_, 1);
v___x_2727_ = l_Array_mkArray1___redArg(v_val_2726_);
v___y_2671_ = v___y_2706_;
v___y_2672_ = v___y_2707_;
v___y_2673_ = v___y_2708_;
v___y_2674_ = v___y_2709_;
v___y_2675_ = v___y_2710_;
v___y_2676_ = v___x_2723_;
v___y_2677_ = v___x_2722_;
v___y_2678_ = v___y_2711_;
v___y_2679_ = v___y_2712_;
v___y_2680_ = v___y_2713_;
v___y_2681_ = v___y_2714_;
v___y_2682_ = v___y_2715_;
v___y_2683_ = v___y_2717_;
v___y_2684_ = v___y_2718_;
v___y_2685_ = v___y_2719_;
v___y_2686_ = v___x_2725_;
v___y_2687_ = v___y_2720_;
v___y_2688_ = v___y_2721_;
v___y_2689_ = v___x_2724_;
v___y_2690_ = v___x_2727_;
goto v___jp_2670_;
}
else
{
lean_object* v___x_2728_; 
lean_dec(v___y_2716_);
v___x_2728_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2671_ = v___y_2706_;
v___y_2672_ = v___y_2707_;
v___y_2673_ = v___y_2708_;
v___y_2674_ = v___y_2709_;
v___y_2675_ = v___y_2710_;
v___y_2676_ = v___x_2723_;
v___y_2677_ = v___x_2722_;
v___y_2678_ = v___y_2711_;
v___y_2679_ = v___y_2712_;
v___y_2680_ = v___y_2713_;
v___y_2681_ = v___y_2714_;
v___y_2682_ = v___y_2715_;
v___y_2683_ = v___y_2717_;
v___y_2684_ = v___y_2718_;
v___y_2685_ = v___y_2719_;
v___y_2686_ = v___x_2725_;
v___y_2687_ = v___y_2720_;
v___y_2688_ = v___y_2721_;
v___y_2689_ = v___x_2724_;
v___y_2690_ = v___x_2728_;
goto v___jp_2670_;
}
}
v___jp_2729_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_2739_, 0, v_prio_x3f_2736_);
v___x_2740_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2739_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v_items_2744_; size_t v_sz_2745_; size_t v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
v___x_2742_ = lean_unsigned_to_nat(7u);
v___x_2743_ = l_Lean_Syntax_getArg(v_x_2384_, v___x_2742_);
v_items_2744_ = l_Lean_Syntax_getArgs(v___x_2743_);
lean_dec(v___x_2743_);
v_sz_2745_ = lean_array_size(v_items_2744_);
v___x_2746_ = ((size_t)0ULL);
v___x_2747_ = lean_box_usize(v_sz_2745_);
v___x_2748_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___boxed__const__1));
lean_inc_ref(v_items_2744_);
v___x_2749_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed), 5, 3);
lean_closure_set(v___x_2749_, 0, v___x_2747_);
lean_closure_set(v___x_2749_, 1, v___x_2748_);
lean_closure_set(v___x_2749_, 2, v_items_2744_);
v___x_2750_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2749_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2752_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v___x_2752_ = l_Lean_Elab_Command_getRef___redArg(v___y_2737_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
v___x_2754_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2737_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_quotContext_x3f_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v_rhs_2760_; lean_object* v_attrs_x3f_2761_; lean_object* v___x_2762_; 
lean_dec_ref_known(v___x_2754_, 1);
v_quotContext_x3f_2755_ = lean_ctor_get(v___y_2737_, 5);
v___x_2756_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
v___x_2757_ = 0;
v___x_2758_ = l_Lean_mkIdentFrom(v_x_2384_, v___x_2756_, v___x_2757_);
v___x_2759_ = lean_unsigned_to_nat(9u);
v_rhs_2760_ = l_Lean_Syntax_getArg(v_x_2384_, v___x_2759_);
lean_dec(v_x_2384_);
lean_inc(v_rhs_2760_);
v_attrs_x3f_2761_ = l_Lean_Elab_Command_addInheritDocDefault(v_rhs_2760_, v___y_2730_);
v___x_2762_ = l_Lean_SourceInfo_fromRef(v_a_2753_, v___x_2757_);
lean_dec(v_a_2753_);
if (lean_obj_tag(v_quotContext_x3f_2755_) == 0)
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2738_);
lean_dec_ref(v___x_2763_);
v___y_2706_ = v___x_2758_;
v___y_2707_ = v_attrs_x3f_2761_;
v___y_2708_ = v___y_2738_;
v___y_2709_ = v_a_2751_;
v___y_2710_ = v___x_2762_;
v___y_2711_ = v___y_2737_;
v___y_2712_ = v___y_2734_;
v___y_2713_ = v___x_2757_;
v___y_2714_ = v___x_2746_;
v___y_2715_ = v_a_2741_;
v___y_2716_ = v___y_2731_;
v___y_2717_ = v_items_2744_;
v___y_2718_ = v___y_2732_;
v___y_2719_ = v___y_2733_;
v___y_2720_ = v___y_2735_;
v___y_2721_ = v_rhs_2760_;
goto v___jp_2705_;
}
else
{
v___y_2706_ = v___x_2758_;
v___y_2707_ = v_attrs_x3f_2761_;
v___y_2708_ = v___y_2738_;
v___y_2709_ = v_a_2751_;
v___y_2710_ = v___x_2762_;
v___y_2711_ = v___y_2737_;
v___y_2712_ = v___y_2734_;
v___y_2713_ = v___x_2757_;
v___y_2714_ = v___x_2746_;
v___y_2715_ = v_a_2741_;
v___y_2716_ = v___y_2731_;
v___y_2717_ = v_items_2744_;
v___y_2718_ = v___y_2732_;
v___y_2719_ = v___y_2733_;
v___y_2720_ = v___y_2735_;
v___y_2721_ = v_rhs_2760_;
goto v___jp_2705_;
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec(v_a_2753_);
lean_dec(v_a_2751_);
lean_dec_ref(v_items_2744_);
lean_dec(v_a_2741_);
lean_dec(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v_x_2384_);
v_a_2764_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2754_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2754_);
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
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v_a_2751_);
lean_dec_ref(v_items_2744_);
lean_dec(v_a_2741_);
lean_dec(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v_x_2384_);
v_a_2772_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2752_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2752_);
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
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec_ref(v_items_2744_);
lean_dec(v_a_2741_);
lean_dec(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v_x_2384_);
v_a_2780_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2750_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2750_);
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
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v_x_2384_);
v_a_2788_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2740_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2740_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
v___jp_2796_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2807_ = lean_unsigned_to_nat(6u);
v___x_2808_ = l_Lean_Syntax_getArg(v_x_2384_, v___x_2807_);
v___x_2809_ = l_Lean_Syntax_isNone(v___x_2808_);
if (v___x_2809_ == 0)
{
uint8_t v___x_2810_; 
lean_inc(v___x_2808_);
v___x_2810_ = l_Lean_Syntax_matchesNull(v___x_2808_, v___y_2798_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
lean_dec(v___x_2808_);
lean_dec(v_name_x3f_2804_);
lean_dec(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec(v___y_2799_);
lean_dec(v___y_2797_);
lean_dec(v_x_2384_);
v___x_2811_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2811_;
}
else
{
lean_object* v___x_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; 
v___x_2812_ = l_Lean_Syntax_getArg(v___x_2808_, v___x_2528_);
lean_dec(v___x_2808_);
v___x_2813_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
lean_inc(v___x_2812_);
v___x_2814_ = l_Lean_Syntax_isOfKind(v___x_2812_, v___x_2813_);
if (v___x_2814_ == 0)
{
lean_object* v___x_2815_; 
lean_dec(v___x_2812_);
lean_dec(v_name_x3f_2804_);
lean_dec(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec(v___y_2799_);
lean_dec(v___y_2797_);
lean_dec(v_x_2384_);
v___x_2815_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2815_;
}
else
{
lean_object* v_prio_x3f_2816_; lean_object* v___x_2817_; 
v_prio_x3f_2816_ = l_Lean_Syntax_getArg(v___x_2812_, v___y_2800_);
lean_dec(v___x_2812_);
v___x_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2817_, 0, v_prio_x3f_2816_);
v___y_2730_ = v___y_2797_;
v___y_2731_ = v___y_2799_;
v___y_2732_ = v___y_2801_;
v___y_2733_ = v___y_2802_;
v___y_2734_ = v_name_x3f_2804_;
v___y_2735_ = v___y_2803_;
v_prio_x3f_2736_ = v___x_2817_;
v___y_2737_ = v___y_2805_;
v___y_2738_ = v___y_2806_;
goto v___jp_2729_;
}
}
}
else
{
lean_object* v___x_2818_; 
lean_dec(v___x_2808_);
v___x_2818_ = lean_box(0);
v___y_2730_ = v___y_2797_;
v___y_2731_ = v___y_2799_;
v___y_2732_ = v___y_2801_;
v___y_2733_ = v___y_2802_;
v___y_2734_ = v_name_x3f_2804_;
v___y_2735_ = v___y_2803_;
v_prio_x3f_2736_ = v___x_2818_;
v___y_2737_ = v___y_2805_;
v___y_2738_ = v___y_2806_;
goto v___jp_2729_;
}
}
v___jp_2819_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v___x_2829_ = lean_unsigned_to_nat(5u);
v___x_2830_ = l_Lean_Syntax_getArg(v_x_2384_, v___x_2829_);
v___x_2831_ = l_Lean_Syntax_isNone(v___x_2830_);
if (v___x_2831_ == 0)
{
uint8_t v___x_2832_; 
lean_inc(v___x_2830_);
v___x_2832_ = l_Lean_Syntax_matchesNull(v___x_2830_, v___y_2821_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; 
lean_dec(v___x_2830_);
lean_dec(v_prec_x3f_2826_);
lean_dec(v___y_2825_);
lean_dec(v___y_2822_);
lean_dec(v___y_2820_);
lean_dec(v_x_2384_);
v___x_2833_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2833_;
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2834_ = l_Lean_Syntax_getArg(v___x_2830_, v___x_2528_);
lean_dec(v___x_2830_);
v___x_2835_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
lean_inc(v___x_2834_);
v___x_2836_ = l_Lean_Syntax_isOfKind(v___x_2834_, v___x_2835_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; 
lean_dec(v___x_2834_);
lean_dec(v_prec_x3f_2826_);
lean_dec(v___y_2825_);
lean_dec(v___y_2822_);
lean_dec(v___y_2820_);
lean_dec(v_x_2384_);
v___x_2837_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2837_;
}
else
{
lean_object* v_name_x3f_2838_; lean_object* v___x_2839_; 
v_name_x3f_2838_ = l_Lean_Syntax_getArg(v___x_2834_, v___y_2823_);
lean_dec(v___x_2834_);
v___x_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2839_, 0, v_name_x3f_2838_);
v___y_2797_ = v___y_2820_;
v___y_2798_ = v___y_2821_;
v___y_2799_ = v___y_2822_;
v___y_2800_ = v___y_2823_;
v___y_2801_ = v___y_2824_;
v___y_2802_ = v_prec_x3f_2826_;
v___y_2803_ = v___y_2825_;
v_name_x3f_2804_ = v___x_2839_;
v___y_2805_ = v___y_2827_;
v___y_2806_ = v___y_2828_;
goto v___jp_2796_;
}
}
}
else
{
lean_object* v___x_2840_; 
lean_dec(v___x_2830_);
v___x_2840_ = lean_box(0);
v___y_2797_ = v___y_2820_;
v___y_2798_ = v___y_2821_;
v___y_2799_ = v___y_2822_;
v___y_2800_ = v___y_2823_;
v___y_2801_ = v___y_2824_;
v___y_2802_ = v_prec_x3f_2826_;
v___y_2803_ = v___y_2825_;
v_name_x3f_2804_ = v___x_2840_;
v___y_2805_ = v___y_2827_;
v___y_2806_ = v___y_2828_;
goto v___jp_2796_;
}
}
v___jp_2841_:
{
lean_object* v___x_2847_; lean_object* v_attrKind_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2847_ = lean_unsigned_to_nat(2u);
v_attrKind_2848_ = l_Lean_Syntax_getArg(v_x_2384_, v___x_2847_);
v___x_2849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2));
v___x_2850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(v_attrKind_2848_);
v___x_2851_ = l_Lean_Syntax_isOfKind(v_attrKind_2848_, v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; 
lean_dec(v_attrKind_2848_);
lean_dec(v_attrs_x3f_2844_);
lean_dec(v___y_2843_);
lean_dec(v_x_2384_);
v___x_2852_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2852_;
}
else
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; 
v___x_2853_ = lean_unsigned_to_nat(3u);
v___x_2854_ = lean_unsigned_to_nat(4u);
v___x_2855_ = l_Lean_Syntax_getArg(v_x_2384_, v___x_2854_);
v___x_2856_ = l_Lean_Syntax_isNone(v___x_2855_);
if (v___x_2856_ == 0)
{
uint8_t v___x_2857_; 
lean_inc(v___x_2855_);
v___x_2857_ = l_Lean_Syntax_matchesNull(v___x_2855_, v___y_2842_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; 
lean_dec(v___x_2855_);
lean_dec(v_attrKind_2848_);
lean_dec(v_attrs_x3f_2844_);
lean_dec(v___y_2843_);
lean_dec(v_x_2384_);
v___x_2858_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2858_;
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v___x_2859_ = l_Lean_Syntax_getArg(v___x_2855_, v___x_2528_);
lean_dec(v___x_2855_);
v___x_2860_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
lean_inc(v___x_2859_);
v___x_2861_ = l_Lean_Syntax_isOfKind(v___x_2859_, v___x_2860_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; 
lean_dec(v___x_2859_);
lean_dec(v_attrKind_2848_);
lean_dec(v_attrs_x3f_2844_);
lean_dec(v___y_2843_);
lean_dec(v_x_2384_);
v___x_2862_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2862_;
}
else
{
lean_object* v_prec_x3f_2863_; lean_object* v___x_2864_; 
v_prec_x3f_2863_ = l_Lean_Syntax_getArg(v___x_2859_, v___y_2842_);
lean_dec(v___x_2859_);
v___x_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2864_, 0, v_prec_x3f_2863_);
v___y_2820_ = v_attrs_x3f_2844_;
v___y_2821_ = v___y_2842_;
v___y_2822_ = v___y_2843_;
v___y_2823_ = v___x_2853_;
v___y_2824_ = v___x_2849_;
v___y_2825_ = v_attrKind_2848_;
v_prec_x3f_2826_ = v___x_2864_;
v___y_2827_ = v___y_2845_;
v___y_2828_ = v___y_2846_;
goto v___jp_2819_;
}
}
}
else
{
lean_object* v___x_2865_; 
lean_dec(v___x_2855_);
v___x_2865_ = lean_box(0);
v___y_2820_ = v_attrs_x3f_2844_;
v___y_2821_ = v___y_2842_;
v___y_2822_ = v___y_2843_;
v___y_2823_ = v___x_2853_;
v___y_2824_ = v___x_2849_;
v___y_2825_ = v_attrKind_2848_;
v_prec_x3f_2826_ = v___x_2865_;
v___y_2827_ = v___y_2845_;
v___y_2828_ = v___y_2846_;
goto v___jp_2819_;
}
}
}
v___jp_2866_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2870_ = lean_unsigned_to_nat(1u);
v___x_2871_ = l_Lean_Syntax_getArg(v_x_2384_, v___x_2870_);
v___x_2872_ = l_Lean_Syntax_isNone(v___x_2871_);
if (v___x_2872_ == 0)
{
uint8_t v___x_2873_; 
lean_inc(v___x_2871_);
v___x_2873_ = l_Lean_Syntax_matchesNull(v___x_2871_, v___x_2870_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; 
lean_dec(v___x_2871_);
lean_dec(v_doc_x3f_2867_);
lean_dec(v_x_2384_);
v___x_2874_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2874_;
}
else
{
lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2875_ = l_Lean_Syntax_getArg(v___x_2871_, v___x_2528_);
lean_dec(v___x_2871_);
v___x_2876_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
lean_inc(v___x_2875_);
v___x_2877_ = l_Lean_Syntax_isOfKind(v___x_2875_, v___x_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
lean_dec(v___x_2875_);
lean_dec(v_doc_x3f_2867_);
lean_dec(v_x_2384_);
v___x_2878_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2878_;
}
else
{
lean_object* v___x_2879_; lean_object* v_attrs_x3f_2880_; lean_object* v___x_2881_; 
v___x_2879_ = l_Lean_Syntax_getArg(v___x_2875_, v___x_2870_);
lean_dec(v___x_2875_);
v_attrs_x3f_2880_ = l_Lean_Syntax_getArgs(v___x_2879_);
lean_dec(v___x_2879_);
v___x_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2881_, 0, v_attrs_x3f_2880_);
v___y_2842_ = v___x_2870_;
v___y_2843_ = v_doc_x3f_2867_;
v_attrs_x3f_2844_ = v___x_2881_;
v___y_2845_ = v___y_2868_;
v___y_2846_ = v___y_2869_;
goto v___jp_2841_;
}
}
}
else
{
lean_object* v___x_2882_; 
lean_dec(v___x_2871_);
v___x_2882_ = lean_box(0);
v___y_2842_ = v___x_2870_;
v___y_2843_ = v_doc_x3f_2867_;
v_attrs_x3f_2844_ = v___x_2882_;
v___y_2845_ = v___y_2868_;
v___y_2846_ = v___y_2869_;
goto v___jp_2841_;
}
}
}
v___jp_2388_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkUnexpander___boxed), 5, 3);
lean_closure_set(v___x_2394_, 0, v___y_2391_);
lean_closure_set(v___x_2394_, 1, v___y_2389_);
lean_closure_set(v___x_2394_, 2, v___y_2390_);
v___x_2395_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2394_, v___y_2392_, v___y_2393_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2406_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2406_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2406_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
if (lean_obj_tag(v_a_2396_) == 1)
{
lean_object* v_val_2400_; lean_object* v___x_2401_; 
lean_del_object(v___x_2398_);
v_val_2400_ = lean_ctor_get(v_a_2396_, 0);
lean_inc(v_val_2400_);
lean_dec_ref_known(v_a_2396_, 1);
v___x_2401_ = l_Lean_Elab_Command_elabCommand(v_val_2400_, v___y_2392_, v___y_2393_);
return v___x_2401_;
}
else
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
lean_dec(v_a_2396_);
v___x_2402_ = lean_box(0);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2402_);
v___x_2404_ = v___x_2398_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
v_a_2407_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2395_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2395_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
v___jp_2419_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2430_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__2));
v___x_2431_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__3));
lean_inc_ref(v___y_2426_);
lean_inc_n(v___y_2429_, 4);
lean_inc_n(v___y_2424_, 15);
v___x_2432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2432_, 0, v___y_2424_);
lean_ctor_set(v___x_2432_, 1, v___y_2429_);
lean_ctor_set(v___x_2432_, 2, v___y_2426_);
v___x_2433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___y_2424_);
lean_ctor_set(v___x_2433_, 1, v___x_2430_);
v___x_2434_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__29));
lean_inc_ref_n(v___y_2423_, 4);
v___x_2435_ = l_Lean_Name_mkStr4(v___x_2415_, v___x_2416_, v___y_2423_, v___x_2434_);
v___x_2436_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__31));
v___x_2437_ = l_Lean_Name_mkStr4(v___x_2415_, v___x_2416_, v___y_2423_, v___x_2436_);
v___x_2438_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
v___x_2439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___y_2424_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__34));
v___x_2441_ = l_Lean_Name_mkStr4(v___x_2415_, v___x_2416_, v___y_2423_, v___x_2440_);
v___x_2442_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
v___x_2443_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___y_2424_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
lean_inc_ref(v___y_2422_);
v___x_2444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___y_2424_);
lean_ctor_set(v___x_2444_, 1, v___y_2422_);
lean_inc_ref(v___x_2444_);
lean_inc(v___y_2421_);
lean_inc_ref(v___x_2443_);
lean_inc(v___x_2441_);
v___x_2445_ = l_Lean_Syntax_node3(v___y_2424_, v___x_2441_, v___x_2443_, v___y_2421_, v___x_2444_);
v___x_2446_ = l_Lean_Syntax_node1(v___y_2424_, v___y_2429_, v___x_2445_);
v___x_2447_ = l_Lean_Syntax_node1(v___y_2424_, v___y_2429_, v___x_2446_);
v___x_2448_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
v___x_2449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___y_2424_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__4));
v___x_2451_ = l_Lean_Name_mkStr4(v___x_2415_, v___x_2416_, v___y_2423_, v___x_2450_);
v___x_2452_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__5));
v___x_2453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___y_2424_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
lean_inc(v___y_2428_);
v___x_2454_ = l_Lean_Syntax_node3(v___y_2424_, v___x_2441_, v___x_2443_, v___y_2428_, v___x_2444_);
v___x_2455_ = l_Lean_Syntax_node2(v___y_2424_, v___x_2451_, v___x_2453_, v___x_2454_);
v___x_2456_ = l_Lean_Syntax_node4(v___y_2424_, v___x_2437_, v___x_2439_, v___x_2447_, v___x_2449_, v___x_2455_);
v___x_2457_ = l_Lean_Syntax_node1(v___y_2424_, v___y_2429_, v___x_2456_);
v___x_2458_ = l_Lean_Syntax_node1(v___y_2424_, v___x_2435_, v___x_2457_);
lean_inc_n(v___y_2427_, 2);
lean_inc_ref_n(v___x_2432_, 2);
v___x_2459_ = l_Lean_Syntax_node6(v___y_2424_, v___x_2431_, v___x_2432_, v___x_2432_, v___y_2427_, v___x_2433_, v___x_2432_, v___x_2458_);
v___x_2460_ = l_Lean_Elab_Command_isLocalAttrKind(v___y_2427_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_Elab_Command_elabCommand(v___x_2459_, v___y_2425_, v___y_2420_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_dec_ref_known(v___x_2461_, 1);
v___y_2389_ = v___y_2421_;
v___y_2390_ = v___y_2428_;
v___y_2391_ = v___y_2427_;
v___y_2392_ = v___y_2425_;
v___y_2393_ = v___y_2420_;
goto v___jp_2388_;
}
else
{
lean_dec(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec(v___y_2421_);
return v___x_2461_;
}
}
else
{
lean_object* v___x_2462_; lean_object* v_scopes_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v_opts_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___f_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2462_ = lean_st_ref_get(v___y_2420_);
v_scopes_2463_ = lean_ctor_get(v___x_2462_, 2);
lean_inc(v_scopes_2463_);
lean_dec(v___x_2462_);
v___x_2464_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2465_ = l_List_head_x21___redArg(v___x_2464_, v_scopes_2463_);
lean_dec(v_scopes_2463_);
v_opts_2466_ = lean_ctor_get(v___x_2465_, 1);
lean_inc_ref(v_opts_2466_);
lean_dec(v___x_2465_);
v___x_2467_ = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
v___x_2468_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_2466_, v___x_2467_, v___x_2418_);
v___f_2469_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___lam__0), 2, 1);
lean_closure_set(v___f_2469_, 0, v___x_2468_);
v___x_2470_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_2470_, 0, v___x_2459_);
v___x_2471_ = l_Lean_Elab_Command_withScope___redArg(v___f_2469_, v___x_2470_, v___y_2425_, v___y_2420_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_dec_ref_known(v___x_2471_, 1);
v___y_2389_ = v___y_2421_;
v___y_2390_ = v___y_2428_;
v___y_2391_ = v___y_2427_;
v___y_2392_ = v___y_2425_;
v___y_2393_ = v___y_2420_;
goto v___jp_2388_;
}
else
{
lean_dec(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec(v___y_2421_);
return v___x_2471_;
}
}
}
v___jp_2472_:
{
size_t v_sz_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_sz_2487_ = lean_array_size(v___y_2480_);
v___x_2488_ = lean_box_usize(v_sz_2487_);
v___x_2489_ = lean_box_usize(v___y_2478_);
v___x_2490_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed), 5, 3);
lean_closure_set(v___x_2490_, 0, v___x_2488_);
lean_closure_set(v___x_2490_, 1, v___x_2489_);
lean_closure_set(v___x_2490_, 2, v___y_2480_);
v___x_2491_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2490_, v___y_2477_, v___y_2473_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2493_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2491_, 1);
v___x_2493_ = l_Lean_Elab_Command_getRef___redArg(v___y_2477_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2495_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2493_, 1);
v___x_2495_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2477_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_quotContext_x3f_2496_; size_t v_sz_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
lean_dec_ref_known(v___x_2495_, 1);
v_quotContext_x3f_2496_ = lean_ctor_get(v___y_2477_, 5);
v_sz_2497_ = lean_array_size(v___y_2486_);
v___x_2498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_2497_, v___y_2478_, v___y_2486_);
v___x_2499_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(v___x_2498_, v___y_2485_);
lean_dec_ref(v___x_2498_);
v___x_2500_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2500_, 0, v___y_2475_);
lean_ctor_set(v___x_2500_, 1, v___y_2474_);
lean_ctor_set(v___x_2500_, 2, v_a_2492_);
v___x_2501_ = l_Lean_SourceInfo_fromRef(v_a_2494_, v___y_2479_);
lean_dec(v_a_2494_);
if (lean_obj_tag(v_quotContext_x3f_2496_) == 0)
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2473_);
lean_dec_ref(v___x_2502_);
v___y_2420_ = v___y_2473_;
v___y_2421_ = v___x_2500_;
v___y_2422_ = v___y_2476_;
v___y_2423_ = v___y_2481_;
v___y_2424_ = v___x_2501_;
v___y_2425_ = v___y_2477_;
v___y_2426_ = v___y_2482_;
v___y_2427_ = v___y_2483_;
v___y_2428_ = v___x_2499_;
v___y_2429_ = v___y_2484_;
goto v___jp_2419_;
}
else
{
v___y_2420_ = v___y_2473_;
v___y_2421_ = v___x_2500_;
v___y_2422_ = v___y_2476_;
v___y_2423_ = v___y_2481_;
v___y_2424_ = v___x_2501_;
v___y_2425_ = v___y_2477_;
v___y_2426_ = v___y_2482_;
v___y_2427_ = v___y_2483_;
v___y_2428_ = v___x_2499_;
v___y_2429_ = v___y_2484_;
goto v___jp_2419_;
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec(v_a_2494_);
lean_dec(v_a_2492_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec(v___y_2483_);
lean_dec(v___y_2475_);
lean_dec(v___y_2474_);
v_a_2503_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2495_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2495_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_dec(v_a_2492_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec(v___y_2483_);
lean_dec(v___y_2475_);
lean_dec(v___y_2474_);
v_a_2511_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2493_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2493_);
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
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec(v___y_2483_);
lean_dec(v___y_2475_);
lean_dec(v___y_2474_);
v_a_2519_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2491_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2491_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___boxed(lean_object* v_x_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Lean_Elab_Command_elabNotation(v_x_2894_, v_a_2895_, v_a_2896_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(lean_object* v_00_u03b1_2899_, lean_object* v_x_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v_x_2900_, v___y_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2904_, lean_object* v_x_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(v_00_u03b1_2904_, v_x_2905_, v___y_2906_, v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec_ref(v_x_2905_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(lean_object* v_00_u03b1_2909_, lean_object* v_ref_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_2910_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___boxed(lean_object* v_00_u03b1_2915_, lean_object* v_ref_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(v_00_u03b1_2915_, v_ref_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(lean_object* v_00_u03b1_2921_, lean_object* v_x_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2922_, v___y_2923_, v___y_2924_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___boxed(lean_object* v_00_u03b1_2927_, lean_object* v_x_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(v_00_u03b1_2927_, v_x_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(lean_object* v_msgData_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msgData_2933_, v___y_2935_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(v_msgData_2938_, v___y_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(lean_object* v_as_2943_, lean_object* v_as_x27_2944_, lean_object* v_b_2945_, lean_object* v_a_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_2944_, v_b_2945_, v___y_2947_, v___y_2948_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___boxed(lean_object* v_as_2951_, lean_object* v_as_x27_2952_, lean_object* v_b_2953_, lean_object* v_a_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(v_as_2951_, v_as_x27_2952_, v_b_2953_, v_a_2954_, v___y_2955_, v___y_2956_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v_as_x27_2952_);
lean_dec(v_as_2951_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(lean_object* v_00_u03b1_2959_, lean_object* v_ref_2960_, lean_object* v_msg_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_ref_2960_, v_msg_2961_, v___y_2962_, v___y_2963_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___boxed(lean_object* v_00_u03b1_2966_, lean_object* v_ref_2967_, lean_object* v_msg_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(v_00_u03b1_2966_, v_ref_2967_, v_msg_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v_ref_2967_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2973_, lean_object* v_m_2974_, lean_object* v_a_2975_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v_m_2974_, v_a_2975_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_2977_, lean_object* v_m_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(v_00_u03b2_2977_, v_m_2978_, v_a_2979_);
lean_dec(v_a_2979_);
lean_dec_ref(v_m_2978_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(lean_object* v_00_u03b1_2981_, lean_object* v_msg_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_2982_, v___y_2983_, v___y_2984_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___boxed(lean_object* v_00_u03b1_2987_, lean_object* v_msg_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(v_00_u03b1_2987_, v_msg_2988_, v___y_2989_, v___y_2990_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
return v_res_2992_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(lean_object* v_00_u03b2_2993_, lean_object* v_x_2994_, lean_object* v_x_2995_){
_start:
{
uint8_t v___x_2996_; 
v___x_2996_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_2994_, v_x_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___boxed(lean_object* v_00_u03b2_2997_, lean_object* v_x_2998_, lean_object* v_x_2999_){
_start:
{
uint8_t v_res_3000_; lean_object* v_r_3001_; 
v_res_3000_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(v_00_u03b2_2997_, v_x_2998_, v_x_2999_);
lean_dec_ref(v_x_2999_);
lean_dec_ref(v_x_2998_);
v_r_3001_ = lean_box(v_res_3000_);
return v_r_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(lean_object* v_00_u03b2_3002_, lean_object* v_a_3003_, lean_object* v_x_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_3003_, v_x_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___boxed(lean_object* v_00_u03b2_3006_, lean_object* v_a_3007_, lean_object* v_x_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(v_00_u03b2_3006_, v_a_3007_, v_x_3008_);
lean_dec(v_x_3008_);
lean_dec(v_a_3007_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(lean_object* v_msgData_3010_, lean_object* v_macroStack_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_msgData_3010_, v_macroStack_3011_, v___y_3013_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___boxed(lean_object* v_msgData_3016_, lean_object* v_macroStack_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(v_msgData_3016_, v_macroStack_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
return v_res_3021_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(lean_object* v_00_u03b2_3022_, lean_object* v_x_3023_, size_t v_x_3024_, lean_object* v_x_3025_){
_start:
{
uint8_t v___x_3026_; 
v___x_3026_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_3023_, v_x_3024_, v_x_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___boxed(lean_object* v_00_u03b2_3027_, lean_object* v_x_3028_, lean_object* v_x_3029_, lean_object* v_x_3030_){
_start:
{
size_t v_x_25605__boxed_3031_; uint8_t v_res_3032_; lean_object* v_r_3033_; 
v_x_25605__boxed_3031_ = lean_unbox_usize(v_x_3029_);
lean_dec(v_x_3029_);
v_res_3032_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(v_00_u03b2_3027_, v_x_3028_, v_x_25605__boxed_3031_, v_x_3030_);
lean_dec_ref(v_x_3030_);
lean_dec_ref(v_x_3028_);
v_r_3033_ = lean_box(v_res_3032_);
return v_r_3033_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(lean_object* v_00_u03b2_3034_, lean_object* v_keys_3035_, lean_object* v_vals_3036_, lean_object* v_heq_3037_, lean_object* v_i_3038_, lean_object* v_k_3039_){
_start:
{
uint8_t v___x_3040_; 
v___x_3040_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_3035_, v_i_3038_, v_k_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___boxed(lean_object* v_00_u03b2_3041_, lean_object* v_keys_3042_, lean_object* v_vals_3043_, lean_object* v_heq_3044_, lean_object* v_i_3045_, lean_object* v_k_3046_){
_start:
{
uint8_t v_res_3047_; lean_object* v_r_3048_; 
v_res_3047_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(v_00_u03b2_3041_, v_keys_3042_, v_vals_3043_, v_heq_3044_, v_i_3045_, v_k_3046_);
lean_dec_ref(v_k_3046_);
lean_dec_ref(v_vals_3043_);
lean_dec_ref(v_keys_3042_);
v_r_3048_ = lean_box(v_res_3047_);
return v_r_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1(){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3056_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3057_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
v___x_3058_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1));
v___x_3059_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___boxed), 4, 0);
v___x_3060_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3056_, v___x_3057_, v___x_3058_, v___x_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___boxed(lean_object* v_a_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
return v_res_3062_;
}
}
lean_object* runtime_initialize_Lean_Elab_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinNotation(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Notation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinNotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Notation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinNotation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Notation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinNotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Notation(builtin);
}
#ifdef __cplusplus
}
#endif
