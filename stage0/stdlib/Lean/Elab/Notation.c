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
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_strLitToPattern___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23_spec__26___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(v___y_309_);
v___x_313_ = l_Array_append___redArg(v___y_309_, v___y_312_);
lean_dec_ref(v___y_312_);
lean_inc(v___y_307_);
lean_inc(v___y_308_);
v___x_314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_314_, 0, v___y_308_);
lean_ctor_set(v___x_314_, 1, v___y_307_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
lean_inc(v___y_306_);
v___x_315_ = l_Lean_Syntax_node2(v___y_308_, v___y_306_, v___y_310_, v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___y_311_);
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
v___y_306_ = v___x_326_;
v___y_307_ = v___x_332_;
v___y_308_ = v___x_325_;
v___y_309_ = v___x_333_;
v___y_310_ = v___x_331_;
v___y_311_ = v___y_320_;
v___y_312_ = v___x_339_;
goto v___jp_305_;
}
else
{
lean_object* v___x_340_; 
lean_dec(v_prec_x3f_318_);
v___x_340_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_306_ = v___x_326_;
v___y_307_ = v___x_332_;
v___y_308_ = v___x_325_;
v___y_309_ = v___x_333_;
v___y_310_ = v___x_331_;
v___y_311_ = v___y_320_;
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
uint8_t v___y_387_; lean_object* v_k_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
lean_inc(v_stx_384_);
v_k_394_ = l_Lean_Syntax_getKind(v_stx_384_);
v___x_395_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
v___x_396_ = lean_name_eq(v_k_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_397_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12));
v___x_398_ = lean_name_eq(v_k_394_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
v___x_400_ = lean_name_eq(v_k_394_, v___x_399_);
lean_dec(v_k_394_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; 
lean_dec(v_stx_384_);
v___x_401_ = l_Lean_Macro_throwUnsupported___redArg(v_a_385_);
return v___x_401_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_402_ = lean_unsigned_to_nat(4u);
v___x_403_ = l_Lean_Syntax_getArg(v_stx_384_, v___x_402_);
v___x_404_ = l_Lean_Syntax_isNone(v___x_403_);
lean_dec(v___x_403_);
if (v___x_404_ == 0)
{
v___y_387_ = v___x_400_;
goto v___jp_386_;
}
else
{
v___y_387_ = v___x_398_;
goto v___jp_386_;
}
}
}
else
{
lean_object* v___x_405_; 
lean_dec(v_k_394_);
v___x_405_ = l_Lean_Elab_Command_strLitToPattern___redArg(v_stx_384_, v_a_385_);
lean_dec(v_stx_384_);
return v___x_405_;
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec(v_k_394_);
v___x_406_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = l_Lean_Syntax_getArg(v_stx_384_, v___x_407_);
lean_dec(v_stx_384_);
v___x_409_ = lean_box(0);
v___x_410_ = l_Lean_Syntax_mkAntiquotNode(v___x_406_, v___x_408_, v___x_407_, v___x_409_, v___x_396_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_a_385_);
return v___x_411_;
}
v___jp_386_:
{
if (v___y_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = lean_unsigned_to_nat(1u);
v___x_389_ = l_Lean_Syntax_getArg(v_stx_384_, v___x_388_);
lean_dec(v_stx_384_);
v___x_390_ = l_Lean_Elab_Command_strLitToPattern___redArg(v___x_389_, v_a_385_);
lean_dec(v___x_389_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = lean_unsigned_to_nat(3u);
v___x_392_ = l_Lean_Syntax_getArg(v_stx_384_, v___x_391_);
lean_dec(v_stx_384_);
v___x_393_ = l_Lean_Elab_Command_strLitToPattern___redArg(v___x_392_, v_a_385_);
lean_dec(v___x_392_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern(lean_object* v_stx_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(v_stx_412_, v_a_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___boxed(lean_object* v_stx_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Elab_Command_expandNotationItemIntoPattern(v_stx_416_, v_a_417_, v_a_418_);
lean_dec_ref(v_a_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux(lean_object* v_parens_420_, lean_object* v_body_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Syntax_getHeadInfo(v_parens_420_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_leading_423_; lean_object* v___x_424_; 
v_leading_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc_ref(v_leading_423_);
lean_dec_ref_known(v___x_422_, 4);
v___x_424_ = l_Lean_Syntax_getHeadInfo(v_body_421_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_pos_425_; lean_object* v_trailing_426_; lean_object* v_endPos_427_; lean_object* v___x_428_; 
v_pos_425_ = lean_ctor_get(v___x_424_, 1);
lean_inc(v_pos_425_);
v_trailing_426_ = lean_ctor_get(v___x_424_, 2);
lean_inc_ref(v_trailing_426_);
v_endPos_427_ = lean_ctor_get(v___x_424_, 3);
lean_inc(v_endPos_427_);
lean_dec_ref_known(v___x_424_, 4);
v___x_428_ = l_Lean_Syntax_getTailInfo(v_body_421_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_leading_429_; lean_object* v_pos_430_; lean_object* v_endPos_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_452_; 
v_leading_429_ = lean_ctor_get(v___x_428_, 0);
v_pos_430_ = lean_ctor_get(v___x_428_, 1);
v_endPos_431_ = lean_ctor_get(v___x_428_, 3);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; 
v_unused_453_ = lean_ctor_get(v___x_428_, 2);
lean_dec(v_unused_453_);
v___x_433_ = v___x_428_;
v_isShared_434_ = v_isSharedCheck_452_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_endPos_431_);
lean_inc(v_pos_430_);
lean_inc(v_leading_429_);
lean_dec(v___x_428_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_452_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Syntax_getTailInfo(v_parens_420_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_trailing_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_448_; 
v_trailing_436_ = lean_ctor_get(v___x_435_, 2);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; lean_object* v_unused_450_; lean_object* v_unused_451_; 
v_unused_449_ = lean_ctor_get(v___x_435_, 3);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v___x_435_, 1);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v___x_435_, 0);
lean_dec(v_unused_451_);
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_448_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_trailing_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_448_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 3, v_endPos_427_);
lean_ctor_set(v___x_438_, 2, v_trailing_426_);
lean_ctor_set(v___x_438_, 1, v_pos_425_);
lean_ctor_set(v___x_438_, 0, v_leading_423_);
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_leading_423_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_pos_425_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_trailing_426_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_endPos_427_);
v___x_441_ = v_reuseFailAlloc_447_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = l_Lean_Syntax_setHeadInfo(v_body_421_, v___x_441_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 2, v_trailing_436_);
v___x_444_ = v___x_433_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_leading_429_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_pos_430_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_trailing_436_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_endPos_431_);
v___x_444_ = v_reuseFailAlloc_446_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Syntax_setTailInfo(v___x_442_, v___x_444_);
return v___x_445_;
}
}
}
}
else
{
lean_dec(v___x_435_);
lean_del_object(v___x_433_);
lean_dec(v_endPos_431_);
lean_dec(v_pos_430_);
lean_dec_ref(v_leading_429_);
lean_dec(v_endPos_427_);
lean_dec_ref(v_trailing_426_);
lean_dec(v_pos_425_);
lean_dec_ref(v_leading_423_);
return v_body_421_;
}
}
}
else
{
lean_dec(v___x_428_);
lean_dec(v_endPos_427_);
lean_dec_ref(v_trailing_426_);
lean_dec(v_pos_425_);
lean_dec_ref(v_leading_423_);
return v_body_421_;
}
}
else
{
lean_dec(v___x_424_);
lean_dec_ref(v_leading_423_);
return v_body_421_;
}
}
else
{
lean_dec(v___x_422_);
return v_body_421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux___boxed(lean_object* v_parens_454_, lean_object* v_body_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Elab_Command_removeParenthesesAux(v_parens_454_, v_body_455_);
lean_dec(v_parens_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses(lean_object* v_stx_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__1));
lean_inc(v_stx_472_);
v___x_476_ = l_Lean_Syntax_isOfKind(v_stx_472_, v___x_475_);
if (v___x_476_ == 0)
{
if (lean_obj_tag(v_stx_472_) == 1)
{
lean_object* v_info_477_; lean_object* v_kind_478_; lean_object* v_args_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_507_; 
v_info_477_ = lean_ctor_get(v_stx_472_, 0);
v_kind_478_ = lean_ctor_get(v_stx_472_, 1);
v_args_479_ = lean_ctor_get(v_stx_472_, 2);
v_isSharedCheck_507_ = !lean_is_exclusive(v_stx_472_);
if (v_isSharedCheck_507_ == 0)
{
v___x_481_ = v_stx_472_;
v_isShared_482_ = v_isSharedCheck_507_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_args_479_);
lean_inc(v_kind_478_);
lean_inc(v_info_477_);
lean_dec(v_stx_472_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_507_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
size_t v_sz_483_; size_t v___x_484_; lean_object* v___x_485_; 
v_sz_483_ = lean_array_size(v_args_479_);
v___x_484_ = ((size_t)0ULL);
v___x_485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_483_, v___x_484_, v_args_479_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_497_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_a_487_ = lean_ctor_get(v___x_485_, 1);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_497_ == 0)
{
v___x_489_ = v___x_485_;
v_isShared_490_ = v_isSharedCheck_497_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_497_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 2, v_a_486_);
v___x_492_ = v___x_481_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_info_477_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_kind_478_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_a_486_);
v___x_492_ = v_reuseFailAlloc_496_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_494_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_492_);
v___x_494_ = v___x_489_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_a_487_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_del_object(v___x_481_);
lean_dec(v_kind_478_);
lean_dec(v_info_477_);
v_a_498_ = lean_ctor_get(v___x_485_, 0);
v_a_499_ = lean_ctor_get(v___x_485_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_485_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_inc(v_a_498_);
lean_dec(v___x_485_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_498_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
else
{
lean_object* v___x_508_; 
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v_stx_472_);
lean_ctor_set(v___x_508_, 1, v_a_474_);
return v___x_508_;
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = l_Lean_Syntax_getArg(v_stx_472_, v___x_509_);
v___x_511_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__3));
lean_inc(v___x_510_);
v___x_512_ = l_Lean_Syntax_isOfKind(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
lean_dec(v___x_510_);
if (lean_obj_tag(v_stx_472_) == 1)
{
lean_object* v_info_513_; lean_object* v_kind_514_; lean_object* v_args_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_543_; 
v_info_513_ = lean_ctor_get(v_stx_472_, 0);
v_kind_514_ = lean_ctor_get(v_stx_472_, 1);
v_args_515_ = lean_ctor_get(v_stx_472_, 2);
v_isSharedCheck_543_ = !lean_is_exclusive(v_stx_472_);
if (v_isSharedCheck_543_ == 0)
{
v___x_517_ = v_stx_472_;
v_isShared_518_ = v_isSharedCheck_543_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_args_515_);
lean_inc(v_kind_514_);
lean_inc(v_info_513_);
lean_dec(v_stx_472_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_543_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
size_t v_sz_519_; size_t v___x_520_; lean_object* v___x_521_; 
v_sz_519_ = lean_array_size(v_args_515_);
v___x_520_ = ((size_t)0ULL);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_519_, v___x_520_, v_args_515_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_533_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_a_523_ = lean_ctor_get(v___x_521_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_533_ == 0)
{
v___x_525_ = v___x_521_;
v_isShared_526_ = v_isSharedCheck_533_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_533_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 2, v_a_522_);
v___x_528_ = v___x_517_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_info_513_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_kind_514_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_a_522_);
v___x_528_ = v_reuseFailAlloc_532_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_528_);
v___x_530_ = v___x_525_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_a_523_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_del_object(v___x_517_);
lean_dec(v_kind_514_);
lean_dec(v_info_513_);
v_a_534_ = lean_ctor_get(v___x_521_, 0);
v_a_535_ = lean_ctor_get(v___x_521_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_521_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_inc(v_a_534_);
lean_dec(v___x_521_);
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
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_534_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_a_535_);
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
else
{
lean_object* v___x_544_; 
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v_stx_472_);
lean_ctor_set(v___x_544_, 1, v_a_474_);
return v___x_544_;
}
}
else
{
lean_object* v___x_545_; lean_object* v_h_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_545_ = lean_unsigned_to_nat(1u);
v_h_546_ = l_Lean_Syntax_getArg(v___x_510_, v___x_545_);
lean_dec(v___x_510_);
v___x_547_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__5));
lean_inc(v_h_546_);
v___x_548_ = l_Lean_Syntax_isOfKind(v_h_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_dec(v_h_546_);
if (lean_obj_tag(v_stx_472_) == 1)
{
lean_object* v_info_549_; lean_object* v_kind_550_; lean_object* v_args_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_579_; 
v_info_549_ = lean_ctor_get(v_stx_472_, 0);
v_kind_550_ = lean_ctor_get(v_stx_472_, 1);
v_args_551_ = lean_ctor_get(v_stx_472_, 2);
v_isSharedCheck_579_ = !lean_is_exclusive(v_stx_472_);
if (v_isSharedCheck_579_ == 0)
{
v___x_553_ = v_stx_472_;
v_isShared_554_ = v_isSharedCheck_579_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_args_551_);
lean_inc(v_kind_550_);
lean_inc(v_info_549_);
lean_dec(v_stx_472_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_579_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
size_t v_sz_555_; size_t v___x_556_; lean_object* v___x_557_; 
v_sz_555_ = lean_array_size(v_args_551_);
v___x_556_ = ((size_t)0ULL);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_555_, v___x_556_, v_args_551_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_569_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
v_a_559_ = lean_ctor_get(v___x_557_, 1);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_569_ == 0)
{
v___x_561_ = v___x_557_;
v_isShared_562_ = v_isSharedCheck_569_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_inc(v_a_558_);
lean_dec(v___x_557_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_569_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 2, v_a_558_);
v___x_564_ = v___x_553_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_info_549_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_kind_550_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_a_558_);
v___x_564_ = v_reuseFailAlloc_568_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_566_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_564_);
v___x_566_ = v___x_561_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_a_559_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_object* v_a_570_; lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_del_object(v___x_553_);
lean_dec(v_kind_550_);
lean_dec(v_info_549_);
v_a_570_ = lean_ctor_get(v___x_557_, 0);
v_a_571_ = lean_ctor_get(v___x_557_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_557_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_inc(v_a_570_);
lean_dec(v___x_557_);
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
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_570_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_a_571_);
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
else
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_stx_472_);
lean_ctor_set(v___x_580_, 1, v_a_474_);
return v___x_580_;
}
}
else
{
lean_object* v_e_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_e_581_ = l_Lean_Syntax_getArg(v_stx_472_, v___x_545_);
v___x_582_ = l_Lean_TSyntax_getHygieneInfo(v_h_546_);
lean_dec(v_h_546_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_inc(v_e_581_);
v___x_584_ = l_Lean_Elab_Term_expandCDot_x3f(v_e_581_, v___x_583_, v_a_473_, v_a_474_);
lean_dec_ref_known(v___x_583_, 1);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v_a_586_; lean_object* v___y_588_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
v_a_586_ = lean_ctor_get(v___x_584_, 1);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_584_, 2);
if (lean_obj_tag(v_a_585_) == 0)
{
v___y_588_ = v_e_581_;
goto v___jp_587_;
}
else
{
lean_object* v_val_600_; 
lean_dec(v_e_581_);
v_val_600_ = lean_ctor_get(v_a_585_, 0);
lean_inc(v_val_600_);
lean_dec_ref_known(v_a_585_, 1);
v___y_588_ = v_val_600_;
goto v___jp_587_;
}
v___jp_587_:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_Elab_Command_removeParentheses(v___y_588_, v_a_473_, v_a_586_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_a_591_ = lean_ctor_get(v___x_589_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_599_ == 0)
{
v___x_593_ = v___x_589_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = l_Lean_Elab_Command_removeParenthesesAux(v_stx_472_, v_a_590_);
lean_dec(v_stx_472_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_a_591_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
lean_dec(v_stx_472_);
return v___x_589_;
}
}
}
else
{
lean_object* v_a_601_; lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec(v_e_581_);
lean_dec(v_stx_472_);
v_a_601_ = lean_ctor_get(v___x_584_, 0);
v_a_602_ = lean_ctor_get(v___x_584_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_584_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_inc(v_a_601_);
lean_dec(v___x_584_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_601_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(size_t v_sz_610_, size_t v_i_611_, lean_object* v_bs_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
uint8_t v___x_615_; 
v___x_615_ = lean_usize_dec_lt(v_i_611_, v_sz_610_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v_bs_612_);
lean_ctor_set(v___x_616_, 1, v___y_614_);
return v___x_616_;
}
else
{
lean_object* v_v_617_; lean_object* v___x_618_; 
v_v_617_ = lean_array_uget_borrowed(v_bs_612_, v_i_611_);
lean_inc(v_v_617_);
v___x_618_ = l_Lean_Elab_Command_removeParentheses(v_v_617_, v___y_613_, v___y_614_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v_a_620_; lean_object* v___x_621_; lean_object* v_bs_x27_622_; size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
v_a_620_ = lean_ctor_get(v___x_618_, 1);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_618_, 2);
v___x_621_ = lean_unsigned_to_nat(0u);
v_bs_x27_622_ = lean_array_uset(v_bs_612_, v_i_611_, v___x_621_);
v___x_623_ = ((size_t)1ULL);
v___x_624_ = lean_usize_add(v_i_611_, v___x_623_);
v___x_625_ = lean_array_uset(v_bs_x27_622_, v_i_611_, v_a_619_);
v_i_611_ = v___x_624_;
v_bs_612_ = v___x_625_;
v___y_614_ = v_a_620_;
goto _start;
}
else
{
lean_object* v_a_627_; lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_bs_612_);
v_a_627_ = lean_ctor_get(v___x_618_, 0);
v_a_628_ = lean_ctor_get(v___x_618_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_618_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_inc(v_a_627_);
lean_dec(v___x_618_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_627_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0___boxed(lean_object* v_sz_636_, lean_object* v_i_637_, lean_object* v_bs_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
size_t v_sz_boxed_641_; size_t v_i_boxed_642_; lean_object* v_res_643_; 
v_sz_boxed_641_ = lean_unbox_usize(v_sz_636_);
lean_dec(v_sz_636_);
v_i_boxed_642_ = lean_unbox_usize(v_i_637_);
lean_dec(v_i_637_);
v_res_643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_boxed_641_, v_i_boxed_642_, v_bs_638_, v___y_639_, v___y_640_);
lean_dec_ref(v___y_639_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses___boxed(lean_object* v_stx_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Elab_Command_removeParentheses(v_stx_644_, v_a_645_, v_a_646_);
lean_dec_ref(v_a_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(lean_object* v___x_651_, uint8_t v_firstChoiceOnly_652_, lean_object* v_stx_653_, lean_object* v_b_654_){
_start:
{
lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_668_; lean_object* v_a_669_; lean_object* v_snd_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_703_; 
v_snd_679_ = lean_ctor_get(v_b_654_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_b_654_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v_b_654_, 0);
lean_dec(v_unused_704_);
v___x_681_ = v_b_654_;
v_isShared_682_ = v_isSharedCheck_703_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_snd_679_);
lean_dec(v_b_654_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_703_;
goto v_resetjp_680_;
}
v___jp_655_:
{
lean_object* v___x_658_; lean_object* v___x_659_; size_t v_sz_660_; size_t v___x_661_; lean_object* v___x_662_; lean_object* v_fst_663_; 
v___x_658_ = lean_box(0);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___y_657_);
v_sz_660_ = lean_array_size(v___y_656_);
v___x_661_ = ((size_t)0ULL);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v___x_651_, v_firstChoiceOnly_652_, v___y_656_, v_sz_660_, v___x_661_, v___x_659_);
v_fst_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_fst_663_);
if (lean_obj_tag(v_fst_663_) == 0)
{
lean_object* v_snd_664_; lean_object* v___x_665_; 
v_snd_664_ = lean_ctor_get(v___x_662_, 1);
lean_inc(v_snd_664_);
lean_dec_ref(v___x_662_);
v___x_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_665_, 0, v_snd_664_);
return v___x_665_;
}
else
{
lean_object* v_val_666_; 
lean_dec_ref(v___x_662_);
v_val_666_ = lean_ctor_get(v_fst_663_, 0);
lean_inc(v_val_666_);
lean_dec_ref_known(v_fst_663_, 1);
return v_val_666_;
}
}
v___jp_667_:
{
if (lean_obj_tag(v_stx_653_) == 1)
{
lean_dec_ref(v___y_668_);
if (v_firstChoiceOnly_652_ == 0)
{
lean_object* v_args_670_; 
v_args_670_ = lean_ctor_get(v_stx_653_, 2);
v___y_656_ = v_args_670_;
v___y_657_ = v_a_669_;
goto v___jp_655_;
}
else
{
lean_object* v_kind_671_; lean_object* v_args_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_kind_671_ = lean_ctor_get(v_stx_653_, 1);
v_args_672_ = lean_ctor_get(v_stx_653_, 2);
v___x_673_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1));
v___x_674_ = lean_name_eq(v_kind_671_, v___x_673_);
if (v___x_674_ == 0)
{
v___y_656_ = v_args_672_;
v___y_657_ = v_a_669_;
goto v___jp_655_;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_box(0);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_array_get_borrowed(v___x_675_, v_args_672_, v___x_676_);
v_stx_653_ = v___x_677_;
v_b_654_ = v_a_669_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_a_669_);
return v___y_668_;
}
}
v_resetjp_680_:
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_box(0);
v___x_684_ = l_Lean_Syntax_isAntiquot(v_stx_653_);
if (v___x_684_ == 0)
{
lean_object* v___x_686_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_683_);
v___x_686_ = v___x_681_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_snd_679_);
v___x_686_ = v_reuseFailAlloc_688_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; 
lean_inc_ref(v___x_686_);
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___y_668_ = v___x_687_;
v_a_669_ = v___x_686_;
goto v___jp_667_;
}
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_689_ = l_Lean_Syntax_getAntiquotTerm(v_stx_653_);
v___x_690_ = l_Lean_Syntax_getId(v___x_689_);
lean_dec(v___x_689_);
v___x_691_ = l_Lean_NameSet_contains(v_snd_679_, v___x_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = l_Lean_NameSet_insert(v_snd_679_, v___x_690_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_692_);
lean_ctor_set(v___x_681_, 0, v___x_683_);
v___x_694_ = v___x_681_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v___x_692_);
v___x_694_ = v_reuseFailAlloc_696_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; 
lean_inc_ref(v___x_694_);
v___x_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
v___y_668_ = v___x_695_;
v_a_669_ = v___x_694_;
goto v___jp_667_;
}
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
lean_dec(v___x_690_);
v___x_697_ = lean_box(v___x_691_);
v___x_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_698_);
v___x_700_ = v___x_681_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_snd_679_);
v___x_700_ = v_reuseFailAlloc_702_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_701_; 
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(lean_object* v___x_705_, uint8_t v_firstChoiceOnly_706_, lean_object* v_as_707_, size_t v_sz_708_, size_t v_i_709_, lean_object* v_b_710_){
_start:
{
uint8_t v___x_711_; 
v___x_711_ = lean_usize_dec_lt(v_i_709_, v_sz_708_);
if (v___x_711_ == 0)
{
return v_b_710_;
}
else
{
lean_object* v_snd_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_730_; 
v_snd_712_ = lean_ctor_get(v_b_710_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_b_710_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; 
v_unused_731_ = lean_ctor_get(v_b_710_, 0);
lean_dec(v_unused_731_);
v___x_714_ = v_b_710_;
v_isShared_715_ = v_isSharedCheck_730_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_snd_712_);
lean_dec(v_b_710_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_730_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_a_716_; lean_object* v___x_717_; 
v_a_716_ = lean_array_uget_borrowed(v_as_707_, v_i_709_);
lean_inc(v_snd_712_);
v___x_717_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_705_, v_firstChoiceOnly_706_, v_a_716_, v_snd_712_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_718_);
v___x_720_ = v___x_714_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_snd_712_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
lean_dec(v_snd_712_);
v_a_722_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_717_, 1);
v___x_723_ = lean_box(0);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v_a_722_);
lean_ctor_set(v___x_714_, 0, v___x_723_);
v___x_725_ = v___x_714_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_a_722_);
v___x_725_ = v_reuseFailAlloc_729_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
size_t v___x_726_; size_t v___x_727_; 
v___x_726_ = ((size_t)1ULL);
v___x_727_ = lean_usize_add(v_i_709_, v___x_726_);
v_i_709_ = v___x_727_;
v_b_710_ = v___x_725_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0___boxed(lean_object* v___x_732_, lean_object* v_firstChoiceOnly_733_, lean_object* v_as_734_, lean_object* v_sz_735_, lean_object* v_i_736_, lean_object* v_b_737_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_738_; size_t v_sz_boxed_739_; size_t v_i_boxed_740_; lean_object* v_res_741_; 
v_firstChoiceOnly_boxed_738_ = lean_unbox(v_firstChoiceOnly_733_);
v_sz_boxed_739_ = lean_unbox_usize(v_sz_735_);
lean_dec(v_sz_735_);
v_i_boxed_740_ = lean_unbox_usize(v_i_736_);
lean_dec(v_i_736_);
v_res_741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v___x_732_, v_firstChoiceOnly_boxed_738_, v_as_734_, v_sz_boxed_739_, v_i_boxed_740_, v_b_737_);
lean_dec_ref(v_as_734_);
lean_dec_ref(v___x_732_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___boxed(lean_object* v___x_742_, lean_object* v_firstChoiceOnly_743_, lean_object* v_stx_744_, lean_object* v_b_745_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_746_; lean_object* v_res_747_; 
v_firstChoiceOnly_boxed_746_ = lean_unbox(v_firstChoiceOnly_743_);
v_res_747_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_742_, v_firstChoiceOnly_boxed_746_, v_stx_744_, v_b_745_);
lean_dec(v_stx_744_);
lean_dec_ref(v___x_742_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(lean_object* v_as_748_, size_t v_sz_749_, size_t v_i_750_, lean_object* v_b_751_){
_start:
{
uint8_t v___x_752_; 
v___x_752_ = lean_usize_dec_lt(v_i_750_, v_sz_749_);
if (v___x_752_ == 0)
{
return v_b_751_;
}
else
{
lean_object* v_snd_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_791_; 
v_snd_753_ = lean_ctor_get(v_b_751_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v_b_751_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v_b_751_, 0);
lean_dec(v_unused_792_);
v___x_755_ = v_b_751_;
v_isShared_756_ = v_isSharedCheck_791_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_snd_753_);
lean_dec(v_b_751_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_791_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_a_757_; lean_object* v___x_758_; uint8_t v_firstChoiceOnly_759_; lean_object* v_stx_760_; lean_object* v___x_761_; lean_object* v___y_763_; lean_object* v___x_787_; 
v_a_757_ = lean_array_uget_borrowed(v_as_748_, v_i_750_);
lean_inc(v_a_757_);
v___x_758_ = l_Lean_Syntax_topDown(v_a_757_, v___x_752_);
v_firstChoiceOnly_759_ = lean_ctor_get_uint8(v___x_758_, sizeof(void*)*1);
v_stx_760_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_stx_760_);
lean_dec_ref(v___x_758_);
v___x_761_ = lean_box(0);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_761_);
v___x_787_ = v___x_755_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_snd_753_);
v___x_787_ = v_reuseFailAlloc_790_;
goto v_reusejp_786_;
}
v___jp_762_:
{
lean_object* v_fst_764_; 
v_fst_764_ = lean_ctor_get(v___y_763_, 0);
if (lean_obj_tag(v_fst_764_) == 0)
{
lean_object* v_snd_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_775_; 
v_snd_765_ = lean_ctor_get(v___y_763_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v___y_763_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v___y_763_, 0);
lean_dec(v_unused_776_);
v___x_767_ = v___y_763_;
v_isShared_768_ = v_isSharedCheck_775_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_snd_765_);
lean_dec(v___y_763_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_775_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_761_);
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_snd_765_);
v___x_770_ = v_reuseFailAlloc_774_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
size_t v___x_771_; size_t v___x_772_; 
v___x_771_ = ((size_t)1ULL);
v___x_772_ = lean_usize_add(v_i_750_, v___x_771_);
v_i_750_ = v___x_772_;
v_b_751_ = v___x_770_;
goto _start;
}
}
}
else
{
lean_object* v_snd_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_inc_ref(v_fst_764_);
v_snd_777_ = lean_ctor_get(v___y_763_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v___y_763_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v___y_763_, 0);
lean_dec(v_unused_785_);
v___x_779_ = v___y_763_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_snd_777_);
lean_dec(v___y_763_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_fst_764_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_snd_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
v_reusejp_786_:
{
lean_object* v___x_788_; lean_object* v_a_789_; 
lean_inc_ref(v___x_787_);
v___x_788_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_787_, v_firstChoiceOnly_759_, v_stx_760_, v___x_787_);
lean_dec(v_stx_760_);
lean_dec_ref(v___x_787_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref(v___x_788_);
v___y_763_ = v_a_789_;
goto v___jp_762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1___boxed(lean_object* v_as_793_, lean_object* v_sz_794_, lean_object* v_i_795_, lean_object* v_b_796_){
_start:
{
size_t v_sz_boxed_797_; size_t v_i_boxed_798_; lean_object* v_res_799_; 
v_sz_boxed_797_ = lean_unbox_usize(v_sz_794_);
lean_dec(v_sz_794_);
v_i_boxed_798_ = lean_unbox_usize(v_i_795_);
lean_dec(v_i_795_);
v_res_799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(v_as_793_, v_sz_boxed_797_, v_i_boxed_798_, v_b_796_);
lean_dec_ref(v_as_793_);
return v_res_799_;
}
}
static lean_object* _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0(void){
_start:
{
lean_object* v_seen_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_seen_800_ = l_Lean_NameSet_empty;
v___x_801_ = lean_box(0);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
lean_ctor_set(v___x_802_, 1, v_seen_800_);
return v___x_802_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_hasDuplicateAntiquot(lean_object* v_stxs_803_){
_start:
{
lean_object* v___x_804_; size_t v_sz_805_; size_t v___x_806_; lean_object* v___x_807_; lean_object* v_fst_808_; 
v___x_804_ = lean_obj_once(&l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0, &l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0_once, _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0);
v_sz_805_ = lean_array_size(v_stxs_803_);
v___x_806_ = ((size_t)0ULL);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(v_stxs_803_, v_sz_805_, v___x_806_, v___x_804_);
v_fst_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_fst_808_);
lean_dec_ref(v___x_807_);
if (lean_obj_tag(v_fst_808_) == 0)
{
uint8_t v___x_809_; 
v___x_809_ = 0;
return v___x_809_;
}
else
{
lean_object* v_val_810_; uint8_t v___x_811_; 
v_val_810_ = lean_ctor_get(v_fst_808_, 0);
lean_inc(v_val_810_);
lean_dec_ref_known(v_fst_808_, 1);
v___x_811_ = lean_unbox(v_val_810_);
lean_dec(v_val_810_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___boxed(lean_object* v_stxs_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l_Lean_Elab_Command_hasDuplicateAntiquot(v_stxs_812_);
lean_dec_ref(v_stxs_812_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__4(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__3));
v___x_822_ = l_String_toRawSubstring_x27(v___x_821_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__15(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__14));
v___x_844_ = l_String_toRawSubstring_x27(v___x_843_);
return v___x_844_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__19(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__18));
v___x_850_ = l_String_toRawSubstring_x27(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__22(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__21));
v___x_855_ = l_String_toRawSubstring_x27(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__40(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__39));
v___x_893_ = l_String_toRawSubstring_x27(v___x_892_);
return v___x_893_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__47(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__46));
v___x_908_ = l_String_toRawSubstring_x27(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__55(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_924_ = l_String_toRawSubstring_x27(v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander(lean_object* v_attrKind_962_, lean_object* v_pat_963_, lean_object* v_qrhs_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v___y_968_; lean_object* v_fst_972_; lean_object* v_snd_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
lean_inc(v_qrhs_964_);
v___x_1169_ = l_Lean_Syntax_isOfKind(v_qrhs_964_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_qrhs_964_);
v___x_1171_ = l_Lean_Syntax_isOfKind(v_qrhs_964_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec(v_qrhs_964_);
lean_dec(v_pat_963_);
lean_dec(v_attrKind_962_);
v___x_1172_ = lean_box(0);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v_a_966_);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; 
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__68));
v_fst_972_ = v_qrhs_964_;
v_snd_973_ = v___x_1174_;
v___y_974_ = v_a_965_;
v___y_975_ = v_a_966_;
goto v___jp_971_;
}
}
else
{
lean_object* v___x_1175_; lean_object* v_c_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1175_ = lean_unsigned_to_nat(0u);
v_c_1176_ = l_Lean_Syntax_getArg(v_qrhs_964_, v___x_1175_);
v___x_1177_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_c_1176_);
v___x_1178_ = l_Lean_Syntax_isOfKind(v_c_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec(v_c_1176_);
lean_dec(v_qrhs_964_);
lean_dec(v_pat_963_);
lean_dec(v_attrKind_962_);
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v_a_966_);
return v___x_1180_;
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v_args_1183_; 
v___x_1181_ = lean_unsigned_to_nat(1u);
v___x_1182_ = l_Lean_Syntax_getArg(v_qrhs_964_, v___x_1181_);
lean_dec(v_qrhs_964_);
v_args_1183_ = l_Lean_Syntax_getArgs(v___x_1182_);
lean_dec(v___x_1182_);
v_fst_972_ = v_c_1176_;
v_snd_973_ = v_args_1183_;
v___y_974_ = v_a_965_;
v___y_975_ = v_a_966_;
goto v___jp_971_;
}
}
v___jp_967_:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_box(0);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v___y_968_);
return v___x_970_;
}
v___jp_971_:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = l_Lean_TSyntax_getId(v_fst_972_);
lean_dec(v_fst_972_);
v___x_977_ = l_Lean_Macro_resolveGlobalName(v___x_976_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
if (lean_obj_tag(v_a_978_) == 1)
{
lean_object* v_head_979_; lean_object* v_snd_980_; 
v_head_979_ = lean_ctor_get(v_a_978_, 0);
lean_inc(v_head_979_);
v_snd_980_ = lean_ctor_get(v_head_979_, 1);
lean_inc(v_snd_980_);
if (lean_obj_tag(v_snd_980_) == 0)
{
lean_object* v_tail_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1155_; 
v_tail_981_ = lean_ctor_get(v_a_978_, 1);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_a_978_);
if (v_isSharedCheck_1155_ == 0)
{
lean_object* v_unused_1156_; 
v_unused_1156_ = lean_ctor_get(v_a_978_, 0);
lean_dec(v_unused_1156_);
v___x_983_ = v_a_978_;
v_isShared_984_ = v_isSharedCheck_1155_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_tail_981_);
lean_dec(v_a_978_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1155_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
if (lean_obj_tag(v_tail_981_) == 0)
{
lean_object* v_a_985_; lean_object* v_fst_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1152_; 
v_a_985_ = lean_ctor_get(v___x_977_, 1);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_977_, 2);
v_fst_986_ = lean_ctor_get(v_head_979_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_head_979_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; 
v_unused_1153_ = lean_ctor_get(v_head_979_, 1);
lean_dec(v_unused_1153_);
v___x_988_ = v_head_979_;
v_isShared_989_ = v_isSharedCheck_1152_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_fst_986_);
lean_dec(v_head_979_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1152_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
size_t v_sz_990_; size_t v___x_991_; lean_object* v___x_992_; 
v_sz_990_ = lean_array_size(v_snd_973_);
v___x_991_ = ((size_t)0ULL);
v___x_992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_990_, v___x_991_, v_snd_973_, v___y_974_, v_a_985_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1142_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_a_994_ = lean_ctor_get(v___x_992_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_996_ = v___x_992_;
v_isShared_997_ = v_isSharedCheck_1142_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1142_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
uint8_t v___x_998_; 
v___x_998_ = l_Lean_Elab_Command_hasDuplicateAntiquot(v_a_993_);
if (v___x_998_ == 0)
{
lean_object* v_quotContext_999_; lean_object* v_currMacroScope_1000_; lean_object* v_ref_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
v_quotContext_999_ = lean_ctor_get(v___y_974_, 1);
v_currMacroScope_1000_ = lean_ctor_get(v___y_974_, 2);
v_ref_1001_ = lean_ctor_get(v___y_974_, 5);
v___x_1002_ = l_Lean_SourceInfo_fromRef(v_ref_1001_, v___x_998_);
v___x_1003_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0));
v___x_1004_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__1));
v___x_1005_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__2));
lean_inc(v___x_1002_);
if (v_isShared_989_ == 0)
{
lean_ctor_set_tag(v___x_988_, 2);
lean_ctor_set(v___x_988_, 1, v___x_1005_);
lean_ctor_set(v___x_988_, 0, v___x_1002_);
v___x_1007_ = v___x_988_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_1009_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
lean_inc_n(v___x_1002_, 18);
v___x_1010_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1002_);
lean_ctor_set(v___x_1010_, 1, v___x_1008_);
lean_ctor_set(v___x_1010_, 2, v___x_1009_);
v___x_1011_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__4, &l_Lean_Elab_Command_mkUnexpander___closed__4_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__4);
v___x_1012_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__5));
lean_inc_n(v_currMacroScope_1000_, 4);
lean_inc_n(v_quotContext_999_, 4);
v___x_1013_ = l_Lean_addMacroScope(v_quotContext_999_, v___x_1012_, v_currMacroScope_1000_);
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1002_);
lean_ctor_set(v___x_1015_, 1, v___x_1011_);
lean_ctor_set(v___x_1015_, 2, v___x_1013_);
lean_ctor_set(v___x_1015_, 3, v___x_1014_);
v___x_1016_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__7));
v___x_1017_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
v___x_1018_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1002_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1002_);
lean_ctor_set(v___x_1019_, 1, v___x_1003_);
lean_inc_ref(v___x_1018_);
v___x_1020_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1016_, v___x_1018_, v___x_1019_);
lean_inc_ref(v___x_1015_);
lean_inc_ref(v___x_1010_);
v___x_1021_ = l_Lean_Syntax_node4(v___x_1002_, v___x_1004_, v___x_1007_, v___x_1010_, v___x_1015_, v___x_1020_);
v___x_1022_ = l_Lean_Syntax_mkApp(v___x_1021_, v_a_993_);
lean_inc(v_attrKind_962_);
v___x_1023_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_962_);
v___x_1024_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__9));
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__10));
v___x_1026_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
v___x_1027_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
v___x_1028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1002_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
v___x_1030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
v___x_1031_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__15, &l_Lean_Elab_Command_mkUnexpander___closed__15_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__15);
v___x_1032_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__16));
v___x_1033_ = l_Lean_addMacroScope(v_quotContext_999_, v___x_1032_, v_currMacroScope_1000_);
v___x_1034_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1002_);
lean_ctor_set(v___x_1034_, 1, v___x_1031_);
lean_ctor_set(v___x_1034_, 2, v___x_1033_);
lean_ctor_set(v___x_1034_, 3, v___x_1014_);
v___x_1035_ = l_Lean_mkIdent(v_fst_986_);
lean_inc(v___x_1035_);
v___x_1036_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1035_);
v___x_1037_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1030_, v___x_1034_, v___x_1036_);
v___x_1038_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1029_, v_attrKind_962_, v___x_1037_);
v___x_1039_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1038_);
v___x_1040_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
v___x_1041_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1002_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = l_Lean_Syntax_node3(v___x_1002_, v___x_1026_, v___x_1028_, v___x_1039_, v___x_1041_);
v___x_1043_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1002_);
lean_ctor_set(v___x_1044_, 1, v___x_1024_);
v___x_1045_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__19, &l_Lean_Elab_Command_mkUnexpander___closed__19_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__19);
v___x_1046_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__20));
v___x_1047_ = l_Lean_addMacroScope(v_quotContext_999_, v___x_1046_, v_currMacroScope_1000_);
v___x_1048_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1002_);
lean_ctor_set(v___x_1048_, 1, v___x_1045_);
lean_ctor_set(v___x_1048_, 2, v___x_1047_);
lean_ctor_set(v___x_1048_, 3, v___x_1014_);
v___x_1049_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1008_, v___x_1048_, v___x_1035_);
v___x_1050_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__22, &l_Lean_Elab_Command_mkUnexpander___closed__22_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__22);
v___x_1051_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__25));
v___x_1052_ = l_Lean_addMacroScope(v_quotContext_999_, v___x_1051_, v_currMacroScope_1000_);
v___x_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v_snd_980_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 1, v___x_1014_);
lean_ctor_set(v___x_983_, 0, v___x_1053_);
v___x_1055_ = v___x_983_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___x_1014_);
v___x_1055_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
lean_inc_n(v___x_1002_, 31);
v___x_1056_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1002_);
lean_ctor_set(v___x_1056_, 1, v___x_1050_);
lean_ctor_set(v___x_1056_, 2, v___x_1052_);
lean_ctor_set(v___x_1056_, 3, v___x_1055_);
v___x_1057_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_1058_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1002_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__27));
v___x_1060_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__28));
v___x_1061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1002_);
lean_ctor_set(v___x_1061_, 1, v___x_1059_);
v___x_1062_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__30));
v___x_1063_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__32));
v___x_1064_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
v___x_1065_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1002_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__35));
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
v___x_1068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1002_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_1070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1002_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
lean_inc_ref_n(v___x_1070_, 2);
lean_inc_ref(v___x_1068_);
v___x_1071_ = l_Lean_Syntax_node3(v___x_1002_, v___x_1066_, v___x_1068_, v___x_1022_, v___x_1070_);
v___x_1072_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1071_);
v___x_1073_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1072_);
v___x_1074_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
v___x_1075_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1002_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
v___x_1077_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__40, &l_Lean_Elab_Command_mkUnexpander___closed__40_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__40);
v___x_1078_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__41));
lean_inc_n(v_currMacroScope_1000_, 3);
lean_inc_n(v_quotContext_999_, 3);
v___x_1079_ = l_Lean_addMacroScope(v_quotContext_999_, v___x_1078_, v_currMacroScope_1000_);
v___x_1080_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__42));
v___x_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v_snd_980_);
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v___x_1014_);
v___x_1083_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1002_);
lean_ctor_set(v___x_1083_, 1, v___x_1077_);
lean_ctor_set(v___x_1083_, 2, v___x_1079_);
lean_ctor_set(v___x_1083_, 3, v___x_1082_);
v___x_1084_ = l_Lean_Syntax_node3(v___x_1002_, v___x_1066_, v___x_1068_, v_pat_963_, v___x_1070_);
v___x_1085_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1008_, v___x_1015_, v___x_1084_);
v___x_1086_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1076_, v___x_1083_, v___x_1085_);
lean_inc_ref(v___x_1075_);
lean_inc_ref(v___x_1065_);
v___x_1087_ = l_Lean_Syntax_node4(v___x_1002_, v___x_1063_, v___x_1065_, v___x_1073_, v___x_1075_, v___x_1086_);
v___x_1088_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__44));
v___x_1089_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__45));
v___x_1090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1002_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1088_, v___x_1090_);
v___x_1092_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1091_);
v___x_1093_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1092_);
v___x_1094_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__47, &l_Lean_Elab_Command_mkUnexpander___closed__47_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__47);
v___x_1095_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__48));
v___x_1096_ = l_Lean_addMacroScope(v_quotContext_999_, v___x_1095_, v_currMacroScope_1000_);
v___x_1097_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__50));
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v_snd_980_);
v___x_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v___x_1014_);
v___x_1100_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1002_);
lean_ctor_set(v___x_1100_, 1, v___x_1094_);
lean_ctor_set(v___x_1100_, 2, v___x_1096_);
lean_ctor_set(v___x_1100_, 3, v___x_1099_);
v___x_1101_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__52));
v___x_1102_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__3));
v___x_1103_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
v___x_1104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1002_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__5));
v___x_1106_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__55, &l_Lean_Elab_Command_mkUnexpander___closed__55_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__55);
v___x_1107_ = lean_box(0);
v___x_1108_ = l_Lean_addMacroScope(v_quotContext_999_, v___x_1107_, v_currMacroScope_1000_);
v___x_1109_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__67));
v___x_1110_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1002_);
lean_ctor_set(v___x_1110_, 1, v___x_1106_);
lean_ctor_set(v___x_1110_, 2, v___x_1108_);
lean_ctor_set(v___x_1110_, 3, v___x_1109_);
v___x_1111_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1105_, v___x_1110_);
v___x_1112_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1102_, v___x_1104_, v___x_1111_);
lean_inc_ref(v___x_1010_);
v___x_1113_ = l_Lean_Syntax_node3(v___x_1002_, v___x_1101_, v___x_1112_, v___x_1010_, v___x_1070_);
v___x_1114_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1113_);
v___x_1115_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1076_, v___x_1100_, v___x_1114_);
v___x_1116_ = l_Lean_Syntax_node4(v___x_1002_, v___x_1063_, v___x_1065_, v___x_1093_, v___x_1075_, v___x_1115_);
v___x_1117_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1008_, v___x_1087_, v___x_1116_);
v___x_1118_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1062_, v___x_1117_);
v___x_1119_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1060_, v___x_1061_, v___x_1118_);
v___x_1120_ = lean_unsigned_to_nat(9u);
v___x_1121_ = lean_mk_empty_array_with_capacity(v___x_1120_);
v___x_1122_ = lean_array_push(v___x_1121_, v___x_1010_);
v___x_1123_ = lean_array_push(v___x_1122_, v___x_1043_);
v___x_1124_ = lean_array_push(v___x_1123_, v___x_1023_);
v___x_1125_ = lean_array_push(v___x_1124_, v___x_1044_);
v___x_1126_ = lean_array_push(v___x_1125_, v___x_1049_);
v___x_1127_ = lean_array_push(v___x_1126_, v___x_1018_);
v___x_1128_ = lean_array_push(v___x_1127_, v___x_1056_);
v___x_1129_ = lean_array_push(v___x_1128_, v___x_1058_);
v___x_1130_ = lean_array_push(v___x_1129_, v___x_1119_);
v___x_1131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1002_);
lean_ctor_set(v___x_1131_, 1, v___x_1025_);
lean_ctor_set(v___x_1131_, 2, v___x_1130_);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1132_);
v___x_1134_ = v___x_996_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_a_994_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
lean_dec(v_a_993_);
lean_del_object(v___x_988_);
lean_dec(v_fst_986_);
lean_del_object(v___x_983_);
lean_dec(v_pat_963_);
lean_dec(v_attrKind_962_);
v___x_1138_ = lean_box(0);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1138_);
v___x_1140_ = v___x_996_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_a_994_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_del_object(v___x_988_);
lean_dec(v_fst_986_);
lean_del_object(v___x_983_);
lean_dec(v_pat_963_);
lean_dec(v_attrKind_962_);
v_a_1143_ = lean_ctor_get(v___x_992_, 0);
v_a_1144_ = lean_ctor_get(v___x_992_, 1);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_992_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_inc(v_a_1143_);
lean_dec(v___x_992_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1143_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
else
{
lean_object* v_a_1154_; 
lean_del_object(v___x_983_);
lean_dec(v_tail_981_);
lean_dec(v_head_979_);
lean_dec_ref(v_snd_973_);
lean_dec(v_pat_963_);
lean_dec(v_attrKind_962_);
v_a_1154_ = lean_ctor_get(v___x_977_, 1);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_977_, 2);
v___y_968_ = v_a_1154_;
goto v___jp_967_;
}
}
}
else
{
lean_object* v_a_1157_; 
lean_dec(v_snd_980_);
lean_dec(v_head_979_);
lean_dec_ref_known(v_a_978_, 2);
lean_dec_ref(v_snd_973_);
lean_dec(v_pat_963_);
lean_dec(v_attrKind_962_);
v_a_1157_ = lean_ctor_get(v___x_977_, 1);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_977_, 2);
v___y_968_ = v_a_1157_;
goto v___jp_967_;
}
}
else
{
lean_object* v_a_1158_; 
lean_dec(v_a_978_);
lean_dec_ref(v_snd_973_);
lean_dec(v_pat_963_);
lean_dec(v_attrKind_962_);
v_a_1158_ = lean_ctor_get(v___x_977_, 1);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_977_, 2);
v___y_968_ = v_a_1158_;
goto v___jp_967_;
}
}
else
{
lean_object* v_a_1159_; lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec_ref(v_snd_973_);
lean_dec(v_pat_963_);
lean_dec(v_attrKind_962_);
v_a_1159_ = lean_ctor_get(v___x_977_, 0);
v_a_1160_ = lean_ctor_get(v___x_977_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_977_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_inc(v_a_1159_);
lean_dec(v___x_977_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1159_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander___boxed(lean_object* v_attrKind_1184_, lean_object* v_pat_1185_, lean_object* v_qrhs_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Elab_Command_mkUnexpander(v_attrKind_1184_, v_pat_1185_, v_qrhs_1186_, v_a_1187_, v_a_1188_);
lean_dec_ref(v_a_1187_);
return v_res_1189_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = lean_box(0);
v___x_1191_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v___x_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg(){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0);
v___x_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___boxed(lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(lean_object* v_00_u03b1_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___boxed(lean_object* v_00_u03b1_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(v_00_u03b1_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; lean_object* v_env_1211_; lean_object* v___x_1212_; lean_object* v_mainModule_1213_; lean_object* v___x_1214_; 
v___x_1210_ = lean_st_ref_get(v___y_1208_);
v_env_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc_ref(v_env_1211_);
lean_dec(v___x_1210_);
v___x_1212_ = l_Lean_Environment_header(v_env_1211_);
lean_dec_ref(v_env_1211_);
v_mainModule_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_mainModule_1213_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_mainModule_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg___boxed(lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_1215_);
lean_dec(v___y_1215_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_1219_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___boxed(lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___lam__0(lean_object* v___x_1226_, lean_object* v_sc_1227_){
_start:
{
lean_object* v_header_1228_; lean_object* v_currNamespace_1229_; lean_object* v_openDecls_1230_; lean_object* v_levelNames_1231_; lean_object* v_varDecls_1232_; lean_object* v_varUIds_1233_; lean_object* v_includedVars_1234_; lean_object* v_omittedVars_1235_; uint8_t v_isNoncomputable_1236_; uint8_t v_isPublic_1237_; uint8_t v_isMeta_1238_; lean_object* v_attrs_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
v_header_1228_ = lean_ctor_get(v_sc_1227_, 0);
v_currNamespace_1229_ = lean_ctor_get(v_sc_1227_, 2);
v_openDecls_1230_ = lean_ctor_get(v_sc_1227_, 3);
v_levelNames_1231_ = lean_ctor_get(v_sc_1227_, 4);
v_varDecls_1232_ = lean_ctor_get(v_sc_1227_, 5);
v_varUIds_1233_ = lean_ctor_get(v_sc_1227_, 6);
v_includedVars_1234_ = lean_ctor_get(v_sc_1227_, 7);
v_omittedVars_1235_ = lean_ctor_get(v_sc_1227_, 8);
v_isNoncomputable_1236_ = lean_ctor_get_uint8(v_sc_1227_, sizeof(void*)*10);
v_isPublic_1237_ = lean_ctor_get_uint8(v_sc_1227_, sizeof(void*)*10 + 1);
v_isMeta_1238_ = lean_ctor_get_uint8(v_sc_1227_, sizeof(void*)*10 + 2);
v_attrs_1239_ = lean_ctor_get(v_sc_1227_, 9);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_sc_1227_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v_sc_1227_, 1);
lean_dec(v_unused_1247_);
v___x_1241_ = v_sc_1227_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_attrs_1239_);
lean_inc(v_omittedVars_1235_);
lean_inc(v_includedVars_1234_);
lean_inc(v_varUIds_1233_);
lean_inc(v_varDecls_1232_);
lean_inc(v_levelNames_1231_);
lean_inc(v_openDecls_1230_);
lean_inc(v_currNamespace_1229_);
lean_inc(v_header_1228_);
lean_dec(v_sc_1227_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v___x_1226_);
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_header_1228_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_currNamespace_1229_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_openDecls_1230_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v_levelNames_1231_);
lean_ctor_set(v_reuseFailAlloc_1245_, 5, v_varDecls_1232_);
lean_ctor_set(v_reuseFailAlloc_1245_, 6, v_varUIds_1233_);
lean_ctor_set(v_reuseFailAlloc_1245_, 7, v_includedVars_1234_);
lean_ctor_set(v_reuseFailAlloc_1245_, 8, v_omittedVars_1235_);
lean_ctor_set(v_reuseFailAlloc_1245_, 9, v_attrs_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1245_, sizeof(void*)*10, v_isNoncomputable_1236_);
lean_ctor_set_uint8(v_reuseFailAlloc_1245_, sizeof(void*)*10 + 1, v_isPublic_1237_);
lean_ctor_set_uint8(v_reuseFailAlloc_1245_, sizeof(void*)*10 + 2, v_isMeta_1238_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(size_t v_sz_1248_, size_t v_i_1249_, lean_object* v_bs_1250_){
_start:
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_usize_dec_lt(v_i_1249_, v_sz_1248_);
if (v___x_1251_ == 0)
{
return v_bs_1250_;
}
else
{
lean_object* v_v_1252_; lean_object* v___x_1253_; lean_object* v_bs_x27_1254_; size_t v___x_1255_; size_t v___x_1256_; lean_object* v___x_1257_; 
v_v_1252_ = lean_array_uget(v_bs_1250_, v_i_1249_);
v___x_1253_ = lean_unsigned_to_nat(0u);
v_bs_x27_1254_ = lean_array_uset(v_bs_1250_, v_i_1249_, v___x_1253_);
v___x_1255_ = ((size_t)1ULL);
v___x_1256_ = lean_usize_add(v_i_1249_, v___x_1255_);
v___x_1257_ = lean_array_uset(v_bs_x27_1254_, v_i_1249_, v_v_1252_);
v_i_1249_ = v___x_1256_;
v_bs_1250_ = v___x_1257_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3___boxed(lean_object* v_sz_1259_, lean_object* v_i_1260_, lean_object* v_bs_1261_){
_start:
{
size_t v_sz_boxed_1262_; size_t v_i_boxed_1263_; lean_object* v_res_1264_; 
v_sz_boxed_1262_ = lean_unbox_usize(v_sz_1259_);
lean_dec(v_sz_1259_);
v_i_boxed_1263_ = lean_unbox_usize(v_i_1260_);
lean_dec(v_i_1260_);
v_res_1264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_boxed_1262_, v_i_boxed_1263_, v_bs_1261_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(size_t v_sz_1265_, size_t v_i_1266_, lean_object* v_bs_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_usize_dec_lt(v_i_1266_, v_sz_1265_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v_bs_1267_);
lean_ctor_set(v___x_1271_, 1, v___y_1269_);
return v___x_1271_;
}
else
{
lean_object* v_v_1272_; lean_object* v___x_1273_; 
v_v_1272_ = lean_array_uget_borrowed(v_bs_1267_, v_i_1266_);
lean_inc(v_v_1272_);
v___x_1273_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(v_v_1272_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v_a_1275_; lean_object* v___x_1276_; lean_object* v_bs_x27_1277_; size_t v___x_1278_; size_t v___x_1279_; lean_object* v___x_1280_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
v_a_1275_ = lean_ctor_get(v___x_1273_, 1);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1273_, 2);
v___x_1276_ = lean_unsigned_to_nat(0u);
v_bs_x27_1277_ = lean_array_uset(v_bs_1267_, v_i_1266_, v___x_1276_);
v___x_1278_ = ((size_t)1ULL);
v___x_1279_ = lean_usize_add(v_i_1266_, v___x_1278_);
v___x_1280_ = lean_array_uset(v_bs_x27_1277_, v_i_1266_, v_a_1274_);
v_i_1266_ = v___x_1279_;
v_bs_1267_ = v___x_1280_;
v___y_1269_ = v_a_1275_;
goto _start;
}
else
{
lean_object* v_a_1282_; lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec_ref(v_bs_1267_);
v_a_1282_ = lean_ctor_get(v___x_1273_, 0);
v_a_1283_ = lean_ctor_get(v___x_1273_, 1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1273_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_inc(v_a_1282_);
lean_dec(v___x_1273_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1282_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed(lean_object* v_sz_1291_, lean_object* v_i_1292_, lean_object* v_bs_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
size_t v_sz_boxed_1296_; size_t v_i_boxed_1297_; lean_object* v_res_1298_; 
v_sz_boxed_1296_ = lean_unbox_usize(v_sz_1291_);
lean_dec(v_sz_1291_);
v_i_boxed_1297_ = lean_unbox_usize(v_i_1292_);
lean_dec(v_i_1292_);
v_res_1298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(v_sz_boxed_1296_, v_i_boxed_1297_, v_bs_1293_, v___y_1294_, v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(lean_object* v_o_1302_, lean_object* v_k_1303_, uint8_t v_v_1304_){
_start:
{
lean_object* v_map_1305_; uint8_t v_hasTrace_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1320_; 
v_map_1305_ = lean_ctor_get(v_o_1302_, 0);
v_hasTrace_1306_ = lean_ctor_get_uint8(v_o_1302_, sizeof(void*)*1);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_o_1302_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1308_ = v_o_1302_;
v_isShared_1309_ = v_isSharedCheck_1320_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_map_1305_);
lean_dec(v_o_1302_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1320_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1310_, 0, v_v_1304_);
lean_inc(v_k_1303_);
v___x_1311_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1303_, v___x_1310_, v_map_1305_);
if (v_hasTrace_1306_ == 0)
{
lean_object* v___x_1312_; uint8_t v___x_1313_; lean_object* v___x_1315_; 
v___x_1312_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
v___x_1313_ = l_Lean_Name_isPrefixOf(v___x_1312_, v_k_1303_);
lean_dec(v_k_1303_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1311_);
v___x_1315_ = v___x_1308_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1311_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*1, v___x_1313_);
return v___x_1315_;
}
}
else
{
lean_object* v___x_1318_; 
lean_dec(v_k_1303_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1311_);
v___x_1318_ = v___x_1308_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1311_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*1, v_hasTrace_1306_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___boxed(lean_object* v_o_1321_, lean_object* v_k_1322_, lean_object* v_v_1323_){
_start:
{
uint8_t v_v_boxed_1324_; lean_object* v_res_1325_; 
v_v_boxed_1324_ = lean_unbox(v_v_1323_);
v_res_1325_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(v_o_1321_, v_k_1322_, v_v_boxed_1324_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(lean_object* v_opts_1326_, lean_object* v_opt_1327_, uint8_t v_val_1328_){
_start:
{
lean_object* v_name_1329_; lean_object* v___x_1330_; 
v_name_1329_ = lean_ctor_get(v_opt_1327_, 0);
lean_inc(v_name_1329_);
lean_dec_ref(v_opt_1327_);
v___x_1330_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(v_opts_1326_, v_name_1329_, v_val_1328_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6___boxed(lean_object* v_opts_1331_, lean_object* v_opt_1332_, lean_object* v_val_1333_){
_start:
{
uint8_t v_val_boxed_1334_; lean_object* v_res_1335_; 
v_val_boxed_1334_ = lean_unbox(v_val_1333_);
v_res_1335_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_1331_, v_opt_1332_, v_val_boxed_1334_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(size_t v_sz_1336_, size_t v_i_1337_, lean_object* v_bs_1338_, lean_object* v___y_1339_){
_start:
{
uint8_t v___x_1340_; 
v___x_1340_ = lean_usize_dec_lt(v_i_1337_, v_sz_1336_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_bs_1338_);
lean_ctor_set(v___x_1341_, 1, v___y_1339_);
return v___x_1341_;
}
else
{
lean_object* v_v_1342_; lean_object* v___x_1343_; 
v_v_1342_ = lean_array_uget_borrowed(v_bs_1338_, v_i_1337_);
lean_inc(v_v_1342_);
v___x_1343_ = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(v_v_1342_, v___y_1339_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v_a_1345_; lean_object* v___x_1346_; lean_object* v_bs_x27_1347_; size_t v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
v_a_1345_ = lean_ctor_get(v___x_1343_, 1);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1343_, 2);
v___x_1346_ = lean_unsigned_to_nat(0u);
v_bs_x27_1347_ = lean_array_uset(v_bs_1338_, v_i_1337_, v___x_1346_);
v___x_1348_ = ((size_t)1ULL);
v___x_1349_ = lean_usize_add(v_i_1337_, v___x_1348_);
v___x_1350_ = lean_array_uset(v_bs_x27_1347_, v_i_1337_, v_a_1344_);
v_i_1337_ = v___x_1349_;
v_bs_1338_ = v___x_1350_;
v___y_1339_ = v_a_1345_;
goto _start;
}
else
{
lean_object* v_a_1352_; lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref(v_bs_1338_);
v_a_1352_ = lean_ctor_get(v___x_1343_, 0);
v_a_1353_ = lean_ctor_get(v___x_1343_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1343_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_inc(v_a_1352_);
lean_dec(v___x_1343_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1352_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg___boxed(lean_object* v_sz_1361_, lean_object* v_i_1362_, lean_object* v_bs_1363_, lean_object* v___y_1364_){
_start:
{
size_t v_sz_boxed_1365_; size_t v_i_boxed_1366_; lean_object* v_res_1367_; 
v_sz_boxed_1365_ = lean_unbox_usize(v_sz_1361_);
lean_dec(v_sz_1361_);
v_i_boxed_1366_ = lean_unbox_usize(v_i_1362_);
lean_dec(v_i_1362_);
v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(v_sz_boxed_1365_, v_i_boxed_1366_, v_bs_1363_, v___y_1364_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(size_t v_sz_1368_, size_t v_i_1369_, lean_object* v_bs_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(v_sz_1368_, v_i_1369_, v_bs_1370_, v___y_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed(lean_object* v_sz_1374_, lean_object* v_i_1375_, lean_object* v_bs_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
size_t v_sz_boxed_1379_; size_t v_i_boxed_1380_; lean_object* v_res_1381_; 
v_sz_boxed_1379_ = lean_unbox_usize(v_sz_1374_);
lean_dec(v_sz_1374_);
v_i_boxed_1380_ = lean_unbox_usize(v_i_1375_);
lean_dec(v_i_1375_);
v_res_1381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(v_sz_boxed_1379_, v_i_boxed_1380_, v_bs_1376_, v___y_1377_, v___y_1378_);
lean_dec_ref(v___y_1377_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(lean_object* v_env_1382_, lean_object* v_currNamespace_1383_, lean_object* v_openDecls_1384_, lean_object* v_n_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = l_Lean_ResolveName_resolveNamespace(v_env_1382_, v_currNamespace_1383_, v_openDecls_1384_, v_n_1385_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
lean_ctor_set(v___x_1389_, 1, v___y_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed(lean_object* v_env_1390_, lean_object* v_currNamespace_1391_, lean_object* v_openDecls_1392_, lean_object* v_n_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(v_env_1390_, v_currNamespace_1391_, v_openDecls_1392_, v_n_1393_, v___y_1394_, v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1396_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1397_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
lean_ctor_set(v___x_1402_, 2, v___x_1401_);
lean_ctor_set(v___x_1402_, 3, v___x_1401_);
lean_ctor_set(v___x_1402_, 4, v___x_1400_);
lean_ctor_set(v___x_1402_, 5, v___x_1400_);
lean_ctor_set(v___x_1402_, 6, v___x_1400_);
lean_ctor_set(v___x_1402_, 7, v___x_1400_);
lean_ctor_set(v___x_1402_, 8, v___x_1400_);
lean_ctor_set(v___x_1402_, 9, v___x_1400_);
lean_ctor_set(v___x_1402_, 10, v___x_1400_);
return v___x_1402_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = lean_unsigned_to_nat(32u);
v___x_1404_ = lean_mk_empty_array_with_capacity(v___x_1403_);
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4(void){
_start:
{
size_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1406_ = ((size_t)5ULL);
v___x_1407_ = lean_unsigned_to_nat(0u);
v___x_1408_ = lean_unsigned_to_nat(32u);
v___x_1409_ = lean_mk_empty_array_with_capacity(v___x_1408_);
v___x_1410_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3);
v___x_1411_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v___x_1409_);
lean_ctor_set(v___x_1411_, 2, v___x_1407_);
lean_ctor_set(v___x_1411_, 3, v___x_1407_);
lean_ctor_set_usize(v___x_1411_, 4, v___x_1406_);
return v___x_1411_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1412_ = lean_box(1);
v___x_1413_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4);
v___x_1414_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_1415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
lean_ctor_set(v___x_1415_, 1, v___x_1413_);
lean_ctor_set(v___x_1415_, 2, v___x_1412_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; lean_object* v_env_1420_; lean_object* v___x_1421_; lean_object* v_scopes_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v_opts_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1419_ = lean_st_ref_get(v___y_1417_);
v_env_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc_ref(v_env_1420_);
lean_dec(v___x_1419_);
v___x_1421_ = lean_st_ref_get(v___y_1417_);
v_scopes_1422_ = lean_ctor_get(v___x_1421_, 2);
lean_inc(v_scopes_1422_);
lean_dec(v___x_1421_);
v___x_1423_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1424_ = l_List_head_x21___redArg(v___x_1423_, v_scopes_1422_);
lean_dec(v_scopes_1422_);
v_opts_1425_ = lean_ctor_get(v___x_1424_, 1);
lean_inc_ref(v_opts_1425_);
lean_dec(v___x_1424_);
v___x_1426_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_1427_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5);
v___x_1428_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1428_, 0, v_env_1420_);
lean_ctor_set(v___x_1428_, 1, v___x_1426_);
lean_ctor_set(v___x_1428_, 2, v___x_1427_);
lean_ctor_set(v___x_1428_, 3, v_opts_1425_);
v___x_1429_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
lean_ctor_set(v___x_1429_, 1, v_msgData_1416_);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msgData_1431_, v___y_1432_);
lean_dec(v___y_1432_);
return v_res_1434_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1435_; double v___x_1436_; 
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = lean_float_of_nat(v___x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(lean_object* v_cls_1439_, lean_object* v_msg_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_Elab_Command_getRef___redArg(v___y_1441_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1494_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v___x_1446_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msg_1440_, v___y_1442_);
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1449_ = v___x_1446_;
v_isShared_1450_ = v_isSharedCheck_1494_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1446_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1494_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v_traceState_1452_; lean_object* v_env_1453_; lean_object* v_messages_1454_; lean_object* v_scopes_1455_; lean_object* v_usedQuotCtxts_1456_; lean_object* v_nextMacroScope_1457_; lean_object* v_maxRecDepth_1458_; lean_object* v_ngen_1459_; lean_object* v_auxDeclNGen_1460_; lean_object* v_infoState_1461_; lean_object* v_snapshotTasks_1462_; lean_object* v_prevLinterStates_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1493_; 
v___x_1451_ = lean_st_ref_take(v___y_1442_);
v_traceState_1452_ = lean_ctor_get(v___x_1451_, 9);
v_env_1453_ = lean_ctor_get(v___x_1451_, 0);
v_messages_1454_ = lean_ctor_get(v___x_1451_, 1);
v_scopes_1455_ = lean_ctor_get(v___x_1451_, 2);
v_usedQuotCtxts_1456_ = lean_ctor_get(v___x_1451_, 3);
v_nextMacroScope_1457_ = lean_ctor_get(v___x_1451_, 4);
v_maxRecDepth_1458_ = lean_ctor_get(v___x_1451_, 5);
v_ngen_1459_ = lean_ctor_get(v___x_1451_, 6);
v_auxDeclNGen_1460_ = lean_ctor_get(v___x_1451_, 7);
v_infoState_1461_ = lean_ctor_get(v___x_1451_, 8);
v_snapshotTasks_1462_ = lean_ctor_get(v___x_1451_, 10);
v_prevLinterStates_1463_ = lean_ctor_get(v___x_1451_, 11);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1465_ = v___x_1451_;
v_isShared_1466_ = v_isSharedCheck_1493_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_prevLinterStates_1463_);
lean_inc(v_snapshotTasks_1462_);
lean_inc(v_traceState_1452_);
lean_inc(v_infoState_1461_);
lean_inc(v_auxDeclNGen_1460_);
lean_inc(v_ngen_1459_);
lean_inc(v_maxRecDepth_1458_);
lean_inc(v_nextMacroScope_1457_);
lean_inc(v_usedQuotCtxts_1456_);
lean_inc(v_scopes_1455_);
lean_inc(v_messages_1454_);
lean_inc(v_env_1453_);
lean_dec(v___x_1451_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1493_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
uint64_t v_tid_1467_; lean_object* v_traces_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1492_; 
v_tid_1467_ = lean_ctor_get_uint64(v_traceState_1452_, sizeof(void*)*1);
v_traces_1468_ = lean_ctor_get(v_traceState_1452_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_traceState_1452_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1470_ = v_traceState_1452_;
v_isShared_1471_ = v_isSharedCheck_1492_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_traces_1468_);
lean_dec(v_traceState_1452_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1492_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; double v___x_1473_; uint8_t v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0);
v___x_1474_ = 0;
v___x_1475_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1476_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1476_, 0, v_cls_1439_);
lean_ctor_set(v___x_1476_, 1, v___x_1472_);
lean_ctor_set(v___x_1476_, 2, v___x_1475_);
lean_ctor_set_float(v___x_1476_, sizeof(void*)*3, v___x_1473_);
lean_ctor_set_float(v___x_1476_, sizeof(void*)*3 + 8, v___x_1473_);
lean_ctor_set_uint8(v___x_1476_, sizeof(void*)*3 + 16, v___x_1474_);
v___x_1477_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__1));
v___x_1478_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set(v___x_1478_, 1, v_a_1447_);
lean_ctor_set(v___x_1478_, 2, v___x_1477_);
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_a_1445_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = l_Lean_PersistentArray_push___redArg(v_traces_1468_, v___x_1479_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v___x_1480_);
v___x_1482_ = v___x_1470_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1480_);
lean_ctor_set_uint64(v_reuseFailAlloc_1491_, sizeof(void*)*1, v_tid_1467_);
v___x_1482_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 9, v___x_1482_);
v___x_1484_ = v___x_1465_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_env_1453_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_messages_1454_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_scopes_1455_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_usedQuotCtxts_1456_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_nextMacroScope_1457_);
lean_ctor_set(v_reuseFailAlloc_1490_, 5, v_maxRecDepth_1458_);
lean_ctor_set(v_reuseFailAlloc_1490_, 6, v_ngen_1459_);
lean_ctor_set(v_reuseFailAlloc_1490_, 7, v_auxDeclNGen_1460_);
lean_ctor_set(v_reuseFailAlloc_1490_, 8, v_infoState_1461_);
lean_ctor_set(v_reuseFailAlloc_1490_, 9, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1490_, 10, v_snapshotTasks_1462_);
lean_ctor_set(v_reuseFailAlloc_1490_, 11, v_prevLinterStates_1463_);
v___x_1484_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1485_ = lean_st_ref_put(v___y_1442_, v___x_1484_);
v___x_1486_ = lean_box(0);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1486_);
v___x_1488_ = v___x_1449_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec_ref(v_msg_1440_);
lean_dec(v_cls_1439_);
v_a_1495_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1444_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1444_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___boxed(lean_object* v_cls_1503_, lean_object* v_msg_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_1503_, v_msg_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(lean_object* v_as_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
if (lean_obj_tag(v_as_1509_) == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_box(0);
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
else
{
lean_object* v_head_1515_; lean_object* v_tail_1516_; lean_object* v_fst_1517_; lean_object* v_snd_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v_scopes_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v_opts_1525_; uint8_t v_hasTrace_1526_; 
v_head_1515_ = lean_ctor_get(v_as_1509_, 0);
lean_inc(v_head_1515_);
v_tail_1516_ = lean_ctor_get(v_as_1509_, 1);
lean_inc(v_tail_1516_);
lean_dec_ref_known(v_as_1509_, 2);
v_fst_1517_ = lean_ctor_get(v_head_1515_, 0);
lean_inc(v_fst_1517_);
v_snd_1518_ = lean_ctor_get(v_head_1515_, 1);
lean_inc(v_snd_1518_);
lean_dec(v_head_1515_);
v___x_1519_ = l_Lean_inheritedTraceOptions;
v___x_1520_ = lean_st_ref_get(v___x_1519_);
v___x_1521_ = lean_st_ref_get(v___y_1511_);
v_scopes_1522_ = lean_ctor_get(v___x_1521_, 2);
lean_inc(v_scopes_1522_);
lean_dec(v___x_1521_);
v___x_1523_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1524_ = l_List_head_x21___redArg(v___x_1523_, v_scopes_1522_);
lean_dec(v_scopes_1522_);
v_opts_1525_ = lean_ctor_get(v___x_1524_, 1);
lean_inc_ref(v_opts_1525_);
lean_dec(v___x_1524_);
v_hasTrace_1526_ = lean_ctor_get_uint8(v_opts_1525_, sizeof(void*)*1);
if (v_hasTrace_1526_ == 0)
{
lean_dec_ref(v_opts_1525_);
lean_dec(v___x_1520_);
lean_dec(v_snd_1518_);
lean_dec(v_fst_1517_);
v_as_1509_ = v_tail_1516_;
goto _start;
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1528_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
lean_inc(v_fst_1517_);
v___x_1529_ = l_Lean_Name_append(v___x_1528_, v_fst_1517_);
v___x_1530_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1520_, v_opts_1525_, v___x_1529_);
lean_dec(v___x_1529_);
lean_dec_ref(v_opts_1525_);
lean_dec(v___x_1520_);
if (v___x_1530_ == 0)
{
lean_dec(v_snd_1518_);
lean_dec(v_fst_1517_);
v_as_1509_ = v_tail_1516_;
goto _start;
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1532_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_snd_1518_);
v___x_1533_ = l_Lean_MessageData_ofFormat(v___x_1532_);
v___x_1534_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_fst_1517_, v___x_1533_, v___y_1510_, v___y_1511_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_dec_ref_known(v___x_1534_, 1);
v_as_1509_ = v_tail_1516_;
goto _start;
}
else
{
lean_dec(v_tail_1516_);
return v___x_1534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___boxed(lean_object* v_as_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v_as_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(lean_object* v_currNamespace_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v_currNamespace_1541_);
lean_ctor_set(v___x_1544_, 1, v___y_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(v_currNamespace_1545_, v___y_1546_, v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(lean_object* v_env_1549_, lean_object* v_opts_1550_, lean_object* v_currNamespace_1551_, lean_object* v_openDecls_1552_, lean_object* v_n_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = l_Lean_ResolveName_resolveGlobalName(v_env_1549_, v_opts_1550_, v_currNamespace_1551_, v_openDecls_1552_, v_n_1553_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v___y_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed(lean_object* v_env_1558_, lean_object* v_opts_1559_, lean_object* v_currNamespace_1560_, lean_object* v_openDecls_1561_, lean_object* v_n_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(v_env_1558_, v_opts_1559_, v_currNamespace_1560_, v_openDecls_1561_, v_n_1562_, v___y_1563_, v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec_ref(v_opts_1559_);
return v_res_1565_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(lean_object* v_opts_1566_, lean_object* v_opt_1567_){
_start:
{
lean_object* v_name_1568_; lean_object* v_defValue_1569_; lean_object* v_map_1570_; lean_object* v___x_1571_; 
v_name_1568_ = lean_ctor_get(v_opt_1567_, 0);
v_defValue_1569_ = lean_ctor_get(v_opt_1567_, 1);
v_map_1570_ = lean_ctor_get(v_opts_1566_, 0);
v___x_1571_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1570_, v_name_1568_);
if (lean_obj_tag(v___x_1571_) == 0)
{
uint8_t v___x_1572_; 
v___x_1572_ = lean_unbox(v_defValue_1569_);
return v___x_1572_;
}
else
{
lean_object* v_val_1573_; 
v_val_1573_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_val_1573_);
lean_dec_ref_known(v___x_1571_, 1);
if (lean_obj_tag(v_val_1573_) == 1)
{
uint8_t v_v_1574_; 
v_v_1574_ = lean_ctor_get_uint8(v_val_1573_, 0);
lean_dec_ref_known(v_val_1573_, 0);
return v_v_1574_;
}
else
{
uint8_t v___x_1575_; 
lean_dec(v_val_1573_);
v___x_1575_ = lean_unbox(v_defValue_1569_);
return v___x_1575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___boxed(lean_object* v_opts_1576_, lean_object* v_opt_1577_){
_start:
{
uint8_t v_res_1578_; lean_object* v_r_1579_; 
v_res_1578_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(v_opts_1576_, v_opt_1577_);
lean_dec_ref(v_opt_1577_);
lean_dec_ref(v_opts_1576_);
v_r_1579_ = lean_box(v_res_1578_);
return v_r_1579_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__0(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_box(1);
v___x_1581_ = l_Lean_MessageData_ofFormat(v___x_1580_);
return v___x_1581_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__3(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__2));
v___x_1586_ = l_Lean_MessageData_ofFormat(v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27(lean_object* v_x_1587_, lean_object* v_x_1588_){
_start:
{
if (lean_obj_tag(v_x_1588_) == 0)
{
return v_x_1587_;
}
else
{
lean_object* v_head_1589_; lean_object* v_tail_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1612_; 
v_head_1589_ = lean_ctor_get(v_x_1588_, 0);
v_tail_1590_ = lean_ctor_get(v_x_1588_, 1);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_x_1588_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1592_ = v_x_1588_;
v_isShared_1593_ = v_isSharedCheck_1612_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_tail_1590_);
lean_inc(v_head_1589_);
lean_dec(v_x_1588_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1612_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_before_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1610_; 
v_before_1594_ = lean_ctor_get(v_head_1589_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_head_1589_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; 
v_unused_1611_ = lean_ctor_get(v_head_1589_, 1);
lean_dec(v_unused_1611_);
v___x_1596_ = v_head_1589_;
v_isShared_1597_ = v_isSharedCheck_1610_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_before_1594_);
lean_dec(v_head_1589_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1610_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1598_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__0);
if (v_isShared_1597_ == 0)
{
lean_ctor_set_tag(v___x_1596_, 7);
lean_ctor_set(v___x_1596_, 1, v___x_1598_);
lean_ctor_set(v___x_1596_, 0, v_x_1587_);
v___x_1600_ = v___x_1596_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_x_1587_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1601_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__3);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 7);
lean_ctor_set(v___x_1592_, 1, v___x_1601_);
lean_ctor_set(v___x_1592_, 0, v___x_1600_);
v___x_1603_ = v___x_1592_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1604_ = l_Lean_MessageData_ofSyntax(v_before_1594_);
v___x_1605_ = l_Lean_indentD(v___x_1604_);
v___x_1606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1603_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v_x_1587_ = v___x_1606_;
v_x_1588_ = v_tail_1590_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__1));
v___x_1617_ = l_Lean_MessageData_ofFormat(v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(lean_object* v_msgData_1618_, lean_object* v_macroStack_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1622_; lean_object* v_scopes_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v_opts_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1622_ = lean_st_ref_get(v___y_1620_);
v_scopes_1623_ = lean_ctor_get(v___x_1622_, 2);
lean_inc(v_scopes_1623_);
lean_dec(v___x_1622_);
v___x_1624_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1625_ = l_List_head_x21___redArg(v___x_1624_, v_scopes_1623_);
lean_dec(v_scopes_1623_);
v_opts_1626_ = lean_ctor_get(v___x_1625_, 1);
lean_inc_ref(v_opts_1626_);
lean_dec(v___x_1625_);
v___x_1627_ = l_Lean_Elab_pp_macroStack;
v___x_1628_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(v_opts_1626_, v___x_1627_);
lean_dec_ref(v_opts_1626_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; 
lean_dec(v_macroStack_1619_);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_msgData_1618_);
return v___x_1629_;
}
else
{
if (lean_obj_tag(v_macroStack_1619_) == 0)
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v_msgData_1618_);
return v___x_1630_;
}
else
{
lean_object* v_head_1631_; lean_object* v_after_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1647_; 
v_head_1631_ = lean_ctor_get(v_macroStack_1619_, 0);
lean_inc(v_head_1631_);
v_after_1632_ = lean_ctor_get(v_head_1631_, 1);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_head_1631_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v_head_1631_, 0);
lean_dec(v_unused_1648_);
v___x_1634_ = v_head_1631_;
v_isShared_1635_ = v_isSharedCheck_1647_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_after_1632_);
lean_dec(v_head_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1647_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1636_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27___closed__0);
if (v_isShared_1635_ == 0)
{
lean_ctor_set_tag(v___x_1634_, 7);
lean_ctor_set(v___x_1634_, 1, v___x_1636_);
lean_ctor_set(v___x_1634_, 0, v_msgData_1618_);
v___x_1638_ = v___x_1634_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_msgData_1618_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_msgData_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1639_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = l_Lean_MessageData_ofSyntax(v_after_1632_);
v___x_1642_ = l_Lean_indentD(v___x_1641_);
v_msgData_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1643_, 0, v___x_1640_);
lean_ctor_set(v_msgData_1643_, 1, v___x_1642_);
v___x_1644_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__27(v_msgData_1643_, v_macroStack_1619_);
v___x_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
return v___x_1645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___boxed(lean_object* v_msgData_1649_, lean_object* v_macroStack_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_msgData_1649_, v_macroStack_1650_, v___y_1651_);
lean_dec(v___y_1651_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(lean_object* v_msg_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_Elab_Command_getRef___redArg(v___y_1655_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v_macroStack_1660_; lean_object* v___x_1661_; lean_object* v_a_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1673_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v_macroStack_1660_ = lean_ctor_get(v___y_1655_, 4);
v___x_1661_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msg_1654_, v___y_1656_);
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref(v___x_1661_);
v___x_1663_ = l_Lean_Elab_getBetterRef(v_a_1659_, v_macroStack_1660_);
lean_dec(v_a_1659_);
lean_inc(v_macroStack_1660_);
v___x_1664_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_a_1662_, v_macroStack_1660_, v___y_1656_);
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1663_);
lean_ctor_set(v___x_1669_, 1, v_a_1665_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 1);
lean_ctor_set(v___x_1667_, 0, v___x_1669_);
v___x_1671_ = v___x_1667_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec_ref(v_msg_1654_);
v_a_1674_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1658_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1658_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg___boxed(lean_object* v_msg_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(lean_object* v_ref_1687_, lean_object* v_msg_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_Elab_Command_getRef___redArg(v___y_1689_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v_fileName_1694_; lean_object* v_fileMap_1695_; lean_object* v_currRecDepth_1696_; lean_object* v_cmdPos_1697_; lean_object* v_macroStack_1698_; lean_object* v_quotContext_x3f_1699_; lean_object* v_currMacroScope_1700_; lean_object* v_snap_x3f_1701_; lean_object* v_cancelTk_x3f_1702_; uint8_t v_suppressElabErrors_1703_; lean_object* v_ref_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v_fileName_1694_ = lean_ctor_get(v___y_1689_, 0);
v_fileMap_1695_ = lean_ctor_get(v___y_1689_, 1);
v_currRecDepth_1696_ = lean_ctor_get(v___y_1689_, 2);
v_cmdPos_1697_ = lean_ctor_get(v___y_1689_, 3);
v_macroStack_1698_ = lean_ctor_get(v___y_1689_, 4);
v_quotContext_x3f_1699_ = lean_ctor_get(v___y_1689_, 5);
v_currMacroScope_1700_ = lean_ctor_get(v___y_1689_, 6);
v_snap_x3f_1701_ = lean_ctor_get(v___y_1689_, 8);
v_cancelTk_x3f_1702_ = lean_ctor_get(v___y_1689_, 9);
v_suppressElabErrors_1703_ = lean_ctor_get_uint8(v___y_1689_, sizeof(void*)*10);
v_ref_1704_ = l_Lean_replaceRef(v_ref_1687_, v_a_1693_);
lean_dec(v_a_1693_);
lean_inc(v_cancelTk_x3f_1702_);
lean_inc(v_snap_x3f_1701_);
lean_inc(v_currMacroScope_1700_);
lean_inc(v_quotContext_x3f_1699_);
lean_inc(v_macroStack_1698_);
lean_inc(v_cmdPos_1697_);
lean_inc(v_currRecDepth_1696_);
lean_inc_ref(v_fileMap_1695_);
lean_inc_ref(v_fileName_1694_);
v___x_1705_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1705_, 0, v_fileName_1694_);
lean_ctor_set(v___x_1705_, 1, v_fileMap_1695_);
lean_ctor_set(v___x_1705_, 2, v_currRecDepth_1696_);
lean_ctor_set(v___x_1705_, 3, v_cmdPos_1697_);
lean_ctor_set(v___x_1705_, 4, v_macroStack_1698_);
lean_ctor_set(v___x_1705_, 5, v_quotContext_x3f_1699_);
lean_ctor_set(v___x_1705_, 6, v_currMacroScope_1700_);
lean_ctor_set(v___x_1705_, 7, v_ref_1704_);
lean_ctor_set(v___x_1705_, 8, v_snap_x3f_1701_);
lean_ctor_set(v___x_1705_, 9, v_cancelTk_x3f_1702_);
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*10, v_suppressElabErrors_1703_);
v___x_1706_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_1688_, v___x_1705_, v___y_1690_);
lean_dec_ref_known(v___x_1705_, 10);
return v___x_1706_;
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec_ref(v_msg_1688_);
v_a_1707_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1692_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1692_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg___boxed(lean_object* v_ref_1715_, lean_object* v_msg_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_ref_1715_, v_msg_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v_ref_1715_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(lean_object* v_env_1721_, lean_object* v_declName_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
uint8_t v___x_1725_; lean_object* v_env_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; uint8_t v___x_1729_; 
v___x_1725_ = 0;
v_env_1726_ = l_Lean_Environment_setExporting(v_env_1721_, v___x_1725_);
lean_inc(v_declName_1722_);
v___x_1727_ = l_Lean_mkPrivateName(v_env_1726_, v_declName_1722_);
v___x_1728_ = 1;
lean_inc_ref(v_env_1726_);
v___x_1729_ = l_Lean_Environment_contains(v_env_1726_, v___x_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1730_ = l_Lean_privateToUserName(v_declName_1722_);
v___x_1731_ = l_Lean_Environment_contains(v_env_1726_, v___x_1730_, v___x_1728_);
v___x_1732_ = lean_box(v___x_1731_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v___y_1724_);
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_dec_ref(v_env_1726_);
lean_dec(v_declName_1722_);
v___x_1734_ = lean_box(v___x_1729_);
v___x_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
lean_ctor_set(v___x_1735_, 1, v___y_1724_);
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed(lean_object* v_env_1736_, lean_object* v_declName_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(v_env_1736_, v_declName_1737_, v___y_1738_, v___y_1739_);
lean_dec_ref(v___y_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(lean_object* v_x_1741_, lean_object* v___y_1742_){
_start:
{
if (lean_obj_tag(v_x_1741_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1744_; 
v_a_1743_ = lean_ctor_get(v_x_1741_, 0);
lean_inc(v_a_1743_);
v___x_1744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1744_, 0, v_a_1743_);
lean_ctor_set(v___x_1744_, 1, v___y_1742_);
return v___x_1744_;
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1746_; 
v_a_1745_ = lean_ctor_get(v_x_1741_, 0);
lean_inc(v_a_1745_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v_a_1745_);
lean_ctor_set(v___x_1746_, 1, v___y_1742_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg___boxed(lean_object* v_x_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v_x_1747_, v___y_1748_);
lean_dec_ref(v_x_1747_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(lean_object* v_env_1750_, lean_object* v_stx_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1750_, v_stx_1751_, v___y_1752_, v___y_1753_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
if (lean_obj_tag(v_a_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1764_; 
v_a_1756_ = lean_ctor_get(v___x_1754_, 1);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1764_ == 0)
{
lean_object* v_unused_1765_; 
v_unused_1765_ = lean_ctor_get(v___x_1754_, 0);
lean_dec(v_unused_1765_);
v___x_1758_ = v___x_1754_;
v_isShared_1759_ = v_isSharedCheck_1764_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1754_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1764_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1760_ = lean_box(0);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1760_);
v___x_1762_ = v___x_1758_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_a_1756_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
else
{
lean_object* v_val_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1794_; 
v_val_1766_ = lean_ctor_get(v_a_1755_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_a_1755_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1768_ = v_a_1755_;
v_isShared_1769_ = v_isSharedCheck_1794_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_val_1766_);
lean_dec(v_a_1755_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1794_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_snd_1770_; 
v_snd_1770_ = lean_ctor_get(v_val_1766_, 1);
lean_inc(v_snd_1770_);
lean_dec(v_val_1766_);
if (lean_obj_tag(v_snd_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1780_; 
lean_del_object(v___x_1768_);
v_a_1771_ = lean_ctor_get(v___x_1754_, 1);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1754_, 2);
v_a_1772_ = lean_ctor_get(v_snd_1770_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_snd_1770_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1774_ = v_snd_1770_;
v_isShared_1775_ = v_isSharedCheck_1780_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v_snd_1770_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1780_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v___x_1777_, v_a_1771_);
lean_dec_ref(v___x_1777_);
return v___x_1778_;
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1793_; 
v_a_1781_ = lean_ctor_get(v___x_1754_, 1);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1754_, 2);
v_a_1782_ = lean_ctor_get(v_snd_1770_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_snd_1770_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1784_ = v_snd_1770_;
v_isShared_1785_ = v_isSharedCheck_1793_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v_snd_1770_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1793_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v_a_1782_);
v___x_1787_ = v___x_1768_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1789_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1787_);
v___x_1789_ = v___x_1784_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v___x_1789_, v_a_1781_);
lean_dec_ref(v___x_1789_);
return v___x_1790_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
v_a_1795_ = lean_ctor_get(v___x_1754_, 0);
v_a_1796_ = lean_ctor_get(v___x_1754_, 1);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1754_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_inc(v_a_1795_);
lean_dec(v___x_1754_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1795_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed(lean_object* v_env_1804_, lean_object* v_stx_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(v_env_1804_, v_stx_1805_, v___y_1806_, v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(lean_object* v_keys_1809_, lean_object* v_i_1810_, lean_object* v_k_1811_){
_start:
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = lean_array_get_size(v_keys_1809_);
v___x_1813_ = lean_nat_dec_lt(v_i_1810_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_dec(v_i_1810_);
return v___x_1813_;
}
else
{
lean_object* v_k_x27_1814_; uint8_t v___x_1815_; 
v_k_x27_1814_ = lean_array_fget_borrowed(v_keys_1809_, v_i_1810_);
v___x_1815_ = l_Lean_instBEqExtraModUse_beq(v_k_1811_, v_k_x27_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = lean_unsigned_to_nat(1u);
v___x_1817_ = lean_nat_add(v_i_1810_, v___x_1816_);
lean_dec(v_i_1810_);
v_i_1810_ = v___x_1817_;
goto _start;
}
else
{
lean_dec(v_i_1810_);
return v___x_1815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg___boxed(lean_object* v_keys_1819_, lean_object* v_i_1820_, lean_object* v_k_1821_){
_start:
{
uint8_t v_res_1822_; lean_object* v_r_1823_; 
v_res_1822_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_1819_, v_i_1820_, v_k_1821_);
lean_dec_ref(v_k_1821_);
lean_dec_ref(v_keys_1819_);
v_r_1823_ = lean_box(v_res_1822_);
return v_r_1823_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(lean_object* v_x_1824_, size_t v_x_1825_, lean_object* v_x_1826_){
_start:
{
if (lean_obj_tag(v_x_1824_) == 0)
{
lean_object* v_es_1827_; lean_object* v___x_1828_; size_t v___x_1829_; size_t v___x_1830_; lean_object* v_j_1831_; lean_object* v___x_1832_; 
v_es_1827_ = lean_ctor_get(v_x_1824_, 0);
v___x_1828_ = lean_box(2);
v___x_1829_ = ((size_t)31ULL);
v___x_1830_ = lean_usize_land(v_x_1825_, v___x_1829_);
v_j_1831_ = lean_usize_to_nat(v___x_1830_);
v___x_1832_ = lean_array_get_borrowed(v___x_1828_, v_es_1827_, v_j_1831_);
lean_dec(v_j_1831_);
switch(lean_obj_tag(v___x_1832_))
{
case 0:
{
lean_object* v_key_1833_; uint8_t v___x_1834_; 
v_key_1833_ = lean_ctor_get(v___x_1832_, 0);
v___x_1834_ = l_Lean_instBEqExtraModUse_beq(v_x_1826_, v_key_1833_);
return v___x_1834_;
}
case 1:
{
lean_object* v_node_1835_; size_t v___x_1836_; size_t v___x_1837_; 
v_node_1835_ = lean_ctor_get(v___x_1832_, 0);
v___x_1836_ = ((size_t)5ULL);
v___x_1837_ = lean_usize_shift_right(v_x_1825_, v___x_1836_);
v_x_1824_ = v_node_1835_;
v_x_1825_ = v___x_1837_;
goto _start;
}
default: 
{
uint8_t v___x_1839_; 
v___x_1839_ = 0;
return v___x_1839_;
}
}
}
else
{
lean_object* v_ks_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v_ks_1840_ = lean_ctor_get(v_x_1824_, 0);
v___x_1841_ = lean_unsigned_to_nat(0u);
v___x_1842_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_ks_1840_, v___x_1841_, v_x_1826_);
return v___x_1842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___boxed(lean_object* v_x_1843_, lean_object* v_x_1844_, lean_object* v_x_1845_){
_start:
{
size_t v_x_23718__boxed_1846_; uint8_t v_res_1847_; lean_object* v_r_1848_; 
v_x_23718__boxed_1846_ = lean_unbox_usize(v_x_1844_);
lean_dec(v_x_1844_);
v_res_1847_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_1843_, v_x_23718__boxed_1846_, v_x_1845_);
lean_dec_ref(v_x_1845_);
lean_dec_ref(v_x_1843_);
v_r_1848_ = lean_box(v_res_1847_);
return v_r_1848_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(lean_object* v_x_1849_, lean_object* v_x_1850_){
_start:
{
uint64_t v___x_1851_; size_t v___x_1852_; uint8_t v___x_1853_; 
v___x_1851_ = l_Lean_instHashableExtraModUse_hash(v_x_1850_);
v___x_1852_ = lean_uint64_to_usize(v___x_1851_);
v___x_1853_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_1849_, v___x_1852_, v_x_1850_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg___boxed(lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
uint8_t v_res_1856_; lean_object* v_r_1857_; 
v_res_1856_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_1854_, v_x_1855_);
lean_dec_ref(v_x_1855_);
lean_dec_ref(v_x_1854_);
v_r_1857_ = lean_box(v_res_1856_);
return v_r_1857_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1));
v___x_1861_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0));
v___x_1862_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1861_, v___x_1860_);
return v___x_1862_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5));
v___x_1868_ = l_Lean_stringToMessageData(v___x_1867_);
return v___x_1868_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7));
v___x_1871_ = l_Lean_stringToMessageData(v___x_1870_);
return v___x_1871_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1873_ = l_Lean_stringToMessageData(v___x_1872_);
return v___x_1873_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10(void){
_start:
{
lean_object* v_cls_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_cls_1874_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4));
v___x_1875_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
v___x_1876_ = l_Lean_Name_append(v___x_1875_, v_cls_1874_);
return v___x_1876_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11));
v___x_1879_ = l_Lean_stringToMessageData(v___x_1878_);
return v___x_1879_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13));
v___x_1882_ = l_Lean_stringToMessageData(v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(lean_object* v_mod_1887_, uint8_t v_isMeta_1888_, lean_object* v_hint_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; lean_object* v_env_1894_; uint8_t v_isExporting_1895_; lean_object* v___x_1896_; lean_object* v_env_1897_; lean_object* v___x_1898_; lean_object* v_entry_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___y_1904_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1893_ = lean_st_ref_get(v___y_1891_);
v_env_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc_ref(v_env_1894_);
lean_dec(v___x_1893_);
v_isExporting_1895_ = lean_ctor_get_uint8(v_env_1894_, sizeof(void*)*8);
lean_dec_ref(v_env_1894_);
v___x_1896_ = lean_st_ref_get(v___y_1891_);
v_env_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc_ref(v_env_1897_);
lean_dec(v___x_1896_);
v___x_1898_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2);
lean_inc(v_mod_1887_);
v_entry_1899_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1899_, 0, v_mod_1887_);
lean_ctor_set_uint8(v_entry_1899_, sizeof(void*)*1, v_isExporting_1895_);
lean_ctor_set_uint8(v_entry_1899_, sizeof(void*)*1 + 1, v_isMeta_1888_);
v___x_1900_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1901_ = lean_box(1);
v___x_1902_ = lean_box(0);
v___x_1931_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1898_, v___x_1900_, v_env_1897_, v___x_1901_, v___x_1902_);
v___x_1932_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v___x_1931_, v_entry_1899_);
lean_dec(v___x_1931_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v_scopes_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v_opts_1939_; uint8_t v_hasTrace_1940_; 
v___x_1933_ = l_Lean_inheritedTraceOptions;
v___x_1934_ = lean_st_ref_get(v___x_1933_);
v___x_1935_ = lean_st_ref_get(v___y_1891_);
v_scopes_1936_ = lean_ctor_get(v___x_1935_, 2);
lean_inc(v_scopes_1936_);
lean_dec(v___x_1935_);
v___x_1937_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1938_ = l_List_head_x21___redArg(v___x_1937_, v_scopes_1936_);
lean_dec(v_scopes_1936_);
v_opts_1939_ = lean_ctor_get(v___x_1938_, 1);
lean_inc_ref(v_opts_1939_);
lean_dec(v___x_1938_);
v_hasTrace_1940_ = lean_ctor_get_uint8(v_opts_1939_, sizeof(void*)*1);
if (v_hasTrace_1940_ == 0)
{
lean_dec_ref(v_opts_1939_);
lean_dec(v___x_1934_);
lean_dec(v_hint_1889_);
lean_dec(v_mod_1887_);
v___y_1904_ = v___y_1891_;
goto v___jp_1903_;
}
else
{
lean_object* v_cls_1941_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v_cls_1941_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4));
v___x_1961_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10);
v___x_1962_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1934_, v_opts_1939_, v___x_1961_);
lean_dec_ref(v_opts_1939_);
lean_dec(v___x_1934_);
if (v___x_1962_ == 0)
{
lean_dec(v_hint_1889_);
lean_dec(v_mod_1887_);
v___y_1904_ = v___y_1891_;
goto v___jp_1903_;
}
else
{
lean_object* v___x_1963_; lean_object* v___y_1965_; 
v___x_1963_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12);
if (v_isExporting_1895_ == 0)
{
lean_object* v___x_1972_; 
v___x_1972_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__17));
v___y_1965_ = v___x_1972_;
goto v___jp_1964_;
}
else
{
lean_object* v___x_1973_; 
v___x_1973_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__18));
v___y_1965_ = v___x_1973_;
goto v___jp_1964_;
}
v___jp_1964_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_inc_ref(v___y_1965_);
v___x_1966_ = l_Lean_stringToMessageData(v___y_1965_);
v___x_1967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1963_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14);
v___x_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
if (v_isMeta_1888_ == 0)
{
lean_object* v___x_1970_; 
v___x_1970_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15));
v___y_1948_ = v___x_1969_;
v___y_1949_ = v___x_1970_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_1971_; 
v___x_1971_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16));
v___y_1948_ = v___x_1969_;
v___y_1949_ = v___x_1971_;
goto v___jp_1947_;
}
}
}
v___jp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___y_1943_);
lean_ctor_set(v___x_1945_, 1, v___y_1944_);
v___x_1946_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_1941_, v___x_1945_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_dec_ref_known(v___x_1946_, 1);
v___y_1904_ = v___y_1891_;
goto v___jp_1903_;
}
else
{
lean_dec_ref_known(v_entry_1899_, 1);
return v___x_1946_;
}
}
v___jp_1947_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
lean_inc_ref(v___y_1949_);
v___x_1950_ = l_Lean_stringToMessageData(v___y_1949_);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___y_1948_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6);
v___x_1953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1951_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = l_Lean_MessageData_ofName(v_mod_1887_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = l_Lean_Name_isAnonymous(v_hint_1889_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1957_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8);
v___x_1958_ = l_Lean_MessageData_ofName(v_hint_1889_);
v___x_1959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___y_1943_ = v___x_1955_;
v___y_1944_ = v___x_1959_;
goto v___jp_1942_;
}
else
{
lean_object* v___x_1960_; 
lean_dec(v_hint_1889_);
v___x_1960_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9);
v___y_1943_ = v___x_1955_;
v___y_1944_ = v___x_1960_;
goto v___jp_1942_;
}
}
}
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_dec_ref_known(v_entry_1899_, 1);
lean_dec(v_hint_1889_);
lean_dec(v_mod_1887_);
v___x_1974_ = lean_box(0);
v___x_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
return v___x_1975_;
}
v___jp_1903_:
{
lean_object* v___x_1905_; lean_object* v_toEnvExtension_1906_; lean_object* v_env_1907_; lean_object* v_messages_1908_; lean_object* v_scopes_1909_; lean_object* v_usedQuotCtxts_1910_; lean_object* v_nextMacroScope_1911_; lean_object* v_maxRecDepth_1912_; lean_object* v_ngen_1913_; lean_object* v_auxDeclNGen_1914_; lean_object* v_infoState_1915_; lean_object* v_traceState_1916_; lean_object* v_snapshotTasks_1917_; lean_object* v_prevLinterStates_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1930_; 
v___x_1905_ = lean_st_ref_take(v___y_1904_);
v_toEnvExtension_1906_ = lean_ctor_get(v___x_1900_, 0);
v_env_1907_ = lean_ctor_get(v___x_1905_, 0);
v_messages_1908_ = lean_ctor_get(v___x_1905_, 1);
v_scopes_1909_ = lean_ctor_get(v___x_1905_, 2);
v_usedQuotCtxts_1910_ = lean_ctor_get(v___x_1905_, 3);
v_nextMacroScope_1911_ = lean_ctor_get(v___x_1905_, 4);
v_maxRecDepth_1912_ = lean_ctor_get(v___x_1905_, 5);
v_ngen_1913_ = lean_ctor_get(v___x_1905_, 6);
v_auxDeclNGen_1914_ = lean_ctor_get(v___x_1905_, 7);
v_infoState_1915_ = lean_ctor_get(v___x_1905_, 8);
v_traceState_1916_ = lean_ctor_get(v___x_1905_, 9);
v_snapshotTasks_1917_ = lean_ctor_get(v___x_1905_, 10);
v_prevLinterStates_1918_ = lean_ctor_get(v___x_1905_, 11);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1920_ = v___x_1905_;
v_isShared_1921_ = v_isSharedCheck_1930_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_prevLinterStates_1918_);
lean_inc(v_snapshotTasks_1917_);
lean_inc(v_traceState_1916_);
lean_inc(v_infoState_1915_);
lean_inc(v_auxDeclNGen_1914_);
lean_inc(v_ngen_1913_);
lean_inc(v_maxRecDepth_1912_);
lean_inc(v_nextMacroScope_1911_);
lean_inc(v_usedQuotCtxts_1910_);
lean_inc(v_scopes_1909_);
lean_inc(v_messages_1908_);
lean_inc(v_env_1907_);
lean_dec(v___x_1905_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1930_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_asyncMode_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v_asyncMode_1922_ = lean_ctor_get(v_toEnvExtension_1906_, 2);
v___x_1923_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1900_, v_env_1907_, v_entry_1899_, v_asyncMode_1922_, v___x_1902_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1923_);
v___x_1925_ = v___x_1920_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_messages_1908_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_scopes_1909_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v_usedQuotCtxts_1910_);
lean_ctor_set(v_reuseFailAlloc_1929_, 4, v_nextMacroScope_1911_);
lean_ctor_set(v_reuseFailAlloc_1929_, 5, v_maxRecDepth_1912_);
lean_ctor_set(v_reuseFailAlloc_1929_, 6, v_ngen_1913_);
lean_ctor_set(v_reuseFailAlloc_1929_, 7, v_auxDeclNGen_1914_);
lean_ctor_set(v_reuseFailAlloc_1929_, 8, v_infoState_1915_);
lean_ctor_set(v_reuseFailAlloc_1929_, 9, v_traceState_1916_);
lean_ctor_set(v_reuseFailAlloc_1929_, 10, v_snapshotTasks_1917_);
lean_ctor_set(v_reuseFailAlloc_1929_, 11, v_prevLinterStates_1918_);
v___x_1925_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = lean_st_ref_put(v___y_1904_, v___x_1925_);
v___x_1927_ = lean_box(0);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
return v___x_1928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___boxed(lean_object* v_mod_1976_, lean_object* v_isMeta_1977_, lean_object* v_hint_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
uint8_t v_isMeta_boxed_1982_; lean_object* v_res_1983_; 
v_isMeta_boxed_1982_ = lean_unbox(v_isMeta_1977_);
v_res_1983_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_mod_1976_, v_isMeta_boxed_1982_, v_hint_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(lean_object* v___x_1984_, lean_object* v_declName_1985_, lean_object* v_as_1986_, size_t v_sz_1987_, size_t v_i_1988_, lean_object* v_b_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
uint8_t v___x_1993_; 
v___x_1993_ = lean_usize_dec_lt(v_i_1988_, v_sz_1987_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; 
lean_dec(v_declName_1985_);
v___x_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1994_, 0, v_b_1989_);
return v___x_1994_;
}
else
{
lean_object* v___x_1995_; lean_object* v_modules_1996_; lean_object* v___x_1997_; lean_object* v_a_1998_; lean_object* v___x_1999_; lean_object* v_toImport_2000_; lean_object* v_module_2001_; uint8_t v___x_2002_; lean_object* v___x_2003_; 
v___x_1995_ = l_Lean_Environment_header(v___x_1984_);
v_modules_1996_ = lean_ctor_get(v___x_1995_, 3);
lean_inc_ref(v_modules_1996_);
lean_dec_ref(v___x_1995_);
v___x_1997_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1998_ = lean_array_uget_borrowed(v_as_1986_, v_i_1988_);
v___x_1999_ = lean_array_get(v___x_1997_, v_modules_1996_, v_a_1998_);
lean_dec_ref(v_modules_1996_);
v_toImport_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc_ref(v_toImport_2000_);
lean_dec(v___x_1999_);
v_module_2001_ = lean_ctor_get(v_toImport_2000_, 0);
lean_inc(v_module_2001_);
lean_dec_ref(v_toImport_2000_);
v___x_2002_ = 0;
lean_inc(v_declName_1985_);
v___x_2003_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_module_2001_, v___x_2002_, v_declName_1985_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v___x_2004_; size_t v___x_2005_; size_t v___x_2006_; 
lean_dec_ref_known(v___x_2003_, 1);
v___x_2004_ = lean_box(0);
v___x_2005_ = ((size_t)1ULL);
v___x_2006_ = lean_usize_add(v_i_1988_, v___x_2005_);
v_i_1988_ = v___x_2006_;
v_b_1989_ = v___x_2004_;
goto _start;
}
else
{
lean_dec(v_declName_1985_);
return v___x_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7___boxed(lean_object* v___x_2008_, lean_object* v_declName_2009_, lean_object* v_as_2010_, lean_object* v_sz_2011_, lean_object* v_i_2012_, lean_object* v_b_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
size_t v_sz_boxed_2017_; size_t v_i_boxed_2018_; lean_object* v_res_2019_; 
v_sz_boxed_2017_ = lean_unbox_usize(v_sz_2011_);
lean_dec(v_sz_2011_);
v_i_boxed_2018_ = lean_unbox_usize(v_i_2012_);
lean_dec(v_i_2012_);
v_res_2019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v___x_2008_, v_declName_2009_, v_as_2010_, v_sz_boxed_2017_, v_i_boxed_2018_, v_b_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec_ref(v_as_2010_);
lean_dec_ref(v___x_2008_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23_spec__26___redArg(lean_object* v_m_2020_, lean_object* v_query_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_, lean_object* v_x_2024_){
_start:
{
lean_object* v_zero_2025_; uint8_t v_isZero_2026_; 
v_zero_2025_ = lean_unsigned_to_nat(0u);
v_isZero_2026_ = lean_nat_dec_eq(v_x_2023_, v_zero_2025_);
if (v_isZero_2026_ == 1)
{
lean_dec(v_x_2024_);
lean_dec(v_x_2023_);
if (lean_obj_tag(v_x_2022_) == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_box(2);
return v___x_2027_;
}
else
{
lean_object* v_val_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v_val_2028_ = lean_ctor_get(v_x_2022_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_x_2022_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v_x_2022_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_val_2028_);
lean_dec(v_x_2022_);
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
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_val_2028_);
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
else
{
lean_object* v_keyArray_2036_; lean_object* v_valueArray_2037_; lean_object* v___x_2038_; uint8_t v_isSome_2039_; 
v_keyArray_2036_ = lean_ctor_get(v_m_2020_, 1);
v_valueArray_2037_ = lean_ctor_get(v_m_2020_, 2);
v___x_2038_ = lean_array_fget_borrowed(v_keyArray_2036_, v_x_2024_);
v_isSome_2039_ = lean_noption_is_some(v___x_2038_);
if (v_isSome_2039_ == 0)
{
lean_dec(v_x_2023_);
if (lean_obj_tag(v_x_2022_) == 0)
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2040_, 0, v_x_2024_);
return v___x_2040_;
}
else
{
lean_object* v_val_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec(v_x_2024_);
v_val_2041_ = lean_ctor_get(v_x_2022_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_x_2022_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v_x_2022_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_val_2041_);
lean_dec(v_x_2022_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_val_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_one_2049_; lean_object* v_n_2050_; lean_object* v___y_2052_; 
v_one_2049_ = lean_unsigned_to_nat(1u);
v_n_2050_ = lean_nat_sub(v_x_2023_, v_one_2049_);
lean_dec(v_x_2023_);
if (v_isSome_2039_ == 0)
{
goto v___jp_2058_;
}
else
{
lean_object* v___x_2060_; uint8_t v_isSome_2061_; 
v___x_2060_ = lean_array_fget_borrowed(v_valueArray_2037_, v_x_2024_);
v_isSome_2061_ = lean_noption_is_some(v___x_2060_);
if (v_isSome_2061_ == 0)
{
goto v___jp_2058_;
}
else
{
lean_object* v_val_2062_; uint8_t v___x_2063_; 
lean_inc(v___x_2038_);
v_val_2062_ = lean_noption_get(v___x_2038_);
v___x_2063_ = lean_name_eq(v_val_2062_, v_query_2021_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
lean_dec(v_val_2062_);
v___x_2064_ = lean_array_get_size(v_keyArray_2036_);
v___x_2065_ = lean_nat_add(v_x_2024_, v_one_2049_);
lean_dec(v_x_2024_);
v___x_2066_ = lean_nat_dec_lt(v___x_2065_, v___x_2064_);
if (v___x_2066_ == 0)
{
lean_dec(v___x_2065_);
v_x_2023_ = v_n_2050_;
v_x_2024_ = v_zero_2025_;
goto _start;
}
else
{
v_x_2023_ = v_n_2050_;
v_x_2024_ = v___x_2065_;
goto _start;
}
}
else
{
lean_object* v_val_2069_; lean_object* v___x_2070_; 
lean_dec(v_n_2050_);
lean_dec(v_x_2022_);
lean_inc(v___x_2060_);
v_val_2069_ = lean_noption_get(v___x_2060_);
v___x_2070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2070_, 0, v_x_2024_);
lean_ctor_set(v___x_2070_, 1, v_val_2062_);
lean_ctor_set(v___x_2070_, 2, v_val_2069_);
return v___x_2070_;
}
}
}
v___jp_2051_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2053_ = lean_array_get_size(v_keyArray_2036_);
v___x_2054_ = lean_nat_add(v_x_2024_, v_one_2049_);
lean_dec(v_x_2024_);
v___x_2055_ = lean_nat_dec_lt(v___x_2054_, v___x_2053_);
if (v___x_2055_ == 0)
{
lean_dec(v___x_2054_);
v_x_2022_ = v___y_2052_;
v_x_2023_ = v_n_2050_;
v_x_2024_ = v_zero_2025_;
goto _start;
}
else
{
v_x_2022_ = v___y_2052_;
v_x_2023_ = v_n_2050_;
v_x_2024_ = v___x_2054_;
goto _start;
}
}
v___jp_2058_:
{
if (lean_obj_tag(v_x_2022_) == 0)
{
lean_object* v___x_2059_; 
lean_inc(v_x_2024_);
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v_x_2024_);
v___y_2052_ = v___x_2059_;
goto v___jp_2051_;
}
else
{
v___y_2052_ = v_x_2022_;
goto v___jp_2051_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23_spec__26___redArg___boxed(lean_object* v_m_2071_, lean_object* v_query_2072_, lean_object* v_x_2073_, lean_object* v_x_2074_, lean_object* v_x_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23_spec__26___redArg(v_m_2071_, v_query_2072_, v_x_2073_, v_x_2074_, v_x_2075_);
lean_dec(v_query_2072_);
lean_dec_ref(v_m_2071_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23___redArg(lean_object* v_m_2077_, lean_object* v_query_2078_){
_start:
{
lean_object* v_keyArray_2079_; lean_object* v___x_2080_; uint64_t v___y_2082_; 
v_keyArray_2079_ = lean_ctor_get(v_m_2077_, 1);
v___x_2080_ = lean_array_get_size(v_keyArray_2079_);
if (lean_obj_tag(v_query_2078_) == 0)
{
uint64_t v___x_2097_; 
v___x_2097_ = 1723ULL;
v___y_2082_ = v___x_2097_;
goto v___jp_2081_;
}
else
{
uint64_t v_hash_2098_; 
v_hash_2098_ = lean_ctor_get_uint64(v_query_2078_, sizeof(void*)*2);
v___y_2082_ = v_hash_2098_;
goto v___jp_2081_;
}
v___jp_2081_:
{
uint64_t v___x_2083_; uint64_t v___x_2084_; uint64_t v_fold_2085_; uint64_t v___x_2086_; uint64_t v___x_2087_; uint64_t v___x_2088_; size_t v___x_2089_; size_t v___x_2090_; size_t v___x_2091_; size_t v___x_2092_; size_t v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2083_ = 32ULL;
v___x_2084_ = lean_uint64_shift_right(v___y_2082_, v___x_2083_);
v_fold_2085_ = lean_uint64_xor(v___y_2082_, v___x_2084_);
v___x_2086_ = 16ULL;
v___x_2087_ = lean_uint64_shift_right(v_fold_2085_, v___x_2086_);
v___x_2088_ = lean_uint64_xor(v_fold_2085_, v___x_2087_);
v___x_2089_ = lean_uint64_to_usize(v___x_2088_);
v___x_2090_ = lean_usize_of_nat(v___x_2080_);
v___x_2091_ = ((size_t)1ULL);
v___x_2092_ = lean_usize_sub(v___x_2090_, v___x_2091_);
v___x_2093_ = lean_usize_land(v___x_2089_, v___x_2092_);
v___x_2094_ = lean_usize_to_nat(v___x_2093_);
v___x_2095_ = lean_box(0);
v___x_2096_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23_spec__26___redArg(v_m_2077_, v_query_2078_, v___x_2095_, v___x_2080_, v___x_2094_);
return v___x_2096_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23___redArg___boxed(lean_object* v_m_2099_, lean_object* v_query_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23___redArg(v_m_2099_, v_query_2100_);
lean_dec(v_query_2100_);
lean_dec_ref(v_m_2099_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(lean_object* v_m_2102_, lean_object* v_query_2103_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23___redArg(v_m_2102_, v_query_2103_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_index_2105_; lean_object* v_key_2106_; lean_object* v_value_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
v_index_2105_ = lean_ctor_get(v___x_2104_, 0);
v_key_2106_ = lean_ctor_get(v___x_2104_, 1);
v_value_2107_ = lean_ctor_get(v___x_2104_, 2);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2104_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_value_2107_);
lean_inc(v_key_2106_);
lean_inc(v_index_2105_);
lean_dec(v___x_2104_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_index_2105_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_key_2106_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_value_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
else
{
lean_object* v___x_2115_; 
lean_dec(v___x_2104_);
v___x_2115_ = lean_box(1);
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg___boxed(lean_object* v_m_2116_, lean_object* v_query_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_m_2116_, v_query_2117_);
lean_dec(v_query_2117_);
lean_dec_ref(v_m_2116_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(lean_object* v_m_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_m_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_value_2122_; lean_object* v___x_2123_; 
v_value_2122_ = lean_ctor_get(v___x_2121_, 2);
lean_inc(v_value_2122_);
lean_dec_ref_known(v___x_2121_, 3);
v___x_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_value_2122_);
return v___x_2123_;
}
else
{
lean_object* v___x_2124_; 
v___x_2124_ = lean_box(0);
return v___x_2124_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_m_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v_m_2125_, v_a_2126_);
lean_dec(v_a_2126_);
lean_dec_ref(v_m_2125_);
return v_res_2127_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1));
v___x_2131_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0));
v___x_2132_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2131_, v___x_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(lean_object* v_declName_2135_, uint8_t v_isMeta_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; lean_object* v_env_2144_; lean_object* v___y_2146_; lean_object* v___x_2159_; 
v___x_2140_ = lean_st_ref_get(v___y_2138_);
v_env_2144_ = lean_ctor_get(v___x_2140_, 0);
lean_inc_ref(v_env_2144_);
lean_dec(v___x_2140_);
v___x_2159_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2144_, v_declName_2135_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_dec_ref(v_env_2144_);
lean_dec(v_declName_2135_);
goto v___jp_2141_;
}
else
{
lean_object* v_val_2160_; lean_object* v___x_2161_; lean_object* v_modules_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v_val_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_val_2160_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2161_ = l_Lean_Environment_header(v_env_2144_);
v_modules_2162_ = lean_ctor_get(v___x_2161_, 3);
lean_inc_ref(v_modules_2162_);
lean_dec_ref(v___x_2161_);
v___x_2163_ = lean_array_get_size(v_modules_2162_);
v___x_2164_ = lean_nat_dec_lt(v_val_2160_, v___x_2163_);
if (v___x_2164_ == 0)
{
lean_dec_ref(v_modules_2162_);
lean_dec(v_val_2160_);
lean_dec_ref(v_env_2144_);
lean_dec(v_declName_2135_);
goto v___jp_2141_;
}
else
{
lean_object* v___x_2165_; lean_object* v_env_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___y_2170_; 
v___x_2165_ = lean_st_ref_get(v___y_2138_);
v_env_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc_ref(v_env_2166_);
lean_dec(v___x_2165_);
v___x_2167_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2);
v___x_2168_ = lean_array_fget(v_modules_2162_, v_val_2160_);
lean_dec(v_val_2160_);
lean_dec_ref(v_modules_2162_);
if (v_isMeta_2136_ == 0)
{
lean_dec_ref(v_env_2166_);
v___y_2170_ = v_isMeta_2136_;
goto v___jp_2169_;
}
else
{
uint8_t v___x_2181_; 
lean_inc(v_declName_2135_);
v___x_2181_ = l_Lean_isMarkedMeta(v_env_2166_, v_declName_2135_);
if (v___x_2181_ == 0)
{
v___y_2170_ = v_isMeta_2136_;
goto v___jp_2169_;
}
else
{
uint8_t v___x_2182_; 
v___x_2182_ = 0;
v___y_2170_ = v___x_2182_;
goto v___jp_2169_;
}
}
v___jp_2169_:
{
lean_object* v_toImport_2171_; lean_object* v_module_2172_; lean_object* v___x_2173_; 
v_toImport_2171_ = lean_ctor_get(v___x_2168_, 0);
lean_inc_ref(v_toImport_2171_);
lean_dec(v___x_2168_);
v_module_2172_ = lean_ctor_get(v_toImport_2171_, 0);
lean_inc(v_module_2172_);
lean_dec_ref(v_toImport_2171_);
lean_inc(v_declName_2135_);
v___x_2173_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_module_2172_, v___y_2170_, v_declName_2135_, v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_dec_ref_known(v___x_2173_, 1);
v___x_2174_ = l_Lean_indirectModUseExt;
v___x_2175_ = lean_box(1);
v___x_2176_ = lean_box(0);
lean_inc_ref(v_env_2144_);
v___x_2177_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2167_, v___x_2174_, v_env_2144_, v___x_2175_, v___x_2176_);
v___x_2178_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v___x_2177_, v_declName_2135_);
lean_dec(v___x_2177_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v___x_2179_; 
v___x_2179_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__3));
v___y_2146_ = v___x_2179_;
goto v___jp_2145_;
}
else
{
lean_object* v_val_2180_; 
v_val_2180_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_val_2180_);
lean_dec_ref_known(v___x_2178_, 1);
v___y_2146_ = v_val_2180_;
goto v___jp_2145_;
}
}
else
{
lean_dec_ref(v_env_2144_);
lean_dec(v_declName_2135_);
return v___x_2173_;
}
}
}
}
v___jp_2141_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_box(0);
v___x_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
return v___x_2143_;
}
v___jp_2145_:
{
lean_object* v___x_2147_; size_t v_sz_2148_; size_t v___x_2149_; lean_object* v___x_2150_; 
v___x_2147_ = lean_box(0);
v_sz_2148_ = lean_array_size(v___y_2146_);
v___x_2149_ = ((size_t)0ULL);
v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v_env_2144_, v_declName_2135_, v___y_2146_, v_sz_2148_, v___x_2149_, v___x_2147_, v___y_2137_, v___y_2138_);
lean_dec_ref(v___y_2146_);
lean_dec_ref(v_env_2144_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; 
v_unused_2158_ = lean_ctor_get(v___x_2150_, 0);
lean_dec(v_unused_2158_);
v___x_2152_ = v___x_2150_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_dec(v___x_2150_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2147_);
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2147_);
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
return v___x_2150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___boxed(lean_object* v_declName_2183_, lean_object* v_isMeta_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
uint8_t v_isMeta_boxed_2188_; lean_object* v_res_2189_; 
v_isMeta_boxed_2188_ = lean_unbox(v_isMeta_2184_);
v_res_2189_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_declName_2183_, v_isMeta_boxed_2188_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(lean_object* v_as_x27_2190_, lean_object* v_b_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
if (lean_obj_tag(v_as_x27_2190_) == 0)
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v_b_2191_);
return v___x_2195_;
}
else
{
lean_object* v_head_2196_; lean_object* v_tail_2197_; uint8_t v___x_2198_; lean_object* v___x_2199_; 
v_head_2196_ = lean_ctor_get(v_as_x27_2190_, 0);
v_tail_2197_ = lean_ctor_get(v_as_x27_2190_, 1);
v___x_2198_ = 1;
lean_inc(v_head_2196_);
v___x_2199_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_head_2196_, v___x_2198_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v___x_2200_; 
lean_dec_ref_known(v___x_2199_, 1);
v___x_2200_ = lean_box(0);
v_as_x27_2190_ = v_tail_2197_;
v_b_2191_ = v___x_2200_;
goto _start;
}
else
{
return v___x_2199_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2202_, lean_object* v_b_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_2202_, v_b_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v_as_x27_2202_);
return v_res_2207_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = l_Lean_maxRecDepthErrorMessage;
v___x_2214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
return v___x_2214_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3);
v___x_2216_ = l_Lean_MessageData_ofFormat(v___x_2215_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4);
v___x_2218_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2));
v___x_2219_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v___x_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(lean_object* v_ref_2220_){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5);
v___x_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2223_, 0, v_ref_2220_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_2225_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(lean_object* v_x_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; lean_object* v_env_2234_; lean_object* v___x_2235_; lean_object* v_scopes_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v_opts_2239_; lean_object* v___x_2240_; 
v___x_2233_ = lean_st_ref_get(v___y_2231_);
v_env_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc_ref(v_env_2234_);
lean_dec(v___x_2233_);
v___x_2235_ = lean_st_ref_get(v___y_2231_);
v_scopes_2236_ = lean_ctor_get(v___x_2235_, 2);
lean_inc(v_scopes_2236_);
lean_dec(v___x_2235_);
v___x_2237_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2238_ = l_List_head_x21___redArg(v___x_2237_, v_scopes_2236_);
lean_dec(v_scopes_2236_);
v_opts_2239_ = lean_ctor_get(v___x_2238_, 1);
lean_inc_ref(v_opts_2239_);
lean_dec(v___x_2238_);
v___x_2240_ = l_Lean_Elab_Command_getScope___redArg(v___y_2231_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v_currNamespace_2242_; lean_object* v___x_2243_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
v_currNamespace_2242_ = lean_ctor_get(v_a_2241_, 2);
lean_inc(v_currNamespace_2242_);
lean_dec(v_a_2241_);
v___x_2243_ = l_Lean_Elab_Command_getScope___redArg(v___y_2231_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v_openDecls_2245_; lean_object* v___x_2246_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___x_2243_, 1);
v_openDecls_2245_ = lean_ctor_get(v_a_2244_, 3);
lean_inc(v_openDecls_2245_);
lean_dec(v_a_2244_);
v___x_2246_ = l_Lean_Elab_Command_getRef___redArg(v___y_2230_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2248_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
v___x_2248_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2230_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v_currRecDepth_2250_; lean_object* v_quotContext_x3f_2251_; lean_object* v___f_2252_; lean_object* v___f_2253_; lean_object* v___f_2254_; lean_object* v___f_2255_; lean_object* v___f_2256_; lean_object* v_methods_2257_; lean_object* v_a_2259_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2249_);
lean_dec_ref_known(v___x_2248_, 1);
v_currRecDepth_2250_ = lean_ctor_get(v___y_2230_, 2);
v_quotContext_x3f_2251_ = lean_ctor_get(v___y_2230_, 5);
lean_inc_ref_n(v_env_2234_, 3);
v___f_2252_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2252_, 0, v_env_2234_);
v___f_2253_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2253_, 0, v_env_2234_);
lean_inc_n(v_currNamespace_2242_, 2);
v___f_2254_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2254_, 0, v_currNamespace_2242_);
lean_inc(v_openDecls_2245_);
v___f_2255_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2255_, 0, v_env_2234_);
lean_closure_set(v___f_2255_, 1, v_currNamespace_2242_);
lean_closure_set(v___f_2255_, 2, v_openDecls_2245_);
v___f_2256_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2256_, 0, v_env_2234_);
lean_closure_set(v___f_2256_, 1, v_opts_2239_);
lean_closure_set(v___f_2256_, 2, v_currNamespace_2242_);
lean_closure_set(v___f_2256_, 3, v_openDecls_2245_);
v_methods_2257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2257_, 0, v___f_2253_);
lean_ctor_set(v_methods_2257_, 1, v___f_2254_);
lean_ctor_set(v_methods_2257_, 2, v___f_2252_);
lean_ctor_set(v_methods_2257_, 3, v___f_2255_);
lean_ctor_set(v_methods_2257_, 4, v___f_2256_);
if (lean_obj_tag(v_quotContext_x3f_2251_) == 0)
{
lean_object* v___x_2332_; lean_object* v_a_2333_; 
v___x_2332_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2231_);
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v___x_2332_);
v_a_2259_ = v_a_2333_;
goto v___jp_2258_;
}
else
{
lean_object* v_val_2334_; 
v_val_2334_ = lean_ctor_get(v_quotContext_x3f_2251_, 0);
lean_inc(v_val_2334_);
v_a_2259_ = v_val_2334_;
goto v___jp_2258_;
}
v___jp_2258_:
{
lean_object* v___x_2260_; lean_object* v_maxRecDepth_2261_; lean_object* v___x_2262_; lean_object* v_nextMacroScope_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2260_ = lean_st_ref_get(v___y_2231_);
v_maxRecDepth_2261_ = lean_ctor_get(v___x_2260_, 5);
lean_inc(v_maxRecDepth_2261_);
lean_dec(v___x_2260_);
v___x_2262_ = lean_st_ref_get(v___y_2231_);
v_nextMacroScope_2263_ = lean_ctor_get(v___x_2262_, 4);
lean_inc(v_nextMacroScope_2263_);
lean_dec(v___x_2262_);
lean_inc(v_currRecDepth_2250_);
v___x_2264_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2264_, 0, v_methods_2257_);
lean_ctor_set(v___x_2264_, 1, v_a_2259_);
lean_ctor_set(v___x_2264_, 2, v_a_2249_);
lean_ctor_set(v___x_2264_, 3, v_currRecDepth_2250_);
lean_ctor_set(v___x_2264_, 4, v_maxRecDepth_2261_);
lean_ctor_set(v___x_2264_, 5, v_a_2247_);
v___x_2265_ = lean_box(0);
v___x_2266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2266_, 0, v_nextMacroScope_2263_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
lean_ctor_set(v___x_2266_, 2, v___x_2265_);
v___x_2267_ = lean_apply_2(v_x_2229_, v___x_2264_, v___x_2266_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v_a_2269_; lean_object* v_macroScope_2270_; lean_object* v_traceMsgs_2271_; lean_object* v_expandedMacroDecls_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 1);
lean_inc(v_a_2268_);
v_a_2269_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2267_, 2);
v_macroScope_2270_ = lean_ctor_get(v_a_2268_, 0);
lean_inc(v_macroScope_2270_);
v_traceMsgs_2271_ = lean_ctor_get(v_a_2268_, 1);
lean_inc(v_traceMsgs_2271_);
v_expandedMacroDecls_2272_ = lean_ctor_get(v_a_2268_, 2);
lean_inc(v_expandedMacroDecls_2272_);
lean_dec(v_a_2268_);
v___x_2273_ = lean_box(0);
v___x_2274_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_expandedMacroDecls_2272_, v___x_2273_, v___y_2230_, v___y_2231_);
lean_dec(v_expandedMacroDecls_2272_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v___x_2275_; lean_object* v_env_2276_; lean_object* v_messages_2277_; lean_object* v_scopes_2278_; lean_object* v_usedQuotCtxts_2279_; lean_object* v_maxRecDepth_2280_; lean_object* v_ngen_2281_; lean_object* v_auxDeclNGen_2282_; lean_object* v_infoState_2283_; lean_object* v_traceState_2284_; lean_object* v_snapshotTasks_2285_; lean_object* v_prevLinterStates_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2312_; 
lean_dec_ref_known(v___x_2274_, 1);
v___x_2275_ = lean_st_ref_take(v___y_2231_);
v_env_2276_ = lean_ctor_get(v___x_2275_, 0);
v_messages_2277_ = lean_ctor_get(v___x_2275_, 1);
v_scopes_2278_ = lean_ctor_get(v___x_2275_, 2);
v_usedQuotCtxts_2279_ = lean_ctor_get(v___x_2275_, 3);
v_maxRecDepth_2280_ = lean_ctor_get(v___x_2275_, 5);
v_ngen_2281_ = lean_ctor_get(v___x_2275_, 6);
v_auxDeclNGen_2282_ = lean_ctor_get(v___x_2275_, 7);
v_infoState_2283_ = lean_ctor_get(v___x_2275_, 8);
v_traceState_2284_ = lean_ctor_get(v___x_2275_, 9);
v_snapshotTasks_2285_ = lean_ctor_get(v___x_2275_, 10);
v_prevLinterStates_2286_ = lean_ctor_get(v___x_2275_, 11);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; 
v_unused_2313_ = lean_ctor_get(v___x_2275_, 4);
lean_dec(v_unused_2313_);
v___x_2288_ = v___x_2275_;
v_isShared_2289_ = v_isSharedCheck_2312_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_prevLinterStates_2286_);
lean_inc(v_snapshotTasks_2285_);
lean_inc(v_traceState_2284_);
lean_inc(v_infoState_2283_);
lean_inc(v_auxDeclNGen_2282_);
lean_inc(v_ngen_2281_);
lean_inc(v_maxRecDepth_2280_);
lean_inc(v_usedQuotCtxts_2279_);
lean_inc(v_scopes_2278_);
lean_inc(v_messages_2277_);
lean_inc(v_env_2276_);
lean_dec(v___x_2275_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2312_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v_macroScope_2270_);
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_env_2276_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_messages_2277_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_scopes_2278_);
lean_ctor_set(v_reuseFailAlloc_2311_, 3, v_usedQuotCtxts_2279_);
lean_ctor_set(v_reuseFailAlloc_2311_, 4, v_macroScope_2270_);
lean_ctor_set(v_reuseFailAlloc_2311_, 5, v_maxRecDepth_2280_);
lean_ctor_set(v_reuseFailAlloc_2311_, 6, v_ngen_2281_);
lean_ctor_set(v_reuseFailAlloc_2311_, 7, v_auxDeclNGen_2282_);
lean_ctor_set(v_reuseFailAlloc_2311_, 8, v_infoState_2283_);
lean_ctor_set(v_reuseFailAlloc_2311_, 9, v_traceState_2284_);
lean_ctor_set(v_reuseFailAlloc_2311_, 10, v_snapshotTasks_2285_);
lean_ctor_set(v_reuseFailAlloc_2311_, 11, v_prevLinterStates_2286_);
v___x_2291_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = lean_st_ref_put(v___y_2231_, v___x_2291_);
v___x_2293_ = l_List_reverse___redArg(v_traceMsgs_2271_);
v___x_2294_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v___x_2293_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; 
v_unused_2302_ = lean_ctor_get(v___x_2294_, 0);
lean_dec(v_unused_2302_);
v___x_2296_ = v___x_2294_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_dec(v___x_2294_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v_a_2269_);
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2269_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec(v_a_2269_);
v_a_2303_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2294_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2294_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec(v_traceMsgs_2271_);
lean_dec(v_macroScope_2270_);
lean_dec(v_a_2269_);
v_a_2314_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2274_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2274_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_object* v_a_2322_; 
v_a_2322_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2267_, 2);
if (lean_obj_tag(v_a_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v_a_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v_a_2323_ = lean_ctor_get(v_a_2322_, 0);
lean_inc(v_a_2323_);
v_a_2324_ = lean_ctor_get(v_a_2322_, 1);
lean_inc_ref(v_a_2324_);
lean_dec_ref_known(v_a_2322_, 2);
v___x_2325_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0));
v___x_2326_ = lean_string_dec_eq(v_a_2324_, v___x_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2327_, 0, v_a_2324_);
v___x_2328_ = l_Lean_MessageData_ofFormat(v___x_2327_);
v___x_2329_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_a_2323_, v___x_2328_, v___y_2230_, v___y_2231_);
lean_dec(v_a_2323_);
return v___x_2329_;
}
else
{
lean_object* v___x_2330_; 
lean_dec_ref(v_a_2324_);
v___x_2330_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_a_2323_);
return v___x_2330_;
}
}
else
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2331_;
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_a_2247_);
lean_dec(v_openDecls_2245_);
lean_dec(v_currNamespace_2242_);
lean_dec_ref(v_opts_2239_);
lean_dec_ref(v_env_2234_);
lean_dec_ref(v_x_2229_);
v_a_2335_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2248_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2248_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_openDecls_2245_);
lean_dec(v_currNamespace_2242_);
lean_dec_ref(v_opts_2239_);
lean_dec_ref(v_env_2234_);
lean_dec_ref(v_x_2229_);
v_a_2343_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2246_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2246_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec(v_currNamespace_2242_);
lean_dec_ref(v_opts_2239_);
lean_dec_ref(v_env_2234_);
lean_dec_ref(v_x_2229_);
v_a_2351_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2243_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2243_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec_ref(v_opts_2239_);
lean_dec_ref(v_env_2234_);
lean_dec_ref(v_x_2229_);
v_a_2359_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2240_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2240_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___boxed(lean_object* v_x_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2367_, v___y_2368_, v___y_2369_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(size_t v_sz_2372_, size_t v_i_2373_, lean_object* v_bs_2374_){
_start:
{
uint8_t v___x_2375_; 
v___x_2375_ = lean_usize_dec_lt(v_i_2373_, v_sz_2372_);
if (v___x_2375_ == 0)
{
return v_bs_2374_;
}
else
{
lean_object* v___x_2376_; lean_object* v_v_2377_; lean_object* v_bs_x27_2378_; lean_object* v___x_2379_; size_t v___x_2380_; size_t v___x_2381_; lean_object* v___x_2382_; 
v___x_2376_ = lean_unsigned_to_nat(0u);
v_v_2377_ = lean_array_uget(v_bs_2374_, v_i_2373_);
v_bs_x27_2378_ = lean_array_uset(v_bs_2374_, v_i_2373_, v___x_2376_);
v___x_2379_ = l_Lean_Syntax_getArg(v_v_2377_, v___x_2376_);
lean_dec(v_v_2377_);
v___x_2380_ = ((size_t)1ULL);
v___x_2381_ = lean_usize_add(v_i_2373_, v___x_2380_);
v___x_2382_ = lean_array_uset(v_bs_x27_2378_, v_i_2373_, v___x_2379_);
v_i_2373_ = v___x_2381_;
v_bs_2374_ = v___x_2382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed(lean_object* v_sz_2384_, lean_object* v_i_2385_, lean_object* v_bs_2386_){
_start:
{
size_t v_sz_boxed_2387_; size_t v_i_boxed_2388_; lean_object* v_res_2389_; 
v_sz_boxed_2387_ = lean_unbox_usize(v_sz_2384_);
lean_dec(v_sz_2384_);
v_i_boxed_2388_ = lean_unbox_usize(v_i_2385_);
lean_dec(v_i_2385_);
v_res_2389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_boxed_2387_, v_i_boxed_2388_, v_bs_2386_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(lean_object* v_as_2390_, size_t v_i_2391_, size_t v_stop_2392_, lean_object* v_b_2393_){
_start:
{
lean_object* v___y_2395_; uint8_t v___x_2399_; 
v___x_2399_ = lean_usize_dec_eq(v_i_2391_, v_stop_2392_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2400_ = lean_array_uget_borrowed(v_as_2390_, v_i_2391_);
lean_inc(v___x_2400_);
v___x_2401_ = l_Lean_Syntax_getKind(v___x_2400_);
v___x_2402_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
v___x_2403_ = lean_name_eq(v___x_2401_, v___x_2402_);
lean_dec(v___x_2401_);
if (v___x_2403_ == 0)
{
v___y_2395_ = v_b_2393_;
goto v___jp_2394_;
}
else
{
lean_object* v___x_2404_; 
lean_inc(v___x_2400_);
v___x_2404_ = lean_array_push(v_b_2393_, v___x_2400_);
v___y_2395_ = v___x_2404_;
goto v___jp_2394_;
}
}
else
{
return v_b_2393_;
}
v___jp_2394_:
{
size_t v___x_2396_; size_t v___x_2397_; 
v___x_2396_ = ((size_t)1ULL);
v___x_2397_ = lean_usize_add(v_i_2391_, v___x_2396_);
v_i_2391_ = v___x_2397_;
v_b_2393_ = v___y_2395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8___boxed(lean_object* v_as_2405_, lean_object* v_i_2406_, lean_object* v_stop_2407_, lean_object* v_b_2408_){
_start:
{
size_t v_i_boxed_2409_; size_t v_stop_boxed_2410_; lean_object* v_res_2411_; 
v_i_boxed_2409_ = lean_unbox_usize(v_i_2406_);
lean_dec(v_i_2406_);
v_stop_boxed_2410_ = lean_unbox_usize(v_stop_2407_);
lean_dec(v_stop_2407_);
v_res_2411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v_as_2405_, v_i_boxed_2409_, v_stop_boxed_2410_, v_b_2408_);
lean_dec_ref(v_as_2405_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation(lean_object* v_x_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2543_; uint8_t v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; size_t v___y_2555_; lean_object* v___y_2556_; 
v___x_2485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0));
v___x_2486_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1));
v___x_2487_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
lean_inc(v_x_2454_);
v___x_2488_ = l_Lean_Syntax_isOfKind(v_x_2454_, v___x_2487_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2597_; 
lean_dec(v_x_2454_);
v___x_2597_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2597_;
}
else
{
lean_object* v___x_2598_; size_t v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; uint8_t v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; uint8_t v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; size_t v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2710_; lean_object* v___y_2711_; uint8_t v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; size_t v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2741_; lean_object* v___y_2742_; uint8_t v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; size_t v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2776_; uint8_t v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; size_t v___y_2791_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v_prio_x3f_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v_name_x3f_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v_prec_x3f_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v_attrs_x3f_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v_doc_x3f_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v___x_2598_ = lean_unsigned_to_nat(0u);
v___x_2953_ = l_Lean_Syntax_getArg(v_x_2454_, v___x_2598_);
v___x_2954_ = l_Lean_Syntax_isNone(v___x_2953_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; uint8_t v___x_2956_; 
v___x_2955_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2953_);
v___x_2956_ = l_Lean_Syntax_matchesNull(v___x_2953_, v___x_2955_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; 
lean_dec(v___x_2953_);
lean_dec(v_x_2454_);
v___x_2957_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2957_;
}
else
{
lean_object* v_doc_x3f_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v_doc_x3f_2958_ = l_Lean_Syntax_getArg(v___x_2953_, v___x_2598_);
lean_dec(v___x_2953_);
v___x_2959_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__15));
lean_inc(v_doc_x3f_2958_);
v___x_2960_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2958_, v___x_2959_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; 
lean_dec(v_doc_x3f_2958_);
lean_dec(v_x_2454_);
v___x_2961_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2961_;
}
else
{
lean_object* v___x_2962_; 
v___x_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2962_, 0, v_doc_x3f_2958_);
v_doc_x3f_2937_ = v___x_2962_;
v___y_2938_ = v_a_2455_;
v___y_2939_ = v_a_2456_;
goto v___jp_2936_;
}
}
}
else
{
lean_object* v___x_2963_; 
lean_dec(v___x_2953_);
v___x_2963_ = lean_box(0);
v_doc_x3f_2937_ = v___x_2963_;
v___y_2938_ = v_a_2455_;
v___y_2939_ = v_a_2456_;
goto v___jp_2936_;
}
v___jp_2599_:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; size_t v_sz_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_inc_ref_n(v___y_2611_, 2);
v___x_2620_ = l_Array_append___redArg(v___y_2611_, v___y_2619_);
lean_dec_ref(v___y_2619_);
lean_inc_n(v___y_2601_, 3);
lean_inc_n(v___y_2609_, 9);
v___x_2621_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2621_, 0, v___y_2609_);
lean_ctor_set(v___x_2621_, 1, v___y_2601_);
lean_ctor_set(v___x_2621_, 2, v___x_2620_);
v___x_2622_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
v___x_2623_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
v___x_2624_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___y_2609_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
v___x_2625_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__8));
v___x_2626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___y_2609_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_2628_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___y_2609_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = l_Nat_reprFast(v___y_2617_);
v___x_2630_ = lean_box(2);
v___x_2631_ = l_Lean_Syntax_mkNumLit(v___x_2629_, v___x_2630_);
v___x_2632_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_2633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___y_2609_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = l_Lean_Syntax_node5(v___y_2609_, v___x_2622_, v___x_2624_, v___x_2626_, v___x_2628_, v___x_2631_, v___x_2633_);
v___x_2635_ = l_Lean_Syntax_node1(v___y_2609_, v___y_2601_, v___x_2634_);
v_sz_2636_ = lean_array_size(v___y_2615_);
v___x_2637_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_2636_, v___y_2600_, v___y_2615_);
v___x_2638_ = l_Array_append___redArg(v___y_2611_, v___x_2637_);
lean_dec_ref(v___x_2637_);
v___x_2639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2639_, 0, v___y_2609_);
lean_ctor_set(v___x_2639_, 1, v___y_2601_);
lean_ctor_set(v___x_2639_, 2, v___x_2638_);
v___x_2640_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
v___x_2641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___y_2609_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = lean_unsigned_to_nat(10u);
v___x_2643_ = lean_mk_empty_array_with_capacity(v___x_2642_);
v___x_2644_ = lean_array_push(v___x_2643_, v___y_2602_);
v___x_2645_ = lean_array_push(v___x_2644_, v___y_2618_);
lean_inc(v___y_2606_);
v___x_2646_ = lean_array_push(v___x_2645_, v___y_2606_);
v___x_2647_ = lean_array_push(v___x_2646_, v___y_2612_);
v___x_2648_ = lean_array_push(v___x_2647_, v___y_2603_);
v___x_2649_ = lean_array_push(v___x_2648_, v___x_2621_);
v___x_2650_ = lean_array_push(v___x_2649_, v___x_2635_);
v___x_2651_ = lean_array_push(v___x_2650_, v___x_2639_);
v___x_2652_ = lean_array_push(v___x_2651_, v___x_2641_);
v___x_2653_ = lean_array_push(v___x_2652_, v___y_2608_);
lean_inc(v___y_2613_);
v___x_2654_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2654_, 0, v___y_2609_);
lean_ctor_set(v___x_2654_, 1, v___y_2613_);
lean_ctor_set(v___x_2654_, 2, v___x_2653_);
v___x_2655_ = l_Lean_Elab_Command_elabSyntax(v___x_2654_, v___y_2610_, v___y_2607_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v___x_2657_ = lean_array_get_size(v___y_2614_);
v___x_2658_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__68));
v___x_2659_ = lean_nat_dec_lt(v___x_2598_, v___x_2657_);
if (v___x_2659_ == 0)
{
v___y_2543_ = v___y_2601_;
v___y_2544_ = v___y_2604_;
v___y_2545_ = v___y_2605_;
v___y_2546_ = v___y_2606_;
v___y_2547_ = v___y_2607_;
v___y_2548_ = v_a_2656_;
v___y_2549_ = v___y_2610_;
v___y_2550_ = v___y_2611_;
v___y_2551_ = v___x_2630_;
v___y_2552_ = v___y_2614_;
v___y_2553_ = v___y_2616_;
v___y_2554_ = v___x_2632_;
v___y_2555_ = v___y_2600_;
v___y_2556_ = v___x_2658_;
goto v___jp_2542_;
}
else
{
uint8_t v___x_2660_; 
v___x_2660_ = lean_nat_dec_le(v___x_2657_, v___x_2657_);
if (v___x_2660_ == 0)
{
if (v___x_2659_ == 0)
{
v___y_2543_ = v___y_2601_;
v___y_2544_ = v___y_2604_;
v___y_2545_ = v___y_2605_;
v___y_2546_ = v___y_2606_;
v___y_2547_ = v___y_2607_;
v___y_2548_ = v_a_2656_;
v___y_2549_ = v___y_2610_;
v___y_2550_ = v___y_2611_;
v___y_2551_ = v___x_2630_;
v___y_2552_ = v___y_2614_;
v___y_2553_ = v___y_2616_;
v___y_2554_ = v___x_2632_;
v___y_2555_ = v___y_2600_;
v___y_2556_ = v___x_2658_;
goto v___jp_2542_;
}
else
{
size_t v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = lean_usize_of_nat(v___x_2657_);
v___x_2662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2614_, v___y_2600_, v___x_2661_, v___x_2658_);
v___y_2543_ = v___y_2601_;
v___y_2544_ = v___y_2604_;
v___y_2545_ = v___y_2605_;
v___y_2546_ = v___y_2606_;
v___y_2547_ = v___y_2607_;
v___y_2548_ = v_a_2656_;
v___y_2549_ = v___y_2610_;
v___y_2550_ = v___y_2611_;
v___y_2551_ = v___x_2630_;
v___y_2552_ = v___y_2614_;
v___y_2553_ = v___y_2616_;
v___y_2554_ = v___x_2632_;
v___y_2555_ = v___y_2600_;
v___y_2556_ = v___x_2662_;
goto v___jp_2542_;
}
}
else
{
size_t v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = lean_usize_of_nat(v___x_2657_);
v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2614_, v___y_2600_, v___x_2663_, v___x_2658_);
v___y_2543_ = v___y_2601_;
v___y_2544_ = v___y_2604_;
v___y_2545_ = v___y_2605_;
v___y_2546_ = v___y_2606_;
v___y_2547_ = v___y_2607_;
v___y_2548_ = v_a_2656_;
v___y_2549_ = v___y_2610_;
v___y_2550_ = v___y_2611_;
v___y_2551_ = v___x_2630_;
v___y_2552_ = v___y_2614_;
v___y_2553_ = v___y_2616_;
v___y_2554_ = v___x_2632_;
v___y_2555_ = v___y_2600_;
v___y_2556_ = v___x_2664_;
goto v___jp_2542_;
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2606_);
v_a_2665_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2655_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2655_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
v___jp_2673_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
lean_inc_ref(v___y_2685_);
v___x_2694_ = l_Array_append___redArg(v___y_2685_, v___y_2693_);
lean_dec_ref(v___y_2693_);
lean_inc(v___y_2675_);
lean_inc(v___y_2682_);
v___x_2695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2695_, 0, v___y_2682_);
lean_ctor_set(v___x_2695_, 1, v___y_2675_);
lean_ctor_set(v___x_2695_, 2, v___x_2694_);
if (lean_obj_tag(v___y_2680_) == 1)
{
lean_object* v_val_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v_val_2696_ = lean_ctor_get(v___y_2680_, 0);
lean_inc(v_val_2696_);
lean_dec_ref_known(v___y_2680_, 1);
v___x_2697_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
v___x_2698_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc_n(v___y_2682_, 5);
v___x_2699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___y_2682_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__11));
v___x_2701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___y_2682_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_2703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___y_2682_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_2705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___y_2682_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = l_Lean_Syntax_node5(v___y_2682_, v___x_2697_, v___x_2699_, v___x_2701_, v___x_2703_, v_val_2696_, v___x_2705_);
v___x_2707_ = l_Array_mkArray1___redArg(v___x_2706_);
v___y_2600_ = v___y_2692_;
v___y_2601_ = v___y_2675_;
v___y_2602_ = v___y_2676_;
v___y_2603_ = v___x_2695_;
v___y_2604_ = v___y_2677_;
v___y_2605_ = v___y_2678_;
v___y_2606_ = v___y_2679_;
v___y_2607_ = v___y_2681_;
v___y_2608_ = v___y_2684_;
v___y_2609_ = v___y_2682_;
v___y_2610_ = v___y_2683_;
v___y_2611_ = v___y_2685_;
v___y_2612_ = v___y_2686_;
v___y_2613_ = v___y_2687_;
v___y_2614_ = v___y_2688_;
v___y_2615_ = v___y_2689_;
v___y_2616_ = v___y_2690_;
v___y_2617_ = v___y_2691_;
v___y_2618_ = v___y_2674_;
v___y_2619_ = v___x_2707_;
goto v___jp_2599_;
}
else
{
lean_object* v___x_2708_; 
lean_dec(v___y_2680_);
v___x_2708_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2600_ = v___y_2692_;
v___y_2601_ = v___y_2675_;
v___y_2602_ = v___y_2676_;
v___y_2603_ = v___x_2695_;
v___y_2604_ = v___y_2677_;
v___y_2605_ = v___y_2678_;
v___y_2606_ = v___y_2679_;
v___y_2607_ = v___y_2681_;
v___y_2608_ = v___y_2684_;
v___y_2609_ = v___y_2682_;
v___y_2610_ = v___y_2683_;
v___y_2611_ = v___y_2685_;
v___y_2612_ = v___y_2686_;
v___y_2613_ = v___y_2687_;
v___y_2614_ = v___y_2688_;
v___y_2615_ = v___y_2689_;
v___y_2616_ = v___y_2690_;
v___y_2617_ = v___y_2691_;
v___y_2618_ = v___y_2674_;
v___y_2619_ = v___x_2708_;
goto v___jp_2599_;
}
}
v___jp_2709_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_inc_ref(v___y_2720_);
v___x_2730_ = l_Array_append___redArg(v___y_2720_, v___y_2729_);
lean_dec_ref(v___y_2729_);
lean_inc(v___y_2710_);
lean_inc_n(v___y_2717_, 2);
v___x_2731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2731_, 0, v___y_2717_);
lean_ctor_set(v___x_2731_, 1, v___y_2710_);
lean_ctor_set(v___x_2731_, 2, v___x_2730_);
lean_inc_ref(v___y_2719_);
v___x_2732_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___y_2717_);
lean_ctor_set(v___x_2732_, 1, v___y_2719_);
if (lean_obj_tag(v___y_2724_) == 1)
{
lean_object* v_val_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v_val_2733_ = lean_ctor_get(v___y_2724_, 0);
lean_inc(v_val_2733_);
lean_dec_ref_known(v___y_2724_, 1);
v___x_2734_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
v___x_2735_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc_n(v___y_2717_, 2);
v___x_2736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___y_2717_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = l_Lean_Syntax_node2(v___y_2717_, v___x_2734_, v___x_2736_, v_val_2733_);
v___x_2738_ = l_Array_mkArray1___redArg(v___x_2737_);
v___y_2674_ = v___x_2731_;
v___y_2675_ = v___y_2710_;
v___y_2676_ = v___y_2711_;
v___y_2677_ = v___y_2712_;
v___y_2678_ = v___y_2713_;
v___y_2679_ = v___y_2714_;
v___y_2680_ = v___y_2715_;
v___y_2681_ = v___y_2716_;
v___y_2682_ = v___y_2717_;
v___y_2683_ = v___y_2718_;
v___y_2684_ = v___y_2721_;
v___y_2685_ = v___y_2720_;
v___y_2686_ = v___x_2732_;
v___y_2687_ = v___y_2722_;
v___y_2688_ = v___y_2723_;
v___y_2689_ = v___y_2725_;
v___y_2690_ = v___y_2726_;
v___y_2691_ = v___y_2727_;
v___y_2692_ = v___y_2728_;
v___y_2693_ = v___x_2738_;
goto v___jp_2673_;
}
else
{
lean_object* v___x_2739_; 
lean_dec(v___y_2724_);
v___x_2739_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2674_ = v___x_2731_;
v___y_2675_ = v___y_2710_;
v___y_2676_ = v___y_2711_;
v___y_2677_ = v___y_2712_;
v___y_2678_ = v___y_2713_;
v___y_2679_ = v___y_2714_;
v___y_2680_ = v___y_2715_;
v___y_2681_ = v___y_2716_;
v___y_2682_ = v___y_2717_;
v___y_2683_ = v___y_2718_;
v___y_2684_ = v___y_2721_;
v___y_2685_ = v___y_2720_;
v___y_2686_ = v___x_2732_;
v___y_2687_ = v___y_2722_;
v___y_2688_ = v___y_2723_;
v___y_2689_ = v___y_2725_;
v___y_2690_ = v___y_2726_;
v___y_2691_ = v___y_2727_;
v___y_2692_ = v___y_2728_;
v___y_2693_ = v___x_2739_;
goto v___jp_2673_;
}
}
v___jp_2740_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_inc_ref(v___y_2751_);
v___x_2761_ = l_Array_append___redArg(v___y_2751_, v___y_2760_);
lean_dec_ref(v___y_2760_);
lean_inc(v___y_2741_);
lean_inc(v___y_2749_);
v___x_2762_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2762_, 0, v___y_2749_);
lean_ctor_set(v___x_2762_, 1, v___y_2741_);
lean_ctor_set(v___x_2762_, 2, v___x_2761_);
if (lean_obj_tag(v___y_2742_) == 1)
{
lean_object* v_val_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_val_2763_ = lean_ctor_get(v___y_2742_, 0);
lean_inc(v_val_2763_);
lean_dec_ref_known(v___y_2742_, 1);
v___x_2764_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__11));
lean_inc_ref(v___y_2744_);
v___x_2765_ = l_Lean_Name_mkStr4(v___x_2485_, v___x_2486_, v___y_2744_, v___x_2764_);
v___x_2766_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc_n(v___y_2749_, 4);
v___x_2767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___y_2749_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
lean_inc_ref(v___y_2751_);
v___x_2768_ = l_Array_append___redArg(v___y_2751_, v_val_2763_);
lean_dec(v_val_2763_);
lean_inc(v___y_2741_);
v___x_2769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2769_, 0, v___y_2749_);
lean_ctor_set(v___x_2769_, 1, v___y_2741_);
lean_ctor_set(v___x_2769_, 2, v___x_2768_);
v___x_2770_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
v___x_2771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___y_2749_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = l_Lean_Syntax_node3(v___y_2749_, v___x_2765_, v___x_2767_, v___x_2769_, v___x_2771_);
v___x_2773_ = l_Array_mkArray1___redArg(v___x_2772_);
v___y_2710_ = v___y_2741_;
v___y_2711_ = v___x_2762_;
v___y_2712_ = v___y_2743_;
v___y_2713_ = v___y_2744_;
v___y_2714_ = v___y_2745_;
v___y_2715_ = v___y_2746_;
v___y_2716_ = v___y_2747_;
v___y_2717_ = v___y_2749_;
v___y_2718_ = v___y_2752_;
v___y_2719_ = v___y_2750_;
v___y_2720_ = v___y_2751_;
v___y_2721_ = v___y_2748_;
v___y_2722_ = v___y_2753_;
v___y_2723_ = v___y_2754_;
v___y_2724_ = v___y_2755_;
v___y_2725_ = v___y_2756_;
v___y_2726_ = v___y_2757_;
v___y_2727_ = v___y_2758_;
v___y_2728_ = v___y_2759_;
v___y_2729_ = v___x_2773_;
goto v___jp_2709_;
}
else
{
lean_object* v___x_2774_; 
lean_dec(v___y_2742_);
v___x_2774_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2710_ = v___y_2741_;
v___y_2711_ = v___x_2762_;
v___y_2712_ = v___y_2743_;
v___y_2713_ = v___y_2744_;
v___y_2714_ = v___y_2745_;
v___y_2715_ = v___y_2746_;
v___y_2716_ = v___y_2747_;
v___y_2717_ = v___y_2749_;
v___y_2718_ = v___y_2752_;
v___y_2719_ = v___y_2750_;
v___y_2720_ = v___y_2751_;
v___y_2721_ = v___y_2748_;
v___y_2722_ = v___y_2753_;
v___y_2723_ = v___y_2754_;
v___y_2724_ = v___y_2755_;
v___y_2725_ = v___y_2756_;
v___y_2726_ = v___y_2757_;
v___y_2727_ = v___y_2758_;
v___y_2728_ = v___y_2759_;
v___y_2729_ = v___x_2774_;
goto v___jp_2709_;
}
}
v___jp_2775_:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2792_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__12));
v___x_2793_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__13));
v___x_2794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_2795_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
if (lean_obj_tag(v___y_2785_) == 1)
{
lean_object* v_val_2796_; lean_object* v___x_2797_; 
v_val_2796_ = lean_ctor_get(v___y_2785_, 0);
lean_inc(v_val_2796_);
lean_dec_ref_known(v___y_2785_, 1);
v___x_2797_ = l_Array_mkArray1___redArg(v_val_2796_);
v___y_2741_ = v___x_2794_;
v___y_2742_ = v___y_2776_;
v___y_2743_ = v___y_2777_;
v___y_2744_ = v___y_2778_;
v___y_2745_ = v___y_2779_;
v___y_2746_ = v___y_2780_;
v___y_2747_ = v___y_2781_;
v___y_2748_ = v___y_2782_;
v___y_2749_ = v___y_2783_;
v___y_2750_ = v___x_2792_;
v___y_2751_ = v___x_2795_;
v___y_2752_ = v___y_2784_;
v___y_2753_ = v___x_2793_;
v___y_2754_ = v___y_2786_;
v___y_2755_ = v___y_2787_;
v___y_2756_ = v___y_2788_;
v___y_2757_ = v___y_2789_;
v___y_2758_ = v___y_2790_;
v___y_2759_ = v___y_2791_;
v___y_2760_ = v___x_2797_;
goto v___jp_2740_;
}
else
{
lean_object* v___x_2798_; 
lean_dec(v___y_2785_);
v___x_2798_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2741_ = v___x_2794_;
v___y_2742_ = v___y_2776_;
v___y_2743_ = v___y_2777_;
v___y_2744_ = v___y_2778_;
v___y_2745_ = v___y_2779_;
v___y_2746_ = v___y_2780_;
v___y_2747_ = v___y_2781_;
v___y_2748_ = v___y_2782_;
v___y_2749_ = v___y_2783_;
v___y_2750_ = v___x_2792_;
v___y_2751_ = v___x_2795_;
v___y_2752_ = v___y_2784_;
v___y_2753_ = v___x_2793_;
v___y_2754_ = v___y_2786_;
v___y_2755_ = v___y_2787_;
v___y_2756_ = v___y_2788_;
v___y_2757_ = v___y_2789_;
v___y_2758_ = v___y_2790_;
v___y_2759_ = v___y_2791_;
v___y_2760_ = v___x_2798_;
goto v___jp_2740_;
}
}
v___jp_2799_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_2809_, 0, v_prio_x3f_2806_);
v___x_2810_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2809_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v_items_2814_; size_t v_sz_2815_; size_t v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
v___x_2812_ = lean_unsigned_to_nat(7u);
v___x_2813_ = l_Lean_Syntax_getArg(v_x_2454_, v___x_2812_);
v_items_2814_ = l_Lean_Syntax_getArgs(v___x_2813_);
lean_dec(v___x_2813_);
v_sz_2815_ = lean_array_size(v_items_2814_);
v___x_2816_ = ((size_t)0ULL);
v___x_2817_ = lean_box_usize(v_sz_2815_);
v___x_2818_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___boxed__const__1));
lean_inc_ref(v_items_2814_);
v___x_2819_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed), 5, 3);
lean_closure_set(v___x_2819_, 0, v___x_2817_);
lean_closure_set(v___x_2819_, 1, v___x_2818_);
lean_closure_set(v___x_2819_, 2, v_items_2814_);
v___x_2820_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2819_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = l_Lean_Elab_Command_getRef___redArg(v___y_2807_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2824_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2822_, 1);
v___x_2824_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2807_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_quotContext_x3f_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v_rhs_2830_; lean_object* v_attrs_x3f_2831_; lean_object* v___x_2832_; 
lean_dec_ref_known(v___x_2824_, 1);
v_quotContext_x3f_2825_ = lean_ctor_get(v___y_2807_, 5);
v___x_2826_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
v___x_2827_ = 0;
v___x_2828_ = l_Lean_mkIdentFrom(v_x_2454_, v___x_2826_, v___x_2827_);
v___x_2829_ = lean_unsigned_to_nat(9u);
v_rhs_2830_ = l_Lean_Syntax_getArg(v_x_2454_, v___x_2829_);
lean_dec(v_x_2454_);
lean_inc(v_rhs_2830_);
v_attrs_x3f_2831_ = l_Lean_Elab_Command_addInheritDocDefault(v_rhs_2830_, v___y_2805_);
v___x_2832_ = l_Lean_SourceInfo_fromRef(v_a_2823_, v___x_2827_);
lean_dec(v_a_2823_);
if (lean_obj_tag(v_quotContext_x3f_2825_) == 0)
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2808_);
lean_dec_ref(v___x_2833_);
v___y_2776_ = v_attrs_x3f_2831_;
v___y_2777_ = v___x_2827_;
v___y_2778_ = v___y_2801_;
v___y_2779_ = v___y_2802_;
v___y_2780_ = v___y_2804_;
v___y_2781_ = v___y_2808_;
v___y_2782_ = v___x_2828_;
v___y_2783_ = v___x_2832_;
v___y_2784_ = v___y_2807_;
v___y_2785_ = v___y_2800_;
v___y_2786_ = v_items_2814_;
v___y_2787_ = v___y_2803_;
v___y_2788_ = v_a_2821_;
v___y_2789_ = v_rhs_2830_;
v___y_2790_ = v_a_2811_;
v___y_2791_ = v___x_2816_;
goto v___jp_2775_;
}
else
{
v___y_2776_ = v_attrs_x3f_2831_;
v___y_2777_ = v___x_2827_;
v___y_2778_ = v___y_2801_;
v___y_2779_ = v___y_2802_;
v___y_2780_ = v___y_2804_;
v___y_2781_ = v___y_2808_;
v___y_2782_ = v___x_2828_;
v___y_2783_ = v___x_2832_;
v___y_2784_ = v___y_2807_;
v___y_2785_ = v___y_2800_;
v___y_2786_ = v_items_2814_;
v___y_2787_ = v___y_2803_;
v___y_2788_ = v_a_2821_;
v___y_2789_ = v_rhs_2830_;
v___y_2790_ = v_a_2811_;
v___y_2791_ = v___x_2816_;
goto v___jp_2775_;
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_a_2823_);
lean_dec(v_a_2821_);
lean_dec_ref(v_items_2814_);
lean_dec(v_a_2811_);
lean_dec(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec(v___y_2800_);
lean_dec(v_x_2454_);
v_a_2834_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2824_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2824_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec(v_a_2821_);
lean_dec_ref(v_items_2814_);
lean_dec(v_a_2811_);
lean_dec(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec(v___y_2800_);
lean_dec(v_x_2454_);
v_a_2842_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2822_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2822_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec_ref(v_items_2814_);
lean_dec(v_a_2811_);
lean_dec(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec(v___y_2800_);
lean_dec(v_x_2454_);
v_a_2850_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2820_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2820_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec(v___y_2800_);
lean_dec(v_x_2454_);
v_a_2858_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2810_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2810_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
v___jp_2866_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; 
v___x_2877_ = lean_unsigned_to_nat(6u);
v___x_2878_ = l_Lean_Syntax_getArg(v_x_2454_, v___x_2877_);
v___x_2879_ = l_Lean_Syntax_isNone(v___x_2878_);
if (v___x_2879_ == 0)
{
uint8_t v___x_2880_; 
lean_inc(v___x_2878_);
v___x_2880_ = l_Lean_Syntax_matchesNull(v___x_2878_, v___y_2871_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; 
lean_dec(v___x_2878_);
lean_dec(v_name_x3f_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v___y_2867_);
lean_dec(v_x_2454_);
v___x_2881_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2881_;
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; 
v___x_2882_ = l_Lean_Syntax_getArg(v___x_2878_, v___x_2598_);
lean_dec(v___x_2878_);
v___x_2883_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
lean_inc(v___x_2882_);
v___x_2884_ = l_Lean_Syntax_isOfKind(v___x_2882_, v___x_2883_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; 
lean_dec(v___x_2882_);
lean_dec(v_name_x3f_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v___y_2867_);
lean_dec(v_x_2454_);
v___x_2885_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2885_;
}
else
{
lean_object* v_prio_x3f_2886_; lean_object* v___x_2887_; 
v_prio_x3f_2886_ = l_Lean_Syntax_getArg(v___x_2882_, v___y_2868_);
lean_dec(v___x_2882_);
v___x_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2887_, 0, v_prio_x3f_2886_);
v___y_2800_ = v___y_2867_;
v___y_2801_ = v___y_2869_;
v___y_2802_ = v___y_2870_;
v___y_2803_ = v___y_2872_;
v___y_2804_ = v_name_x3f_2874_;
v___y_2805_ = v___y_2873_;
v_prio_x3f_2806_ = v___x_2887_;
v___y_2807_ = v___y_2875_;
v___y_2808_ = v___y_2876_;
goto v___jp_2799_;
}
}
}
else
{
lean_object* v___x_2888_; 
lean_dec(v___x_2878_);
v___x_2888_ = lean_box(0);
v___y_2800_ = v___y_2867_;
v___y_2801_ = v___y_2869_;
v___y_2802_ = v___y_2870_;
v___y_2803_ = v___y_2872_;
v___y_2804_ = v_name_x3f_2874_;
v___y_2805_ = v___y_2873_;
v_prio_x3f_2806_ = v___x_2888_;
v___y_2807_ = v___y_2875_;
v___y_2808_ = v___y_2876_;
goto v___jp_2799_;
}
}
v___jp_2889_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; uint8_t v___x_2901_; 
v___x_2899_ = lean_unsigned_to_nat(5u);
v___x_2900_ = l_Lean_Syntax_getArg(v_x_2454_, v___x_2899_);
v___x_2901_ = l_Lean_Syntax_isNone(v___x_2900_);
if (v___x_2901_ == 0)
{
uint8_t v___x_2902_; 
lean_inc(v___x_2900_);
v___x_2902_ = l_Lean_Syntax_matchesNull(v___x_2900_, v___y_2894_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; 
lean_dec(v___x_2900_);
lean_dec(v_prec_x3f_2896_);
lean_dec(v___y_2895_);
lean_dec(v___y_2893_);
lean_dec(v___y_2890_);
lean_dec(v_x_2454_);
v___x_2903_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2903_;
}
else
{
lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2904_ = l_Lean_Syntax_getArg(v___x_2900_, v___x_2598_);
lean_dec(v___x_2900_);
v___x_2905_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
lean_inc(v___x_2904_);
v___x_2906_ = l_Lean_Syntax_isOfKind(v___x_2904_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; 
lean_dec(v___x_2904_);
lean_dec(v_prec_x3f_2896_);
lean_dec(v___y_2895_);
lean_dec(v___y_2893_);
lean_dec(v___y_2890_);
lean_dec(v_x_2454_);
v___x_2907_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2907_;
}
else
{
lean_object* v_name_x3f_2908_; lean_object* v___x_2909_; 
v_name_x3f_2908_ = l_Lean_Syntax_getArg(v___x_2904_, v___y_2891_);
lean_dec(v___x_2904_);
v___x_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2909_, 0, v_name_x3f_2908_);
v___y_2867_ = v___y_2890_;
v___y_2868_ = v___y_2891_;
v___y_2869_ = v___y_2892_;
v___y_2870_ = v___y_2893_;
v___y_2871_ = v___y_2894_;
v___y_2872_ = v_prec_x3f_2896_;
v___y_2873_ = v___y_2895_;
v_name_x3f_2874_ = v___x_2909_;
v___y_2875_ = v___y_2897_;
v___y_2876_ = v___y_2898_;
goto v___jp_2866_;
}
}
}
else
{
lean_object* v___x_2910_; 
lean_dec(v___x_2900_);
v___x_2910_ = lean_box(0);
v___y_2867_ = v___y_2890_;
v___y_2868_ = v___y_2891_;
v___y_2869_ = v___y_2892_;
v___y_2870_ = v___y_2893_;
v___y_2871_ = v___y_2894_;
v___y_2872_ = v_prec_x3f_2896_;
v___y_2873_ = v___y_2895_;
v_name_x3f_2874_ = v___x_2910_;
v___y_2875_ = v___y_2897_;
v___y_2876_ = v___y_2898_;
goto v___jp_2866_;
}
}
v___jp_2911_:
{
lean_object* v___x_2917_; lean_object* v_attrKind_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; uint8_t v___x_2921_; 
v___x_2917_ = lean_unsigned_to_nat(2u);
v_attrKind_2918_ = l_Lean_Syntax_getArg(v_x_2454_, v___x_2917_);
v___x_2919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2));
v___x_2920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(v_attrKind_2918_);
v___x_2921_ = l_Lean_Syntax_isOfKind(v_attrKind_2918_, v___x_2920_);
if (v___x_2921_ == 0)
{
lean_object* v___x_2922_; 
lean_dec(v_attrKind_2918_);
lean_dec(v_attrs_x3f_2914_);
lean_dec(v___y_2912_);
lean_dec(v_x_2454_);
v___x_2922_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2922_;
}
else
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v___x_2923_ = lean_unsigned_to_nat(3u);
v___x_2924_ = lean_unsigned_to_nat(4u);
v___x_2925_ = l_Lean_Syntax_getArg(v_x_2454_, v___x_2924_);
v___x_2926_ = l_Lean_Syntax_isNone(v___x_2925_);
if (v___x_2926_ == 0)
{
uint8_t v___x_2927_; 
lean_inc(v___x_2925_);
v___x_2927_ = l_Lean_Syntax_matchesNull(v___x_2925_, v___y_2913_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; 
lean_dec(v___x_2925_);
lean_dec(v_attrKind_2918_);
lean_dec(v_attrs_x3f_2914_);
lean_dec(v___y_2912_);
lean_dec(v_x_2454_);
v___x_2928_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2928_;
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2929_ = l_Lean_Syntax_getArg(v___x_2925_, v___x_2598_);
lean_dec(v___x_2925_);
v___x_2930_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
lean_inc(v___x_2929_);
v___x_2931_ = l_Lean_Syntax_isOfKind(v___x_2929_, v___x_2930_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; 
lean_dec(v___x_2929_);
lean_dec(v_attrKind_2918_);
lean_dec(v_attrs_x3f_2914_);
lean_dec(v___y_2912_);
lean_dec(v_x_2454_);
v___x_2932_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2932_;
}
else
{
lean_object* v_prec_x3f_2933_; lean_object* v___x_2934_; 
v_prec_x3f_2933_ = l_Lean_Syntax_getArg(v___x_2929_, v___y_2913_);
lean_dec(v___x_2929_);
v___x_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2934_, 0, v_prec_x3f_2933_);
v___y_2890_ = v___y_2912_;
v___y_2891_ = v___x_2923_;
v___y_2892_ = v___x_2919_;
v___y_2893_ = v_attrKind_2918_;
v___y_2894_ = v___y_2913_;
v___y_2895_ = v_attrs_x3f_2914_;
v_prec_x3f_2896_ = v___x_2934_;
v___y_2897_ = v___y_2915_;
v___y_2898_ = v___y_2916_;
goto v___jp_2889_;
}
}
}
else
{
lean_object* v___x_2935_; 
lean_dec(v___x_2925_);
v___x_2935_ = lean_box(0);
v___y_2890_ = v___y_2912_;
v___y_2891_ = v___x_2923_;
v___y_2892_ = v___x_2919_;
v___y_2893_ = v_attrKind_2918_;
v___y_2894_ = v___y_2913_;
v___y_2895_ = v_attrs_x3f_2914_;
v_prec_x3f_2896_ = v___x_2935_;
v___y_2897_ = v___y_2915_;
v___y_2898_ = v___y_2916_;
goto v___jp_2889_;
}
}
}
v___jp_2936_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; 
v___x_2940_ = lean_unsigned_to_nat(1u);
v___x_2941_ = l_Lean_Syntax_getArg(v_x_2454_, v___x_2940_);
v___x_2942_ = l_Lean_Syntax_isNone(v___x_2941_);
if (v___x_2942_ == 0)
{
uint8_t v___x_2943_; 
lean_inc(v___x_2941_);
v___x_2943_ = l_Lean_Syntax_matchesNull(v___x_2941_, v___x_2940_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; 
lean_dec(v___x_2941_);
lean_dec(v_doc_x3f_2937_);
lean_dec(v_x_2454_);
v___x_2944_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2944_;
}
else
{
lean_object* v___x_2945_; lean_object* v___x_2946_; uint8_t v___x_2947_; 
v___x_2945_ = l_Lean_Syntax_getArg(v___x_2941_, v___x_2598_);
lean_dec(v___x_2941_);
v___x_2946_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
lean_inc(v___x_2945_);
v___x_2947_ = l_Lean_Syntax_isOfKind(v___x_2945_, v___x_2946_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; 
lean_dec(v___x_2945_);
lean_dec(v_doc_x3f_2937_);
lean_dec(v_x_2454_);
v___x_2948_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2948_;
}
else
{
lean_object* v___x_2949_; lean_object* v_attrs_x3f_2950_; lean_object* v___x_2951_; 
v___x_2949_ = l_Lean_Syntax_getArg(v___x_2945_, v___x_2940_);
lean_dec(v___x_2945_);
v_attrs_x3f_2950_ = l_Lean_Syntax_getArgs(v___x_2949_);
lean_dec(v___x_2949_);
v___x_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2951_, 0, v_attrs_x3f_2950_);
v___y_2912_ = v_doc_x3f_2937_;
v___y_2913_ = v___x_2940_;
v_attrs_x3f_2914_ = v___x_2951_;
v___y_2915_ = v___y_2938_;
v___y_2916_ = v___y_2939_;
goto v___jp_2911_;
}
}
}
else
{
lean_object* v___x_2952_; 
lean_dec(v___x_2941_);
v___x_2952_ = lean_box(0);
v___y_2912_ = v_doc_x3f_2937_;
v___y_2913_ = v___x_2940_;
v_attrs_x3f_2914_ = v___x_2952_;
v___y_2915_ = v___y_2938_;
v___y_2916_ = v___y_2939_;
goto v___jp_2911_;
}
}
}
v___jp_2458_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkUnexpander___boxed), 5, 3);
lean_closure_set(v___x_2464_, 0, v___y_2460_);
lean_closure_set(v___x_2464_, 1, v___y_2459_);
lean_closure_set(v___x_2464_, 2, v___y_2461_);
v___x_2465_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2464_, v___y_2462_, v___y_2463_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2476_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2476_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2476_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
if (lean_obj_tag(v_a_2466_) == 1)
{
lean_object* v_val_2470_; lean_object* v___x_2471_; 
lean_del_object(v___x_2468_);
v_val_2470_ = lean_ctor_get(v_a_2466_, 0);
lean_inc(v_val_2470_);
lean_dec_ref_known(v_a_2466_, 1);
v___x_2471_ = l_Lean_Elab_Command_elabCommand(v_val_2470_, v___y_2462_, v___y_2463_);
return v___x_2471_;
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_dec(v_a_2466_);
v___x_2472_ = lean_box(0);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2472_);
v___x_2474_ = v___x_2468_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
v_a_2477_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2465_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2465_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
v___jp_2489_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2500_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__2));
v___x_2501_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__3));
lean_inc_ref(v___y_2491_);
lean_inc_n(v___y_2490_, 4);
lean_inc_n(v___y_2497_, 15);
v___x_2502_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2502_, 0, v___y_2497_);
lean_ctor_set(v___x_2502_, 1, v___y_2490_);
lean_ctor_set(v___x_2502_, 2, v___y_2491_);
v___x_2503_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___y_2497_);
lean_ctor_set(v___x_2503_, 1, v___x_2500_);
v___x_2504_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__29));
lean_inc_ref_n(v___y_2493_, 4);
v___x_2505_ = l_Lean_Name_mkStr4(v___x_2485_, v___x_2486_, v___y_2493_, v___x_2504_);
v___x_2506_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__31));
v___x_2507_ = l_Lean_Name_mkStr4(v___x_2485_, v___x_2486_, v___y_2493_, v___x_2506_);
v___x_2508_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
v___x_2509_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___y_2497_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__34));
v___x_2511_ = l_Lean_Name_mkStr4(v___x_2485_, v___x_2486_, v___y_2493_, v___x_2510_);
v___x_2512_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
v___x_2513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___y_2497_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
lean_inc_ref(v___y_2498_);
v___x_2514_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___y_2497_);
lean_ctor_set(v___x_2514_, 1, v___y_2498_);
lean_inc_ref(v___x_2514_);
lean_inc(v___y_2492_);
lean_inc_ref(v___x_2513_);
lean_inc(v___x_2511_);
v___x_2515_ = l_Lean_Syntax_node3(v___y_2497_, v___x_2511_, v___x_2513_, v___y_2492_, v___x_2514_);
v___x_2516_ = l_Lean_Syntax_node1(v___y_2497_, v___y_2490_, v___x_2515_);
v___x_2517_ = l_Lean_Syntax_node1(v___y_2497_, v___y_2490_, v___x_2516_);
v___x_2518_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
v___x_2519_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___y_2497_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__4));
v___x_2521_ = l_Lean_Name_mkStr4(v___x_2485_, v___x_2486_, v___y_2493_, v___x_2520_);
v___x_2522_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__5));
v___x_2523_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___y_2497_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
lean_inc(v___y_2495_);
v___x_2524_ = l_Lean_Syntax_node3(v___y_2497_, v___x_2511_, v___x_2513_, v___y_2495_, v___x_2514_);
v___x_2525_ = l_Lean_Syntax_node2(v___y_2497_, v___x_2521_, v___x_2523_, v___x_2524_);
v___x_2526_ = l_Lean_Syntax_node4(v___y_2497_, v___x_2507_, v___x_2509_, v___x_2517_, v___x_2519_, v___x_2525_);
v___x_2527_ = l_Lean_Syntax_node1(v___y_2497_, v___y_2490_, v___x_2526_);
v___x_2528_ = l_Lean_Syntax_node1(v___y_2497_, v___x_2505_, v___x_2527_);
lean_inc_n(v___y_2494_, 2);
lean_inc_ref_n(v___x_2502_, 2);
v___x_2529_ = l_Lean_Syntax_node6(v___y_2497_, v___x_2501_, v___x_2502_, v___x_2502_, v___y_2494_, v___x_2503_, v___x_2502_, v___x_2528_);
v___x_2530_ = l_Lean_Elab_Command_isLocalAttrKind(v___y_2494_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Lean_Elab_Command_elabCommand(v___x_2529_, v___y_2499_, v___y_2496_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_dec_ref_known(v___x_2531_, 1);
v___y_2459_ = v___y_2492_;
v___y_2460_ = v___y_2494_;
v___y_2461_ = v___y_2495_;
v___y_2462_ = v___y_2499_;
v___y_2463_ = v___y_2496_;
goto v___jp_2458_;
}
else
{
lean_dec(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec(v___y_2492_);
return v___x_2531_;
}
}
else
{
lean_object* v___x_2532_; lean_object* v_scopes_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v_opts_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___f_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2532_ = lean_st_ref_get(v___y_2496_);
v_scopes_2533_ = lean_ctor_get(v___x_2532_, 2);
lean_inc(v_scopes_2533_);
lean_dec(v___x_2532_);
v___x_2534_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2535_ = l_List_head_x21___redArg(v___x_2534_, v_scopes_2533_);
lean_dec(v_scopes_2533_);
v_opts_2536_ = lean_ctor_get(v___x_2535_, 1);
lean_inc_ref(v_opts_2536_);
lean_dec(v___x_2535_);
v___x_2537_ = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
v___x_2538_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_2536_, v___x_2537_, v___x_2488_);
v___f_2539_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___lam__0), 2, 1);
lean_closure_set(v___f_2539_, 0, v___x_2538_);
v___x_2540_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_2540_, 0, v___x_2529_);
v___x_2541_ = l_Lean_Elab_Command_withScope___redArg(v___f_2539_, v___x_2540_, v___y_2499_, v___y_2496_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_dec_ref_known(v___x_2541_, 1);
v___y_2459_ = v___y_2492_;
v___y_2460_ = v___y_2494_;
v___y_2461_ = v___y_2495_;
v___y_2462_ = v___y_2499_;
v___y_2463_ = v___y_2496_;
goto v___jp_2458_;
}
else
{
lean_dec(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec(v___y_2492_);
return v___x_2541_;
}
}
}
v___jp_2542_:
{
size_t v_sz_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v_sz_2557_ = lean_array_size(v___y_2552_);
v___x_2558_ = lean_box_usize(v_sz_2557_);
v___x_2559_ = lean_box_usize(v___y_2555_);
v___x_2560_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed), 5, 3);
lean_closure_set(v___x_2560_, 0, v___x_2558_);
lean_closure_set(v___x_2560_, 1, v___x_2559_);
lean_closure_set(v___x_2560_, 2, v___y_2552_);
v___x_2561_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2560_, v___y_2549_, v___y_2547_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2563_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v___x_2563_ = l_Lean_Elab_Command_getRef___redArg(v___y_2549_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2565_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
v___x_2565_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2549_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_quotContext_x3f_2566_; size_t v_sz_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
lean_dec_ref_known(v___x_2565_, 1);
v_quotContext_x3f_2566_ = lean_ctor_get(v___y_2549_, 5);
v_sz_2567_ = lean_array_size(v___y_2556_);
v___x_2568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_2567_, v___y_2555_, v___y_2556_);
v___x_2569_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(v___x_2568_, v___y_2553_);
lean_dec_ref(v___x_2568_);
v___x_2570_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2570_, 0, v___y_2551_);
lean_ctor_set(v___x_2570_, 1, v___y_2548_);
lean_ctor_set(v___x_2570_, 2, v_a_2562_);
v___x_2571_ = l_Lean_SourceInfo_fromRef(v_a_2564_, v___y_2544_);
lean_dec(v_a_2564_);
if (lean_obj_tag(v_quotContext_x3f_2566_) == 0)
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2547_);
lean_dec_ref(v___x_2572_);
v___y_2490_ = v___y_2543_;
v___y_2491_ = v___y_2550_;
v___y_2492_ = v___x_2570_;
v___y_2493_ = v___y_2545_;
v___y_2494_ = v___y_2546_;
v___y_2495_ = v___x_2569_;
v___y_2496_ = v___y_2547_;
v___y_2497_ = v___x_2571_;
v___y_2498_ = v___y_2554_;
v___y_2499_ = v___y_2549_;
goto v___jp_2489_;
}
else
{
v___y_2490_ = v___y_2543_;
v___y_2491_ = v___y_2550_;
v___y_2492_ = v___x_2570_;
v___y_2493_ = v___y_2545_;
v___y_2494_ = v___y_2546_;
v___y_2495_ = v___x_2569_;
v___y_2496_ = v___y_2547_;
v___y_2497_ = v___x_2571_;
v___y_2498_ = v___y_2554_;
v___y_2499_ = v___y_2549_;
goto v___jp_2489_;
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec(v_a_2564_);
lean_dec(v_a_2562_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2553_);
lean_dec(v___y_2551_);
lean_dec(v___y_2548_);
lean_dec(v___y_2546_);
v_a_2573_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2565_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2565_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v_a_2562_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2553_);
lean_dec(v___y_2551_);
lean_dec(v___y_2548_);
lean_dec(v___y_2546_);
v_a_2581_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2563_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2563_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2553_);
lean_dec(v___y_2551_);
lean_dec(v___y_2548_);
lean_dec(v___y_2546_);
v_a_2589_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2561_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2561_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___boxed(lean_object* v_x_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_Elab_Command_elabNotation(v_x_2964_, v_a_2965_, v_a_2966_);
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2965_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(lean_object* v_00_u03b1_2969_, lean_object* v_x_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v_x_2970_, v___y_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2974_, lean_object* v_x_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(v_00_u03b1_2974_, v_x_2975_, v___y_2976_, v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec_ref(v_x_2975_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(lean_object* v_00_u03b1_2979_, lean_object* v_ref_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_2980_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___boxed(lean_object* v_00_u03b1_2985_, lean_object* v_ref_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(v_00_u03b1_2985_, v_ref_2986_, v___y_2987_, v___y_2988_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(lean_object* v_00_u03b1_2991_, lean_object* v_x_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2992_, v___y_2993_, v___y_2994_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___boxed(lean_object* v_00_u03b1_2997_, lean_object* v_x_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(v_00_u03b1_2997_, v_x_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(lean_object* v_msgData_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msgData_3003_, v___y_3005_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(v_msgData_3008_, v___y_3009_, v___y_3010_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(lean_object* v_as_3013_, lean_object* v_as_x27_3014_, lean_object* v_b_3015_, lean_object* v_a_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_3014_, v_b_3015_, v___y_3017_, v___y_3018_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___boxed(lean_object* v_as_3021_, lean_object* v_as_x27_3022_, lean_object* v_b_3023_, lean_object* v_a_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(v_as_3021_, v_as_x27_3022_, v_b_3023_, v_a_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v_as_x27_3022_);
lean_dec(v_as_3021_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(lean_object* v_00_u03b1_3029_, lean_object* v_ref_3030_, lean_object* v_msg_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_ref_3030_, v_msg_3031_, v___y_3032_, v___y_3033_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3036_, lean_object* v_ref_3037_, lean_object* v_msg_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(v_00_u03b1_3036_, v_ref_3037_, v_msg_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v_ref_3037_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_3043_, lean_object* v_m_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v_m_3044_, v_a_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_3047_, lean_object* v_m_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(v_00_u03b2_3047_, v_m_3048_, v_a_3049_);
lean_dec(v_a_3049_);
lean_dec_ref(v_m_3048_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(lean_object* v_00_u03b1_3051_, lean_object* v_msg_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_3052_, v___y_3053_, v___y_3054_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___boxed(lean_object* v_00_u03b1_3057_, lean_object* v_msg_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(v_00_u03b1_3057_, v_msg_3058_, v___y_3059_, v___y_3060_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
return v_res_3062_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(lean_object* v_00_u03b2_3063_, lean_object* v_x_3064_, lean_object* v_x_3065_){
_start:
{
uint8_t v___x_3066_; 
v___x_3066_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_3064_, v_x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3067_, lean_object* v_x_3068_, lean_object* v_x_3069_){
_start:
{
uint8_t v_res_3070_; lean_object* v_r_3071_; 
v_res_3070_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(v_00_u03b2_3067_, v_x_3068_, v_x_3069_);
lean_dec_ref(v_x_3069_);
lean_dec_ref(v_x_3068_);
v_r_3071_ = lean_box(v_res_3070_);
return v_r_3071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(lean_object* v_00_u03b2_3072_, lean_object* v_m_3073_, lean_object* v_query_3074_){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_m_3073_, v_query_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___boxed(lean_object* v_00_u03b2_3076_, lean_object* v_m_3077_, lean_object* v_query_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(v_00_u03b2_3076_, v_m_3077_, v_query_3078_);
lean_dec(v_query_3078_);
lean_dec_ref(v_m_3077_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(lean_object* v_msgData_3080_, lean_object* v_macroStack_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_msgData_3080_, v_macroStack_3081_, v___y_3083_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___boxed(lean_object* v_msgData_3086_, lean_object* v_macroStack_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(v_msgData_3086_, v_macroStack_3087_, v___y_3088_, v___y_3089_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
return v_res_3091_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(lean_object* v_00_u03b2_3092_, lean_object* v_x_3093_, size_t v_x_3094_, lean_object* v_x_3095_){
_start:
{
uint8_t v___x_3096_; 
v___x_3096_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_3093_, v_x_3094_, v_x_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___boxed(lean_object* v_00_u03b2_3097_, lean_object* v_x_3098_, lean_object* v_x_3099_, lean_object* v_x_3100_){
_start:
{
size_t v_x_25935__boxed_3101_; uint8_t v_res_3102_; lean_object* v_r_3103_; 
v_x_25935__boxed_3101_ = lean_unbox_usize(v_x_3099_);
lean_dec(v_x_3099_);
v_res_3102_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(v_00_u03b2_3097_, v_x_3098_, v_x_25935__boxed_3101_, v_x_3100_);
lean_dec_ref(v_x_3100_);
lean_dec_ref(v_x_3098_);
v_r_3103_ = lean_box(v_res_3102_);
return v_r_3103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23(lean_object* v_00_u03b2_3104_, lean_object* v_m_3105_, lean_object* v_query_3106_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23___redArg(v_m_3105_, v_query_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3108_, lean_object* v_m_3109_, lean_object* v_query_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23(v_00_u03b2_3108_, v_m_3109_, v_query_3110_);
lean_dec(v_query_3110_);
lean_dec_ref(v_m_3109_);
return v_res_3111_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(lean_object* v_00_u03b2_3112_, lean_object* v_keys_3113_, lean_object* v_vals_3114_, lean_object* v_heq_3115_, lean_object* v_i_3116_, lean_object* v_k_3117_){
_start:
{
uint8_t v___x_3118_; 
v___x_3118_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_3113_, v_i_3116_, v_k_3117_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___boxed(lean_object* v_00_u03b2_3119_, lean_object* v_keys_3120_, lean_object* v_vals_3121_, lean_object* v_heq_3122_, lean_object* v_i_3123_, lean_object* v_k_3124_){
_start:
{
uint8_t v_res_3125_; lean_object* v_r_3126_; 
v_res_3125_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(v_00_u03b2_3119_, v_keys_3120_, v_vals_3121_, v_heq_3122_, v_i_3123_, v_k_3124_);
lean_dec_ref(v_k_3124_);
lean_dec_ref(v_vals_3121_);
lean_dec_ref(v_keys_3120_);
v_r_3126_ = lean_box(v_res_3125_);
return v_r_3126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23_spec__26(lean_object* v_00_u03b2_3127_, lean_object* v_m_3128_, lean_object* v_query_3129_, lean_object* v_x_3130_, lean_object* v_x_3131_, lean_object* v_x_3132_, lean_object* v_x_3133_){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23_spec__26___redArg(v_m_3128_, v_query_3129_, v_x_3130_, v_x_3131_, v_x_3132_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23_spec__26___boxed(lean_object* v_00_u03b2_3135_, lean_object* v_m_3136_, lean_object* v_query_3137_, lean_object* v_x_3138_, lean_object* v_x_3139_, lean_object* v_x_3140_, lean_object* v_x_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18_spec__23_spec__26(v_00_u03b2_3135_, v_m_3136_, v_query_3137_, v_x_3138_, v_x_3139_, v_x_3140_, v_x_3141_);
lean_dec(v_query_3137_);
lean_dec_ref(v_m_3136_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1(){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3150_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3151_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
v___x_3152_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1));
v___x_3153_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___boxed), 4, 0);
v___x_3154_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3150_, v___x_3151_, v___x_3152_, v___x_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___boxed(lean_object* v_a_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
return v_res_3156_;
}
}
lean_object* runtime_initialize_Lean_Elab_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinNotation(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Notation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
