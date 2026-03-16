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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_strLitToPattern___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object*);
lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_topDown(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
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
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Macro_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Command_visibility_ofAttrKind(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_isLocalAttrKind(lean_object*);
extern lean_object* l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSyntax(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
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
static const lean_string_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabNotation"};
static const lean_object* l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkUnexpander___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 81, 117, 114, 113, 220, 215, 248)}};
static const lean_object* l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___boxed(lean_object*);
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
v___x_138_ = lean_erase_macro_scopes(v___x_137_);
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
lean_inc(v___x_142_);
v___x_145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_142_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
lean_ctor_set(v___x_145_, 2, v___x_144_);
lean_inc(v___x_142_);
v___x_146_ = l_Lean_Syntax_node1(v___x_142_, v___x_124_, v___x_145_);
lean_inc(v___x_107_);
lean_inc(v___x_142_);
v___x_147_ = l_Lean_Syntax_node1(v___x_142_, v___x_143_, v___x_107_);
lean_inc(v___x_142_);
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
uint8_t v___x_10646__boxed_155_; size_t v_sz_boxed_156_; size_t v_i_boxed_157_; lean_object* v_res_158_; 
v___x_10646__boxed_155_ = lean_unbox(v___x_150_);
v_sz_boxed_156_ = lean_unbox_usize(v_sz_152_);
lean_dec(v_sz_152_);
v_i_boxed_157_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_res_158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(v___x_10646__boxed_155_, v___x_151_, v_sz_boxed_156_, v_i_boxed_157_, v_bs_154_);
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
v___x_201_ = lean_erase_macro_scopes(v___x_200_);
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
lean_dec_ref(v_a_303_);
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
lean_inc(v_ref_349_);
lean_dec_ref(v_a_303_);
v___x_350_ = l_Lean_SourceInfo_fromRef(v_ref_349_, v___x_342_);
lean_dec(v_ref_349_);
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
lean_dec_ref(v_a_303_);
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
lean_dec_ref(v_a_303_);
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
lean_dec_ref(v_a_303_);
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
v___x_313_ = l_Array_append___redArg(v___y_308_, v___y_312_);
lean_dec_ref(v___y_312_);
lean_inc(v___y_311_);
v___x_314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_314_, 0, v___y_311_);
lean_ctor_set(v___x_314_, 1, v___y_309_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
v___x_315_ = l_Lean_Syntax_node2(v___y_311_, v___y_307_, v___y_306_, v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___y_310_);
return v___x_316_;
}
v___jp_317_:
{
lean_object* v_quotContext_321_; lean_object* v_currMacroScope_322_; lean_object* v_ref_323_; uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_quotContext_321_ = lean_ctor_get(v___y_319_, 1);
lean_inc(v_quotContext_321_);
v_currMacroScope_322_ = lean_ctor_get(v___y_319_, 2);
lean_inc(v_currMacroScope_322_);
v_ref_323_ = lean_ctor_get(v___y_319_, 5);
lean_inc(v_ref_323_);
lean_dec_ref(v___y_319_);
v___x_324_ = 0;
v___x_325_ = l_Lean_SourceInfo_fromRef(v_ref_323_, v___x_324_);
lean_dec(v_ref_323_);
v___x_326_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2));
v___x_327_ = lean_obj_once(&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3, &l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3_once, _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3);
v___x_328_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
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
lean_dec_ref(v_prec_x3f_318_);
v___x_335_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
v___x_336_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc(v___x_325_);
v___x_337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_325_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
lean_inc(v___x_325_);
v___x_338_ = l_Lean_Syntax_node2(v___x_325_, v___x_335_, v___x_337_, v_val_334_);
v___x_339_ = l_Array_mkArray1___redArg(v___x_338_);
v___y_306_ = v___x_331_;
v___y_307_ = v___x_326_;
v___y_308_ = v___x_333_;
v___y_309_ = v___x_332_;
v___y_310_ = v___y_320_;
v___y_311_ = v___x_325_;
v___y_312_ = v___x_339_;
goto v___jp_305_;
}
else
{
lean_object* v___x_340_; 
lean_dec(v_prec_x3f_318_);
v___x_340_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_306_ = v___x_331_;
v___y_307_ = v___x_326_;
v___y_308_ = v___x_333_;
v___y_309_ = v___x_332_;
v___y_310_ = v___y_320_;
v___y_311_ = v___x_325_;
v___y_312_ = v___x_340_;
goto v___jp_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(lean_object* v_stx_380_, lean_object* v_a_381_){
_start:
{
uint8_t v___y_383_; lean_object* v_k_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
lean_inc(v_stx_380_);
v_k_390_ = l_Lean_Syntax_getKind(v_stx_380_);
v___x_391_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
v___x_392_ = lean_name_eq(v_k_390_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12));
v___x_394_ = lean_name_eq(v_k_390_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
v___x_396_ = lean_name_eq(v_k_390_, v___x_395_);
lean_dec(v_k_390_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
lean_dec(v_stx_380_);
v___x_397_ = l_Lean_Macro_throwUnsupported___redArg(v_a_381_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_398_ = lean_unsigned_to_nat(4u);
v___x_399_ = l_Lean_Syntax_getArg(v_stx_380_, v___x_398_);
v___x_400_ = l_Lean_Syntax_isNone(v___x_399_);
lean_dec(v___x_399_);
if (v___x_400_ == 0)
{
v___y_383_ = v___x_396_;
goto v___jp_382_;
}
else
{
v___y_383_ = v___x_394_;
goto v___jp_382_;
}
}
}
else
{
lean_object* v___x_401_; 
lean_dec(v_k_390_);
v___x_401_ = l_Lean_Elab_Command_strLitToPattern___redArg(v_stx_380_, v_a_381_);
lean_dec(v_stx_380_);
return v___x_401_;
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec(v_k_390_);
v___x_402_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = l_Lean_Syntax_getArg(v_stx_380_, v___x_403_);
lean_dec(v_stx_380_);
v___x_405_ = lean_box(0);
v___x_406_ = l_Lean_Syntax_mkAntiquotNode(v___x_402_, v___x_404_, v___x_403_, v___x_405_, v___x_392_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v_a_381_);
return v___x_407_;
}
v___jp_382_:
{
if (v___y_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = l_Lean_Syntax_getArg(v_stx_380_, v___x_384_);
lean_dec(v_stx_380_);
v___x_386_ = l_Lean_Elab_Command_strLitToPattern___redArg(v___x_385_, v_a_381_);
lean_dec(v___x_385_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = lean_unsigned_to_nat(3u);
v___x_388_ = l_Lean_Syntax_getArg(v_stx_380_, v___x_387_);
lean_dec(v_stx_380_);
v___x_389_ = l_Lean_Elab_Command_strLitToPattern___redArg(v___x_388_, v_a_381_);
lean_dec(v___x_388_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern(lean_object* v_stx_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(v_stx_408_, v_a_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___boxed(lean_object* v_stx_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Elab_Command_expandNotationItemIntoPattern(v_stx_412_, v_a_413_, v_a_414_);
lean_dec_ref(v_a_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux(lean_object* v_parens_416_, lean_object* v_body_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Syntax_getHeadInfo(v_parens_416_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_leading_419_; lean_object* v___x_420_; 
v_leading_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc_ref(v_leading_419_);
lean_dec_ref(v___x_418_);
v___x_420_ = l_Lean_Syntax_getHeadInfo(v_body_417_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_pos_421_; lean_object* v_trailing_422_; lean_object* v_endPos_423_; lean_object* v___x_424_; 
v_pos_421_ = lean_ctor_get(v___x_420_, 1);
lean_inc(v_pos_421_);
v_trailing_422_ = lean_ctor_get(v___x_420_, 2);
lean_inc_ref(v_trailing_422_);
v_endPos_423_ = lean_ctor_get(v___x_420_, 3);
lean_inc(v_endPos_423_);
lean_dec_ref(v___x_420_);
v___x_424_ = l_Lean_Syntax_getTailInfo(v_body_417_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_leading_425_; lean_object* v_pos_426_; lean_object* v_endPos_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_448_; 
v_leading_425_ = lean_ctor_get(v___x_424_, 0);
v_pos_426_ = lean_ctor_get(v___x_424_, 1);
v_endPos_427_ = lean_ctor_get(v___x_424_, 3);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v___x_424_, 2);
lean_dec(v_unused_449_);
v___x_429_ = v___x_424_;
v_isShared_430_ = v_isSharedCheck_448_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_endPos_427_);
lean_inc(v_pos_426_);
lean_inc(v_leading_425_);
lean_dec(v___x_424_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_448_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Syntax_getTailInfo(v_parens_416_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_trailing_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_444_; 
v_trailing_432_ = lean_ctor_get(v___x_431_, 2);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; lean_object* v_unused_446_; lean_object* v_unused_447_; 
v_unused_445_ = lean_ctor_get(v___x_431_, 3);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v___x_431_, 1);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v___x_431_, 0);
lean_dec(v_unused_447_);
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_444_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_trailing_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_444_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 3, v_endPos_423_);
lean_ctor_set(v___x_434_, 2, v_trailing_422_);
lean_ctor_set(v___x_434_, 1, v_pos_421_);
lean_ctor_set(v___x_434_, 0, v_leading_419_);
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_leading_419_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_pos_421_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_trailing_422_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v_endPos_423_);
v___x_437_ = v_reuseFailAlloc_443_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_438_ = l_Lean_Syntax_setHeadInfo(v_body_417_, v___x_437_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 2, v_trailing_432_);
v___x_440_ = v___x_429_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_leading_425_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_pos_426_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_trailing_432_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v_endPos_427_);
v___x_440_ = v_reuseFailAlloc_442_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Syntax_setTailInfo(v___x_438_, v___x_440_);
return v___x_441_;
}
}
}
}
else
{
lean_dec(v___x_431_);
lean_del_object(v___x_429_);
lean_dec(v_endPos_427_);
lean_dec(v_pos_426_);
lean_dec_ref(v_leading_425_);
lean_dec(v_endPos_423_);
lean_dec_ref(v_trailing_422_);
lean_dec(v_pos_421_);
lean_dec_ref(v_leading_419_);
return v_body_417_;
}
}
}
else
{
lean_dec(v___x_424_);
lean_dec(v_endPos_423_);
lean_dec_ref(v_trailing_422_);
lean_dec(v_pos_421_);
lean_dec_ref(v_leading_419_);
return v_body_417_;
}
}
else
{
lean_dec(v___x_420_);
lean_dec_ref(v_leading_419_);
return v_body_417_;
}
}
else
{
lean_dec(v___x_418_);
return v_body_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux___boxed(lean_object* v_parens_450_, lean_object* v_body_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Elab_Command_removeParenthesesAux(v_parens_450_, v_body_451_);
lean_dec(v_parens_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses(lean_object* v_stx_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__1));
lean_inc(v_stx_468_);
v___x_472_ = l_Lean_Syntax_isOfKind(v_stx_468_, v___x_471_);
if (v___x_472_ == 0)
{
if (lean_obj_tag(v_stx_468_) == 1)
{
lean_object* v_info_473_; lean_object* v_kind_474_; lean_object* v_args_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_503_; 
v_info_473_ = lean_ctor_get(v_stx_468_, 0);
v_kind_474_ = lean_ctor_get(v_stx_468_, 1);
v_args_475_ = lean_ctor_get(v_stx_468_, 2);
v_isSharedCheck_503_ = !lean_is_exclusive(v_stx_468_);
if (v_isSharedCheck_503_ == 0)
{
v___x_477_ = v_stx_468_;
v_isShared_478_ = v_isSharedCheck_503_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_args_475_);
lean_inc(v_kind_474_);
lean_inc(v_info_473_);
lean_dec(v_stx_468_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_503_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
size_t v_sz_479_; size_t v___x_480_; lean_object* v___x_481_; 
v_sz_479_ = lean_array_size(v_args_475_);
v___x_480_ = ((size_t)0ULL);
v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_479_, v___x_480_, v_args_475_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_493_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_a_483_ = lean_ctor_get(v___x_481_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_493_ == 0)
{
v___x_485_ = v___x_481_;
v_isShared_486_ = v_isSharedCheck_493_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_493_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 2, v_a_482_);
v___x_488_ = v___x_477_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_info_473_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_kind_474_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_a_482_);
v___x_488_ = v_reuseFailAlloc_492_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_488_);
v___x_490_ = v___x_485_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_a_483_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_del_object(v___x_477_);
lean_dec(v_kind_474_);
lean_dec(v_info_473_);
v_a_494_ = lean_ctor_get(v___x_481_, 0);
v_a_495_ = lean_ctor_get(v___x_481_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_481_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_inc(v_a_494_);
lean_dec(v___x_481_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_494_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
else
{
lean_object* v___x_504_; 
lean_dec_ref(v_a_469_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v_stx_468_);
lean_ctor_set(v___x_504_, 1, v_a_470_);
return v___x_504_;
}
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = l_Lean_Syntax_getArg(v_stx_468_, v___x_505_);
v___x_507_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__3));
lean_inc(v___x_506_);
v___x_508_ = l_Lean_Syntax_isOfKind(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_dec(v___x_506_);
if (lean_obj_tag(v_stx_468_) == 1)
{
lean_object* v_info_509_; lean_object* v_kind_510_; lean_object* v_args_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_539_; 
v_info_509_ = lean_ctor_get(v_stx_468_, 0);
v_kind_510_ = lean_ctor_get(v_stx_468_, 1);
v_args_511_ = lean_ctor_get(v_stx_468_, 2);
v_isSharedCheck_539_ = !lean_is_exclusive(v_stx_468_);
if (v_isSharedCheck_539_ == 0)
{
v___x_513_ = v_stx_468_;
v_isShared_514_ = v_isSharedCheck_539_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_args_511_);
lean_inc(v_kind_510_);
lean_inc(v_info_509_);
lean_dec(v_stx_468_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_539_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
size_t v_sz_515_; size_t v___x_516_; lean_object* v___x_517_; 
v_sz_515_ = lean_array_size(v_args_511_);
v___x_516_ = ((size_t)0ULL);
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_515_, v___x_516_, v_args_511_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_529_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_a_519_ = lean_ctor_get(v___x_517_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_529_ == 0)
{
v___x_521_ = v___x_517_;
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 2, v_a_518_);
v___x_524_ = v___x_513_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_info_509_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_kind_510_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_a_518_);
v___x_524_ = v_reuseFailAlloc_528_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_526_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_524_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_a_519_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_object* v_a_530_; lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_del_object(v___x_513_);
lean_dec(v_kind_510_);
lean_dec(v_info_509_);
v_a_530_ = lean_ctor_get(v___x_517_, 0);
v_a_531_ = lean_ctor_get(v___x_517_, 1);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_517_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_inc(v_a_530_);
lean_dec(v___x_517_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_530_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
else
{
lean_object* v___x_540_; 
lean_dec_ref(v_a_469_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v_stx_468_);
lean_ctor_set(v___x_540_, 1, v_a_470_);
return v___x_540_;
}
}
else
{
lean_object* v___x_541_; lean_object* v_h_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_541_ = lean_unsigned_to_nat(1u);
v_h_542_ = l_Lean_Syntax_getArg(v___x_506_, v___x_541_);
lean_dec(v___x_506_);
v___x_543_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__5));
lean_inc(v_h_542_);
v___x_544_ = l_Lean_Syntax_isOfKind(v_h_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_dec(v_h_542_);
if (lean_obj_tag(v_stx_468_) == 1)
{
lean_object* v_info_545_; lean_object* v_kind_546_; lean_object* v_args_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_575_; 
v_info_545_ = lean_ctor_get(v_stx_468_, 0);
v_kind_546_ = lean_ctor_get(v_stx_468_, 1);
v_args_547_ = lean_ctor_get(v_stx_468_, 2);
v_isSharedCheck_575_ = !lean_is_exclusive(v_stx_468_);
if (v_isSharedCheck_575_ == 0)
{
v___x_549_ = v_stx_468_;
v_isShared_550_ = v_isSharedCheck_575_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_args_547_);
lean_inc(v_kind_546_);
lean_inc(v_info_545_);
lean_dec(v_stx_468_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_575_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
size_t v_sz_551_; size_t v___x_552_; lean_object* v___x_553_; 
v_sz_551_ = lean_array_size(v_args_547_);
v___x_552_ = ((size_t)0ULL);
v___x_553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_551_, v___x_552_, v_args_547_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_565_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_a_555_ = lean_ctor_get(v___x_553_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_565_ == 0)
{
v___x_557_ = v___x_553_;
v_isShared_558_ = v_isSharedCheck_565_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_565_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 2, v_a_554_);
v___x_560_ = v___x_549_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_info_545_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_kind_546_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_a_554_);
v___x_560_ = v_reuseFailAlloc_564_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_562_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_560_);
v___x_562_ = v___x_557_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_a_555_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_object* v_a_566_; lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_del_object(v___x_549_);
lean_dec(v_kind_546_);
lean_dec(v_info_545_);
v_a_566_ = lean_ctor_get(v___x_553_, 0);
v_a_567_ = lean_ctor_get(v___x_553_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_553_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_inc(v_a_566_);
lean_dec(v___x_553_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_566_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
else
{
lean_object* v___x_576_; 
lean_dec_ref(v_a_469_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_stx_468_);
lean_ctor_set(v___x_576_, 1, v_a_470_);
return v___x_576_;
}
}
else
{
lean_object* v_e_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_e_577_ = l_Lean_Syntax_getArg(v_stx_468_, v___x_541_);
v___x_578_ = l_Lean_TSyntax_getHygieneInfo(v_h_542_);
lean_dec(v_h_542_);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_inc_ref(v_a_469_);
lean_inc(v_e_577_);
v___x_580_ = l_Lean_Elab_Term_expandCDot_x3f(v_e_577_, v___x_579_, v_a_469_, v_a_470_);
lean_dec_ref(v___x_579_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v_a_582_; lean_object* v___y_584_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
v_a_582_ = lean_ctor_get(v___x_580_, 1);
lean_inc(v_a_582_);
lean_dec_ref(v___x_580_);
if (lean_obj_tag(v_a_581_) == 0)
{
v___y_584_ = v_e_577_;
goto v___jp_583_;
}
else
{
lean_object* v_val_596_; 
lean_dec(v_e_577_);
v_val_596_ = lean_ctor_get(v_a_581_, 0);
lean_inc(v_val_596_);
lean_dec_ref(v_a_581_);
v___y_584_ = v_val_596_;
goto v___jp_583_;
}
v___jp_583_:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Elab_Command_removeParentheses(v___y_584_, v_a_469_, v_a_582_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_595_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_a_587_ = lean_ctor_get(v___x_585_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_595_ == 0)
{
v___x_589_ = v___x_585_;
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = l_Lean_Elab_Command_removeParenthesesAux(v_stx_468_, v_a_586_);
lean_dec(v_stx_468_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_591_);
v___x_593_ = v___x_589_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_a_587_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
lean_dec(v_stx_468_);
return v___x_585_;
}
}
}
else
{
lean_object* v_a_597_; lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_e_577_);
lean_dec_ref(v_a_469_);
lean_dec(v_stx_468_);
v_a_597_ = lean_ctor_get(v___x_580_, 0);
v_a_598_ = lean_ctor_get(v___x_580_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_580_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_inc(v_a_597_);
lean_dec(v___x_580_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_597_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_a_598_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(size_t v_sz_606_, size_t v_i_607_, lean_object* v_bs_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
uint8_t v___x_611_; 
v___x_611_ = lean_usize_dec_lt(v_i_607_, v_sz_606_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
lean_dec_ref(v___y_609_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_bs_608_);
lean_ctor_set(v___x_612_, 1, v___y_610_);
return v___x_612_;
}
else
{
lean_object* v_v_613_; lean_object* v___x_614_; 
v_v_613_ = lean_array_uget_borrowed(v_bs_608_, v_i_607_);
lean_inc_ref(v___y_609_);
lean_inc(v_v_613_);
v___x_614_ = l_Lean_Elab_Command_removeParentheses(v_v_613_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v_a_616_; lean_object* v___x_617_; lean_object* v_bs_x27_618_; size_t v___x_619_; size_t v___x_620_; lean_object* v___x_621_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
v_a_616_ = lean_ctor_get(v___x_614_, 1);
lean_inc(v_a_616_);
lean_dec_ref(v___x_614_);
v___x_617_ = lean_unsigned_to_nat(0u);
v_bs_x27_618_ = lean_array_uset(v_bs_608_, v_i_607_, v___x_617_);
v___x_619_ = ((size_t)1ULL);
v___x_620_ = lean_usize_add(v_i_607_, v___x_619_);
v___x_621_ = lean_array_uset(v_bs_x27_618_, v_i_607_, v_a_615_);
v_i_607_ = v___x_620_;
v_bs_608_ = v___x_621_;
v___y_610_ = v_a_616_;
goto _start;
}
else
{
lean_object* v_a_623_; lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v___y_609_);
lean_dec_ref(v_bs_608_);
v_a_623_ = lean_ctor_get(v___x_614_, 0);
v_a_624_ = lean_ctor_get(v___x_614_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_614_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_inc(v_a_623_);
lean_dec(v___x_614_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_623_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0___boxed(lean_object* v_sz_632_, lean_object* v_i_633_, lean_object* v_bs_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
size_t v_sz_boxed_637_; size_t v_i_boxed_638_; lean_object* v_res_639_; 
v_sz_boxed_637_ = lean_unbox_usize(v_sz_632_);
lean_dec(v_sz_632_);
v_i_boxed_638_ = lean_unbox_usize(v_i_633_);
lean_dec(v_i_633_);
v_res_639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_boxed_637_, v_i_boxed_638_, v_bs_634_, v___y_635_, v___y_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(uint8_t v_firstChoiceOnly_643_, lean_object* v_stx_644_, lean_object* v_b_645_, lean_object* v_inst_646_){
_start:
{
lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_660_; lean_object* v_a_661_; lean_object* v_snd_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_695_; 
v_snd_671_ = lean_ctor_get(v_b_645_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_b_645_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v_b_645_, 0);
lean_dec(v_unused_696_);
v___x_673_ = v_b_645_;
v_isShared_674_ = v_isSharedCheck_695_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_snd_671_);
lean_dec(v_b_645_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_695_;
goto v_resetjp_672_;
}
v___jp_647_:
{
lean_object* v___x_650_; lean_object* v___x_651_; size_t v_sz_652_; size_t v___x_653_; lean_object* v___x_654_; lean_object* v_fst_655_; 
v___x_650_ = lean_box(0);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___y_649_);
v_sz_652_ = lean_array_size(v___y_648_);
v___x_653_ = ((size_t)0ULL);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v_firstChoiceOnly_643_, v_inst_646_, v___y_648_, v_sz_652_, v___x_653_, v___x_651_);
lean_dec_ref(v___y_648_);
v_fst_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_fst_655_);
if (lean_obj_tag(v_fst_655_) == 0)
{
lean_object* v_snd_656_; lean_object* v___x_657_; 
v_snd_656_ = lean_ctor_get(v___x_654_, 1);
lean_inc(v_snd_656_);
lean_dec_ref(v___x_654_);
v___x_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_657_, 0, v_snd_656_);
return v___x_657_;
}
else
{
lean_object* v_val_658_; 
lean_dec_ref(v___x_654_);
v_val_658_ = lean_ctor_get(v_fst_655_, 0);
lean_inc(v_val_658_);
lean_dec_ref(v_fst_655_);
return v_val_658_;
}
}
v___jp_659_:
{
if (lean_obj_tag(v_stx_644_) == 1)
{
lean_dec_ref(v___y_660_);
if (v_firstChoiceOnly_643_ == 0)
{
lean_object* v_args_662_; 
v_args_662_ = lean_ctor_get(v_stx_644_, 2);
lean_inc_ref(v_args_662_);
lean_dec_ref(v_stx_644_);
v___y_648_ = v_args_662_;
v___y_649_ = v_a_661_;
goto v___jp_647_;
}
else
{
lean_object* v_kind_663_; lean_object* v_args_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_kind_663_ = lean_ctor_get(v_stx_644_, 1);
lean_inc(v_kind_663_);
v_args_664_ = lean_ctor_get(v_stx_644_, 2);
lean_inc_ref(v_args_664_);
lean_dec_ref(v_stx_644_);
v___x_665_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1));
v___x_666_ = lean_name_eq(v_kind_663_, v___x_665_);
lean_dec(v_kind_663_);
if (v___x_666_ == 0)
{
v___y_648_ = v_args_664_;
v___y_649_ = v_a_661_;
goto v___jp_647_;
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_box(0);
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_array_get(v___x_667_, v_args_664_, v___x_668_);
lean_dec_ref(v_args_664_);
v_stx_644_ = v___x_669_;
v_b_645_ = v_a_661_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_a_661_);
lean_dec(v_stx_644_);
return v___y_660_;
}
}
v_resetjp_672_:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_box(0);
v___x_676_ = l_Lean_Syntax_isAntiquot(v_stx_644_);
if (v___x_676_ == 0)
{
lean_object* v___x_678_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_678_ = v___x_673_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_snd_671_);
v___x_678_ = v_reuseFailAlloc_680_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; 
lean_inc_ref(v___x_678_);
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
v___y_660_ = v___x_679_;
v_a_661_ = v___x_678_;
goto v___jp_659_;
}
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_681_ = l_Lean_Syntax_getAntiquotTerm(v_stx_644_);
v___x_682_ = l_Lean_Syntax_getId(v___x_681_);
lean_dec(v___x_681_);
v___x_683_ = l_Lean_NameSet_contains(v_snd_671_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = l_Lean_NameSet_insert(v_snd_671_, v___x_682_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v___x_684_);
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_686_ = v___x_673_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___x_684_);
v___x_686_ = v_reuseFailAlloc_688_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; 
lean_inc_ref(v___x_686_);
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___y_660_ = v___x_687_;
v_a_661_ = v___x_686_;
goto v___jp_659_;
}
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
lean_dec(v___x_682_);
lean_dec(v_stx_644_);
v___x_689_ = lean_box(v___x_683_);
v___x_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_690_);
v___x_692_ = v___x_673_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_snd_671_);
v___x_692_ = v_reuseFailAlloc_694_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; 
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(uint8_t v_firstChoiceOnly_697_, lean_object* v_inst_698_, lean_object* v_as_699_, size_t v_sz_700_, size_t v_i_701_, lean_object* v_b_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = lean_usize_dec_lt(v_i_701_, v_sz_700_);
if (v___x_703_ == 0)
{
return v_b_702_;
}
else
{
lean_object* v_snd_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_722_; 
v_snd_704_ = lean_ctor_get(v_b_702_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_b_702_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v_b_702_, 0);
lean_dec(v_unused_723_);
v___x_706_ = v_b_702_;
v_isShared_707_ = v_isSharedCheck_722_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_snd_704_);
lean_dec(v_b_702_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_722_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_a_708_; lean_object* v___x_709_; 
v_a_708_ = lean_array_uget_borrowed(v_as_699_, v_i_701_);
lean_inc(v_snd_704_);
lean_inc(v_a_708_);
v___x_709_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v_firstChoiceOnly_697_, v_a_708_, v_snd_704_, v_inst_698_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_710_);
v___x_712_ = v___x_706_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_snd_704_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
lean_dec(v_snd_704_);
v_a_714_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_714_);
lean_dec_ref(v___x_709_);
v___x_715_ = lean_box(0);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v_a_714_);
lean_ctor_set(v___x_706_, 0, v___x_715_);
v___x_717_ = v___x_706_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_a_714_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
size_t v___x_718_; size_t v___x_719_; 
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_add(v_i_701_, v___x_718_);
v_i_701_ = v___x_719_;
v_b_702_ = v___x_717_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0___boxed(lean_object* v_firstChoiceOnly_724_, lean_object* v_inst_725_, lean_object* v_as_726_, lean_object* v_sz_727_, lean_object* v_i_728_, lean_object* v_b_729_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_730_; size_t v_sz_boxed_731_; size_t v_i_boxed_732_; lean_object* v_res_733_; 
v_firstChoiceOnly_boxed_730_ = lean_unbox(v_firstChoiceOnly_724_);
v_sz_boxed_731_ = lean_unbox_usize(v_sz_727_);
lean_dec(v_sz_727_);
v_i_boxed_732_ = lean_unbox_usize(v_i_728_);
lean_dec(v_i_728_);
v_res_733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v_firstChoiceOnly_boxed_730_, v_inst_725_, v_as_726_, v_sz_boxed_731_, v_i_boxed_732_, v_b_729_);
lean_dec_ref(v_as_726_);
lean_dec_ref(v_inst_725_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___boxed(lean_object* v_firstChoiceOnly_734_, lean_object* v_stx_735_, lean_object* v_b_736_, lean_object* v_inst_737_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_738_; lean_object* v_res_739_; 
v_firstChoiceOnly_boxed_738_ = lean_unbox(v_firstChoiceOnly_734_);
v_res_739_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v_firstChoiceOnly_boxed_738_, v_stx_735_, v_b_736_, v_inst_737_);
lean_dec_ref(v_inst_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(lean_object* v_as_740_, size_t v_sz_741_, size_t v_i_742_, lean_object* v_b_743_){
_start:
{
uint8_t v___x_744_; 
v___x_744_ = lean_usize_dec_lt(v_i_742_, v_sz_741_);
if (v___x_744_ == 0)
{
return v_b_743_;
}
else
{
lean_object* v_snd_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_783_; 
v_snd_745_ = lean_ctor_get(v_b_743_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_b_743_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v_b_743_, 0);
lean_dec(v_unused_784_);
v___x_747_ = v_b_743_;
v_isShared_748_ = v_isSharedCheck_783_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_snd_745_);
lean_dec(v_b_743_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_783_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v_a_749_; lean_object* v___x_750_; uint8_t v_firstChoiceOnly_751_; lean_object* v_stx_752_; lean_object* v___x_753_; lean_object* v___y_755_; lean_object* v___x_779_; 
v_a_749_ = lean_array_uget_borrowed(v_as_740_, v_i_742_);
lean_inc(v_a_749_);
v___x_750_ = l_Lean_Syntax_topDown(v_a_749_, v___x_744_);
v_firstChoiceOnly_751_ = lean_ctor_get_uint8(v___x_750_, sizeof(void*)*1);
v_stx_752_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_stx_752_);
lean_dec_ref(v___x_750_);
v___x_753_ = lean_box(0);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_753_);
v___x_779_ = v___x_747_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_snd_745_);
v___x_779_ = v_reuseFailAlloc_782_;
goto v_reusejp_778_;
}
v___jp_754_:
{
lean_object* v_fst_756_; 
v_fst_756_ = lean_ctor_get(v___y_755_, 0);
if (lean_obj_tag(v_fst_756_) == 0)
{
lean_object* v_snd_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_767_; 
v_snd_757_ = lean_ctor_get(v___y_755_, 1);
v_isSharedCheck_767_ = !lean_is_exclusive(v___y_755_);
if (v_isSharedCheck_767_ == 0)
{
lean_object* v_unused_768_; 
v_unused_768_ = lean_ctor_get(v___y_755_, 0);
lean_dec(v_unused_768_);
v___x_759_ = v___y_755_;
v_isShared_760_ = v_isSharedCheck_767_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_snd_757_);
lean_dec(v___y_755_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_767_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_753_);
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_snd_757_);
v___x_762_ = v_reuseFailAlloc_766_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
size_t v___x_763_; size_t v___x_764_; 
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_add(v_i_742_, v___x_763_);
v_i_742_ = v___x_764_;
v_b_743_ = v___x_762_;
goto _start;
}
}
}
else
{
lean_object* v_snd_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_inc_ref(v_fst_756_);
v_snd_769_ = lean_ctor_get(v___y_755_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v___y_755_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v___y_755_, 0);
lean_dec(v_unused_777_);
v___x_771_ = v___y_755_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_snd_769_);
lean_dec(v___y_755_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_fst_756_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_snd_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
v_reusejp_778_:
{
lean_object* v___x_780_; lean_object* v_a_781_; 
lean_inc_ref(v___x_779_);
v___x_780_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v_firstChoiceOnly_751_, v_stx_752_, v___x_779_, v___x_779_);
lean_dec_ref(v___x_779_);
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref(v___x_780_);
v___y_755_ = v_a_781_;
goto v___jp_754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1___boxed(lean_object* v_as_785_, lean_object* v_sz_786_, lean_object* v_i_787_, lean_object* v_b_788_){
_start:
{
size_t v_sz_boxed_789_; size_t v_i_boxed_790_; lean_object* v_res_791_; 
v_sz_boxed_789_ = lean_unbox_usize(v_sz_786_);
lean_dec(v_sz_786_);
v_i_boxed_790_ = lean_unbox_usize(v_i_787_);
lean_dec(v_i_787_);
v_res_791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(v_as_785_, v_sz_boxed_789_, v_i_boxed_790_, v_b_788_);
lean_dec_ref(v_as_785_);
return v_res_791_;
}
}
static lean_object* _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0(void){
_start:
{
lean_object* v_seen_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_seen_792_ = l_Lean_NameSet_empty;
v___x_793_ = lean_box(0);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v_seen_792_);
return v___x_794_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_hasDuplicateAntiquot(lean_object* v_stxs_795_){
_start:
{
lean_object* v___x_796_; size_t v_sz_797_; size_t v___x_798_; lean_object* v___x_799_; lean_object* v_fst_800_; 
v___x_796_ = lean_obj_once(&l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0, &l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0_once, _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0);
v_sz_797_ = lean_array_size(v_stxs_795_);
v___x_798_ = ((size_t)0ULL);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(v_stxs_795_, v_sz_797_, v___x_798_, v___x_796_);
v_fst_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_fst_800_);
lean_dec_ref(v___x_799_);
if (lean_obj_tag(v_fst_800_) == 0)
{
uint8_t v___x_801_; 
v___x_801_ = 0;
return v___x_801_;
}
else
{
lean_object* v_val_802_; uint8_t v___x_803_; 
v_val_802_ = lean_ctor_get(v_fst_800_, 0);
lean_inc(v_val_802_);
lean_dec_ref(v_fst_800_);
v___x_803_ = lean_unbox(v_val_802_);
lean_dec(v_val_802_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___boxed(lean_object* v_stxs_804_){
_start:
{
uint8_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l_Lean_Elab_Command_hasDuplicateAntiquot(v_stxs_804_);
lean_dec_ref(v_stxs_804_);
v_r_806_ = lean_box(v_res_805_);
return v_r_806_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__4(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__3));
v___x_814_ = l_String_toRawSubstring_x27(v___x_813_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__15(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__14));
v___x_836_ = l_String_toRawSubstring_x27(v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__19(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__18));
v___x_842_ = l_String_toRawSubstring_x27(v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__22(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__21));
v___x_847_ = l_String_toRawSubstring_x27(v___x_846_);
return v___x_847_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__40(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__39));
v___x_885_ = l_String_toRawSubstring_x27(v___x_884_);
return v___x_885_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__47(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__46));
v___x_900_ = l_String_toRawSubstring_x27(v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__55(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_916_ = l_String_toRawSubstring_x27(v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander(lean_object* v_attrKind_954_, lean_object* v_pat_955_, lean_object* v_qrhs_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___y_960_; lean_object* v_fst_964_; lean_object* v_snd_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
lean_inc(v_qrhs_956_);
v___x_1161_ = l_Lean_Syntax_isOfKind(v_qrhs_956_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_qrhs_956_);
v___x_1163_ = l_Lean_Syntax_isOfKind(v_qrhs_956_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec_ref(v_a_957_);
lean_dec(v_qrhs_956_);
lean_dec(v_pat_955_);
lean_dec(v_attrKind_954_);
v___x_1164_ = lean_box(0);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v_a_958_);
return v___x_1165_;
}
else
{
lean_object* v___x_1166_; 
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__68));
v_fst_964_ = v_qrhs_956_;
v_snd_965_ = v___x_1166_;
v___y_966_ = v_a_957_;
v___y_967_ = v_a_958_;
goto v___jp_963_;
}
}
else
{
lean_object* v___x_1167_; lean_object* v_c_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1167_ = lean_unsigned_to_nat(0u);
v_c_1168_ = l_Lean_Syntax_getArg(v_qrhs_956_, v___x_1167_);
v___x_1169_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_c_1168_);
v___x_1170_ = l_Lean_Syntax_isOfKind(v_c_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec(v_c_1168_);
lean_dec_ref(v_a_957_);
lean_dec(v_qrhs_956_);
lean_dec(v_pat_955_);
lean_dec(v_attrKind_954_);
v___x_1171_ = lean_box(0);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v_a_958_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v_args_1175_; 
v___x_1173_ = lean_unsigned_to_nat(1u);
v___x_1174_ = l_Lean_Syntax_getArg(v_qrhs_956_, v___x_1173_);
lean_dec(v_qrhs_956_);
v_args_1175_ = l_Lean_Syntax_getArgs(v___x_1174_);
lean_dec(v___x_1174_);
v_fst_964_ = v_c_1168_;
v_snd_965_ = v_args_1175_;
v___y_966_ = v_a_957_;
v___y_967_ = v_a_958_;
goto v___jp_963_;
}
}
v___jp_959_:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_box(0);
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set(v___x_962_, 1, v___y_960_);
return v___x_962_;
}
v___jp_963_:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = l_Lean_TSyntax_getId(v_fst_964_);
lean_dec(v_fst_964_);
lean_inc_ref(v___y_966_);
v___x_969_ = l_Lean_Macro_resolveGlobalName(v___x_968_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
if (lean_obj_tag(v_a_970_) == 1)
{
lean_object* v_head_971_; lean_object* v_snd_972_; 
v_head_971_ = lean_ctor_get(v_a_970_, 0);
lean_inc(v_head_971_);
v_snd_972_ = lean_ctor_get(v_head_971_, 1);
lean_inc(v_snd_972_);
if (lean_obj_tag(v_snd_972_) == 0)
{
lean_object* v_tail_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1147_; 
v_tail_973_ = lean_ctor_get(v_a_970_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_a_970_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; 
v_unused_1148_ = lean_ctor_get(v_a_970_, 0);
lean_dec(v_unused_1148_);
v___x_975_ = v_a_970_;
v_isShared_976_ = v_isSharedCheck_1147_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_tail_973_);
lean_dec(v_a_970_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1147_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
if (lean_obj_tag(v_tail_973_) == 0)
{
lean_object* v_a_977_; lean_object* v_fst_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1144_; 
v_a_977_ = lean_ctor_get(v___x_969_, 1);
lean_inc(v_a_977_);
lean_dec_ref(v___x_969_);
v_fst_978_ = lean_ctor_get(v_head_971_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_head_971_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v_head_971_, 1);
lean_dec(v_unused_1145_);
v___x_980_ = v_head_971_;
v_isShared_981_ = v_isSharedCheck_1144_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_fst_978_);
lean_dec(v_head_971_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1144_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
size_t v_sz_982_; size_t v___x_983_; lean_object* v___x_984_; 
v_sz_982_ = lean_array_size(v_snd_965_);
v___x_983_ = ((size_t)0ULL);
lean_inc_ref(v___y_966_);
v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_982_, v___x_983_, v_snd_965_, v___y_966_, v_a_977_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1134_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_a_986_ = lean_ctor_get(v___x_984_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_988_ = v___x_984_;
v_isShared_989_ = v_isSharedCheck_1134_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1134_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
uint8_t v___x_990_; 
v___x_990_ = l_Lean_Elab_Command_hasDuplicateAntiquot(v_a_985_);
if (v___x_990_ == 0)
{
lean_object* v_quotContext_991_; lean_object* v_currMacroScope_992_; lean_object* v_ref_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v_quotContext_991_ = lean_ctor_get(v___y_966_, 1);
lean_inc(v_quotContext_991_);
v_currMacroScope_992_ = lean_ctor_get(v___y_966_, 2);
lean_inc(v_currMacroScope_992_);
v_ref_993_ = lean_ctor_get(v___y_966_, 5);
lean_inc(v_ref_993_);
lean_dec_ref(v___y_966_);
v___x_994_ = l_Lean_SourceInfo_fromRef(v_ref_993_, v___x_990_);
lean_dec(v_ref_993_);
v___x_995_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0));
v___x_996_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__1));
v___x_997_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__2));
lean_inc(v___x_994_);
if (v_isShared_981_ == 0)
{
lean_ctor_set_tag(v___x_980_, 2);
lean_ctor_set(v___x_980_, 1, v___x_997_);
lean_ctor_set(v___x_980_, 0, v___x_994_);
v___x_999_ = v___x_980_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1129_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_1001_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
lean_inc(v___x_994_);
v___x_1002_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1002_, 0, v___x_994_);
lean_ctor_set(v___x_1002_, 1, v___x_1000_);
lean_ctor_set(v___x_1002_, 2, v___x_1001_);
v___x_1003_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__4, &l_Lean_Elab_Command_mkUnexpander___closed__4_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__4);
v___x_1004_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__5));
lean_inc(v_currMacroScope_992_);
lean_inc(v_quotContext_991_);
v___x_1005_ = l_Lean_addMacroScope(v_quotContext_991_, v___x_1004_, v_currMacroScope_992_);
v___x_1006_ = lean_box(0);
lean_inc(v___x_994_);
v___x_1007_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1007_, 0, v___x_994_);
lean_ctor_set(v___x_1007_, 1, v___x_1003_);
lean_ctor_set(v___x_1007_, 2, v___x_1005_);
lean_ctor_set(v___x_1007_, 3, v___x_1006_);
v___x_1008_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__7));
v___x_1009_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc(v___x_994_);
v___x_1010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_994_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
lean_inc(v___x_994_);
v___x_1011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_994_);
lean_ctor_set(v___x_1011_, 1, v___x_995_);
lean_inc_ref(v___x_1010_);
lean_inc(v___x_994_);
v___x_1012_ = l_Lean_Syntax_node2(v___x_994_, v___x_1008_, v___x_1010_, v___x_1011_);
lean_inc_ref(v___x_1007_);
lean_inc_ref(v___x_1002_);
lean_inc(v___x_994_);
v___x_1013_ = l_Lean_Syntax_node4(v___x_994_, v___x_996_, v___x_999_, v___x_1002_, v___x_1007_, v___x_1012_);
v___x_1014_ = l_Lean_Syntax_mkApp(v___x_1013_, v_a_985_);
lean_inc(v_attrKind_954_);
v___x_1015_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_954_);
v___x_1016_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__9));
v___x_1017_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__10));
v___x_1018_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
v___x_1019_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc(v___x_994_);
v___x_1020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_994_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
v___x_1022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
v___x_1023_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__15, &l_Lean_Elab_Command_mkUnexpander___closed__15_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__15);
v___x_1024_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__16));
lean_inc(v_currMacroScope_992_);
lean_inc(v_quotContext_991_);
v___x_1025_ = l_Lean_addMacroScope(v_quotContext_991_, v___x_1024_, v_currMacroScope_992_);
lean_inc(v___x_994_);
v___x_1026_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1026_, 0, v___x_994_);
lean_ctor_set(v___x_1026_, 1, v___x_1023_);
lean_ctor_set(v___x_1026_, 2, v___x_1025_);
lean_ctor_set(v___x_1026_, 3, v___x_1006_);
v___x_1027_ = lean_mk_syntax_ident(v_fst_978_);
lean_inc(v___x_1027_);
lean_inc(v___x_994_);
v___x_1028_ = l_Lean_Syntax_node1(v___x_994_, v___x_1000_, v___x_1027_);
lean_inc(v___x_994_);
v___x_1029_ = l_Lean_Syntax_node2(v___x_994_, v___x_1022_, v___x_1026_, v___x_1028_);
lean_inc(v___x_994_);
v___x_1030_ = l_Lean_Syntax_node2(v___x_994_, v___x_1021_, v_attrKind_954_, v___x_1029_);
lean_inc(v___x_994_);
v___x_1031_ = l_Lean_Syntax_node1(v___x_994_, v___x_1000_, v___x_1030_);
v___x_1032_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
lean_inc(v___x_994_);
v___x_1033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_994_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
lean_inc(v___x_994_);
v___x_1034_ = l_Lean_Syntax_node3(v___x_994_, v___x_1018_, v___x_1020_, v___x_1031_, v___x_1033_);
lean_inc(v___x_994_);
v___x_1035_ = l_Lean_Syntax_node1(v___x_994_, v___x_1000_, v___x_1034_);
lean_inc(v___x_994_);
v___x_1036_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_994_);
lean_ctor_set(v___x_1036_, 1, v___x_1016_);
v___x_1037_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__19, &l_Lean_Elab_Command_mkUnexpander___closed__19_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__19);
v___x_1038_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__20));
lean_inc(v_currMacroScope_992_);
lean_inc(v_quotContext_991_);
v___x_1039_ = l_Lean_addMacroScope(v_quotContext_991_, v___x_1038_, v_currMacroScope_992_);
lean_inc(v___x_994_);
v___x_1040_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1040_, 0, v___x_994_);
lean_ctor_set(v___x_1040_, 1, v___x_1037_);
lean_ctor_set(v___x_1040_, 2, v___x_1039_);
lean_ctor_set(v___x_1040_, 3, v___x_1006_);
lean_inc(v___x_994_);
v___x_1041_ = l_Lean_Syntax_node2(v___x_994_, v___x_1000_, v___x_1040_, v___x_1027_);
v___x_1042_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__22, &l_Lean_Elab_Command_mkUnexpander___closed__22_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__22);
v___x_1043_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__25));
lean_inc(v_currMacroScope_992_);
lean_inc(v_quotContext_991_);
v___x_1044_ = l_Lean_addMacroScope(v_quotContext_991_, v___x_1043_, v_currMacroScope_992_);
v___x_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v_snd_972_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 1, v___x_1006_);
lean_ctor_set(v___x_975_, 0, v___x_1045_);
v___x_1047_ = v___x_975_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1006_);
v___x_1047_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_inc(v___x_994_);
v___x_1048_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1048_, 0, v___x_994_);
lean_ctor_set(v___x_1048_, 1, v___x_1042_);
lean_ctor_set(v___x_1048_, 2, v___x_1044_);
lean_ctor_set(v___x_1048_, 3, v___x_1047_);
v___x_1049_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
lean_inc(v___x_994_);
v___x_1050_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_994_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__27));
v___x_1052_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__28));
lean_inc(v___x_994_);
v___x_1053_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_994_);
lean_ctor_set(v___x_1053_, 1, v___x_1051_);
v___x_1054_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__30));
v___x_1055_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__32));
v___x_1056_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
lean_inc(v___x_994_);
v___x_1057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_994_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__35));
v___x_1059_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
lean_inc(v___x_994_);
v___x_1060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_994_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
lean_inc(v___x_994_);
v___x_1062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_994_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
lean_inc_ref(v___x_1062_);
lean_inc_ref(v___x_1060_);
lean_inc(v___x_994_);
v___x_1063_ = l_Lean_Syntax_node3(v___x_994_, v___x_1058_, v___x_1060_, v___x_1014_, v___x_1062_);
lean_inc(v___x_994_);
v___x_1064_ = l_Lean_Syntax_node1(v___x_994_, v___x_1000_, v___x_1063_);
lean_inc(v___x_994_);
v___x_1065_ = l_Lean_Syntax_node1(v___x_994_, v___x_1000_, v___x_1064_);
v___x_1066_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
lean_inc(v___x_994_);
v___x_1067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_994_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
v___x_1069_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__40, &l_Lean_Elab_Command_mkUnexpander___closed__40_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__40);
v___x_1070_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__41));
lean_inc(v_currMacroScope_992_);
lean_inc(v_quotContext_991_);
v___x_1071_ = l_Lean_addMacroScope(v_quotContext_991_, v___x_1070_, v_currMacroScope_992_);
v___x_1072_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__42));
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v_snd_972_);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___x_1006_);
lean_inc(v___x_994_);
v___x_1075_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1075_, 0, v___x_994_);
lean_ctor_set(v___x_1075_, 1, v___x_1069_);
lean_ctor_set(v___x_1075_, 2, v___x_1071_);
lean_ctor_set(v___x_1075_, 3, v___x_1074_);
lean_inc_ref(v___x_1062_);
lean_inc(v___x_994_);
v___x_1076_ = l_Lean_Syntax_node3(v___x_994_, v___x_1058_, v___x_1060_, v_pat_955_, v___x_1062_);
lean_inc(v___x_994_);
v___x_1077_ = l_Lean_Syntax_node2(v___x_994_, v___x_1000_, v___x_1007_, v___x_1076_);
lean_inc(v___x_994_);
v___x_1078_ = l_Lean_Syntax_node2(v___x_994_, v___x_1068_, v___x_1075_, v___x_1077_);
lean_inc_ref(v___x_1067_);
lean_inc_ref(v___x_1057_);
lean_inc(v___x_994_);
v___x_1079_ = l_Lean_Syntax_node4(v___x_994_, v___x_1055_, v___x_1057_, v___x_1065_, v___x_1067_, v___x_1078_);
v___x_1080_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__44));
v___x_1081_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__45));
lean_inc(v___x_994_);
v___x_1082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_994_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
lean_inc(v___x_994_);
v___x_1083_ = l_Lean_Syntax_node1(v___x_994_, v___x_1080_, v___x_1082_);
lean_inc(v___x_994_);
v___x_1084_ = l_Lean_Syntax_node1(v___x_994_, v___x_1000_, v___x_1083_);
lean_inc(v___x_994_);
v___x_1085_ = l_Lean_Syntax_node1(v___x_994_, v___x_1000_, v___x_1084_);
v___x_1086_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__47, &l_Lean_Elab_Command_mkUnexpander___closed__47_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__47);
v___x_1087_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__48));
lean_inc(v_currMacroScope_992_);
lean_inc(v_quotContext_991_);
v___x_1088_ = l_Lean_addMacroScope(v_quotContext_991_, v___x_1087_, v_currMacroScope_992_);
v___x_1089_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__50));
v___x_1090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v_snd_972_);
v___x_1091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v___x_1006_);
lean_inc(v___x_994_);
v___x_1092_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1092_, 0, v___x_994_);
lean_ctor_set(v___x_1092_, 1, v___x_1086_);
lean_ctor_set(v___x_1092_, 2, v___x_1088_);
lean_ctor_set(v___x_1092_, 3, v___x_1091_);
v___x_1093_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__52));
v___x_1094_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__3));
v___x_1095_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc(v___x_994_);
v___x_1096_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_994_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__5));
v___x_1098_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__55, &l_Lean_Elab_Command_mkUnexpander___closed__55_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__55);
v___x_1099_ = lean_box(0);
v___x_1100_ = l_Lean_addMacroScope(v_quotContext_991_, v___x_1099_, v_currMacroScope_992_);
v___x_1101_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__67));
lean_inc(v___x_994_);
v___x_1102_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1102_, 0, v___x_994_);
lean_ctor_set(v___x_1102_, 1, v___x_1098_);
lean_ctor_set(v___x_1102_, 2, v___x_1100_);
lean_ctor_set(v___x_1102_, 3, v___x_1101_);
lean_inc(v___x_994_);
v___x_1103_ = l_Lean_Syntax_node1(v___x_994_, v___x_1097_, v___x_1102_);
lean_inc(v___x_994_);
v___x_1104_ = l_Lean_Syntax_node2(v___x_994_, v___x_1094_, v___x_1096_, v___x_1103_);
lean_inc_ref(v___x_1002_);
lean_inc(v___x_994_);
v___x_1105_ = l_Lean_Syntax_node3(v___x_994_, v___x_1093_, v___x_1104_, v___x_1002_, v___x_1062_);
lean_inc(v___x_994_);
v___x_1106_ = l_Lean_Syntax_node1(v___x_994_, v___x_1000_, v___x_1105_);
lean_inc(v___x_994_);
v___x_1107_ = l_Lean_Syntax_node2(v___x_994_, v___x_1068_, v___x_1092_, v___x_1106_);
lean_inc(v___x_994_);
v___x_1108_ = l_Lean_Syntax_node4(v___x_994_, v___x_1055_, v___x_1057_, v___x_1085_, v___x_1067_, v___x_1107_);
lean_inc(v___x_994_);
v___x_1109_ = l_Lean_Syntax_node2(v___x_994_, v___x_1000_, v___x_1079_, v___x_1108_);
lean_inc(v___x_994_);
v___x_1110_ = l_Lean_Syntax_node1(v___x_994_, v___x_1054_, v___x_1109_);
lean_inc(v___x_994_);
v___x_1111_ = l_Lean_Syntax_node2(v___x_994_, v___x_1052_, v___x_1053_, v___x_1110_);
v___x_1112_ = lean_unsigned_to_nat(9u);
v___x_1113_ = lean_mk_empty_array_with_capacity(v___x_1112_);
v___x_1114_ = lean_array_push(v___x_1113_, v___x_1002_);
v___x_1115_ = lean_array_push(v___x_1114_, v___x_1035_);
v___x_1116_ = lean_array_push(v___x_1115_, v___x_1015_);
v___x_1117_ = lean_array_push(v___x_1116_, v___x_1036_);
v___x_1118_ = lean_array_push(v___x_1117_, v___x_1041_);
v___x_1119_ = lean_array_push(v___x_1118_, v___x_1010_);
v___x_1120_ = lean_array_push(v___x_1119_, v___x_1048_);
v___x_1121_ = lean_array_push(v___x_1120_, v___x_1050_);
v___x_1122_ = lean_array_push(v___x_1121_, v___x_1111_);
v___x_1123_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1123_, 0, v___x_994_);
lean_ctor_set(v___x_1123_, 1, v___x_1017_);
lean_ctor_set(v___x_1123_, 2, v___x_1122_);
v___x_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_1124_);
v___x_1126_ = v___x_988_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_a_986_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_dec(v_a_985_);
lean_del_object(v___x_980_);
lean_dec(v_fst_978_);
lean_del_object(v___x_975_);
lean_dec_ref(v___y_966_);
lean_dec(v_pat_955_);
lean_dec(v_attrKind_954_);
v___x_1130_ = lean_box(0);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_1130_);
v___x_1132_ = v___x_988_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_a_986_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_del_object(v___x_980_);
lean_dec(v_fst_978_);
lean_del_object(v___x_975_);
lean_dec_ref(v___y_966_);
lean_dec(v_pat_955_);
lean_dec(v_attrKind_954_);
v_a_1135_ = lean_ctor_get(v___x_984_, 0);
v_a_1136_ = lean_ctor_get(v___x_984_, 1);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_984_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_inc(v_a_1135_);
lean_dec(v___x_984_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1135_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
else
{
lean_object* v_a_1146_; 
lean_del_object(v___x_975_);
lean_dec(v_tail_973_);
lean_dec(v_head_971_);
lean_dec_ref(v___y_966_);
lean_dec_ref(v_snd_965_);
lean_dec(v_pat_955_);
lean_dec(v_attrKind_954_);
v_a_1146_ = lean_ctor_get(v___x_969_, 1);
lean_inc(v_a_1146_);
lean_dec_ref(v___x_969_);
v___y_960_ = v_a_1146_;
goto v___jp_959_;
}
}
}
else
{
lean_object* v_a_1149_; 
lean_dec(v_snd_972_);
lean_dec(v_head_971_);
lean_dec_ref(v_a_970_);
lean_dec_ref(v___y_966_);
lean_dec_ref(v_snd_965_);
lean_dec(v_pat_955_);
lean_dec(v_attrKind_954_);
v_a_1149_ = lean_ctor_get(v___x_969_, 1);
lean_inc(v_a_1149_);
lean_dec_ref(v___x_969_);
v___y_960_ = v_a_1149_;
goto v___jp_959_;
}
}
else
{
lean_object* v_a_1150_; 
lean_dec(v_a_970_);
lean_dec_ref(v___y_966_);
lean_dec_ref(v_snd_965_);
lean_dec(v_pat_955_);
lean_dec(v_attrKind_954_);
v_a_1150_ = lean_ctor_get(v___x_969_, 1);
lean_inc(v_a_1150_);
lean_dec_ref(v___x_969_);
v___y_960_ = v_a_1150_;
goto v___jp_959_;
}
}
else
{
lean_object* v_a_1151_; lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v___y_966_);
lean_dec_ref(v_snd_965_);
lean_dec(v_pat_955_);
lean_dec(v_attrKind_954_);
v_a_1151_ = lean_ctor_get(v___x_969_, 0);
v_a_1152_ = lean_ctor_get(v___x_969_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_969_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_inc(v_a_1151_);
lean_dec(v___x_969_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1151_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1176_ = lean_box(0);
v___x_1177_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v___x_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg(){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0);
v___x_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___boxed(lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(lean_object* v_00_u03b1_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___boxed(lean_object* v_00_u03b1_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(v_00_u03b1_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; lean_object* v_env_1197_; lean_object* v___x_1198_; lean_object* v_mainModule_1199_; lean_object* v___x_1200_; 
v___x_1196_ = lean_st_ref_get(v___y_1194_);
v_env_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc_ref(v_env_1197_);
lean_dec(v___x_1196_);
v___x_1198_ = l_Lean_Environment_header(v_env_1197_);
lean_dec_ref(v_env_1197_);
v_mainModule_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_mainModule_1199_);
lean_dec_ref(v___x_1198_);
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v_mainModule_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg___boxed(lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_1201_);
lean_dec(v___y_1201_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_1205_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___boxed(lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___lam__0(lean_object* v___x_1212_, lean_object* v_sc_1213_){
_start:
{
lean_object* v_header_1214_; lean_object* v_currNamespace_1215_; lean_object* v_openDecls_1216_; lean_object* v_levelNames_1217_; lean_object* v_varDecls_1218_; lean_object* v_varUIds_1219_; lean_object* v_includedVars_1220_; lean_object* v_omittedVars_1221_; uint8_t v_isNoncomputable_1222_; uint8_t v_isPublic_1223_; uint8_t v_isMeta_1224_; lean_object* v_attrs_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
v_header_1214_ = lean_ctor_get(v_sc_1213_, 0);
v_currNamespace_1215_ = lean_ctor_get(v_sc_1213_, 2);
v_openDecls_1216_ = lean_ctor_get(v_sc_1213_, 3);
v_levelNames_1217_ = lean_ctor_get(v_sc_1213_, 4);
v_varDecls_1218_ = lean_ctor_get(v_sc_1213_, 5);
v_varUIds_1219_ = lean_ctor_get(v_sc_1213_, 6);
v_includedVars_1220_ = lean_ctor_get(v_sc_1213_, 7);
v_omittedVars_1221_ = lean_ctor_get(v_sc_1213_, 8);
v_isNoncomputable_1222_ = lean_ctor_get_uint8(v_sc_1213_, sizeof(void*)*10);
v_isPublic_1223_ = lean_ctor_get_uint8(v_sc_1213_, sizeof(void*)*10 + 1);
v_isMeta_1224_ = lean_ctor_get_uint8(v_sc_1213_, sizeof(void*)*10 + 2);
v_attrs_1225_ = lean_ctor_get(v_sc_1213_, 9);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_sc_1213_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; 
v_unused_1233_ = lean_ctor_get(v_sc_1213_, 1);
lean_dec(v_unused_1233_);
v___x_1227_ = v_sc_1213_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_attrs_1225_);
lean_inc(v_omittedVars_1221_);
lean_inc(v_includedVars_1220_);
lean_inc(v_varUIds_1219_);
lean_inc(v_varDecls_1218_);
lean_inc(v_levelNames_1217_);
lean_inc(v_openDecls_1216_);
lean_inc(v_currNamespace_1215_);
lean_inc(v_header_1214_);
lean_dec(v_sc_1213_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v___x_1212_);
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_header_1214_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_currNamespace_1215_);
lean_ctor_set(v_reuseFailAlloc_1231_, 3, v_openDecls_1216_);
lean_ctor_set(v_reuseFailAlloc_1231_, 4, v_levelNames_1217_);
lean_ctor_set(v_reuseFailAlloc_1231_, 5, v_varDecls_1218_);
lean_ctor_set(v_reuseFailAlloc_1231_, 6, v_varUIds_1219_);
lean_ctor_set(v_reuseFailAlloc_1231_, 7, v_includedVars_1220_);
lean_ctor_set(v_reuseFailAlloc_1231_, 8, v_omittedVars_1221_);
lean_ctor_set(v_reuseFailAlloc_1231_, 9, v_attrs_1225_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*10, v_isNoncomputable_1222_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*10 + 1, v_isPublic_1223_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*10 + 2, v_isMeta_1224_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(size_t v_sz_1234_, size_t v_i_1235_, lean_object* v_bs_1236_){
_start:
{
uint8_t v___x_1237_; 
v___x_1237_ = lean_usize_dec_lt(v_i_1235_, v_sz_1234_);
if (v___x_1237_ == 0)
{
return v_bs_1236_;
}
else
{
lean_object* v_v_1238_; lean_object* v___x_1239_; lean_object* v_bs_x27_1240_; size_t v___x_1241_; size_t v___x_1242_; lean_object* v___x_1243_; 
v_v_1238_ = lean_array_uget(v_bs_1236_, v_i_1235_);
v___x_1239_ = lean_unsigned_to_nat(0u);
v_bs_x27_1240_ = lean_array_uset(v_bs_1236_, v_i_1235_, v___x_1239_);
v___x_1241_ = ((size_t)1ULL);
v___x_1242_ = lean_usize_add(v_i_1235_, v___x_1241_);
v___x_1243_ = lean_array_uset(v_bs_x27_1240_, v_i_1235_, v_v_1238_);
v_i_1235_ = v___x_1242_;
v_bs_1236_ = v___x_1243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3___boxed(lean_object* v_sz_1245_, lean_object* v_i_1246_, lean_object* v_bs_1247_){
_start:
{
size_t v_sz_boxed_1248_; size_t v_i_boxed_1249_; lean_object* v_res_1250_; 
v_sz_boxed_1248_ = lean_unbox_usize(v_sz_1245_);
lean_dec(v_sz_1245_);
v_i_boxed_1249_ = lean_unbox_usize(v_i_1246_);
lean_dec(v_i_1246_);
v_res_1250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_boxed_1248_, v_i_boxed_1249_, v_bs_1247_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14(lean_object* v_o_1254_, lean_object* v_k_1255_, uint8_t v_v_1256_){
_start:
{
lean_object* v_map_1257_; uint8_t v_hasTrace_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1272_; 
v_map_1257_ = lean_ctor_get(v_o_1254_, 0);
v_hasTrace_1258_ = lean_ctor_get_uint8(v_o_1254_, sizeof(void*)*1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_o_1254_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1260_ = v_o_1254_;
v_isShared_1261_ = v_isSharedCheck_1272_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_map_1257_);
lean_dec(v_o_1254_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1272_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1262_, 0, v_v_1256_);
lean_inc(v_k_1255_);
v___x_1263_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1255_, v___x_1262_, v_map_1257_);
if (v_hasTrace_1258_ == 0)
{
lean_object* v___x_1264_; uint8_t v___x_1265_; lean_object* v___x_1267_; 
v___x_1264_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__1));
v___x_1265_ = l_Lean_Name_isPrefixOf(v___x_1264_, v_k_1255_);
lean_dec(v_k_1255_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1263_);
v___x_1267_ = v___x_1260_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1263_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_ctor_set_uint8(v___x_1267_, sizeof(void*)*1, v___x_1265_);
return v___x_1267_;
}
}
else
{
lean_object* v___x_1270_; 
lean_dec(v_k_1255_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1263_);
v___x_1270_ = v___x_1260_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, sizeof(void*)*1, v_hasTrace_1258_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___boxed(lean_object* v_o_1273_, lean_object* v_k_1274_, lean_object* v_v_1275_){
_start:
{
uint8_t v_v_boxed_1276_; lean_object* v_res_1277_; 
v_v_boxed_1276_ = lean_unbox(v_v_1275_);
v_res_1277_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14(v_o_1273_, v_k_1274_, v_v_boxed_1276_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(lean_object* v_opts_1278_, lean_object* v_opt_1279_, uint8_t v_val_1280_){
_start:
{
lean_object* v_name_1281_; lean_object* v___x_1282_; 
v_name_1281_ = lean_ctor_get(v_opt_1279_, 0);
lean_inc(v_name_1281_);
lean_dec_ref(v_opt_1279_);
v___x_1282_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14(v_opts_1278_, v_name_1281_, v_val_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6___boxed(lean_object* v_opts_1283_, lean_object* v_opt_1284_, lean_object* v_val_1285_){
_start:
{
uint8_t v_val_boxed_1286_; lean_object* v_res_1287_; 
v_val_boxed_1286_ = lean_unbox(v_val_1285_);
v_res_1287_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_1283_, v_opt_1284_, v_val_boxed_1286_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(size_t v_sz_1288_, size_t v_i_1289_, lean_object* v_bs_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
uint8_t v___x_1293_; 
v___x_1293_ = lean_usize_dec_lt(v_i_1289_, v_sz_1288_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; 
lean_dec_ref(v___y_1291_);
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_bs_1290_);
lean_ctor_set(v___x_1294_, 1, v___y_1292_);
return v___x_1294_;
}
else
{
lean_object* v_v_1295_; lean_object* v___x_1296_; 
v_v_1295_ = lean_array_uget_borrowed(v_bs_1290_, v_i_1289_);
lean_inc_ref(v___y_1291_);
lean_inc(v_v_1295_);
v___x_1296_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(v_v_1295_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v_a_1298_; lean_object* v___x_1299_; lean_object* v_bs_x27_1300_; size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
v_a_1298_ = lean_ctor_get(v___x_1296_, 1);
lean_inc(v_a_1298_);
lean_dec_ref(v___x_1296_);
v___x_1299_ = lean_unsigned_to_nat(0u);
v_bs_x27_1300_ = lean_array_uset(v_bs_1290_, v_i_1289_, v___x_1299_);
v___x_1301_ = ((size_t)1ULL);
v___x_1302_ = lean_usize_add(v_i_1289_, v___x_1301_);
v___x_1303_ = lean_array_uset(v_bs_x27_1300_, v_i_1289_, v_a_1297_);
v_i_1289_ = v___x_1302_;
v_bs_1290_ = v___x_1303_;
v___y_1292_ = v_a_1298_;
goto _start;
}
else
{
lean_object* v_a_1305_; lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v___y_1291_);
lean_dec_ref(v_bs_1290_);
v_a_1305_ = lean_ctor_get(v___x_1296_, 0);
v_a_1306_ = lean_ctor_get(v___x_1296_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1296_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_inc(v_a_1305_);
lean_dec(v___x_1296_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1305_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed(lean_object* v_sz_1314_, lean_object* v_i_1315_, lean_object* v_bs_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
size_t v_sz_boxed_1319_; size_t v_i_boxed_1320_; lean_object* v_res_1321_; 
v_sz_boxed_1319_ = lean_unbox_usize(v_sz_1314_);
lean_dec(v_sz_1314_);
v_i_boxed_1320_ = lean_unbox_usize(v_i_1315_);
lean_dec(v_i_1315_);
v_res_1321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(v_sz_boxed_1319_, v_i_boxed_1320_, v_bs_1316_, v___y_1317_, v___y_1318_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(size_t v_sz_1322_, size_t v_i_1323_, lean_object* v_bs_1324_){
_start:
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_usize_dec_lt(v_i_1323_, v_sz_1322_);
if (v___x_1325_ == 0)
{
return v_bs_1324_;
}
else
{
lean_object* v___x_1326_; lean_object* v_v_1327_; lean_object* v_bs_x27_1328_; lean_object* v___x_1329_; size_t v___x_1330_; size_t v___x_1331_; lean_object* v___x_1332_; 
v___x_1326_ = lean_unsigned_to_nat(0u);
v_v_1327_ = lean_array_uget(v_bs_1324_, v_i_1323_);
v_bs_x27_1328_ = lean_array_uset(v_bs_1324_, v_i_1323_, v___x_1326_);
v___x_1329_ = l_Lean_Syntax_getArg(v_v_1327_, v___x_1326_);
lean_dec(v_v_1327_);
v___x_1330_ = ((size_t)1ULL);
v___x_1331_ = lean_usize_add(v_i_1323_, v___x_1330_);
v___x_1332_ = lean_array_uset(v_bs_x27_1328_, v_i_1323_, v___x_1329_);
v_i_1323_ = v___x_1331_;
v_bs_1324_ = v___x_1332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed(lean_object* v_sz_1334_, lean_object* v_i_1335_, lean_object* v_bs_1336_){
_start:
{
size_t v_sz_boxed_1337_; size_t v_i_boxed_1338_; lean_object* v_res_1339_; 
v_sz_boxed_1337_ = lean_unbox_usize(v_sz_1334_);
lean_dec(v_sz_1334_);
v_i_boxed_1338_ = lean_unbox_usize(v_i_1335_);
lean_dec(v_i_1335_);
v_res_1339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_boxed_1337_, v_i_boxed_1338_, v_bs_1336_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(size_t v_sz_1340_, size_t v_i_1341_, lean_object* v_bs_1342_, lean_object* v___y_1343_){
_start:
{
uint8_t v___x_1344_; 
v___x_1344_ = lean_usize_dec_lt(v_i_1341_, v_sz_1340_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v_bs_1342_);
lean_ctor_set(v___x_1345_, 1, v___y_1343_);
return v___x_1345_;
}
else
{
lean_object* v_v_1346_; lean_object* v___x_1347_; 
v_v_1346_ = lean_array_uget_borrowed(v_bs_1342_, v_i_1341_);
lean_inc(v_v_1346_);
v___x_1347_ = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(v_v_1346_, v___y_1343_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v_a_1349_; lean_object* v___x_1350_; lean_object* v_bs_x27_1351_; size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
v_a_1349_ = lean_ctor_get(v___x_1347_, 1);
lean_inc(v_a_1349_);
lean_dec_ref(v___x_1347_);
v___x_1350_ = lean_unsigned_to_nat(0u);
v_bs_x27_1351_ = lean_array_uset(v_bs_1342_, v_i_1341_, v___x_1350_);
v___x_1352_ = ((size_t)1ULL);
v___x_1353_ = lean_usize_add(v_i_1341_, v___x_1352_);
v___x_1354_ = lean_array_uset(v_bs_x27_1351_, v_i_1341_, v_a_1348_);
v_i_1341_ = v___x_1353_;
v_bs_1342_ = v___x_1354_;
v___y_1343_ = v_a_1349_;
goto _start;
}
else
{
lean_object* v_a_1356_; lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref(v_bs_1342_);
v_a_1356_ = lean_ctor_get(v___x_1347_, 0);
v_a_1357_ = lean_ctor_get(v___x_1347_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1347_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_inc(v_a_1356_);
lean_dec(v___x_1347_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1356_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg___boxed(lean_object* v_sz_1365_, lean_object* v_i_1366_, lean_object* v_bs_1367_, lean_object* v___y_1368_){
_start:
{
size_t v_sz_boxed_1369_; size_t v_i_boxed_1370_; lean_object* v_res_1371_; 
v_sz_boxed_1369_ = lean_unbox_usize(v_sz_1365_);
lean_dec(v_sz_1365_);
v_i_boxed_1370_ = lean_unbox_usize(v_i_1366_);
lean_dec(v_i_1366_);
v_res_1371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(v_sz_boxed_1369_, v_i_boxed_1370_, v_bs_1367_, v___y_1368_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(size_t v_sz_1372_, size_t v_i_1373_, lean_object* v_bs_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(v_sz_1372_, v_i_1373_, v_bs_1374_, v___y_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed(lean_object* v_sz_1378_, lean_object* v_i_1379_, lean_object* v_bs_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
size_t v_sz_boxed_1383_; size_t v_i_boxed_1384_; lean_object* v_res_1385_; 
v_sz_boxed_1383_ = lean_unbox_usize(v_sz_1378_);
lean_dec(v_sz_1378_);
v_i_boxed_1384_ = lean_unbox_usize(v_i_1379_);
lean_dec(v_i_1379_);
v_res_1385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(v_sz_boxed_1383_, v_i_boxed_1384_, v_bs_1380_, v___y_1381_, v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1385_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_box(1);
v___x_1387_ = l_Lean_MessageData_ofFormat(v___x_1386_);
return v___x_1387_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__2));
v___x_1392_ = l_Lean_MessageData_ofFormat(v___x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27(lean_object* v_x_1393_, lean_object* v_x_1394_){
_start:
{
if (lean_obj_tag(v_x_1394_) == 0)
{
return v_x_1393_;
}
else
{
lean_object* v_head_1395_; lean_object* v_tail_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1418_; 
v_head_1395_ = lean_ctor_get(v_x_1394_, 0);
v_tail_1396_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1398_ = v_x_1394_;
v_isShared_1399_ = v_isSharedCheck_1418_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_tail_1396_);
lean_inc(v_head_1395_);
lean_dec(v_x_1394_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1418_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v_before_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1416_; 
v_before_1400_ = lean_ctor_get(v_head_1395_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_head_1395_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; 
v_unused_1417_ = lean_ctor_get(v_head_1395_, 1);
lean_dec(v_unused_1417_);
v___x_1402_ = v_head_1395_;
v_isShared_1403_ = v_isSharedCheck_1416_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_before_1400_);
lean_dec(v_head_1395_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1416_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1404_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0);
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 7);
lean_ctor_set(v___x_1402_, 1, v___x_1404_);
lean_ctor_set(v___x_1402_, 0, v_x_1393_);
v___x_1406_ = v___x_1402_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_x_1393_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1407_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3);
if (v_isShared_1399_ == 0)
{
lean_ctor_set_tag(v___x_1398_, 7);
lean_ctor_set(v___x_1398_, 1, v___x_1407_);
lean_ctor_set(v___x_1398_, 0, v___x_1406_);
v___x_1409_ = v___x_1398_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = l_Lean_MessageData_ofSyntax(v_before_1400_);
v___x_1411_ = l_Lean_indentD(v___x_1410_);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1409_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v_x_1393_ = v___x_1412_;
v_x_1394_ = v_tail_1396_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26(lean_object* v_opts_1419_, lean_object* v_opt_1420_){
_start:
{
lean_object* v_name_1421_; lean_object* v_defValue_1422_; lean_object* v_map_1423_; lean_object* v___x_1424_; 
v_name_1421_ = lean_ctor_get(v_opt_1420_, 0);
v_defValue_1422_ = lean_ctor_get(v_opt_1420_, 1);
v_map_1423_ = lean_ctor_get(v_opts_1419_, 0);
v___x_1424_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1423_, v_name_1421_);
if (lean_obj_tag(v___x_1424_) == 0)
{
uint8_t v___x_1425_; 
v___x_1425_ = lean_unbox(v_defValue_1422_);
return v___x_1425_;
}
else
{
lean_object* v_val_1426_; 
v_val_1426_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_val_1426_);
lean_dec_ref(v___x_1424_);
if (lean_obj_tag(v_val_1426_) == 1)
{
uint8_t v_v_1427_; 
v_v_1427_ = lean_ctor_get_uint8(v_val_1426_, 0);
lean_dec_ref(v_val_1426_);
return v_v_1427_;
}
else
{
uint8_t v___x_1428_; 
lean_dec(v_val_1426_);
v___x_1428_ = lean_unbox(v_defValue_1422_);
return v___x_1428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26___boxed(lean_object* v_opts_1429_, lean_object* v_opt_1430_){
_start:
{
uint8_t v_res_1431_; lean_object* v_r_1432_; 
v_res_1431_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26(v_opts_1429_, v_opt_1430_);
lean_dec_ref(v_opt_1430_);
lean_dec_ref(v_opts_1429_);
v_r_1432_ = lean_box(v_res_1431_);
return v_r_1432_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__1));
v___x_1437_ = l_Lean_MessageData_ofFormat(v___x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg(lean_object* v_msgData_1438_, lean_object* v_macroStack_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; lean_object* v_scopes_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v_opts_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1442_ = lean_st_ref_get(v___y_1440_);
v_scopes_1443_ = lean_ctor_get(v___x_1442_, 2);
lean_inc(v_scopes_1443_);
lean_dec(v___x_1442_);
v___x_1444_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1445_ = l_List_head_x21___redArg(v___x_1444_, v_scopes_1443_);
lean_dec(v_scopes_1443_);
v_opts_1446_ = lean_ctor_get(v___x_1445_, 1);
lean_inc_ref(v_opts_1446_);
lean_dec(v___x_1445_);
v___x_1447_ = l_Lean_Elab_pp_macroStack;
v___x_1448_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26(v_opts_1446_, v___x_1447_);
lean_dec_ref(v_opts_1446_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec(v_macroStack_1439_);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v_msgData_1438_);
return v___x_1449_;
}
else
{
if (lean_obj_tag(v_macroStack_1439_) == 0)
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v_msgData_1438_);
return v___x_1450_;
}
else
{
lean_object* v_head_1451_; lean_object* v_after_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1467_; 
v_head_1451_ = lean_ctor_get(v_macroStack_1439_, 0);
lean_inc(v_head_1451_);
v_after_1452_ = lean_ctor_get(v_head_1451_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_head_1451_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v_head_1451_, 0);
lean_dec(v_unused_1468_);
v___x_1454_ = v_head_1451_;
v_isShared_1455_ = v_isSharedCheck_1467_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_after_1452_);
lean_dec(v_head_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1467_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1456_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0);
if (v_isShared_1455_ == 0)
{
lean_ctor_set_tag(v___x_1454_, 7);
lean_ctor_set(v___x_1454_, 1, v___x_1456_);
lean_ctor_set(v___x_1454_, 0, v_msgData_1438_);
v___x_1458_ = v___x_1454_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_msgData_1438_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v_msgData_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1459_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2);
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1458_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = l_Lean_MessageData_ofSyntax(v_after_1452_);
v___x_1462_ = l_Lean_indentD(v___x_1461_);
v_msgData_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1463_, 0, v___x_1460_);
lean_ctor_set(v_msgData_1463_, 1, v___x_1462_);
v___x_1464_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27(v_msgData_1463_, v_macroStack_1439_);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
return v___x_1465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___boxed(lean_object* v_msgData_1469_, lean_object* v_macroStack_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg(v_msgData_1469_, v_macroStack_1470_, v___y_1471_);
lean_dec(v___y_1471_);
return v_res_1473_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1474_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
return v___x_1476_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1477_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
lean_ctor_set(v___x_1479_, 2, v___x_1478_);
lean_ctor_set(v___x_1479_, 3, v___x_1477_);
lean_ctor_set(v___x_1479_, 4, v___x_1477_);
lean_ctor_set(v___x_1479_, 5, v___x_1477_);
lean_ctor_set(v___x_1479_, 6, v___x_1477_);
lean_ctor_set(v___x_1479_, 7, v___x_1477_);
lean_ctor_set(v___x_1479_, 8, v___x_1477_);
return v___x_1479_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1480_ = lean_unsigned_to_nat(32u);
v___x_1481_ = lean_mk_empty_array_with_capacity(v___x_1480_);
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1483_ = ((size_t)5ULL);
v___x_1484_ = lean_unsigned_to_nat(0u);
v___x_1485_ = lean_unsigned_to_nat(32u);
v___x_1486_ = lean_mk_empty_array_with_capacity(v___x_1485_);
v___x_1487_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3);
v___x_1488_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v___x_1486_);
lean_ctor_set(v___x_1488_, 2, v___x_1484_);
lean_ctor_set(v___x_1488_, 3, v___x_1484_);
lean_ctor_set_usize(v___x_1488_, 4, v___x_1483_);
return v___x_1488_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1489_ = lean_box(1);
v___x_1490_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4);
v___x_1491_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_1492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v___x_1490_);
lean_ctor_set(v___x_1492_, 2, v___x_1489_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(lean_object* v_msgData_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v___x_1496_; lean_object* v_env_1497_; lean_object* v___x_1498_; lean_object* v_scopes_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v_opts_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1496_ = lean_st_ref_get(v___y_1494_);
v_env_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc_ref(v_env_1497_);
lean_dec(v___x_1496_);
v___x_1498_ = lean_st_ref_get(v___y_1494_);
v_scopes_1499_ = lean_ctor_get(v___x_1498_, 2);
lean_inc(v_scopes_1499_);
lean_dec(v___x_1498_);
v___x_1500_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1501_ = l_List_head_x21___redArg(v___x_1500_, v_scopes_1499_);
lean_dec(v_scopes_1499_);
v_opts_1502_ = lean_ctor_get(v___x_1501_, 1);
lean_inc_ref(v_opts_1502_);
lean_dec(v___x_1501_);
v___x_1503_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2);
v___x_1504_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5);
v___x_1505_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1505_, 0, v_env_1497_);
lean_ctor_set(v___x_1505_, 1, v___x_1503_);
lean_ctor_set(v___x_1505_, 2, v___x_1504_);
lean_ctor_set(v___x_1505_, 3, v_opts_1502_);
v___x_1506_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v_msgData_1493_);
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(v_msgData_1508_, v___y_1509_);
lean_dec(v___y_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(lean_object* v_msg_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_Elab_Command_getRef___redArg(v___y_1513_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v_macroStack_1518_; lean_object* v___x_1519_; lean_object* v_a_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1531_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v___x_1516_);
v_macroStack_1518_ = lean_ctor_get(v___y_1513_, 4);
lean_inc(v_macroStack_1518_);
lean_dec_ref(v___y_1513_);
v___x_1519_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(v_msg_1512_, v___y_1514_);
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref(v___x_1519_);
lean_inc(v_macroStack_1518_);
v___x_1521_ = l_Lean_Elab_getBetterRef(v_a_1517_, v_macroStack_1518_);
lean_dec(v_a_1517_);
v___x_1522_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg(v_a_1520_, v_macroStack_1518_, v___y_1514_);
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1525_ = v___x_1522_;
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1521_);
lean_ctor_set(v___x_1527_, 1, v_a_1523_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set_tag(v___x_1525_, 1);
lean_ctor_set(v___x_1525_, 0, v___x_1527_);
v___x_1529_ = v___x_1525_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec_ref(v___y_1513_);
lean_dec_ref(v_msg_1512_);
v_a_1532_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1516_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1516_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg___boxed(lean_object* v_msg_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(v_msg_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(lean_object* v_ref_1545_, lean_object* v_msg_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_Elab_Command_getRef___redArg(v___y_1547_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v_fileName_1552_; lean_object* v_fileMap_1553_; lean_object* v_currRecDepth_1554_; lean_object* v_cmdPos_1555_; lean_object* v_macroStack_1556_; lean_object* v_quotContext_x3f_1557_; lean_object* v_currMacroScope_1558_; lean_object* v_snap_x3f_1559_; lean_object* v_cancelTk_x3f_1560_; uint8_t v_suppressElabErrors_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1570_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref(v___x_1550_);
v_fileName_1552_ = lean_ctor_get(v___y_1547_, 0);
v_fileMap_1553_ = lean_ctor_get(v___y_1547_, 1);
v_currRecDepth_1554_ = lean_ctor_get(v___y_1547_, 2);
v_cmdPos_1555_ = lean_ctor_get(v___y_1547_, 3);
v_macroStack_1556_ = lean_ctor_get(v___y_1547_, 4);
v_quotContext_x3f_1557_ = lean_ctor_get(v___y_1547_, 5);
v_currMacroScope_1558_ = lean_ctor_get(v___y_1547_, 6);
v_snap_x3f_1559_ = lean_ctor_get(v___y_1547_, 8);
v_cancelTk_x3f_1560_ = lean_ctor_get(v___y_1547_, 9);
v_suppressElabErrors_1561_ = lean_ctor_get_uint8(v___y_1547_, sizeof(void*)*10);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___y_1547_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v___y_1547_, 7);
lean_dec(v_unused_1571_);
v___x_1563_ = v___y_1547_;
v_isShared_1564_ = v_isSharedCheck_1570_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_cancelTk_x3f_1560_);
lean_inc(v_snap_x3f_1559_);
lean_inc(v_currMacroScope_1558_);
lean_inc(v_quotContext_x3f_1557_);
lean_inc(v_macroStack_1556_);
lean_inc(v_cmdPos_1555_);
lean_inc(v_currRecDepth_1554_);
lean_inc(v_fileMap_1553_);
lean_inc(v_fileName_1552_);
lean_dec(v___y_1547_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1570_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v_ref_1565_; lean_object* v___x_1567_; 
v_ref_1565_ = l_Lean_replaceRef(v_ref_1545_, v_a_1551_);
lean_dec(v_a_1551_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 7, v_ref_1565_);
v___x_1567_ = v___x_1563_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_fileName_1552_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_fileMap_1553_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_currRecDepth_1554_);
lean_ctor_set(v_reuseFailAlloc_1569_, 3, v_cmdPos_1555_);
lean_ctor_set(v_reuseFailAlloc_1569_, 4, v_macroStack_1556_);
lean_ctor_set(v_reuseFailAlloc_1569_, 5, v_quotContext_x3f_1557_);
lean_ctor_set(v_reuseFailAlloc_1569_, 6, v_currMacroScope_1558_);
lean_ctor_set(v_reuseFailAlloc_1569_, 7, v_ref_1565_);
lean_ctor_set(v_reuseFailAlloc_1569_, 8, v_snap_x3f_1559_);
lean_ctor_set(v_reuseFailAlloc_1569_, 9, v_cancelTk_x3f_1560_);
lean_ctor_set_uint8(v_reuseFailAlloc_1569_, sizeof(void*)*10, v_suppressElabErrors_1561_);
v___x_1567_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(v_msg_1546_, v___x_1567_, v___y_1548_);
return v___x_1568_;
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec_ref(v___y_1547_);
lean_dec_ref(v_msg_1546_);
v_a_1572_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1550_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1550_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___boxed(lean_object* v_ref_1580_, lean_object* v_msg_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_1580_, v_msg_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec(v_ref_1580_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(lean_object* v_env_1586_, lean_object* v_currNamespace_1587_, lean_object* v_openDecls_1588_, lean_object* v_n_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = l_Lean_ResolveName_resolveNamespace(v_env_1586_, v_currNamespace_1587_, v_openDecls_1588_, v_n_1589_);
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
lean_ctor_set(v___x_1593_, 1, v___y_1591_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed(lean_object* v_env_1594_, lean_object* v_currNamespace_1595_, lean_object* v_openDecls_1596_, lean_object* v_n_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(v_env_1594_, v_currNamespace_1595_, v_openDecls_1596_, v_n_1597_, v___y_1598_, v___y_1599_);
lean_dec_ref(v___y_1598_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(lean_object* v_currNamespace_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v_currNamespace_1601_);
lean_ctor_set(v___x_1604_, 1, v___y_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(v_currNamespace_1605_, v___y_1606_, v___y_1607_);
lean_dec_ref(v___y_1606_);
return v_res_1608_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = l_Lean_maxRecDepthErrorMessage;
v___x_1615_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3);
v___x_1617_ = l_Lean_MessageData_ofFormat(v___x_1616_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4);
v___x_1619_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__2));
v___x_1620_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
lean_ctor_set(v___x_1620_, 1, v___x_1618_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg(lean_object* v_ref_1621_){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v_ref_1621_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___boxed(lean_object* v_ref_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg(v_ref_1626_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(lean_object* v_cls_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v_scopes_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v_opts_1638_; uint8_t v_hasTrace_1639_; 
v___x_1632_ = l_Lean_inheritedTraceOptions;
v___x_1633_ = lean_st_ref_get(v___x_1632_);
v___x_1634_ = lean_st_ref_get(v___y_1630_);
v_scopes_1635_ = lean_ctor_get(v___x_1634_, 2);
lean_inc(v_scopes_1635_);
lean_dec(v___x_1634_);
v___x_1636_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1637_ = l_List_head_x21___redArg(v___x_1636_, v_scopes_1635_);
lean_dec(v_scopes_1635_);
v_opts_1638_ = lean_ctor_get(v___x_1637_, 1);
lean_inc_ref(v_opts_1638_);
lean_dec(v___x_1637_);
v_hasTrace_1639_ = lean_ctor_get_uint8(v_opts_1638_, sizeof(void*)*1);
if (v_hasTrace_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec_ref(v_opts_1638_);
lean_dec(v___x_1633_);
lean_dec(v_cls_1629_);
v___x_1640_ = lean_box(v_hasTrace_1639_);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
return v___x_1641_;
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1642_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__1));
v___x_1643_ = l_Lean_Name_append(v___x_1642_, v_cls_1629_);
v___x_1644_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1633_, v_opts_1638_, v___x_1643_);
lean_dec(v___x_1643_);
lean_dec_ref(v_opts_1638_);
lean_dec(v___x_1633_);
v___x_1645_ = lean_box(v___x_1644_);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
return v___x_1646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg___boxed(lean_object* v_cls_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(v_cls_1647_, v___y_1648_);
lean_dec(v___y_1648_);
return v_res_1650_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1651_; double v___x_1652_; 
v___x_1651_ = lean_unsigned_to_nat(0u);
v___x_1652_ = lean_float_of_nat(v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(lean_object* v_cls_1655_, lean_object* v_msg_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_Elab_Command_getRef___redArg(v___y_1657_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1662_; lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1709_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref(v___x_1660_);
v___x_1662_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(v_msg_1656_, v___y_1658_);
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1709_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1709_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v_traceState_1668_; lean_object* v_env_1669_; lean_object* v_messages_1670_; lean_object* v_scopes_1671_; lean_object* v_usedQuotCtxts_1672_; lean_object* v_nextMacroScope_1673_; lean_object* v_maxRecDepth_1674_; lean_object* v_ngen_1675_; lean_object* v_auxDeclNGen_1676_; lean_object* v_infoState_1677_; lean_object* v_snapshotTasks_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1708_; 
v___x_1667_ = lean_st_ref_take(v___y_1658_);
v_traceState_1668_ = lean_ctor_get(v___x_1667_, 9);
v_env_1669_ = lean_ctor_get(v___x_1667_, 0);
v_messages_1670_ = lean_ctor_get(v___x_1667_, 1);
v_scopes_1671_ = lean_ctor_get(v___x_1667_, 2);
v_usedQuotCtxts_1672_ = lean_ctor_get(v___x_1667_, 3);
v_nextMacroScope_1673_ = lean_ctor_get(v___x_1667_, 4);
v_maxRecDepth_1674_ = lean_ctor_get(v___x_1667_, 5);
v_ngen_1675_ = lean_ctor_get(v___x_1667_, 6);
v_auxDeclNGen_1676_ = lean_ctor_get(v___x_1667_, 7);
v_infoState_1677_ = lean_ctor_get(v___x_1667_, 8);
v_snapshotTasks_1678_ = lean_ctor_get(v___x_1667_, 10);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1680_ = v___x_1667_;
v_isShared_1681_ = v_isSharedCheck_1708_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_snapshotTasks_1678_);
lean_inc(v_traceState_1668_);
lean_inc(v_infoState_1677_);
lean_inc(v_auxDeclNGen_1676_);
lean_inc(v_ngen_1675_);
lean_inc(v_maxRecDepth_1674_);
lean_inc(v_nextMacroScope_1673_);
lean_inc(v_usedQuotCtxts_1672_);
lean_inc(v_scopes_1671_);
lean_inc(v_messages_1670_);
lean_inc(v_env_1669_);
lean_dec(v___x_1667_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1708_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
uint64_t v_tid_1682_; lean_object* v_traces_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1707_; 
v_tid_1682_ = lean_ctor_get_uint64(v_traceState_1668_, sizeof(void*)*1);
v_traces_1683_ = lean_ctor_get(v_traceState_1668_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_traceState_1668_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1685_ = v_traceState_1668_;
v_isShared_1686_ = v_isSharedCheck_1707_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_traces_1683_);
lean_dec(v_traceState_1668_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1707_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; double v___x_1688_; uint8_t v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1687_ = lean_box(0);
v___x_1688_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0);
v___x_1689_ = 0;
v___x_1690_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1691_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1691_, 0, v_cls_1655_);
lean_ctor_set(v___x_1691_, 1, v___x_1687_);
lean_ctor_set(v___x_1691_, 2, v___x_1690_);
lean_ctor_set_float(v___x_1691_, sizeof(void*)*3, v___x_1688_);
lean_ctor_set_float(v___x_1691_, sizeof(void*)*3 + 8, v___x_1688_);
lean_ctor_set_uint8(v___x_1691_, sizeof(void*)*3 + 16, v___x_1689_);
v___x_1692_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__1));
v___x_1693_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set(v___x_1693_, 1, v_a_1663_);
lean_ctor_set(v___x_1693_, 2, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_a_1661_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = l_Lean_PersistentArray_push___redArg(v_traces_1683_, v___x_1694_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1695_);
v___x_1697_ = v___x_1685_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1695_);
lean_ctor_set_uint64(v_reuseFailAlloc_1706_, sizeof(void*)*1, v_tid_1682_);
v___x_1697_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
lean_object* v___x_1699_; 
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 9, v___x_1697_);
v___x_1699_ = v___x_1680_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_env_1669_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_messages_1670_);
lean_ctor_set(v_reuseFailAlloc_1705_, 2, v_scopes_1671_);
lean_ctor_set(v_reuseFailAlloc_1705_, 3, v_usedQuotCtxts_1672_);
lean_ctor_set(v_reuseFailAlloc_1705_, 4, v_nextMacroScope_1673_);
lean_ctor_set(v_reuseFailAlloc_1705_, 5, v_maxRecDepth_1674_);
lean_ctor_set(v_reuseFailAlloc_1705_, 6, v_ngen_1675_);
lean_ctor_set(v_reuseFailAlloc_1705_, 7, v_auxDeclNGen_1676_);
lean_ctor_set(v_reuseFailAlloc_1705_, 8, v_infoState_1677_);
lean_ctor_set(v_reuseFailAlloc_1705_, 9, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1705_, 10, v_snapshotTasks_1678_);
v___x_1699_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1700_ = lean_st_ref_set(v___y_1658_, v___x_1699_);
v___x_1701_ = lean_box(0);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1701_);
v___x_1703_ = v___x_1665_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec_ref(v_msg_1656_);
lean_dec(v_cls_1655_);
v_a_1710_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1660_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1660_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___boxed(lean_object* v_cls_1718_, lean_object* v_msg_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(v_cls_1718_, v_msg_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
return v_res_1723_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg(lean_object* v_keys_1724_, lean_object* v_i_1725_, lean_object* v_k_1726_){
_start:
{
lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = lean_array_get_size(v_keys_1724_);
v___x_1728_ = lean_nat_dec_lt(v_i_1725_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_dec(v_i_1725_);
return v___x_1728_;
}
else
{
lean_object* v_k_x27_1729_; uint8_t v___x_1730_; 
v_k_x27_1729_ = lean_array_fget_borrowed(v_keys_1724_, v_i_1725_);
v___x_1730_ = l_Lean_instBEqExtraModUse_beq(v_k_1726_, v_k_x27_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = lean_nat_add(v_i_1725_, v___x_1731_);
lean_dec(v_i_1725_);
v_i_1725_ = v___x_1732_;
goto _start;
}
else
{
lean_dec(v_i_1725_);
return v___x_1730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg___boxed(lean_object* v_keys_1734_, lean_object* v_i_1735_, lean_object* v_k_1736_){
_start:
{
uint8_t v_res_1737_; lean_object* v_r_1738_; 
v_res_1737_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg(v_keys_1734_, v_i_1735_, v_k_1736_);
lean_dec_ref(v_k_1736_);
lean_dec_ref(v_keys_1734_);
v_r_1738_ = lean_box(v_res_1737_);
return v_r_1738_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0(void){
_start:
{
size_t v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; 
v___x_1739_ = ((size_t)5ULL);
v___x_1740_ = ((size_t)1ULL);
v___x_1741_ = lean_usize_shift_left(v___x_1740_, v___x_1739_);
return v___x_1741_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1(void){
_start:
{
size_t v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; 
v___x_1742_ = ((size_t)1ULL);
v___x_1743_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0);
v___x_1744_ = lean_usize_sub(v___x_1743_, v___x_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg(lean_object* v_x_1745_, size_t v_x_1746_, lean_object* v_x_1747_){
_start:
{
if (lean_obj_tag(v_x_1745_) == 0)
{
lean_object* v_es_1748_; lean_object* v___x_1749_; size_t v___x_1750_; size_t v___x_1751_; size_t v___x_1752_; lean_object* v_j_1753_; lean_object* v___x_1754_; 
v_es_1748_ = lean_ctor_get(v_x_1745_, 0);
lean_inc_ref(v_es_1748_);
lean_dec_ref(v_x_1745_);
v___x_1749_ = lean_box(2);
v___x_1750_ = ((size_t)5ULL);
v___x_1751_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1);
v___x_1752_ = lean_usize_land(v_x_1746_, v___x_1751_);
v_j_1753_ = lean_usize_to_nat(v___x_1752_);
v___x_1754_ = lean_array_get(v___x_1749_, v_es_1748_, v_j_1753_);
lean_dec(v_j_1753_);
lean_dec_ref(v_es_1748_);
switch(lean_obj_tag(v___x_1754_))
{
case 0:
{
lean_object* v_key_1755_; uint8_t v___x_1756_; 
v_key_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_key_1755_);
lean_dec_ref(v___x_1754_);
v___x_1756_ = l_Lean_instBEqExtraModUse_beq(v_x_1747_, v_key_1755_);
lean_dec(v_key_1755_);
return v___x_1756_;
}
case 1:
{
lean_object* v_node_1757_; size_t v___x_1758_; 
v_node_1757_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_node_1757_);
lean_dec_ref(v___x_1754_);
v___x_1758_ = lean_usize_shift_right(v_x_1746_, v___x_1750_);
v_x_1745_ = v_node_1757_;
v_x_1746_ = v___x_1758_;
goto _start;
}
default: 
{
uint8_t v___x_1760_; 
v___x_1760_ = 0;
return v___x_1760_;
}
}
}
else
{
lean_object* v_ks_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v_ks_1761_ = lean_ctor_get(v_x_1745_, 0);
lean_inc_ref(v_ks_1761_);
lean_dec_ref(v_x_1745_);
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg(v_ks_1761_, v___x_1762_, v_x_1747_);
lean_dec_ref(v_ks_1761_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___boxed(lean_object* v_x_1764_, lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
size_t v_x_23265__boxed_1767_; uint8_t v_res_1768_; lean_object* v_r_1769_; 
v_x_23265__boxed_1767_ = lean_unbox_usize(v_x_1765_);
lean_dec(v_x_1765_);
v_res_1768_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg(v_x_1764_, v_x_23265__boxed_1767_, v_x_1766_);
lean_dec_ref(v_x_1766_);
v_r_1769_ = lean_box(v_res_1768_);
return v_r_1769_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg(lean_object* v_x_1770_, lean_object* v_x_1771_){
_start:
{
uint64_t v___x_1772_; size_t v___x_1773_; uint8_t v___x_1774_; 
v___x_1772_ = l_Lean_instHashableExtraModUse_hash(v_x_1771_);
v___x_1773_ = lean_uint64_to_usize(v___x_1772_);
v___x_1774_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg(v_x_1770_, v___x_1773_, v_x_1771_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg___boxed(lean_object* v_x_1775_, lean_object* v_x_1776_){
_start:
{
uint8_t v_res_1777_; lean_object* v_r_1778_; 
v_res_1777_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg(v_x_1775_, v_x_1776_);
lean_dec_ref(v_x_1776_);
v_r_1778_ = lean_box(v_res_1777_);
return v_r_1778_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__1));
v___x_1782_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__0));
v___x_1783_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1782_, v___x_1781_);
return v___x_1783_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__5));
v___x_1789_ = l_Lean_stringToMessageData(v___x_1788_);
return v___x_1789_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__7));
v___x_1792_ = l_Lean_stringToMessageData(v___x_1791_);
return v___x_1792_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1794_ = l_Lean_stringToMessageData(v___x_1793_);
return v___x_1794_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__10));
v___x_1797_ = l_Lean_stringToMessageData(v___x_1796_);
return v___x_1797_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__12));
v___x_1800_ = l_Lean_stringToMessageData(v___x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7(lean_object* v_mod_1805_, uint8_t v_isMeta_1806_, lean_object* v_hint_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; lean_object* v_env_1812_; uint8_t v_isExporting_1813_; lean_object* v___x_1814_; lean_object* v_env_1815_; lean_object* v___x_1816_; lean_object* v_entry_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___y_1822_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1811_ = lean_st_ref_get(v___y_1809_);
v_env_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc_ref(v_env_1812_);
lean_dec(v___x_1811_);
v_isExporting_1813_ = lean_ctor_get_uint8(v_env_1812_, sizeof(void*)*8);
lean_dec_ref(v_env_1812_);
v___x_1814_ = lean_st_ref_get(v___y_1809_);
v_env_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc_ref(v_env_1815_);
lean_dec(v___x_1814_);
v___x_1816_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2);
lean_inc(v_mod_1805_);
v_entry_1817_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1817_, 0, v_mod_1805_);
lean_ctor_set_uint8(v_entry_1817_, sizeof(void*)*1, v_isExporting_1813_);
lean_ctor_set_uint8(v_entry_1817_, sizeof(void*)*1 + 1, v_isMeta_1806_);
v___x_1818_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1819_ = lean_box(1);
v___x_1820_ = lean_box(0);
v___x_1848_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1816_, v___x_1818_, v_env_1815_, v___x_1819_, v___x_1820_);
v___x_1849_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg(v___x_1848_, v_entry_1817_);
if (v___x_1849_ == 0)
{
lean_object* v_cls_1850_; lean_object* v___x_1851_; lean_object* v_a_1852_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1859_; lean_object* v___y_1860_; uint8_t v___x_1872_; 
v_cls_1850_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__4));
v___x_1851_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(v_cls_1850_, v___y_1809_);
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref(v___x_1851_);
v___x_1872_ = lean_unbox(v_a_1852_);
lean_dec(v_a_1852_);
if (v___x_1872_ == 0)
{
lean_dec(v_hint_1807_);
lean_dec(v_mod_1805_);
v___y_1822_ = v___y_1809_;
goto v___jp_1821_;
}
else
{
lean_object* v___x_1873_; lean_object* v___y_1875_; 
v___x_1873_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11);
if (v_isExporting_1813_ == 0)
{
lean_object* v___x_1882_; 
v___x_1882_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__16));
v___y_1875_ = v___x_1882_;
goto v___jp_1874_;
}
else
{
lean_object* v___x_1883_; 
v___x_1883_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__17));
v___y_1875_ = v___x_1883_;
goto v___jp_1874_;
}
v___jp_1874_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1876_ = l_Lean_stringToMessageData(v___y_1875_);
v___x_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1873_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13);
v___x_1879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
if (v_isMeta_1806_ == 0)
{
lean_object* v___x_1880_; 
v___x_1880_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__14));
v___y_1859_ = v___x_1879_;
v___y_1860_ = v___x_1880_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1881_; 
v___x_1881_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__15));
v___y_1859_ = v___x_1879_;
v___y_1860_ = v___x_1881_;
goto v___jp_1858_;
}
}
}
v___jp_1853_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___y_1854_);
lean_ctor_set(v___x_1856_, 1, v___y_1855_);
v___x_1857_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(v_cls_1850_, v___x_1856_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_dec_ref(v___x_1857_);
v___y_1822_ = v___y_1809_;
goto v___jp_1821_;
}
else
{
lean_dec_ref(v_entry_1817_);
return v___x_1857_;
}
}
v___jp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1861_ = l_Lean_stringToMessageData(v___y_1860_);
v___x_1862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___y_1859_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6);
v___x_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = l_Lean_MessageData_ofName(v_mod_1805_);
v___x_1866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = l_Lean_Name_isAnonymous(v_hint_1807_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8);
v___x_1869_ = l_Lean_MessageData_ofName(v_hint_1807_);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___y_1854_ = v___x_1866_;
v___y_1855_ = v___x_1870_;
goto v___jp_1853_;
}
else
{
lean_object* v___x_1871_; 
lean_dec(v_hint_1807_);
v___x_1871_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9);
v___y_1854_ = v___x_1866_;
v___y_1855_ = v___x_1871_;
goto v___jp_1853_;
}
}
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec_ref(v_entry_1817_);
lean_dec(v_hint_1807_);
lean_dec(v_mod_1805_);
v___x_1884_ = lean_box(0);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
v___jp_1821_:
{
lean_object* v___x_1823_; lean_object* v_toEnvExtension_1824_; lean_object* v_env_1825_; lean_object* v_messages_1826_; lean_object* v_scopes_1827_; lean_object* v_usedQuotCtxts_1828_; lean_object* v_nextMacroScope_1829_; lean_object* v_maxRecDepth_1830_; lean_object* v_ngen_1831_; lean_object* v_auxDeclNGen_1832_; lean_object* v_infoState_1833_; lean_object* v_traceState_1834_; lean_object* v_snapshotTasks_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1847_; 
v___x_1823_ = lean_st_ref_take(v___y_1822_);
v_toEnvExtension_1824_ = lean_ctor_get(v___x_1818_, 0);
lean_inc_ref(v_toEnvExtension_1824_);
v_env_1825_ = lean_ctor_get(v___x_1823_, 0);
v_messages_1826_ = lean_ctor_get(v___x_1823_, 1);
v_scopes_1827_ = lean_ctor_get(v___x_1823_, 2);
v_usedQuotCtxts_1828_ = lean_ctor_get(v___x_1823_, 3);
v_nextMacroScope_1829_ = lean_ctor_get(v___x_1823_, 4);
v_maxRecDepth_1830_ = lean_ctor_get(v___x_1823_, 5);
v_ngen_1831_ = lean_ctor_get(v___x_1823_, 6);
v_auxDeclNGen_1832_ = lean_ctor_get(v___x_1823_, 7);
v_infoState_1833_ = lean_ctor_get(v___x_1823_, 8);
v_traceState_1834_ = lean_ctor_get(v___x_1823_, 9);
v_snapshotTasks_1835_ = lean_ctor_get(v___x_1823_, 10);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1837_ = v___x_1823_;
v_isShared_1838_ = v_isSharedCheck_1847_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_snapshotTasks_1835_);
lean_inc(v_traceState_1834_);
lean_inc(v_infoState_1833_);
lean_inc(v_auxDeclNGen_1832_);
lean_inc(v_ngen_1831_);
lean_inc(v_maxRecDepth_1830_);
lean_inc(v_nextMacroScope_1829_);
lean_inc(v_usedQuotCtxts_1828_);
lean_inc(v_scopes_1827_);
lean_inc(v_messages_1826_);
lean_inc(v_env_1825_);
lean_dec(v___x_1823_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1847_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v_asyncMode_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v_asyncMode_1839_ = lean_ctor_get(v_toEnvExtension_1824_, 2);
lean_inc(v_asyncMode_1839_);
lean_dec_ref(v_toEnvExtension_1824_);
v___x_1840_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1818_, v_env_1825_, v_entry_1817_, v_asyncMode_1839_, v___x_1820_);
lean_dec(v_asyncMode_1839_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1840_);
v___x_1842_ = v___x_1837_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_messages_1826_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_scopes_1827_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_usedQuotCtxts_1828_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v_nextMacroScope_1829_);
lean_ctor_set(v_reuseFailAlloc_1846_, 5, v_maxRecDepth_1830_);
lean_ctor_set(v_reuseFailAlloc_1846_, 6, v_ngen_1831_);
lean_ctor_set(v_reuseFailAlloc_1846_, 7, v_auxDeclNGen_1832_);
lean_ctor_set(v_reuseFailAlloc_1846_, 8, v_infoState_1833_);
lean_ctor_set(v_reuseFailAlloc_1846_, 9, v_traceState_1834_);
lean_ctor_set(v_reuseFailAlloc_1846_, 10, v_snapshotTasks_1835_);
v___x_1842_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = lean_st_ref_set(v___y_1822_, v___x_1842_);
v___x_1844_ = lean_box(0);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___boxed(lean_object* v_mod_1886_, lean_object* v_isMeta_1887_, lean_object* v_hint_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
uint8_t v_isMeta_boxed_1892_; lean_object* v_res_1893_; 
v_isMeta_boxed_1892_ = lean_unbox(v_isMeta_1887_);
v_res_1893_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7(v_mod_1886_, v_isMeta_boxed_1892_, v_hint_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8(lean_object* v___x_1894_, lean_object* v_declName_1895_, lean_object* v_as_1896_, size_t v_sz_1897_, size_t v_i_1898_, lean_object* v_b_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
uint8_t v___x_1903_; 
v___x_1903_ = lean_usize_dec_lt(v_i_1898_, v_sz_1897_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; 
lean_dec(v_declName_1895_);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_b_1899_);
return v___x_1904_;
}
else
{
lean_object* v___x_1905_; lean_object* v_modules_1906_; lean_object* v___x_1907_; lean_object* v_a_1908_; lean_object* v___x_1909_; lean_object* v_toImport_1910_; lean_object* v_module_1911_; uint8_t v___x_1912_; lean_object* v___x_1913_; 
v___x_1905_ = l_Lean_Environment_header(v___x_1894_);
v_modules_1906_ = lean_ctor_get(v___x_1905_, 3);
lean_inc_ref(v_modules_1906_);
lean_dec_ref(v___x_1905_);
v___x_1907_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1908_ = lean_array_uget_borrowed(v_as_1896_, v_i_1898_);
v___x_1909_ = lean_array_get(v___x_1907_, v_modules_1906_, v_a_1908_);
lean_dec_ref(v_modules_1906_);
v_toImport_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc_ref(v_toImport_1910_);
lean_dec(v___x_1909_);
v_module_1911_ = lean_ctor_get(v_toImport_1910_, 0);
lean_inc(v_module_1911_);
lean_dec_ref(v_toImport_1910_);
v___x_1912_ = 0;
lean_inc(v_declName_1895_);
v___x_1913_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7(v_module_1911_, v___x_1912_, v_declName_1895_, v___y_1900_, v___y_1901_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v___x_1914_; size_t v___x_1915_; size_t v___x_1916_; 
lean_dec_ref(v___x_1913_);
v___x_1914_ = lean_box(0);
v___x_1915_ = ((size_t)1ULL);
v___x_1916_ = lean_usize_add(v_i_1898_, v___x_1915_);
v_i_1898_ = v___x_1916_;
v_b_1899_ = v___x_1914_;
goto _start;
}
else
{
lean_dec(v_declName_1895_);
return v___x_1913_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8___boxed(lean_object* v___x_1918_, lean_object* v_declName_1919_, lean_object* v_as_1920_, lean_object* v_sz_1921_, lean_object* v_i_1922_, lean_object* v_b_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
size_t v_sz_boxed_1927_; size_t v_i_boxed_1928_; lean_object* v_res_1929_; 
v_sz_boxed_1927_ = lean_unbox_usize(v_sz_1921_);
lean_dec(v_sz_1921_);
v_i_boxed_1928_ = lean_unbox_usize(v_i_1922_);
lean_dec(v_i_1922_);
v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8(v___x_1918_, v_declName_1919_, v_as_1920_, v_sz_boxed_1927_, v_i_boxed_1928_, v_b_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec_ref(v_as_1920_);
lean_dec_ref(v___x_1918_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg(lean_object* v_a_1930_, lean_object* v_x_1931_){
_start:
{
if (lean_obj_tag(v_x_1931_) == 0)
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_box(0);
return v___x_1932_;
}
else
{
lean_object* v_key_1933_; lean_object* v_value_1934_; lean_object* v_tail_1935_; uint8_t v___x_1936_; 
v_key_1933_ = lean_ctor_get(v_x_1931_, 0);
v_value_1934_ = lean_ctor_get(v_x_1931_, 1);
v_tail_1935_ = lean_ctor_get(v_x_1931_, 2);
v___x_1936_ = lean_name_eq(v_key_1933_, v_a_1930_);
if (v___x_1936_ == 0)
{
v_x_1931_ = v_tail_1935_;
goto _start;
}
else
{
lean_object* v___x_1938_; 
lean_inc(v_value_1934_);
v___x_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1938_, 0, v_value_1934_);
return v___x_1938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg___boxed(lean_object* v_a_1939_, lean_object* v_x_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg(v_a_1939_, v_x_1940_);
lean_dec(v_x_1940_);
lean_dec(v_a_1939_);
return v_res_1941_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1942_; uint64_t v___x_1943_; 
v___x_1942_ = lean_unsigned_to_nat(1723u);
v___x_1943_ = lean_uint64_of_nat(v___x_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg(lean_object* v_m_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v_buckets_1946_; lean_object* v___x_1947_; uint64_t v___y_1949_; 
v_buckets_1946_ = lean_ctor_get(v_m_1944_, 1);
v___x_1947_ = lean_array_get_size(v_buckets_1946_);
if (lean_obj_tag(v_a_1945_) == 0)
{
uint64_t v___x_1963_; 
v___x_1963_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___closed__0);
v___y_1949_ = v___x_1963_;
goto v___jp_1948_;
}
else
{
uint64_t v_hash_1964_; 
v_hash_1964_ = lean_ctor_get_uint64(v_a_1945_, sizeof(void*)*2);
v___y_1949_ = v_hash_1964_;
goto v___jp_1948_;
}
v___jp_1948_:
{
uint64_t v___x_1950_; uint64_t v___x_1951_; uint64_t v_fold_1952_; uint64_t v___x_1953_; uint64_t v___x_1954_; uint64_t v___x_1955_; size_t v___x_1956_; size_t v___x_1957_; size_t v___x_1958_; size_t v___x_1959_; size_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1950_ = 32ULL;
v___x_1951_ = lean_uint64_shift_right(v___y_1949_, v___x_1950_);
v_fold_1952_ = lean_uint64_xor(v___y_1949_, v___x_1951_);
v___x_1953_ = 16ULL;
v___x_1954_ = lean_uint64_shift_right(v_fold_1952_, v___x_1953_);
v___x_1955_ = lean_uint64_xor(v_fold_1952_, v___x_1954_);
v___x_1956_ = lean_uint64_to_usize(v___x_1955_);
v___x_1957_ = lean_usize_of_nat(v___x_1947_);
v___x_1958_ = ((size_t)1ULL);
v___x_1959_ = lean_usize_sub(v___x_1957_, v___x_1958_);
v___x_1960_ = lean_usize_land(v___x_1956_, v___x_1959_);
v___x_1961_ = lean_array_uget_borrowed(v_buckets_1946_, v___x_1960_);
v___x_1962_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg(v_a_1945_, v___x_1961_);
return v___x_1962_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___boxed(lean_object* v_m_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg(v_m_1965_, v_a_1966_);
lean_dec(v_a_1966_);
lean_dec_ref(v_m_1965_);
return v_res_1967_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1970_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__1));
v___x_1971_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__0));
v___x_1972_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1971_, v___x_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(lean_object* v_declName_1975_, uint8_t v_isMeta_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v___x_1980_; lean_object* v_env_1984_; lean_object* v___y_1986_; lean_object* v___x_1999_; 
v___x_1980_ = lean_st_ref_get(v___y_1978_);
v_env_1984_ = lean_ctor_get(v___x_1980_, 0);
lean_inc_ref(v_env_1984_);
lean_dec(v___x_1980_);
v___x_1999_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1984_, v_declName_1975_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_dec_ref(v_env_1984_);
lean_dec(v_declName_1975_);
goto v___jp_1981_;
}
else
{
lean_object* v_val_2000_; lean_object* v___x_2001_; lean_object* v_modules_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
v_val_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_val_2000_);
lean_dec_ref(v___x_1999_);
v___x_2001_ = l_Lean_Environment_header(v_env_1984_);
v_modules_2002_ = lean_ctor_get(v___x_2001_, 3);
lean_inc_ref(v_modules_2002_);
lean_dec_ref(v___x_2001_);
v___x_2003_ = lean_array_get_size(v_modules_2002_);
v___x_2004_ = lean_nat_dec_lt(v_val_2000_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_dec_ref(v_modules_2002_);
lean_dec(v_val_2000_);
lean_dec_ref(v_env_1984_);
lean_dec(v_declName_1975_);
goto v___jp_1981_;
}
else
{
lean_object* v___x_2005_; lean_object* v_env_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___y_2010_; 
v___x_2005_ = lean_st_ref_get(v___y_1978_);
v_env_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc_ref(v_env_2006_);
lean_dec(v___x_2005_);
v___x_2007_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2);
v___x_2008_ = lean_array_fget(v_modules_2002_, v_val_2000_);
lean_dec(v_val_2000_);
lean_dec_ref(v_modules_2002_);
if (v_isMeta_1976_ == 0)
{
lean_dec_ref(v_env_2006_);
v___y_2010_ = v_isMeta_1976_;
goto v___jp_2009_;
}
else
{
uint8_t v___x_2021_; 
lean_inc(v_declName_1975_);
v___x_2021_ = l_Lean_isMarkedMeta(v_env_2006_, v_declName_1975_);
if (v___x_2021_ == 0)
{
v___y_2010_ = v_isMeta_1976_;
goto v___jp_2009_;
}
else
{
uint8_t v___x_2022_; 
v___x_2022_ = 0;
v___y_2010_ = v___x_2022_;
goto v___jp_2009_;
}
}
v___jp_2009_:
{
lean_object* v_toImport_2011_; lean_object* v_module_2012_; lean_object* v___x_2013_; 
v_toImport_2011_ = lean_ctor_get(v___x_2008_, 0);
lean_inc_ref(v_toImport_2011_);
lean_dec(v___x_2008_);
v_module_2012_ = lean_ctor_get(v_toImport_2011_, 0);
lean_inc(v_module_2012_);
lean_dec_ref(v_toImport_2011_);
lean_inc(v_declName_1975_);
v___x_2013_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7(v_module_2012_, v___y_2010_, v_declName_1975_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_dec_ref(v___x_2013_);
v___x_2014_ = l_Lean_indirectModUseExt;
v___x_2015_ = lean_box(1);
v___x_2016_ = lean_box(0);
lean_inc_ref(v_env_1984_);
v___x_2017_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2007_, v___x_2014_, v_env_1984_, v___x_2015_, v___x_2016_);
v___x_2018_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg(v___x_2017_, v_declName_1975_);
lean_dec(v___x_2017_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__3));
v___y_1986_ = v___x_2019_;
goto v___jp_1985_;
}
else
{
lean_object* v_val_2020_; 
v_val_2020_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_val_2020_);
lean_dec_ref(v___x_2018_);
v___y_1986_ = v_val_2020_;
goto v___jp_1985_;
}
}
else
{
lean_dec_ref(v_env_1984_);
lean_dec(v_declName_1975_);
return v___x_2013_;
}
}
}
}
v___jp_1981_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = lean_box(0);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
return v___x_1983_;
}
v___jp_1985_:
{
lean_object* v___x_1987_; size_t v_sz_1988_; size_t v___x_1989_; lean_object* v___x_1990_; 
v___x_1987_ = lean_box(0);
v_sz_1988_ = lean_array_size(v___y_1986_);
v___x_1989_ = ((size_t)0ULL);
v___x_1990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8(v_env_1984_, v_declName_1975_, v___y_1986_, v_sz_1988_, v___x_1989_, v___x_1987_, v___y_1977_, v___y_1978_);
lean_dec_ref(v___y_1986_);
lean_dec_ref(v_env_1984_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; 
v_unused_1998_ = lean_ctor_get(v___x_1990_, 0);
lean_dec(v_unused_1998_);
v___x_1992_ = v___x_1990_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_dec(v___x_1990_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1987_);
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1987_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
else
{
return v___x_1990_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___boxed(lean_object* v_declName_2023_, lean_object* v_isMeta_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
uint8_t v_isMeta_boxed_2028_; lean_object* v_res_2029_; 
v_isMeta_boxed_2028_ = lean_unbox(v_isMeta_2024_);
v_res_2029_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(v_declName_2023_, v_isMeta_boxed_2028_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg(lean_object* v_as_x27_2030_, lean_object* v_b_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
if (lean_obj_tag(v_as_x27_2030_) == 0)
{
lean_object* v___x_2035_; 
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_b_2031_);
return v___x_2035_;
}
else
{
lean_object* v_head_2036_; lean_object* v_tail_2037_; uint8_t v___x_2038_; lean_object* v___x_2039_; 
v_head_2036_ = lean_ctor_get(v_as_x27_2030_, 0);
lean_inc(v_head_2036_);
v_tail_2037_ = lean_ctor_get(v_as_x27_2030_, 1);
lean_inc(v_tail_2037_);
lean_dec_ref(v_as_x27_2030_);
v___x_2038_ = 1;
v___x_2039_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(v_head_2036_, v___x_2038_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v___x_2040_; 
lean_dec_ref(v___x_2039_);
v___x_2040_ = lean_box(0);
v_as_x27_2030_ = v_tail_2037_;
v_b_2031_ = v___x_2040_;
goto _start;
}
else
{
lean_dec(v_tail_2037_);
return v___x_2039_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg___boxed(lean_object* v_as_x27_2042_, lean_object* v_b_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg(v_as_x27_2042_, v_b_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(lean_object* v_env_2048_, lean_object* v_opts_2049_, lean_object* v_currNamespace_2050_, lean_object* v_openDecls_2051_, lean_object* v_n_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = l_Lean_ResolveName_resolveGlobalName(v_env_2048_, v_opts_2049_, v_currNamespace_2050_, v_openDecls_2051_, v_n_2052_);
v___x_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
lean_ctor_set(v___x_2056_, 1, v___y_2054_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed(lean_object* v_env_2057_, lean_object* v_opts_2058_, lean_object* v_currNamespace_2059_, lean_object* v_openDecls_2060_, lean_object* v_n_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(v_env_2057_, v_opts_2058_, v_currNamespace_2059_, v_openDecls_2060_, v_n_2061_, v___y_2062_, v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec_ref(v_opts_2058_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(lean_object* v_env_2065_, lean_object* v_declName_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
uint8_t v___x_2069_; lean_object* v_env_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; uint8_t v___x_2073_; 
v___x_2069_ = 0;
v_env_2070_ = l_Lean_Environment_setExporting(v_env_2065_, v___x_2069_);
lean_inc(v_declName_2066_);
v___x_2071_ = l_Lean_mkPrivateName(v_env_2070_, v_declName_2066_);
v___x_2072_ = 1;
lean_inc_ref(v_env_2070_);
v___x_2073_ = l_Lean_Environment_contains(v_env_2070_, v___x_2071_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; uint8_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2074_ = l_Lean_privateToUserName(v_declName_2066_);
v___x_2075_ = l_Lean_Environment_contains(v_env_2070_, v___x_2074_, v___x_2072_);
v___x_2076_ = lean_box(v___x_2075_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
lean_ctor_set(v___x_2077_, 1, v___y_2068_);
return v___x_2077_;
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
lean_dec_ref(v_env_2070_);
lean_dec(v_declName_2066_);
v___x_2078_ = lean_box(v___x_2073_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v___y_2068_);
return v___x_2079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed(lean_object* v_env_2080_, lean_object* v_declName_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(v_env_2080_, v_declName_2081_, v___y_2082_, v___y_2083_);
lean_dec_ref(v___y_2082_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(lean_object* v_x_2085_, lean_object* v___y_2086_){
_start:
{
if (lean_obj_tag(v_x_2085_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2088_; 
v_a_2087_ = lean_ctor_get(v_x_2085_, 0);
lean_inc(v_a_2087_);
v___x_2088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2088_, 0, v_a_2087_);
lean_ctor_set(v___x_2088_, 1, v___y_2086_);
return v___x_2088_;
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2090_; 
v_a_2089_ = lean_ctor_get(v_x_2085_, 0);
lean_inc(v_a_2089_);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v_a_2089_);
lean_ctor_set(v___x_2090_, 1, v___y_2086_);
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg___boxed(lean_object* v_x_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(v_x_2091_, v___y_2092_);
lean_dec_ref(v_x_2091_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(lean_object* v_env_2094_, lean_object* v_stx_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2094_, v_stx_2095_, v___y_2096_, v___y_2097_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
if (lean_obj_tag(v_a_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2108_; 
v_a_2100_ = lean_ctor_get(v___x_2098_, 1);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; 
v_unused_2109_ = lean_ctor_get(v___x_2098_, 0);
lean_dec(v_unused_2109_);
v___x_2102_ = v___x_2098_;
v_isShared_2103_ = v_isSharedCheck_2108_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2098_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2108_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = lean_box(0);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2104_);
v___x_2106_ = v___x_2102_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_a_2100_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
else
{
lean_object* v_val_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2138_; 
v_val_2110_ = lean_ctor_get(v_a_2099_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_a_2099_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2112_ = v_a_2099_;
v_isShared_2113_ = v_isSharedCheck_2138_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_val_2110_);
lean_dec(v_a_2099_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2138_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_snd_2114_; 
v_snd_2114_ = lean_ctor_get(v_val_2110_, 1);
lean_inc(v_snd_2114_);
lean_dec(v_val_2110_);
if (lean_obj_tag(v_snd_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2124_; 
lean_del_object(v___x_2112_);
v_a_2115_ = lean_ctor_get(v___x_2098_, 1);
lean_inc(v_a_2115_);
lean_dec_ref(v___x_2098_);
v_a_2116_ = lean_ctor_get(v_snd_2114_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_snd_2114_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2118_ = v_snd_2114_;
v_isShared_2119_ = v_isSharedCheck_2124_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v_snd_2114_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2124_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(v___x_2121_, v_a_2115_);
lean_dec_ref(v___x_2121_);
return v___x_2122_;
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2137_; 
v_a_2125_ = lean_ctor_get(v___x_2098_, 1);
lean_inc(v_a_2125_);
lean_dec_ref(v___x_2098_);
v_a_2126_ = lean_ctor_get(v_snd_2114_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_snd_2114_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2128_ = v_snd_2114_;
v_isShared_2129_ = v_isSharedCheck_2137_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v_snd_2114_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2137_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v_a_2126_);
v___x_2131_ = v___x_2112_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2133_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2131_);
v___x_2133_ = v___x_2128_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(v___x_2133_, v_a_2125_);
lean_dec_ref(v___x_2133_);
return v___x_2134_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
v_a_2139_ = lean_ctor_get(v___x_2098_, 0);
v_a_2140_ = lean_ctor_get(v___x_2098_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2098_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_inc(v_a_2139_);
lean_dec(v___x_2098_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2139_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed(lean_object* v_env_2148_, lean_object* v_stx_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(v_env_2148_, v_stx_2149_, v___y_2150_, v___y_2151_);
lean_dec_ref(v___y_2150_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(lean_object* v_as_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
if (lean_obj_tag(v_as_2153_) == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
else
{
lean_object* v_head_2159_; lean_object* v_tail_2160_; lean_object* v_fst_2161_; lean_object* v_snd_2162_; lean_object* v___x_2163_; lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2176_; 
v_head_2159_ = lean_ctor_get(v_as_2153_, 0);
lean_inc(v_head_2159_);
v_tail_2160_ = lean_ctor_get(v_as_2153_, 1);
lean_inc(v_tail_2160_);
lean_dec_ref(v_as_2153_);
v_fst_2161_ = lean_ctor_get(v_head_2159_, 0);
lean_inc(v_fst_2161_);
v_snd_2162_ = lean_ctor_get(v_head_2159_, 1);
lean_inc(v_snd_2162_);
lean_dec(v_head_2159_);
lean_inc(v_fst_2161_);
v___x_2163_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(v_fst_2161_, v___y_2155_);
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2176_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2176_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
uint8_t v___x_2168_; 
v___x_2168_ = lean_unbox(v_a_2164_);
lean_dec(v_a_2164_);
if (v___x_2168_ == 0)
{
lean_del_object(v___x_2166_);
lean_dec(v_snd_2162_);
lean_dec(v_fst_2161_);
v_as_2153_ = v_tail_2160_;
goto _start;
}
else
{
lean_object* v___x_2171_; 
if (v_isShared_2167_ == 0)
{
lean_ctor_set_tag(v___x_2166_, 3);
lean_ctor_set(v___x_2166_, 0, v_snd_2162_);
v___x_2171_ = v___x_2166_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_snd_2162_);
v___x_2171_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = l_Lean_MessageData_ofFormat(v___x_2171_);
v___x_2173_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(v_fst_2161_, v___x_2172_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_dec_ref(v___x_2173_);
v_as_2153_ = v_tail_2160_;
goto _start;
}
else
{
lean_dec(v_tail_2160_);
return v___x_2173_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___boxed(lean_object* v_as_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(v_as_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(lean_object* v_x_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v___x_2187_; lean_object* v_env_2188_; lean_object* v___x_2189_; lean_object* v_scopes_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v_opts_2193_; lean_object* v___x_2194_; 
v___x_2187_ = lean_st_ref_get(v___y_2185_);
v_env_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc_ref(v_env_2188_);
lean_dec(v___x_2187_);
v___x_2189_ = lean_st_ref_get(v___y_2185_);
v_scopes_2190_ = lean_ctor_get(v___x_2189_, 2);
lean_inc(v_scopes_2190_);
lean_dec(v___x_2189_);
v___x_2191_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2192_ = l_List_head_x21___redArg(v___x_2191_, v_scopes_2190_);
lean_dec(v_scopes_2190_);
v_opts_2193_ = lean_ctor_get(v___x_2192_, 1);
lean_inc_ref(v_opts_2193_);
lean_dec(v___x_2192_);
v___x_2194_ = l_Lean_Elab_Command_getScope___redArg(v___y_2185_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v_currNamespace_2196_; lean_object* v___x_2197_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref(v___x_2194_);
v_currNamespace_2196_ = lean_ctor_get(v_a_2195_, 2);
lean_inc(v_currNamespace_2196_);
lean_dec(v_a_2195_);
v___x_2197_ = l_Lean_Elab_Command_getScope___redArg(v___y_2185_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v_openDecls_2199_; lean_object* v___x_2200_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref(v___x_2197_);
v_openDecls_2199_ = lean_ctor_get(v_a_2198_, 3);
lean_inc(v_openDecls_2199_);
lean_dec(v_a_2198_);
v___x_2200_ = l_Lean_Elab_Command_getRef___redArg(v___y_2184_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2202_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v___x_2200_);
v___x_2202_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2184_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v_currRecDepth_2204_; lean_object* v_quotContext_x3f_2205_; lean_object* v___f_2206_; lean_object* v___f_2207_; lean_object* v___f_2208_; lean_object* v___f_2209_; lean_object* v___f_2210_; lean_object* v_methods_2211_; lean_object* v_a_2213_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
v_currRecDepth_2204_ = lean_ctor_get(v___y_2184_, 2);
v_quotContext_x3f_2205_ = lean_ctor_get(v___y_2184_, 5);
lean_inc_ref(v_env_2188_);
v___f_2206_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2206_, 0, v_env_2188_);
lean_inc_ref(v_env_2188_);
v___f_2207_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2207_, 0, v_env_2188_);
lean_inc(v_currNamespace_2196_);
v___f_2208_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2208_, 0, v_currNamespace_2196_);
lean_inc(v_openDecls_2199_);
lean_inc(v_currNamespace_2196_);
lean_inc_ref(v_env_2188_);
v___f_2209_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2209_, 0, v_env_2188_);
lean_closure_set(v___f_2209_, 1, v_currNamespace_2196_);
lean_closure_set(v___f_2209_, 2, v_openDecls_2199_);
v___f_2210_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2210_, 0, v_env_2188_);
lean_closure_set(v___f_2210_, 1, v_opts_2193_);
lean_closure_set(v___f_2210_, 2, v_currNamespace_2196_);
lean_closure_set(v___f_2210_, 3, v_openDecls_2199_);
v_methods_2211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2211_, 0, v___f_2207_);
lean_ctor_set(v_methods_2211_, 1, v___f_2208_);
lean_ctor_set(v_methods_2211_, 2, v___f_2206_);
lean_ctor_set(v_methods_2211_, 3, v___f_2209_);
lean_ctor_set(v_methods_2211_, 4, v___f_2210_);
if (lean_obj_tag(v_quotContext_x3f_2205_) == 0)
{
lean_object* v___x_2285_; lean_object* v_a_2286_; 
v___x_2285_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2185_);
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref(v___x_2285_);
v_a_2213_ = v_a_2286_;
goto v___jp_2212_;
}
else
{
lean_object* v_val_2287_; 
v_val_2287_ = lean_ctor_get(v_quotContext_x3f_2205_, 0);
lean_inc(v_val_2287_);
v_a_2213_ = v_val_2287_;
goto v___jp_2212_;
}
v___jp_2212_:
{
lean_object* v___x_2214_; lean_object* v_maxRecDepth_2215_; lean_object* v___x_2216_; lean_object* v_nextMacroScope_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2214_ = lean_st_ref_get(v___y_2185_);
v_maxRecDepth_2215_ = lean_ctor_get(v___x_2214_, 5);
lean_inc(v_maxRecDepth_2215_);
lean_dec(v___x_2214_);
v___x_2216_ = lean_st_ref_get(v___y_2185_);
v_nextMacroScope_2217_ = lean_ctor_get(v___x_2216_, 4);
lean_inc(v_nextMacroScope_2217_);
lean_dec(v___x_2216_);
lean_inc(v_currRecDepth_2204_);
v___x_2218_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2218_, 0, v_methods_2211_);
lean_ctor_set(v___x_2218_, 1, v_a_2213_);
lean_ctor_set(v___x_2218_, 2, v_a_2203_);
lean_ctor_set(v___x_2218_, 3, v_currRecDepth_2204_);
lean_ctor_set(v___x_2218_, 4, v_maxRecDepth_2215_);
lean_ctor_set(v___x_2218_, 5, v_a_2201_);
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2220_, 0, v_nextMacroScope_2217_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
lean_ctor_set(v___x_2220_, 2, v___x_2219_);
v___x_2221_ = lean_apply_2(v_x_2183_, v___x_2218_, v___x_2220_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v_a_2223_; lean_object* v_macroScope_2224_; lean_object* v_traceMsgs_2225_; lean_object* v_expandedMacroDecls_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 1);
lean_inc(v_a_2222_);
v_a_2223_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2223_);
lean_dec_ref(v___x_2221_);
v_macroScope_2224_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_macroScope_2224_);
v_traceMsgs_2225_ = lean_ctor_get(v_a_2222_, 1);
lean_inc(v_traceMsgs_2225_);
v_expandedMacroDecls_2226_ = lean_ctor_get(v_a_2222_, 2);
lean_inc(v_expandedMacroDecls_2226_);
lean_dec(v_a_2222_);
v___x_2227_ = lean_box(0);
v___x_2228_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg(v_expandedMacroDecls_2226_, v___x_2227_, v___y_2184_, v___y_2185_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v___x_2229_; lean_object* v_env_2230_; lean_object* v_messages_2231_; lean_object* v_scopes_2232_; lean_object* v_usedQuotCtxts_2233_; lean_object* v_maxRecDepth_2234_; lean_object* v_ngen_2235_; lean_object* v_auxDeclNGen_2236_; lean_object* v_infoState_2237_; lean_object* v_traceState_2238_; lean_object* v_snapshotTasks_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2265_; 
lean_dec_ref(v___x_2228_);
v___x_2229_ = lean_st_ref_take(v___y_2185_);
v_env_2230_ = lean_ctor_get(v___x_2229_, 0);
v_messages_2231_ = lean_ctor_get(v___x_2229_, 1);
v_scopes_2232_ = lean_ctor_get(v___x_2229_, 2);
v_usedQuotCtxts_2233_ = lean_ctor_get(v___x_2229_, 3);
v_maxRecDepth_2234_ = lean_ctor_get(v___x_2229_, 5);
v_ngen_2235_ = lean_ctor_get(v___x_2229_, 6);
v_auxDeclNGen_2236_ = lean_ctor_get(v___x_2229_, 7);
v_infoState_2237_ = lean_ctor_get(v___x_2229_, 8);
v_traceState_2238_ = lean_ctor_get(v___x_2229_, 9);
v_snapshotTasks_2239_ = lean_ctor_get(v___x_2229_, 10);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2265_ == 0)
{
lean_object* v_unused_2266_; 
v_unused_2266_ = lean_ctor_get(v___x_2229_, 4);
lean_dec(v_unused_2266_);
v___x_2241_ = v___x_2229_;
v_isShared_2242_ = v_isSharedCheck_2265_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_snapshotTasks_2239_);
lean_inc(v_traceState_2238_);
lean_inc(v_infoState_2237_);
lean_inc(v_auxDeclNGen_2236_);
lean_inc(v_ngen_2235_);
lean_inc(v_maxRecDepth_2234_);
lean_inc(v_usedQuotCtxts_2233_);
lean_inc(v_scopes_2232_);
lean_inc(v_messages_2231_);
lean_inc(v_env_2230_);
lean_dec(v___x_2229_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2265_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 4, v_macroScope_2224_);
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_env_2230_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_messages_2231_);
lean_ctor_set(v_reuseFailAlloc_2264_, 2, v_scopes_2232_);
lean_ctor_set(v_reuseFailAlloc_2264_, 3, v_usedQuotCtxts_2233_);
lean_ctor_set(v_reuseFailAlloc_2264_, 4, v_macroScope_2224_);
lean_ctor_set(v_reuseFailAlloc_2264_, 5, v_maxRecDepth_2234_);
lean_ctor_set(v_reuseFailAlloc_2264_, 6, v_ngen_2235_);
lean_ctor_set(v_reuseFailAlloc_2264_, 7, v_auxDeclNGen_2236_);
lean_ctor_set(v_reuseFailAlloc_2264_, 8, v_infoState_2237_);
lean_ctor_set(v_reuseFailAlloc_2264_, 9, v_traceState_2238_);
lean_ctor_set(v_reuseFailAlloc_2264_, 10, v_snapshotTasks_2239_);
v___x_2244_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_st_ref_set(v___y_2185_, v___x_2244_);
v___x_2246_ = l_List_reverse___redArg(v_traceMsgs_2225_);
v___x_2247_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(v___x_2246_, v___y_2184_, v___y_2185_);
lean_dec_ref(v___y_2184_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; 
v_unused_2255_ = lean_ctor_get(v___x_2247_, 0);
lean_dec(v_unused_2255_);
v___x_2249_ = v___x_2247_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_dec(v___x_2247_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v_a_2223_);
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2223_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec(v_a_2223_);
v_a_2256_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2247_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2247_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec(v_traceMsgs_2225_);
lean_dec(v_macroScope_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v___y_2184_);
v_a_2267_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2228_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2228_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
else
{
lean_object* v_a_2275_; 
v_a_2275_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2275_);
lean_dec_ref(v___x_2221_);
if (lean_obj_tag(v_a_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v_a_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; 
v_a_2276_ = lean_ctor_get(v_a_2275_, 0);
lean_inc(v_a_2276_);
v_a_2277_ = lean_ctor_get(v_a_2275_, 1);
lean_inc_ref(v_a_2277_);
lean_dec_ref(v_a_2275_);
v___x_2278_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0));
v___x_2279_ = lean_string_dec_eq(v_a_2277_, v___x_2278_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2280_, 0, v_a_2277_);
v___x_2281_ = l_Lean_MessageData_ofFormat(v___x_2280_);
v___x_2282_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_a_2276_, v___x_2281_, v___y_2184_, v___y_2185_);
lean_dec(v_a_2276_);
return v___x_2282_;
}
else
{
lean_object* v___x_2283_; 
lean_dec_ref(v_a_2277_);
lean_dec_ref(v___y_2184_);
v___x_2283_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg(v_a_2276_);
return v___x_2283_;
}
}
else
{
lean_object* v___x_2284_; 
lean_dec_ref(v___y_2184_);
v___x_2284_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2284_;
}
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v_a_2201_);
lean_dec(v_openDecls_2199_);
lean_dec(v_currNamespace_2196_);
lean_dec_ref(v_opts_2193_);
lean_dec_ref(v_env_2188_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v_x_2183_);
v_a_2288_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2202_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2202_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec(v_openDecls_2199_);
lean_dec(v_currNamespace_2196_);
lean_dec_ref(v_opts_2193_);
lean_dec_ref(v_env_2188_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v_x_2183_);
v_a_2296_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2200_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2200_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec(v_currNamespace_2196_);
lean_dec_ref(v_opts_2193_);
lean_dec_ref(v_env_2188_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v_x_2183_);
v_a_2304_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2197_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2197_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v_opts_2193_);
lean_dec_ref(v_env_2188_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v_x_2183_);
v_a_2312_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2194_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2194_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___boxed(lean_object* v_x_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(lean_object* v_as_2325_, size_t v_i_2326_, size_t v_stop_2327_, lean_object* v_b_2328_){
_start:
{
lean_object* v___y_2330_; uint8_t v___x_2334_; 
v___x_2334_ = lean_usize_dec_eq(v_i_2326_, v_stop_2327_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2335_ = lean_array_uget_borrowed(v_as_2325_, v_i_2326_);
lean_inc(v___x_2335_);
v___x_2336_ = l_Lean_Syntax_getKind(v___x_2335_);
v___x_2337_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
v___x_2338_ = lean_name_eq(v___x_2336_, v___x_2337_);
lean_dec(v___x_2336_);
if (v___x_2338_ == 0)
{
v___y_2330_ = v_b_2328_;
goto v___jp_2329_;
}
else
{
lean_object* v___x_2339_; 
lean_inc(v___x_2335_);
v___x_2339_ = lean_array_push(v_b_2328_, v___x_2335_);
v___y_2330_ = v___x_2339_;
goto v___jp_2329_;
}
}
else
{
return v_b_2328_;
}
v___jp_2329_:
{
size_t v___x_2331_; size_t v___x_2332_; 
v___x_2331_ = ((size_t)1ULL);
v___x_2332_ = lean_usize_add(v_i_2326_, v___x_2331_);
v_i_2326_ = v___x_2332_;
v_b_2328_ = v___y_2330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8___boxed(lean_object* v_as_2340_, lean_object* v_i_2341_, lean_object* v_stop_2342_, lean_object* v_b_2343_){
_start:
{
size_t v_i_boxed_2344_; size_t v_stop_boxed_2345_; lean_object* v_res_2346_; 
v_i_boxed_2344_ = lean_unbox_usize(v_i_2341_);
lean_dec(v_i_2341_);
v_stop_boxed_2345_ = lean_unbox_usize(v_stop_2342_);
lean_dec(v_stop_2342_);
v_res_2346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v_as_2340_, v_i_boxed_2344_, v_stop_boxed_2345_, v_b_2343_);
lean_dec_ref(v_as_2340_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation(lean_object* v_x_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; uint8_t v___y_2489_; size_t v___y_2490_; lean_object* v___y_2491_; 
v___x_2420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0));
v___x_2421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1));
v___x_2422_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
lean_inc(v_x_2389_);
v___x_2423_ = l_Lean_Syntax_isOfKind(v_x_2389_, v___x_2422_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2532_; 
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_x_2389_);
v___x_2532_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2532_;
}
else
{
lean_object* v___x_2533_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; uint8_t v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; size_t v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; uint8_t v___y_2626_; size_t v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; uint8_t v___y_2661_; lean_object* v___y_2662_; size_t v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; uint8_t v___y_2693_; size_t v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; uint8_t v___y_2725_; size_t v___y_2726_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v_prio_x3f_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v_name_x3f_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v_prec_x3f_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v_attrs_x3f_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v_doc_x3f_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2888_ = l_Lean_Syntax_getArg(v_x_2389_, v___x_2533_);
v___x_2889_ = l_Lean_Syntax_isNone(v___x_2888_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; uint8_t v___x_2891_; 
v___x_2890_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2888_);
v___x_2891_ = l_Lean_Syntax_matchesNull(v___x_2888_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; 
lean_dec(v___x_2888_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_x_2389_);
v___x_2892_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2892_;
}
else
{
lean_object* v_doc_x3f_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; 
v_doc_x3f_2893_ = l_Lean_Syntax_getArg(v___x_2888_, v___x_2533_);
lean_dec(v___x_2888_);
v___x_2894_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__15));
lean_inc(v_doc_x3f_2893_);
v___x_2895_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2893_, v___x_2894_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; 
lean_dec(v_doc_x3f_2893_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_x_2389_);
v___x_2896_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2896_;
}
else
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2897_, 0, v_doc_x3f_2893_);
v_doc_x3f_2872_ = v___x_2897_;
v___y_2873_ = v_a_2390_;
v___y_2874_ = v_a_2391_;
goto v___jp_2871_;
}
}
}
else
{
lean_object* v___x_2898_; 
lean_dec(v___x_2888_);
v___x_2898_ = lean_box(0);
v_doc_x3f_2872_ = v___x_2898_;
v___y_2873_ = v_a_2390_;
v___y_2874_ = v_a_2391_;
goto v___jp_2871_;
}
v___jp_2534_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; size_t v_sz_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
lean_inc_ref(v___y_2543_);
v___x_2555_ = l_Array_append___redArg(v___y_2543_, v___y_2554_);
lean_dec_ref(v___y_2554_);
lean_inc(v___y_2540_);
lean_inc(v___y_2547_);
v___x_2556_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2556_, 0, v___y_2547_);
lean_ctor_set(v___x_2556_, 1, v___y_2540_);
lean_ctor_set(v___x_2556_, 2, v___x_2555_);
v___x_2557_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
v___x_2558_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc(v___y_2547_);
v___x_2559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___y_2547_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__8));
lean_inc(v___y_2547_);
v___x_2561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___y_2547_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
lean_inc(v___y_2547_);
v___x_2563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___y_2547_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = l_Nat_reprFast(v___y_2542_);
v___x_2565_ = lean_box(2);
v___x_2566_ = l_Lean_Syntax_mkNumLit(v___x_2564_, v___x_2565_);
v___x_2567_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
lean_inc(v___y_2547_);
v___x_2568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___y_2547_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
lean_inc(v___y_2547_);
v___x_2569_ = l_Lean_Syntax_node5(v___y_2547_, v___x_2557_, v___x_2559_, v___x_2561_, v___x_2563_, v___x_2566_, v___x_2568_);
lean_inc(v___y_2540_);
lean_inc(v___y_2547_);
v___x_2570_ = l_Lean_Syntax_node1(v___y_2547_, v___y_2540_, v___x_2569_);
v_sz_2571_ = lean_array_size(v___y_2536_);
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_2571_, v___y_2553_, v___y_2536_);
lean_inc_ref(v___y_2543_);
v___x_2573_ = l_Array_append___redArg(v___y_2543_, v___x_2572_);
lean_dec_ref(v___x_2572_);
lean_inc(v___y_2540_);
lean_inc(v___y_2547_);
v___x_2574_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2574_, 0, v___y_2547_);
lean_ctor_set(v___x_2574_, 1, v___y_2540_);
lean_ctor_set(v___x_2574_, 2, v___x_2573_);
v___x_2575_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc(v___y_2547_);
v___x_2576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___y_2547_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = lean_unsigned_to_nat(10u);
v___x_2578_ = lean_mk_empty_array_with_capacity(v___x_2577_);
v___x_2579_ = lean_array_push(v___x_2578_, v___y_2551_);
v___x_2580_ = lean_array_push(v___x_2579_, v___y_2537_);
lean_inc(v___y_2549_);
v___x_2581_ = lean_array_push(v___x_2580_, v___y_2549_);
v___x_2582_ = lean_array_push(v___x_2581_, v___y_2538_);
v___x_2583_ = lean_array_push(v___x_2582_, v___y_2552_);
v___x_2584_ = lean_array_push(v___x_2583_, v___x_2556_);
v___x_2585_ = lean_array_push(v___x_2584_, v___x_2570_);
v___x_2586_ = lean_array_push(v___x_2585_, v___x_2574_);
v___x_2587_ = lean_array_push(v___x_2586_, v___x_2576_);
v___x_2588_ = lean_array_push(v___x_2587_, v___y_2544_);
v___x_2589_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2589_, 0, v___y_2547_);
lean_ctor_set(v___x_2589_, 1, v___y_2545_);
lean_ctor_set(v___x_2589_, 2, v___x_2588_);
lean_inc(v___y_2535_);
lean_inc_ref(v___y_2539_);
v___x_2590_ = l_Lean_Elab_Command_elabSyntax(v___x_2589_, v___y_2539_, v___y_2535_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref(v___x_2590_);
v___x_2592_ = lean_array_get_size(v___y_2548_);
v___x_2593_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__68));
v___x_2594_ = lean_nat_dec_lt(v___x_2533_, v___x_2592_);
if (v___x_2594_ == 0)
{
v___y_2478_ = v___y_2535_;
v___y_2479_ = v___x_2567_;
v___y_2480_ = v___y_2539_;
v___y_2481_ = v___y_2540_;
v___y_2482_ = v___y_2541_;
v___y_2483_ = v___x_2565_;
v___y_2484_ = v___y_2543_;
v___y_2485_ = v___y_2546_;
v___y_2486_ = v_a_2591_;
v___y_2487_ = v___y_2548_;
v___y_2488_ = v___y_2549_;
v___y_2489_ = v___y_2550_;
v___y_2490_ = v___y_2553_;
v___y_2491_ = v___x_2593_;
goto v___jp_2477_;
}
else
{
uint8_t v___x_2595_; 
v___x_2595_ = lean_nat_dec_le(v___x_2592_, v___x_2592_);
if (v___x_2595_ == 0)
{
if (v___x_2594_ == 0)
{
v___y_2478_ = v___y_2535_;
v___y_2479_ = v___x_2567_;
v___y_2480_ = v___y_2539_;
v___y_2481_ = v___y_2540_;
v___y_2482_ = v___y_2541_;
v___y_2483_ = v___x_2565_;
v___y_2484_ = v___y_2543_;
v___y_2485_ = v___y_2546_;
v___y_2486_ = v_a_2591_;
v___y_2487_ = v___y_2548_;
v___y_2488_ = v___y_2549_;
v___y_2489_ = v___y_2550_;
v___y_2490_ = v___y_2553_;
v___y_2491_ = v___x_2593_;
goto v___jp_2477_;
}
else
{
size_t v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_usize_of_nat(v___x_2592_);
v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2548_, v___y_2553_, v___x_2596_, v___x_2593_);
v___y_2478_ = v___y_2535_;
v___y_2479_ = v___x_2567_;
v___y_2480_ = v___y_2539_;
v___y_2481_ = v___y_2540_;
v___y_2482_ = v___y_2541_;
v___y_2483_ = v___x_2565_;
v___y_2484_ = v___y_2543_;
v___y_2485_ = v___y_2546_;
v___y_2486_ = v_a_2591_;
v___y_2487_ = v___y_2548_;
v___y_2488_ = v___y_2549_;
v___y_2489_ = v___y_2550_;
v___y_2490_ = v___y_2553_;
v___y_2491_ = v___x_2597_;
goto v___jp_2477_;
}
}
else
{
size_t v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_usize_of_nat(v___x_2592_);
v___x_2599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2548_, v___y_2553_, v___x_2598_, v___x_2593_);
v___y_2478_ = v___y_2535_;
v___y_2479_ = v___x_2567_;
v___y_2480_ = v___y_2539_;
v___y_2481_ = v___y_2540_;
v___y_2482_ = v___y_2541_;
v___y_2483_ = v___x_2565_;
v___y_2484_ = v___y_2543_;
v___y_2485_ = v___y_2546_;
v___y_2486_ = v_a_2591_;
v___y_2487_ = v___y_2548_;
v___y_2488_ = v___y_2549_;
v___y_2489_ = v___y_2550_;
v___y_2490_ = v___y_2553_;
v___y_2491_ = v___x_2599_;
goto v___jp_2477_;
}
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2543_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2535_);
v_a_2600_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2590_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2590_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
v___jp_2608_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_inc_ref(v___y_2618_);
v___x_2629_ = l_Array_append___redArg(v___y_2618_, v___y_2628_);
lean_dec_ref(v___y_2628_);
lean_inc(v___y_2614_);
lean_inc(v___y_2622_);
v___x_2630_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2630_, 0, v___y_2622_);
lean_ctor_set(v___x_2630_, 1, v___y_2614_);
lean_ctor_set(v___x_2630_, 2, v___x_2629_);
if (lean_obj_tag(v___y_2613_) == 1)
{
lean_object* v_val_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v_val_2631_ = lean_ctor_get(v___y_2613_, 0);
lean_inc(v_val_2631_);
lean_dec_ref(v___y_2613_);
v___x_2632_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
v___x_2633_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc(v___y_2622_);
v___x_2634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___y_2622_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__11));
lean_inc(v___y_2622_);
v___x_2636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___y_2622_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
v___x_2637_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
lean_inc(v___y_2622_);
v___x_2638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___y_2622_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
lean_inc(v___y_2622_);
v___x_2640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___y_2622_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
lean_inc(v___y_2622_);
v___x_2641_ = l_Lean_Syntax_node5(v___y_2622_, v___x_2632_, v___x_2634_, v___x_2636_, v___x_2638_, v_val_2631_, v___x_2640_);
v___x_2642_ = l_Array_mkArray1___redArg(v___x_2641_);
v___y_2535_ = v___y_2609_;
v___y_2536_ = v___y_2610_;
v___y_2537_ = v___y_2611_;
v___y_2538_ = v___y_2612_;
v___y_2539_ = v___y_2615_;
v___y_2540_ = v___y_2614_;
v___y_2541_ = v___y_2616_;
v___y_2542_ = v___y_2617_;
v___y_2543_ = v___y_2618_;
v___y_2544_ = v___y_2619_;
v___y_2545_ = v___y_2620_;
v___y_2546_ = v___y_2621_;
v___y_2547_ = v___y_2622_;
v___y_2548_ = v___y_2624_;
v___y_2549_ = v___y_2623_;
v___y_2550_ = v___y_2626_;
v___y_2551_ = v___y_2625_;
v___y_2552_ = v___x_2630_;
v___y_2553_ = v___y_2627_;
v___y_2554_ = v___x_2642_;
goto v___jp_2534_;
}
else
{
lean_object* v___x_2643_; 
lean_dec(v___y_2613_);
v___x_2643_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2535_ = v___y_2609_;
v___y_2536_ = v___y_2610_;
v___y_2537_ = v___y_2611_;
v___y_2538_ = v___y_2612_;
v___y_2539_ = v___y_2615_;
v___y_2540_ = v___y_2614_;
v___y_2541_ = v___y_2616_;
v___y_2542_ = v___y_2617_;
v___y_2543_ = v___y_2618_;
v___y_2544_ = v___y_2619_;
v___y_2545_ = v___y_2620_;
v___y_2546_ = v___y_2621_;
v___y_2547_ = v___y_2622_;
v___y_2548_ = v___y_2624_;
v___y_2549_ = v___y_2623_;
v___y_2550_ = v___y_2626_;
v___y_2551_ = v___y_2625_;
v___y_2552_ = v___x_2630_;
v___y_2553_ = v___y_2627_;
v___y_2554_ = v___x_2643_;
goto v___jp_2534_;
}
}
v___jp_2644_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_inc_ref(v___y_2654_);
v___x_2665_ = l_Array_append___redArg(v___y_2654_, v___y_2664_);
lean_dec_ref(v___y_2664_);
lean_inc(v___y_2650_);
lean_inc(v___y_2658_);
v___x_2666_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2666_, 0, v___y_2658_);
lean_ctor_set(v___x_2666_, 1, v___y_2650_);
lean_ctor_set(v___x_2666_, 2, v___x_2665_);
lean_inc(v___y_2658_);
v___x_2667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___y_2658_);
lean_ctor_set(v___x_2667_, 1, v___y_2649_);
if (lean_obj_tag(v___y_2647_) == 1)
{
lean_object* v_val_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_val_2668_ = lean_ctor_get(v___y_2647_, 0);
lean_inc(v_val_2668_);
lean_dec_ref(v___y_2647_);
v___x_2669_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
v___x_2670_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc(v___y_2658_);
v___x_2671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___y_2658_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
lean_inc(v___y_2658_);
v___x_2672_ = l_Lean_Syntax_node2(v___y_2658_, v___x_2669_, v___x_2671_, v_val_2668_);
v___x_2673_ = l_Array_mkArray1___redArg(v___x_2672_);
v___y_2609_ = v___y_2645_;
v___y_2610_ = v___y_2646_;
v___y_2611_ = v___x_2666_;
v___y_2612_ = v___x_2667_;
v___y_2613_ = v___y_2648_;
v___y_2614_ = v___y_2650_;
v___y_2615_ = v___y_2651_;
v___y_2616_ = v___y_2652_;
v___y_2617_ = v___y_2653_;
v___y_2618_ = v___y_2654_;
v___y_2619_ = v___y_2655_;
v___y_2620_ = v___y_2656_;
v___y_2621_ = v___y_2657_;
v___y_2622_ = v___y_2658_;
v___y_2623_ = v___y_2660_;
v___y_2624_ = v___y_2659_;
v___y_2625_ = v___y_2662_;
v___y_2626_ = v___y_2661_;
v___y_2627_ = v___y_2663_;
v___y_2628_ = v___x_2673_;
goto v___jp_2608_;
}
else
{
lean_object* v___x_2674_; 
lean_dec(v___y_2647_);
v___x_2674_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2609_ = v___y_2645_;
v___y_2610_ = v___y_2646_;
v___y_2611_ = v___x_2666_;
v___y_2612_ = v___x_2667_;
v___y_2613_ = v___y_2648_;
v___y_2614_ = v___y_2650_;
v___y_2615_ = v___y_2651_;
v___y_2616_ = v___y_2652_;
v___y_2617_ = v___y_2653_;
v___y_2618_ = v___y_2654_;
v___y_2619_ = v___y_2655_;
v___y_2620_ = v___y_2656_;
v___y_2621_ = v___y_2657_;
v___y_2622_ = v___y_2658_;
v___y_2623_ = v___y_2660_;
v___y_2624_ = v___y_2659_;
v___y_2625_ = v___y_2662_;
v___y_2626_ = v___y_2661_;
v___y_2627_ = v___y_2663_;
v___y_2628_ = v___x_2674_;
goto v___jp_2608_;
}
}
v___jp_2675_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_inc_ref(v___y_2686_);
v___x_2696_ = l_Array_append___redArg(v___y_2686_, v___y_2695_);
lean_dec_ref(v___y_2695_);
lean_inc(v___y_2682_);
lean_inc(v___y_2690_);
v___x_2697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2697_, 0, v___y_2690_);
lean_ctor_set(v___x_2697_, 1, v___y_2682_);
lean_ctor_set(v___x_2697_, 2, v___x_2696_);
if (lean_obj_tag(v___y_2676_) == 1)
{
lean_object* v_val_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_val_2698_ = lean_ctor_get(v___y_2676_, 0);
lean_inc(v_val_2698_);
lean_dec_ref(v___y_2676_);
v___x_2699_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__11));
lean_inc_ref(v___y_2684_);
v___x_2700_ = l_Lean_Name_mkStr4(v___x_2420_, v___x_2421_, v___y_2684_, v___x_2699_);
v___x_2701_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc(v___y_2690_);
v___x_2702_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___y_2690_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
lean_inc_ref(v___y_2686_);
v___x_2703_ = l_Array_append___redArg(v___y_2686_, v_val_2698_);
lean_dec(v_val_2698_);
lean_inc(v___y_2682_);
lean_inc(v___y_2690_);
v___x_2704_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2704_, 0, v___y_2690_);
lean_ctor_set(v___x_2704_, 1, v___y_2682_);
lean_ctor_set(v___x_2704_, 2, v___x_2703_);
v___x_2705_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
lean_inc(v___y_2690_);
v___x_2706_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___y_2690_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
lean_inc(v___y_2690_);
v___x_2707_ = l_Lean_Syntax_node3(v___y_2690_, v___x_2700_, v___x_2702_, v___x_2704_, v___x_2706_);
v___x_2708_ = l_Array_mkArray1___redArg(v___x_2707_);
v___y_2645_ = v___y_2677_;
v___y_2646_ = v___y_2678_;
v___y_2647_ = v___y_2679_;
v___y_2648_ = v___y_2680_;
v___y_2649_ = v___y_2681_;
v___y_2650_ = v___y_2682_;
v___y_2651_ = v___y_2683_;
v___y_2652_ = v___y_2684_;
v___y_2653_ = v___y_2685_;
v___y_2654_ = v___y_2686_;
v___y_2655_ = v___y_2687_;
v___y_2656_ = v___y_2688_;
v___y_2657_ = v___y_2689_;
v___y_2658_ = v___y_2690_;
v___y_2659_ = v___y_2692_;
v___y_2660_ = v___y_2691_;
v___y_2661_ = v___y_2693_;
v___y_2662_ = v___x_2697_;
v___y_2663_ = v___y_2694_;
v___y_2664_ = v___x_2708_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2709_; 
lean_dec(v___y_2676_);
v___x_2709_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2645_ = v___y_2677_;
v___y_2646_ = v___y_2678_;
v___y_2647_ = v___y_2679_;
v___y_2648_ = v___y_2680_;
v___y_2649_ = v___y_2681_;
v___y_2650_ = v___y_2682_;
v___y_2651_ = v___y_2683_;
v___y_2652_ = v___y_2684_;
v___y_2653_ = v___y_2685_;
v___y_2654_ = v___y_2686_;
v___y_2655_ = v___y_2687_;
v___y_2656_ = v___y_2688_;
v___y_2657_ = v___y_2689_;
v___y_2658_ = v___y_2690_;
v___y_2659_ = v___y_2692_;
v___y_2660_ = v___y_2691_;
v___y_2661_ = v___y_2693_;
v___y_2662_ = v___x_2697_;
v___y_2663_ = v___y_2694_;
v___y_2664_ = v___x_2709_;
goto v___jp_2644_;
}
}
v___jp_2710_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2727_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__12));
v___x_2728_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__13));
v___x_2729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_2730_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
if (lean_obj_tag(v___y_2715_) == 1)
{
lean_object* v_val_2731_; lean_object* v___x_2732_; 
v_val_2731_ = lean_ctor_get(v___y_2715_, 0);
lean_inc(v_val_2731_);
lean_dec_ref(v___y_2715_);
v___x_2732_ = l_Array_mkArray1___redArg(v_val_2731_);
v___y_2676_ = v___y_2711_;
v___y_2677_ = v___y_2712_;
v___y_2678_ = v___y_2713_;
v___y_2679_ = v___y_2714_;
v___y_2680_ = v___y_2716_;
v___y_2681_ = v___x_2727_;
v___y_2682_ = v___x_2729_;
v___y_2683_ = v___y_2717_;
v___y_2684_ = v___y_2718_;
v___y_2685_ = v___y_2719_;
v___y_2686_ = v___x_2730_;
v___y_2687_ = v___y_2720_;
v___y_2688_ = v___x_2728_;
v___y_2689_ = v___y_2721_;
v___y_2690_ = v___y_2722_;
v___y_2691_ = v___y_2723_;
v___y_2692_ = v___y_2724_;
v___y_2693_ = v___y_2725_;
v___y_2694_ = v___y_2726_;
v___y_2695_ = v___x_2732_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2733_; 
lean_dec(v___y_2715_);
v___x_2733_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2676_ = v___y_2711_;
v___y_2677_ = v___y_2712_;
v___y_2678_ = v___y_2713_;
v___y_2679_ = v___y_2714_;
v___y_2680_ = v___y_2716_;
v___y_2681_ = v___x_2727_;
v___y_2682_ = v___x_2729_;
v___y_2683_ = v___y_2717_;
v___y_2684_ = v___y_2718_;
v___y_2685_ = v___y_2719_;
v___y_2686_ = v___x_2730_;
v___y_2687_ = v___y_2720_;
v___y_2688_ = v___x_2728_;
v___y_2689_ = v___y_2721_;
v___y_2690_ = v___y_2722_;
v___y_2691_ = v___y_2723_;
v___y_2692_ = v___y_2724_;
v___y_2693_ = v___y_2725_;
v___y_2694_ = v___y_2726_;
v___y_2695_ = v___x_2733_;
goto v___jp_2675_;
}
}
v___jp_2734_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio), 3, 1);
lean_closure_set(v___x_2744_, 0, v_prio_x3f_2741_);
lean_inc_ref(v___y_2742_);
v___x_2745_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2744_, v___y_2742_, v___y_2743_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v_items_2749_; size_t v_sz_2750_; size_t v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref(v___x_2745_);
v___x_2747_ = lean_unsigned_to_nat(7u);
v___x_2748_ = l_Lean_Syntax_getArg(v_x_2389_, v___x_2747_);
v_items_2749_ = l_Lean_Syntax_getArgs(v___x_2748_);
lean_dec(v___x_2748_);
v_sz_2750_ = lean_array_size(v_items_2749_);
v___x_2751_ = ((size_t)0ULL);
v___x_2752_ = lean_box_usize(v_sz_2750_);
v___x_2753_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___boxed__const__1));
lean_inc_ref(v_items_2749_);
v___x_2754_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed), 5, 3);
lean_closure_set(v___x_2754_, 0, v___x_2752_);
lean_closure_set(v___x_2754_, 1, v___x_2753_);
lean_closure_set(v___x_2754_, 2, v_items_2749_);
lean_inc_ref(v___y_2742_);
v___x_2755_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2754_, v___y_2742_, v___y_2743_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2757_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref(v___x_2755_);
v___x_2757_ = l_Lean_Elab_Command_getRef___redArg(v___y_2742_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2759_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2758_);
lean_dec_ref(v___x_2757_);
v___x_2759_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2742_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_quotContext_x3f_2760_; lean_object* v___x_2761_; uint8_t v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v_rhs_2765_; lean_object* v_attrs_x3f_2766_; lean_object* v___x_2767_; 
lean_dec_ref(v___x_2759_);
v_quotContext_x3f_2760_ = lean_ctor_get(v___y_2742_, 5);
v___x_2761_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
v___x_2762_ = 0;
v___x_2763_ = l_Lean_mkIdentFrom(v_x_2389_, v___x_2761_, v___x_2762_);
v___x_2764_ = lean_unsigned_to_nat(9u);
v_rhs_2765_ = l_Lean_Syntax_getArg(v_x_2389_, v___x_2764_);
lean_dec(v_x_2389_);
lean_inc(v_rhs_2765_);
v_attrs_x3f_2766_ = l_Lean_Elab_Command_addInheritDocDefault(v_rhs_2765_, v___y_2738_);
v___x_2767_ = l_Lean_SourceInfo_fromRef(v_a_2758_, v___x_2762_);
lean_dec(v_a_2758_);
if (lean_obj_tag(v_quotContext_x3f_2760_) == 0)
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2743_);
lean_dec_ref(v___x_2768_);
v___y_2711_ = v_attrs_x3f_2766_;
v___y_2712_ = v___y_2743_;
v___y_2713_ = v_a_2756_;
v___y_2714_ = v___y_2735_;
v___y_2715_ = v___y_2737_;
v___y_2716_ = v___y_2736_;
v___y_2717_ = v___y_2742_;
v___y_2718_ = v___y_2740_;
v___y_2719_ = v_a_2746_;
v___y_2720_ = v___x_2763_;
v___y_2721_ = v_rhs_2765_;
v___y_2722_ = v___x_2767_;
v___y_2723_ = v___y_2739_;
v___y_2724_ = v_items_2749_;
v___y_2725_ = v___x_2762_;
v___y_2726_ = v___x_2751_;
goto v___jp_2710_;
}
else
{
v___y_2711_ = v_attrs_x3f_2766_;
v___y_2712_ = v___y_2743_;
v___y_2713_ = v_a_2756_;
v___y_2714_ = v___y_2735_;
v___y_2715_ = v___y_2737_;
v___y_2716_ = v___y_2736_;
v___y_2717_ = v___y_2742_;
v___y_2718_ = v___y_2740_;
v___y_2719_ = v_a_2746_;
v___y_2720_ = v___x_2763_;
v___y_2721_ = v_rhs_2765_;
v___y_2722_ = v___x_2767_;
v___y_2723_ = v___y_2739_;
v___y_2724_ = v_items_2749_;
v___y_2725_ = v___x_2762_;
v___y_2726_ = v___x_2751_;
goto v___jp_2710_;
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_a_2758_);
lean_dec(v_a_2756_);
lean_dec_ref(v_items_2749_);
lean_dec(v_a_2746_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v_x_2389_);
v_a_2769_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2759_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2759_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec(v_a_2756_);
lean_dec_ref(v_items_2749_);
lean_dec(v_a_2746_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v_x_2389_);
v_a_2777_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2757_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2757_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec_ref(v_items_2749_);
lean_dec(v_a_2746_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v_x_2389_);
v_a_2785_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2755_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2755_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
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
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v_x_2389_);
v_a_2793_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2745_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2745_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
v___jp_2801_:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; 
v___x_2812_ = lean_unsigned_to_nat(6u);
v___x_2813_ = l_Lean_Syntax_getArg(v_x_2389_, v___x_2812_);
v___x_2814_ = l_Lean_Syntax_isNone(v___x_2813_);
if (v___x_2814_ == 0)
{
uint8_t v___x_2815_; 
lean_inc(v___x_2813_);
v___x_2815_ = l_Lean_Syntax_matchesNull(v___x_2813_, v___y_2804_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; 
lean_dec(v___x_2813_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v_name_x3f_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec(v_x_2389_);
v___x_2816_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2816_;
}
else
{
lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v___x_2817_ = l_Lean_Syntax_getArg(v___x_2813_, v___x_2533_);
lean_dec(v___x_2813_);
v___x_2818_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
lean_inc(v___x_2817_);
v___x_2819_ = l_Lean_Syntax_isOfKind(v___x_2817_, v___x_2818_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; 
lean_dec(v___x_2817_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v_name_x3f_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec(v_x_2389_);
v___x_2820_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2820_;
}
else
{
lean_object* v_prio_x3f_2821_; lean_object* v___x_2822_; 
v_prio_x3f_2821_ = l_Lean_Syntax_getArg(v___x_2817_, v___y_2807_);
lean_dec(v___x_2817_);
v___x_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2822_, 0, v_prio_x3f_2821_);
v___y_2735_ = v___y_2802_;
v___y_2736_ = v_name_x3f_2809_;
v___y_2737_ = v___y_2803_;
v___y_2738_ = v___y_2805_;
v___y_2739_ = v___y_2806_;
v___y_2740_ = v___y_2808_;
v_prio_x3f_2741_ = v___x_2822_;
v___y_2742_ = v___y_2810_;
v___y_2743_ = v___y_2811_;
goto v___jp_2734_;
}
}
}
else
{
lean_object* v___x_2823_; 
lean_dec(v___x_2813_);
v___x_2823_ = lean_box(0);
v___y_2735_ = v___y_2802_;
v___y_2736_ = v_name_x3f_2809_;
v___y_2737_ = v___y_2803_;
v___y_2738_ = v___y_2805_;
v___y_2739_ = v___y_2806_;
v___y_2740_ = v___y_2808_;
v_prio_x3f_2741_ = v___x_2823_;
v___y_2742_ = v___y_2810_;
v___y_2743_ = v___y_2811_;
goto v___jp_2734_;
}
}
v___jp_2824_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2834_ = lean_unsigned_to_nat(5u);
v___x_2835_ = l_Lean_Syntax_getArg(v_x_2389_, v___x_2834_);
v___x_2836_ = l_Lean_Syntax_isNone(v___x_2835_);
if (v___x_2836_ == 0)
{
uint8_t v___x_2837_; 
lean_inc(v___x_2835_);
v___x_2837_ = l_Lean_Syntax_matchesNull(v___x_2835_, v___y_2827_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; 
lean_dec(v___x_2835_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v_prec_x3f_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2828_);
lean_dec(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec(v_x_2389_);
v___x_2838_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2838_;
}
else
{
lean_object* v___x_2839_; lean_object* v___x_2840_; uint8_t v___x_2841_; 
v___x_2839_ = l_Lean_Syntax_getArg(v___x_2835_, v___x_2533_);
lean_dec(v___x_2835_);
v___x_2840_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
lean_inc(v___x_2839_);
v___x_2841_ = l_Lean_Syntax_isOfKind(v___x_2839_, v___x_2840_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; 
lean_dec(v___x_2839_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v_prec_x3f_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2828_);
lean_dec(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec(v_x_2389_);
v___x_2842_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2842_;
}
else
{
lean_object* v_name_x3f_2843_; lean_object* v___x_2844_; 
v_name_x3f_2843_ = l_Lean_Syntax_getArg(v___x_2839_, v___y_2829_);
lean_dec(v___x_2839_);
v___x_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2844_, 0, v_name_x3f_2843_);
v___y_2802_ = v_prec_x3f_2831_;
v___y_2803_ = v___y_2825_;
v___y_2804_ = v___y_2827_;
v___y_2805_ = v___y_2826_;
v___y_2806_ = v___y_2828_;
v___y_2807_ = v___y_2829_;
v___y_2808_ = v___y_2830_;
v_name_x3f_2809_ = v___x_2844_;
v___y_2810_ = v___y_2832_;
v___y_2811_ = v___y_2833_;
goto v___jp_2801_;
}
}
}
else
{
lean_object* v___x_2845_; 
lean_dec(v___x_2835_);
v___x_2845_ = lean_box(0);
v___y_2802_ = v_prec_x3f_2831_;
v___y_2803_ = v___y_2825_;
v___y_2804_ = v___y_2827_;
v___y_2805_ = v___y_2826_;
v___y_2806_ = v___y_2828_;
v___y_2807_ = v___y_2829_;
v___y_2808_ = v___y_2830_;
v_name_x3f_2809_ = v___x_2845_;
v___y_2810_ = v___y_2832_;
v___y_2811_ = v___y_2833_;
goto v___jp_2801_;
}
}
v___jp_2846_:
{
lean_object* v___x_2852_; lean_object* v_attrKind_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; 
v___x_2852_ = lean_unsigned_to_nat(2u);
v_attrKind_2853_ = l_Lean_Syntax_getArg(v_x_2389_, v___x_2852_);
v___x_2854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2));
v___x_2855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(v_attrKind_2853_);
v___x_2856_ = l_Lean_Syntax_isOfKind(v_attrKind_2853_, v___x_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
lean_dec(v_attrKind_2853_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v_attrs_x3f_2849_);
lean_dec(v___y_2847_);
lean_dec(v_x_2389_);
v___x_2857_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2857_;
}
else
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v___x_2858_ = lean_unsigned_to_nat(3u);
v___x_2859_ = lean_unsigned_to_nat(4u);
v___x_2860_ = l_Lean_Syntax_getArg(v_x_2389_, v___x_2859_);
v___x_2861_ = l_Lean_Syntax_isNone(v___x_2860_);
if (v___x_2861_ == 0)
{
uint8_t v___x_2862_; 
lean_inc(v___x_2860_);
v___x_2862_ = l_Lean_Syntax_matchesNull(v___x_2860_, v___y_2848_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; 
lean_dec(v___x_2860_);
lean_dec(v_attrKind_2853_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v_attrs_x3f_2849_);
lean_dec(v___y_2847_);
lean_dec(v_x_2389_);
v___x_2863_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2863_;
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; 
v___x_2864_ = l_Lean_Syntax_getArg(v___x_2860_, v___x_2533_);
lean_dec(v___x_2860_);
v___x_2865_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
lean_inc(v___x_2864_);
v___x_2866_ = l_Lean_Syntax_isOfKind(v___x_2864_, v___x_2865_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; 
lean_dec(v___x_2864_);
lean_dec(v_attrKind_2853_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v_attrs_x3f_2849_);
lean_dec(v___y_2847_);
lean_dec(v_x_2389_);
v___x_2867_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2867_;
}
else
{
lean_object* v_prec_x3f_2868_; lean_object* v___x_2869_; 
v_prec_x3f_2868_ = l_Lean_Syntax_getArg(v___x_2864_, v___y_2848_);
lean_dec(v___x_2864_);
v___x_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2869_, 0, v_prec_x3f_2868_);
v___y_2825_ = v___y_2847_;
v___y_2826_ = v_attrs_x3f_2849_;
v___y_2827_ = v___y_2848_;
v___y_2828_ = v_attrKind_2853_;
v___y_2829_ = v___x_2858_;
v___y_2830_ = v___x_2854_;
v_prec_x3f_2831_ = v___x_2869_;
v___y_2832_ = v___y_2850_;
v___y_2833_ = v___y_2851_;
goto v___jp_2824_;
}
}
}
else
{
lean_object* v___x_2870_; 
lean_dec(v___x_2860_);
v___x_2870_ = lean_box(0);
v___y_2825_ = v___y_2847_;
v___y_2826_ = v_attrs_x3f_2849_;
v___y_2827_ = v___y_2848_;
v___y_2828_ = v_attrKind_2853_;
v___y_2829_ = v___x_2858_;
v___y_2830_ = v___x_2854_;
v_prec_x3f_2831_ = v___x_2870_;
v___y_2832_ = v___y_2850_;
v___y_2833_ = v___y_2851_;
goto v___jp_2824_;
}
}
}
v___jp_2871_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2875_ = lean_unsigned_to_nat(1u);
v___x_2876_ = l_Lean_Syntax_getArg(v_x_2389_, v___x_2875_);
v___x_2877_ = l_Lean_Syntax_isNone(v___x_2876_);
if (v___x_2877_ == 0)
{
uint8_t v___x_2878_; 
lean_inc(v___x_2876_);
v___x_2878_ = l_Lean_Syntax_matchesNull(v___x_2876_, v___x_2875_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; 
lean_dec(v___x_2876_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v_doc_x3f_2872_);
lean_dec(v_x_2389_);
v___x_2879_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2879_;
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; 
v___x_2880_ = l_Lean_Syntax_getArg(v___x_2876_, v___x_2533_);
lean_dec(v___x_2876_);
v___x_2881_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
lean_inc(v___x_2880_);
v___x_2882_ = l_Lean_Syntax_isOfKind(v___x_2880_, v___x_2881_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2883_; 
lean_dec(v___x_2880_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v_doc_x3f_2872_);
lean_dec(v_x_2389_);
v___x_2883_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2883_;
}
else
{
lean_object* v___x_2884_; lean_object* v_attrs_x3f_2885_; lean_object* v___x_2886_; 
v___x_2884_ = l_Lean_Syntax_getArg(v___x_2880_, v___x_2875_);
lean_dec(v___x_2880_);
v_attrs_x3f_2885_ = l_Lean_Syntax_getArgs(v___x_2884_);
lean_dec(v___x_2884_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v_attrs_x3f_2885_);
v___y_2847_ = v_doc_x3f_2872_;
v___y_2848_ = v___x_2875_;
v_attrs_x3f_2849_ = v___x_2886_;
v___y_2850_ = v___y_2873_;
v___y_2851_ = v___y_2874_;
goto v___jp_2846_;
}
}
}
else
{
lean_object* v___x_2887_; 
lean_dec(v___x_2876_);
v___x_2887_ = lean_box(0);
v___y_2847_ = v_doc_x3f_2872_;
v___y_2848_ = v___x_2875_;
v_attrs_x3f_2849_ = v___x_2887_;
v___y_2850_ = v___y_2873_;
v___y_2851_ = v___y_2874_;
goto v___jp_2846_;
}
}
}
v___jp_2393_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkUnexpander), 5, 3);
lean_closure_set(v___x_2399_, 0, v___y_2396_);
lean_closure_set(v___x_2399_, 1, v___y_2395_);
lean_closure_set(v___x_2399_, 2, v___y_2394_);
lean_inc_ref(v___y_2397_);
v___x_2400_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2399_, v___y_2397_, v___y_2398_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2411_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2411_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2411_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
if (lean_obj_tag(v_a_2401_) == 1)
{
lean_object* v_val_2405_; lean_object* v___x_2406_; 
lean_del_object(v___x_2403_);
v_val_2405_ = lean_ctor_get(v_a_2401_, 0);
lean_inc(v_val_2405_);
lean_dec_ref(v_a_2401_);
v___x_2406_ = l_Lean_Elab_Command_elabCommand(v_val_2405_, v___y_2397_, v___y_2398_);
return v___x_2406_;
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
lean_dec(v_a_2401_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
v___x_2407_ = lean_box(0);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2407_);
v___x_2409_ = v___x_2403_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
v_a_2412_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2400_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2400_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
v___jp_2424_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2435_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__2));
v___x_2436_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__3));
lean_inc(v___y_2432_);
lean_inc(v___y_2430_);
v___x_2437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2437_, 0, v___y_2430_);
lean_ctor_set(v___x_2437_, 1, v___y_2432_);
lean_ctor_set(v___x_2437_, 2, v___y_2425_);
lean_inc(v___y_2430_);
v___x_2438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___y_2430_);
lean_ctor_set(v___x_2438_, 1, v___x_2435_);
v___x_2439_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__29));
lean_inc_ref(v___y_2434_);
v___x_2440_ = l_Lean_Name_mkStr4(v___x_2420_, v___x_2421_, v___y_2434_, v___x_2439_);
v___x_2441_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__31));
lean_inc_ref(v___y_2434_);
v___x_2442_ = l_Lean_Name_mkStr4(v___x_2420_, v___x_2421_, v___y_2434_, v___x_2441_);
v___x_2443_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
lean_inc(v___y_2430_);
v___x_2444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___y_2430_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
v___x_2445_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__34));
lean_inc_ref(v___y_2434_);
v___x_2446_ = l_Lean_Name_mkStr4(v___x_2420_, v___x_2421_, v___y_2434_, v___x_2445_);
v___x_2447_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
lean_inc(v___y_2430_);
v___x_2448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___y_2430_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
lean_inc(v___y_2430_);
v___x_2449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___y_2430_);
lean_ctor_set(v___x_2449_, 1, v___y_2427_);
lean_inc_ref(v___x_2449_);
lean_inc(v___y_2429_);
lean_inc_ref(v___x_2448_);
lean_inc(v___x_2446_);
lean_inc(v___y_2430_);
v___x_2450_ = l_Lean_Syntax_node3(v___y_2430_, v___x_2446_, v___x_2448_, v___y_2429_, v___x_2449_);
lean_inc(v___y_2432_);
lean_inc(v___y_2430_);
v___x_2451_ = l_Lean_Syntax_node1(v___y_2430_, v___y_2432_, v___x_2450_);
lean_inc(v___y_2432_);
lean_inc(v___y_2430_);
v___x_2452_ = l_Lean_Syntax_node1(v___y_2430_, v___y_2432_, v___x_2451_);
v___x_2453_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
lean_inc(v___y_2430_);
v___x_2454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___y_2430_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__4));
v___x_2456_ = l_Lean_Name_mkStr4(v___x_2420_, v___x_2421_, v___y_2434_, v___x_2455_);
v___x_2457_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__5));
lean_inc(v___y_2430_);
v___x_2458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___y_2430_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
lean_inc(v___y_2428_);
lean_inc(v___y_2430_);
v___x_2459_ = l_Lean_Syntax_node3(v___y_2430_, v___x_2446_, v___x_2448_, v___y_2428_, v___x_2449_);
lean_inc(v___y_2430_);
v___x_2460_ = l_Lean_Syntax_node2(v___y_2430_, v___x_2456_, v___x_2458_, v___x_2459_);
lean_inc(v___y_2430_);
v___x_2461_ = l_Lean_Syntax_node4(v___y_2430_, v___x_2442_, v___x_2444_, v___x_2452_, v___x_2454_, v___x_2460_);
lean_inc(v___y_2430_);
v___x_2462_ = l_Lean_Syntax_node1(v___y_2430_, v___y_2432_, v___x_2461_);
lean_inc(v___y_2430_);
v___x_2463_ = l_Lean_Syntax_node1(v___y_2430_, v___x_2440_, v___x_2462_);
lean_inc(v___y_2433_);
lean_inc_ref_n(v___x_2437_, 2);
v___x_2464_ = l_Lean_Syntax_node6(v___y_2430_, v___x_2436_, v___x_2437_, v___x_2437_, v___y_2433_, v___x_2438_, v___x_2437_, v___x_2463_);
lean_inc(v___y_2433_);
v___x_2465_ = l_Lean_Elab_Command_isLocalAttrKind(v___y_2433_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; 
lean_inc(v___y_2426_);
lean_inc_ref(v___y_2431_);
v___x_2466_ = l_Lean_Elab_Command_elabCommand(v___x_2464_, v___y_2431_, v___y_2426_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_dec_ref(v___x_2466_);
v___y_2394_ = v___y_2428_;
v___y_2395_ = v___y_2429_;
v___y_2396_ = v___y_2433_;
v___y_2397_ = v___y_2431_;
v___y_2398_ = v___y_2426_;
goto v___jp_2393_;
}
else
{
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec(v___y_2426_);
return v___x_2466_;
}
}
else
{
lean_object* v___x_2467_; lean_object* v_scopes_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v_opts_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___f_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2467_ = lean_st_ref_get(v___y_2426_);
v_scopes_2468_ = lean_ctor_get(v___x_2467_, 2);
lean_inc(v_scopes_2468_);
lean_dec(v___x_2467_);
v___x_2469_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2470_ = l_List_head_x21___redArg(v___x_2469_, v_scopes_2468_);
lean_dec(v_scopes_2468_);
v_opts_2471_ = lean_ctor_get(v___x_2470_, 1);
lean_inc_ref(v_opts_2471_);
lean_dec(v___x_2470_);
v___x_2472_ = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
v___x_2473_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_2471_, v___x_2472_, v___x_2423_);
v___f_2474_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___lam__0), 2, 1);
lean_closure_set(v___f_2474_, 0, v___x_2473_);
v___x_2475_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_2475_, 0, v___x_2464_);
lean_inc(v___y_2426_);
lean_inc_ref(v___y_2431_);
v___x_2476_ = l_Lean_Elab_Command_withScope___redArg(v___f_2474_, v___x_2475_, v___y_2431_, v___y_2426_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_dec_ref(v___x_2476_);
v___y_2394_ = v___y_2428_;
v___y_2395_ = v___y_2429_;
v___y_2396_ = v___y_2433_;
v___y_2397_ = v___y_2431_;
v___y_2398_ = v___y_2426_;
goto v___jp_2393_;
}
else
{
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec(v___y_2426_);
return v___x_2476_;
}
}
}
v___jp_2477_:
{
size_t v_sz_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v_sz_2492_ = lean_array_size(v___y_2487_);
v___x_2493_ = lean_box_usize(v_sz_2492_);
v___x_2494_ = lean_box_usize(v___y_2490_);
v___x_2495_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed), 5, 3);
lean_closure_set(v___x_2495_, 0, v___x_2493_);
lean_closure_set(v___x_2495_, 1, v___x_2494_);
lean_closure_set(v___x_2495_, 2, v___y_2487_);
lean_inc_ref(v___y_2480_);
v___x_2496_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2495_, v___y_2480_, v___y_2478_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; lean_object* v___x_2498_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref(v___x_2496_);
v___x_2498_ = l_Lean_Elab_Command_getRef___redArg(v___y_2480_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2500_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref(v___x_2498_);
v___x_2500_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2480_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_quotContext_x3f_2501_; size_t v_sz_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec_ref(v___x_2500_);
v_quotContext_x3f_2501_ = lean_ctor_get(v___y_2480_, 5);
v_sz_2502_ = lean_array_size(v___y_2491_);
v___x_2503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_2502_, v___y_2490_, v___y_2491_);
v___x_2504_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(v___x_2503_, v___y_2485_);
lean_dec_ref(v___x_2503_);
v___x_2505_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2505_, 0, v___y_2483_);
lean_ctor_set(v___x_2505_, 1, v___y_2486_);
lean_ctor_set(v___x_2505_, 2, v_a_2497_);
v___x_2506_ = l_Lean_SourceInfo_fromRef(v_a_2499_, v___y_2489_);
lean_dec(v_a_2499_);
if (lean_obj_tag(v_quotContext_x3f_2501_) == 0)
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2478_);
lean_dec_ref(v___x_2507_);
v___y_2425_ = v___y_2484_;
v___y_2426_ = v___y_2478_;
v___y_2427_ = v___y_2479_;
v___y_2428_ = v___x_2504_;
v___y_2429_ = v___x_2505_;
v___y_2430_ = v___x_2506_;
v___y_2431_ = v___y_2480_;
v___y_2432_ = v___y_2481_;
v___y_2433_ = v___y_2488_;
v___y_2434_ = v___y_2482_;
goto v___jp_2424_;
}
else
{
v___y_2425_ = v___y_2484_;
v___y_2426_ = v___y_2478_;
v___y_2427_ = v___y_2479_;
v___y_2428_ = v___x_2504_;
v___y_2429_ = v___x_2505_;
v___y_2430_ = v___x_2506_;
v___y_2431_ = v___y_2480_;
v___y_2432_ = v___y_2481_;
v___y_2433_ = v___y_2488_;
v___y_2434_ = v___y_2482_;
goto v___jp_2424_;
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_a_2499_);
lean_dec(v_a_2497_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2488_);
lean_dec(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
v_a_2508_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2500_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2500_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v_a_2497_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2488_);
lean_dec(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
v_a_2516_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2498_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2498_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2488_);
lean_dec(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
v_a_2524_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2496_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2496_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___boxed(lean_object* v_x_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_Elab_Command_elabNotation(v_x_2899_, v_a_2900_, v_a_2901_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(lean_object* v_cls_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(v_cls_2904_, v___y_2906_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___boxed(lean_object* v_cls_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(lean_object* v_00_u03b1_2914_, lean_object* v_x_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(v_x_2915_, v___y_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2919_, lean_object* v_x_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_00_u03b1_2919_, v_x_2920_, v___y_2921_, v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec_ref(v_x_2920_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8(lean_object* v_00_u03b1_2924_, lean_object* v_ref_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg(v_ref_2925_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___boxed(lean_object* v_00_u03b1_2930_, lean_object* v_ref_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8(v_00_u03b1_2930_, v_ref_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(lean_object* v_00_u03b1_2936_, lean_object* v_x_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2937_, v___y_2938_, v___y_2939_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___boxed(lean_object* v_00_u03b1_2942_, lean_object* v_x_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(v_00_u03b1_2942_, v_x_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4(lean_object* v_msgData_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(v_msgData_2948_, v___y_2950_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4(v_msgData_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(lean_object* v_as_2958_, lean_object* v_as_x27_2959_, lean_object* v_b_2960_, lean_object* v_a_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg(v_as_x27_2959_, v_b_2960_, v___y_2962_, v___y_2963_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___boxed(lean_object* v_as_2966_, lean_object* v_as_x27_2967_, lean_object* v_b_2968_, lean_object* v_a_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v_as_2966_, v_as_x27_2967_, v_b_2968_, v_a_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v_as_2966_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(lean_object* v_00_u03b1_2974_, lean_object* v_ref_2975_, lean_object* v_msg_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_2975_, v_msg_2976_, v___y_2977_, v___y_2978_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___boxed(lean_object* v_00_u03b1_2981_, lean_object* v_ref_2982_, lean_object* v_msg_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(v_00_u03b1_2981_, v_ref_2982_, v_msg_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec(v_ref_2982_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_2988_, lean_object* v_m_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg(v_m_2989_, v_a_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___boxed(lean_object* v_00_u03b2_2992_, lean_object* v_m_2993_, lean_object* v_a_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9(v_00_u03b2_2992_, v_m_2993_, v_a_2994_);
lean_dec(v_a_2994_);
lean_dec_ref(v_m_2993_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13(lean_object* v_00_u03b1_2996_, lean_object* v_msg_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(v_msg_2997_, v___y_2998_, v___y_2999_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___boxed(lean_object* v_00_u03b1_3002_, lean_object* v_msg_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13(v_00_u03b1_3002_, v_msg_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
return v_res_3007_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16(lean_object* v_00_u03b2_3008_, lean_object* v_x_3009_, lean_object* v_x_3010_){
_start:
{
uint8_t v___x_3011_; 
v___x_3011_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg(v_x_3009_, v_x_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___boxed(lean_object* v_00_u03b2_3012_, lean_object* v_x_3013_, lean_object* v_x_3014_){
_start:
{
uint8_t v_res_3015_; lean_object* v_r_3016_; 
v_res_3015_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16(v_00_u03b2_3012_, v_x_3013_, v_x_3014_);
lean_dec_ref(v_x_3014_);
v_r_3016_ = lean_box(v_res_3015_);
return v_r_3016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19(lean_object* v_00_u03b2_3017_, lean_object* v_a_3018_, lean_object* v_x_3019_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg(v_a_3018_, v_x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___boxed(lean_object* v_00_u03b2_3021_, lean_object* v_a_3022_, lean_object* v_x_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19(v_00_u03b2_3021_, v_a_3022_, v_x_3023_);
lean_dec(v_x_3023_);
lean_dec(v_a_3022_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24(lean_object* v_msgData_3025_, lean_object* v_macroStack_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg(v_msgData_3025_, v_macroStack_3026_, v___y_3028_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___boxed(lean_object* v_msgData_3031_, lean_object* v_macroStack_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24(v_msgData_3031_, v_macroStack_3032_, v___y_3033_, v___y_3034_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
return v_res_3036_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20(lean_object* v_00_u03b2_3037_, lean_object* v_x_3038_, size_t v_x_3039_, lean_object* v_x_3040_){
_start:
{
uint8_t v___x_3041_; 
v___x_3041_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg(v_x_3038_, v_x_3039_, v_x_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___boxed(lean_object* v_00_u03b2_3042_, lean_object* v_x_3043_, lean_object* v_x_3044_, lean_object* v_x_3045_){
_start:
{
size_t v_x_25540__boxed_3046_; uint8_t v_res_3047_; lean_object* v_r_3048_; 
v_x_25540__boxed_3046_ = lean_unbox_usize(v_x_3044_);
lean_dec(v_x_3044_);
v_res_3047_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20(v_00_u03b2_3042_, v_x_3043_, v_x_25540__boxed_3046_, v_x_3045_);
lean_dec_ref(v_x_3045_);
v_r_3048_ = lean_box(v_res_3047_);
return v_r_3048_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24(lean_object* v_00_u03b2_3049_, lean_object* v_keys_3050_, lean_object* v_vals_3051_, lean_object* v_heq_3052_, lean_object* v_i_3053_, lean_object* v_k_3054_){
_start:
{
uint8_t v___x_3055_; 
v___x_3055_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg(v_keys_3050_, v_i_3053_, v_k_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___boxed(lean_object* v_00_u03b2_3056_, lean_object* v_keys_3057_, lean_object* v_vals_3058_, lean_object* v_heq_3059_, lean_object* v_i_3060_, lean_object* v_k_3061_){
_start:
{
uint8_t v_res_3062_; lean_object* v_r_3063_; 
v_res_3062_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24(v_00_u03b2_3056_, v_keys_3057_, v_vals_3058_, v_heq_3059_, v_i_3060_, v_k_3061_);
lean_dec_ref(v_k_3061_);
lean_dec_ref(v_vals_3058_);
lean_dec_ref(v_keys_3057_);
v_r_3063_ = lean_box(v_res_3062_);
return v_r_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1(){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3071_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3072_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
v___x_3073_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1));
v___x_3074_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___boxed), 4, 0);
v___x_3075_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3071_, v___x_3072_, v___x_3073_, v___x_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___boxed(lean_object* v_a_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
return v_res_3077_;
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
res = l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
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
