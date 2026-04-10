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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* lean_erase_macro_scopes(lean_object*);
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
lean_object* lean_mk_syntax_ident(lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__1;
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
uint8_t v___x_10650__boxed_155_; size_t v_sz_boxed_156_; size_t v_i_boxed_157_; lean_object* v_res_158_; 
v___x_10650__boxed_155_ = lean_unbox(v___x_150_);
v_sz_boxed_156_ = lean_unbox_usize(v_sz_152_);
lean_dec(v_sz_152_);
v_i_boxed_157_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_res_158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(v___x_10650__boxed_155_, v___x_151_, v_sz_boxed_156_, v_i_boxed_157_, v_bs_154_);
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
lean_inc_ref(v___y_308_);
v___x_313_ = l_Array_append___redArg(v___y_308_, v___y_312_);
lean_dec_ref(v___y_312_);
lean_inc(v___y_309_);
lean_inc(v___y_310_);
v___x_314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_314_, 0, v___y_310_);
lean_ctor_set(v___x_314_, 1, v___y_309_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
lean_inc(v___y_311_);
v___x_315_ = l_Lean_Syntax_node2(v___y_310_, v___y_311_, v___y_307_, v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___y_306_);
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
lean_dec_ref(v_prec_x3f_318_);
v___x_335_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
v___x_336_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc_n(v___x_325_, 2);
v___x_337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_325_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = l_Lean_Syntax_node2(v___x_325_, v___x_335_, v___x_337_, v_val_334_);
v___x_339_ = l_Array_mkArray1___redArg(v___x_338_);
v___y_306_ = v___y_320_;
v___y_307_ = v___x_331_;
v___y_308_ = v___x_333_;
v___y_309_ = v___x_332_;
v___y_310_ = v___x_325_;
v___y_311_ = v___x_326_;
v___y_312_ = v___x_339_;
goto v___jp_305_;
}
else
{
lean_object* v___x_340_; 
lean_dec(v_prec_x3f_318_);
v___x_340_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_306_ = v___y_320_;
v___y_307_ = v___x_331_;
v___y_308_ = v___x_333_;
v___y_309_ = v___x_332_;
v___y_310_ = v___x_325_;
v___y_311_ = v___x_326_;
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
lean_dec_ref(v___x_422_);
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
lean_dec_ref(v___x_424_);
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
lean_dec_ref(v___x_583_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v_a_586_; lean_object* v___y_588_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
v_a_586_ = lean_ctor_get(v___x_584_, 1);
lean_inc(v_a_586_);
lean_dec_ref(v___x_584_);
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
lean_dec_ref(v_a_585_);
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
lean_dec_ref(v___x_618_);
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
lean_ctor_set(v___x_659_, 1, v___y_656_);
v_sz_660_ = lean_array_size(v___y_657_);
v___x_661_ = ((size_t)0ULL);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v___x_651_, v_firstChoiceOnly_652_, v___y_657_, v_sz_660_, v___x_661_, v___x_659_);
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
lean_dec_ref(v_fst_663_);
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
v___y_656_ = v_a_669_;
v___y_657_ = v_args_670_;
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
v___y_656_ = v_a_669_;
v___y_657_ = v_args_672_;
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
lean_dec_ref(v___x_717_);
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
lean_dec_ref(v_fst_808_);
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
lean_dec_ref(v___x_977_);
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
v___x_1035_ = lean_mk_syntax_ident(v_fst_986_);
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
lean_dec_ref(v___x_977_);
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
lean_dec_ref(v_a_978_);
lean_dec_ref(v_snd_973_);
lean_dec(v_pat_963_);
lean_dec(v_attrKind_962_);
v_a_1157_ = lean_ctor_get(v___x_977_, 1);
lean_inc(v_a_1157_);
lean_dec_ref(v___x_977_);
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
lean_dec_ref(v___x_977_);
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(lean_object* v_o_1268_, lean_object* v_k_1269_, uint8_t v_v_1270_){
_start:
{
lean_object* v_map_1271_; uint8_t v_hasTrace_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1286_; 
v_map_1271_ = lean_ctor_get(v_o_1268_, 0);
v_hasTrace_1272_ = lean_ctor_get_uint8(v_o_1268_, sizeof(void*)*1);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_o_1268_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1274_ = v_o_1268_;
v_isShared_1275_ = v_isSharedCheck_1286_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_map_1271_);
lean_dec(v_o_1268_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1286_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1276_, 0, v_v_1270_);
lean_inc(v_k_1269_);
v___x_1277_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1269_, v___x_1276_, v_map_1271_);
if (v_hasTrace_1272_ == 0)
{
lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1281_; 
v___x_1278_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
v___x_1279_ = l_Lean_Name_isPrefixOf(v___x_1278_, v_k_1269_);
lean_dec(v_k_1269_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1277_);
v___x_1281_ = v___x_1274_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1277_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*1, v___x_1279_);
return v___x_1281_;
}
}
else
{
lean_object* v___x_1284_; 
lean_dec(v_k_1269_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1277_);
v___x_1284_ = v___x_1274_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1277_);
lean_ctor_set_uint8(v_reuseFailAlloc_1285_, sizeof(void*)*1, v_hasTrace_1272_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___boxed(lean_object* v_o_1287_, lean_object* v_k_1288_, lean_object* v_v_1289_){
_start:
{
uint8_t v_v_boxed_1290_; lean_object* v_res_1291_; 
v_v_boxed_1290_ = lean_unbox(v_v_1289_);
v_res_1291_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(v_o_1287_, v_k_1288_, v_v_boxed_1290_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(lean_object* v_opts_1292_, lean_object* v_opt_1293_, uint8_t v_val_1294_){
_start:
{
lean_object* v_name_1295_; lean_object* v___x_1296_; 
v_name_1295_ = lean_ctor_get(v_opt_1293_, 0);
lean_inc(v_name_1295_);
lean_dec_ref(v_opt_1293_);
v___x_1296_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(v_opts_1292_, v_name_1295_, v_val_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6___boxed(lean_object* v_opts_1297_, lean_object* v_opt_1298_, lean_object* v_val_1299_){
_start:
{
uint8_t v_val_boxed_1300_; lean_object* v_res_1301_; 
v_val_boxed_1300_ = lean_unbox(v_val_1299_);
v_res_1301_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_1297_, v_opt_1298_, v_val_boxed_1300_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(size_t v_sz_1302_, size_t v_i_1303_, lean_object* v_bs_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
uint8_t v___x_1307_; 
v___x_1307_ = lean_usize_dec_lt(v_i_1303_, v_sz_1302_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v_bs_1304_);
lean_ctor_set(v___x_1308_, 1, v___y_1306_);
return v___x_1308_;
}
else
{
lean_object* v_v_1309_; lean_object* v___x_1310_; 
v_v_1309_ = lean_array_uget_borrowed(v_bs_1304_, v_i_1303_);
lean_inc(v_v_1309_);
v___x_1310_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(v_v_1309_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v_a_1312_; lean_object* v___x_1313_; lean_object* v_bs_x27_1314_; size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
v_a_1312_ = lean_ctor_get(v___x_1310_, 1);
lean_inc(v_a_1312_);
lean_dec_ref(v___x_1310_);
v___x_1313_ = lean_unsigned_to_nat(0u);
v_bs_x27_1314_ = lean_array_uset(v_bs_1304_, v_i_1303_, v___x_1313_);
v___x_1315_ = ((size_t)1ULL);
v___x_1316_ = lean_usize_add(v_i_1303_, v___x_1315_);
v___x_1317_ = lean_array_uset(v_bs_x27_1314_, v_i_1303_, v_a_1311_);
v_i_1303_ = v___x_1316_;
v_bs_1304_ = v___x_1317_;
v___y_1306_ = v_a_1312_;
goto _start;
}
else
{
lean_object* v_a_1319_; lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v_bs_1304_);
v_a_1319_ = lean_ctor_get(v___x_1310_, 0);
v_a_1320_ = lean_ctor_get(v___x_1310_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1310_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_inc(v_a_1319_);
lean_dec(v___x_1310_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1319_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed(lean_object* v_sz_1328_, lean_object* v_i_1329_, lean_object* v_bs_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
size_t v_sz_boxed_1333_; size_t v_i_boxed_1334_; lean_object* v_res_1335_; 
v_sz_boxed_1333_ = lean_unbox_usize(v_sz_1328_);
lean_dec(v_sz_1328_);
v_i_boxed_1334_ = lean_unbox_usize(v_i_1329_);
lean_dec(v_i_1329_);
v_res_1335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(v_sz_boxed_1333_, v_i_boxed_1334_, v_bs_1330_, v___y_1331_, v___y_1332_);
lean_dec_ref(v___y_1331_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(size_t v_sz_1336_, size_t v_i_1337_, lean_object* v_bs_1338_){
_start:
{
uint8_t v___x_1339_; 
v___x_1339_ = lean_usize_dec_lt(v_i_1337_, v_sz_1336_);
if (v___x_1339_ == 0)
{
return v_bs_1338_;
}
else
{
lean_object* v___x_1340_; lean_object* v_v_1341_; lean_object* v_bs_x27_1342_; lean_object* v___x_1343_; size_t v___x_1344_; size_t v___x_1345_; lean_object* v___x_1346_; 
v___x_1340_ = lean_unsigned_to_nat(0u);
v_v_1341_ = lean_array_uget(v_bs_1338_, v_i_1337_);
v_bs_x27_1342_ = lean_array_uset(v_bs_1338_, v_i_1337_, v___x_1340_);
v___x_1343_ = l_Lean_Syntax_getArg(v_v_1341_, v___x_1340_);
lean_dec(v_v_1341_);
v___x_1344_ = ((size_t)1ULL);
v___x_1345_ = lean_usize_add(v_i_1337_, v___x_1344_);
v___x_1346_ = lean_array_uset(v_bs_x27_1342_, v_i_1337_, v___x_1343_);
v_i_1337_ = v___x_1345_;
v_bs_1338_ = v___x_1346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed(lean_object* v_sz_1348_, lean_object* v_i_1349_, lean_object* v_bs_1350_){
_start:
{
size_t v_sz_boxed_1351_; size_t v_i_boxed_1352_; lean_object* v_res_1353_; 
v_sz_boxed_1351_ = lean_unbox_usize(v_sz_1348_);
lean_dec(v_sz_1348_);
v_i_boxed_1352_ = lean_unbox_usize(v_i_1349_);
lean_dec(v_i_1349_);
v_res_1353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_boxed_1351_, v_i_boxed_1352_, v_bs_1350_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(size_t v_sz_1354_, size_t v_i_1355_, lean_object* v_bs_1356_, lean_object* v___y_1357_){
_start:
{
uint8_t v___x_1358_; 
v___x_1358_ = lean_usize_dec_lt(v_i_1355_, v_sz_1354_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_bs_1356_);
lean_ctor_set(v___x_1359_, 1, v___y_1357_);
return v___x_1359_;
}
else
{
lean_object* v_v_1360_; lean_object* v___x_1361_; 
v_v_1360_ = lean_array_uget_borrowed(v_bs_1356_, v_i_1355_);
lean_inc(v_v_1360_);
v___x_1361_ = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(v_v_1360_, v___y_1357_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v_a_1363_; lean_object* v___x_1364_; lean_object* v_bs_x27_1365_; size_t v___x_1366_; size_t v___x_1367_; lean_object* v___x_1368_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
v_a_1363_ = lean_ctor_get(v___x_1361_, 1);
lean_inc(v_a_1363_);
lean_dec_ref(v___x_1361_);
v___x_1364_ = lean_unsigned_to_nat(0u);
v_bs_x27_1365_ = lean_array_uset(v_bs_1356_, v_i_1355_, v___x_1364_);
v___x_1366_ = ((size_t)1ULL);
v___x_1367_ = lean_usize_add(v_i_1355_, v___x_1366_);
v___x_1368_ = lean_array_uset(v_bs_x27_1365_, v_i_1355_, v_a_1362_);
v_i_1355_ = v___x_1367_;
v_bs_1356_ = v___x_1368_;
v___y_1357_ = v_a_1363_;
goto _start;
}
else
{
lean_object* v_a_1370_; lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v_bs_1356_);
v_a_1370_ = lean_ctor_get(v___x_1361_, 0);
v_a_1371_ = lean_ctor_get(v___x_1361_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1361_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_inc(v_a_1370_);
lean_dec(v___x_1361_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1370_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg___boxed(lean_object* v_sz_1379_, lean_object* v_i_1380_, lean_object* v_bs_1381_, lean_object* v___y_1382_){
_start:
{
size_t v_sz_boxed_1383_; size_t v_i_boxed_1384_; lean_object* v_res_1385_; 
v_sz_boxed_1383_ = lean_unbox_usize(v_sz_1379_);
lean_dec(v_sz_1379_);
v_i_boxed_1384_ = lean_unbox_usize(v_i_1380_);
lean_dec(v_i_1380_);
v_res_1385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(v_sz_boxed_1383_, v_i_boxed_1384_, v_bs_1381_, v___y_1382_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(size_t v_sz_1386_, size_t v_i_1387_, lean_object* v_bs_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(v_sz_1386_, v_i_1387_, v_bs_1388_, v___y_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed(lean_object* v_sz_1392_, lean_object* v_i_1393_, lean_object* v_bs_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
size_t v_sz_boxed_1397_; size_t v_i_boxed_1398_; lean_object* v_res_1399_; 
v_sz_boxed_1397_ = lean_unbox_usize(v_sz_1392_);
lean_dec(v_sz_1392_);
v_i_boxed_1398_ = lean_unbox_usize(v_i_1393_);
lean_dec(v_i_1393_);
v_res_1399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(v_sz_boxed_1397_, v_i_boxed_1398_, v_bs_1394_, v___y_1395_, v___y_1396_);
lean_dec_ref(v___y_1395_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(lean_object* v_env_1400_, lean_object* v_currNamespace_1401_, lean_object* v_openDecls_1402_, lean_object* v_n_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = l_Lean_ResolveName_resolveNamespace(v_env_1400_, v_currNamespace_1401_, v_openDecls_1402_, v_n_1403_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v___y_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed(lean_object* v_env_1408_, lean_object* v_currNamespace_1409_, lean_object* v_openDecls_1410_, lean_object* v_n_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(v_env_1408_, v_currNamespace_1409_, v_openDecls_1410_, v_n_1411_, v___y_1412_, v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1414_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1415_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_1419_ = lean_unsigned_to_nat(0u);
v___x_1420_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
lean_ctor_set(v___x_1420_, 2, v___x_1419_);
lean_ctor_set(v___x_1420_, 3, v___x_1419_);
lean_ctor_set(v___x_1420_, 4, v___x_1418_);
lean_ctor_set(v___x_1420_, 5, v___x_1418_);
lean_ctor_set(v___x_1420_, 6, v___x_1418_);
lean_ctor_set(v___x_1420_, 7, v___x_1418_);
lean_ctor_set(v___x_1420_, 8, v___x_1418_);
lean_ctor_set(v___x_1420_, 9, v___x_1418_);
return v___x_1420_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = lean_unsigned_to_nat(32u);
v___x_1422_ = lean_mk_empty_array_with_capacity(v___x_1421_);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4(void){
_start:
{
size_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1424_ = ((size_t)5ULL);
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = lean_unsigned_to_nat(32u);
v___x_1427_ = lean_mk_empty_array_with_capacity(v___x_1426_);
v___x_1428_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3);
v___x_1429_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
lean_ctor_set(v___x_1429_, 1, v___x_1427_);
lean_ctor_set(v___x_1429_, 2, v___x_1425_);
lean_ctor_set(v___x_1429_, 3, v___x_1425_);
lean_ctor_set_usize(v___x_1429_, 4, v___x_1424_);
return v___x_1429_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1430_ = lean_box(1);
v___x_1431_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4);
v___x_1432_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_1433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v___x_1431_);
lean_ctor_set(v___x_1433_, 2, v___x_1430_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v_env_1438_; lean_object* v___x_1439_; lean_object* v_scopes_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v_opts_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1437_ = lean_st_ref_get(v___y_1435_);
v_env_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc_ref(v_env_1438_);
lean_dec(v___x_1437_);
v___x_1439_ = lean_st_ref_get(v___y_1435_);
v_scopes_1440_ = lean_ctor_get(v___x_1439_, 2);
lean_inc(v_scopes_1440_);
lean_dec(v___x_1439_);
v___x_1441_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1442_ = l_List_head_x21___redArg(v___x_1441_, v_scopes_1440_);
lean_dec(v_scopes_1440_);
v_opts_1443_ = lean_ctor_get(v___x_1442_, 1);
lean_inc_ref(v_opts_1443_);
lean_dec(v___x_1442_);
v___x_1444_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_1445_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5);
v___x_1446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1446_, 0, v_env_1438_);
lean_ctor_set(v___x_1446_, 1, v___x_1444_);
lean_ctor_set(v___x_1446_, 2, v___x_1445_);
lean_ctor_set(v___x_1446_, 3, v_opts_1443_);
v___x_1447_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
lean_ctor_set(v___x_1447_, 1, v_msgData_1434_);
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msgData_1449_, v___y_1450_);
lean_dec(v___y_1450_);
return v_res_1452_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1453_; double v___x_1454_; 
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_float_of_nat(v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(lean_object* v_cls_1457_, lean_object* v_msg_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_Elab_Command_getRef___redArg(v___y_1459_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1511_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref(v___x_1462_);
v___x_1464_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msg_1458_, v___y_1460_);
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1511_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1511_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v_traceState_1470_; lean_object* v_env_1471_; lean_object* v_messages_1472_; lean_object* v_scopes_1473_; lean_object* v_usedQuotCtxts_1474_; lean_object* v_nextMacroScope_1475_; lean_object* v_maxRecDepth_1476_; lean_object* v_ngen_1477_; lean_object* v_auxDeclNGen_1478_; lean_object* v_infoState_1479_; lean_object* v_snapshotTasks_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1510_; 
v___x_1469_ = lean_st_ref_take(v___y_1460_);
v_traceState_1470_ = lean_ctor_get(v___x_1469_, 9);
v_env_1471_ = lean_ctor_get(v___x_1469_, 0);
v_messages_1472_ = lean_ctor_get(v___x_1469_, 1);
v_scopes_1473_ = lean_ctor_get(v___x_1469_, 2);
v_usedQuotCtxts_1474_ = lean_ctor_get(v___x_1469_, 3);
v_nextMacroScope_1475_ = lean_ctor_get(v___x_1469_, 4);
v_maxRecDepth_1476_ = lean_ctor_get(v___x_1469_, 5);
v_ngen_1477_ = lean_ctor_get(v___x_1469_, 6);
v_auxDeclNGen_1478_ = lean_ctor_get(v___x_1469_, 7);
v_infoState_1479_ = lean_ctor_get(v___x_1469_, 8);
v_snapshotTasks_1480_ = lean_ctor_get(v___x_1469_, 10);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1482_ = v___x_1469_;
v_isShared_1483_ = v_isSharedCheck_1510_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_snapshotTasks_1480_);
lean_inc(v_traceState_1470_);
lean_inc(v_infoState_1479_);
lean_inc(v_auxDeclNGen_1478_);
lean_inc(v_ngen_1477_);
lean_inc(v_maxRecDepth_1476_);
lean_inc(v_nextMacroScope_1475_);
lean_inc(v_usedQuotCtxts_1474_);
lean_inc(v_scopes_1473_);
lean_inc(v_messages_1472_);
lean_inc(v_env_1471_);
lean_dec(v___x_1469_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1510_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
uint64_t v_tid_1484_; lean_object* v_traces_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1509_; 
v_tid_1484_ = lean_ctor_get_uint64(v_traceState_1470_, sizeof(void*)*1);
v_traces_1485_ = lean_ctor_get(v_traceState_1470_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_traceState_1470_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1487_ = v_traceState_1470_;
v_isShared_1488_ = v_isSharedCheck_1509_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_traces_1485_);
lean_dec(v_traceState_1470_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1509_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; double v___x_1490_; uint8_t v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1489_ = lean_box(0);
v___x_1490_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0);
v___x_1491_ = 0;
v___x_1492_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1493_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1493_, 0, v_cls_1457_);
lean_ctor_set(v___x_1493_, 1, v___x_1489_);
lean_ctor_set(v___x_1493_, 2, v___x_1492_);
lean_ctor_set_float(v___x_1493_, sizeof(void*)*3, v___x_1490_);
lean_ctor_set_float(v___x_1493_, sizeof(void*)*3 + 8, v___x_1490_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*3 + 16, v___x_1491_);
v___x_1494_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__1));
v___x_1495_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1493_);
lean_ctor_set(v___x_1495_, 1, v_a_1465_);
lean_ctor_set(v___x_1495_, 2, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v_a_1463_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = l_Lean_PersistentArray_push___redArg(v_traces_1485_, v___x_1496_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1497_);
v___x_1499_ = v___x_1487_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1497_);
lean_ctor_set_uint64(v_reuseFailAlloc_1508_, sizeof(void*)*1, v_tid_1484_);
v___x_1499_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 9, v___x_1499_);
v___x_1501_ = v___x_1482_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_env_1471_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_messages_1472_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_scopes_1473_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v_usedQuotCtxts_1474_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v_nextMacroScope_1475_);
lean_ctor_set(v_reuseFailAlloc_1507_, 5, v_maxRecDepth_1476_);
lean_ctor_set(v_reuseFailAlloc_1507_, 6, v_ngen_1477_);
lean_ctor_set(v_reuseFailAlloc_1507_, 7, v_auxDeclNGen_1478_);
lean_ctor_set(v_reuseFailAlloc_1507_, 8, v_infoState_1479_);
lean_ctor_set(v_reuseFailAlloc_1507_, 9, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1507_, 10, v_snapshotTasks_1480_);
v___x_1501_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1502_ = lean_st_ref_set(v___y_1460_, v___x_1501_);
v___x_1503_ = lean_box(0);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1503_);
v___x_1505_ = v___x_1467_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec_ref(v_msg_1458_);
lean_dec(v_cls_1457_);
v_a_1512_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1462_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1462_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___boxed(lean_object* v_cls_1520_, lean_object* v_msg_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_1520_, v_msg_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(lean_object* v_as_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
if (lean_obj_tag(v_as_1526_) == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
return v___x_1531_;
}
else
{
lean_object* v_head_1532_; lean_object* v_tail_1533_; lean_object* v_fst_1534_; lean_object* v_snd_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v_scopes_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v_opts_1542_; uint8_t v_hasTrace_1543_; 
v_head_1532_ = lean_ctor_get(v_as_1526_, 0);
lean_inc(v_head_1532_);
v_tail_1533_ = lean_ctor_get(v_as_1526_, 1);
lean_inc(v_tail_1533_);
lean_dec_ref(v_as_1526_);
v_fst_1534_ = lean_ctor_get(v_head_1532_, 0);
lean_inc(v_fst_1534_);
v_snd_1535_ = lean_ctor_get(v_head_1532_, 1);
lean_inc(v_snd_1535_);
lean_dec(v_head_1532_);
v___x_1536_ = l_Lean_inheritedTraceOptions;
v___x_1537_ = lean_st_ref_get(v___x_1536_);
v___x_1538_ = lean_st_ref_get(v___y_1528_);
v_scopes_1539_ = lean_ctor_get(v___x_1538_, 2);
lean_inc(v_scopes_1539_);
lean_dec(v___x_1538_);
v___x_1540_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1541_ = l_List_head_x21___redArg(v___x_1540_, v_scopes_1539_);
lean_dec(v_scopes_1539_);
v_opts_1542_ = lean_ctor_get(v___x_1541_, 1);
lean_inc_ref(v_opts_1542_);
lean_dec(v___x_1541_);
v_hasTrace_1543_ = lean_ctor_get_uint8(v_opts_1542_, sizeof(void*)*1);
if (v_hasTrace_1543_ == 0)
{
lean_dec_ref(v_opts_1542_);
lean_dec(v___x_1537_);
lean_dec(v_snd_1535_);
lean_dec(v_fst_1534_);
v_as_1526_ = v_tail_1533_;
goto _start;
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1545_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
lean_inc(v_fst_1534_);
v___x_1546_ = l_Lean_Name_append(v___x_1545_, v_fst_1534_);
v___x_1547_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1537_, v_opts_1542_, v___x_1546_);
lean_dec(v___x_1546_);
lean_dec_ref(v_opts_1542_);
lean_dec(v___x_1537_);
if (v___x_1547_ == 0)
{
lean_dec(v_snd_1535_);
lean_dec(v_fst_1534_);
v_as_1526_ = v_tail_1533_;
goto _start;
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1549_, 0, v_snd_1535_);
v___x_1550_ = l_Lean_MessageData_ofFormat(v___x_1549_);
v___x_1551_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_fst_1534_, v___x_1550_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_dec_ref(v___x_1551_);
v_as_1526_ = v_tail_1533_;
goto _start;
}
else
{
lean_dec(v_tail_1533_);
return v___x_1551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___boxed(lean_object* v_as_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v_as_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(lean_object* v_currNamespace_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v_currNamespace_1558_);
lean_ctor_set(v___x_1561_, 1, v___y_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(v_currNamespace_1562_, v___y_1563_, v___y_1564_);
lean_dec_ref(v___y_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(lean_object* v_env_1566_, lean_object* v_opts_1567_, lean_object* v_currNamespace_1568_, lean_object* v_openDecls_1569_, lean_object* v_n_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = l_Lean_ResolveName_resolveGlobalName(v_env_1566_, v_opts_1567_, v_currNamespace_1568_, v_openDecls_1569_, v_n_1570_);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v___y_1572_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed(lean_object* v_env_1575_, lean_object* v_opts_1576_, lean_object* v_currNamespace_1577_, lean_object* v_openDecls_1578_, lean_object* v_n_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(v_env_1575_, v_opts_1576_, v_currNamespace_1577_, v_openDecls_1578_, v_n_1579_, v___y_1580_, v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec_ref(v_opts_1576_);
return v_res_1582_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_box(1);
v___x_1584_ = l_Lean_MessageData_ofFormat(v___x_1583_);
return v___x_1584_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__2));
v___x_1589_ = l_Lean_MessageData_ofFormat(v___x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(lean_object* v_x_1590_, lean_object* v_x_1591_){
_start:
{
if (lean_obj_tag(v_x_1591_) == 0)
{
return v_x_1590_;
}
else
{
lean_object* v_head_1592_; lean_object* v_tail_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1615_; 
v_head_1592_ = lean_ctor_get(v_x_1591_, 0);
v_tail_1593_ = lean_ctor_get(v_x_1591_, 1);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_x_1591_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1595_ = v_x_1591_;
v_isShared_1596_ = v_isSharedCheck_1615_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_tail_1593_);
lean_inc(v_head_1592_);
lean_dec(v_x_1591_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1615_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_before_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1613_; 
v_before_1597_ = lean_ctor_get(v_head_1592_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_head_1592_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v_head_1592_, 1);
lean_dec(v_unused_1614_);
v___x_1599_ = v_head_1592_;
v_isShared_1600_ = v_isSharedCheck_1613_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_before_1597_);
lean_dec(v_head_1592_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1613_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1601_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0);
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 7);
lean_ctor_set(v___x_1599_, 1, v___x_1601_);
lean_ctor_set(v___x_1599_, 0, v_x_1590_);
v___x_1603_ = v___x_1599_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_x_1590_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3);
if (v_isShared_1596_ == 0)
{
lean_ctor_set_tag(v___x_1595_, 7);
lean_ctor_set(v___x_1595_, 1, v___x_1604_);
lean_ctor_set(v___x_1595_, 0, v___x_1603_);
v___x_1606_ = v___x_1595_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = l_Lean_MessageData_ofSyntax(v_before_1597_);
v___x_1608_ = l_Lean_indentD(v___x_1607_);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1606_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v_x_1590_ = v___x_1609_;
v_x_1591_ = v_tail_1593_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(lean_object* v_opts_1616_, lean_object* v_opt_1617_){
_start:
{
lean_object* v_name_1618_; lean_object* v_defValue_1619_; lean_object* v_map_1620_; lean_object* v___x_1621_; 
v_name_1618_ = lean_ctor_get(v_opt_1617_, 0);
v_defValue_1619_ = lean_ctor_get(v_opt_1617_, 1);
v_map_1620_ = lean_ctor_get(v_opts_1616_, 0);
v___x_1621_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1620_, v_name_1618_);
if (lean_obj_tag(v___x_1621_) == 0)
{
uint8_t v___x_1622_; 
v___x_1622_ = lean_unbox(v_defValue_1619_);
return v___x_1622_;
}
else
{
lean_object* v_val_1623_; 
v_val_1623_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_val_1623_);
lean_dec_ref(v___x_1621_);
if (lean_obj_tag(v_val_1623_) == 1)
{
uint8_t v_v_1624_; 
v_v_1624_ = lean_ctor_get_uint8(v_val_1623_, 0);
lean_dec_ref(v_val_1623_);
return v_v_1624_;
}
else
{
uint8_t v___x_1625_; 
lean_dec(v_val_1623_);
v___x_1625_ = lean_unbox(v_defValue_1619_);
return v___x_1625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25___boxed(lean_object* v_opts_1626_, lean_object* v_opt_1627_){
_start:
{
uint8_t v_res_1628_; lean_object* v_r_1629_; 
v_res_1628_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(v_opts_1626_, v_opt_1627_);
lean_dec_ref(v_opt_1627_);
lean_dec_ref(v_opts_1626_);
v_r_1629_ = lean_box(v_res_1628_);
return v_r_1629_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__1));
v___x_1634_ = l_Lean_MessageData_ofFormat(v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(lean_object* v_msgData_1635_, lean_object* v_macroStack_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; lean_object* v_scopes_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_opts_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1639_ = lean_st_ref_get(v___y_1637_);
v_scopes_1640_ = lean_ctor_get(v___x_1639_, 2);
lean_inc(v_scopes_1640_);
lean_dec(v___x_1639_);
v___x_1641_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1642_ = l_List_head_x21___redArg(v___x_1641_, v_scopes_1640_);
lean_dec(v_scopes_1640_);
v_opts_1643_ = lean_ctor_get(v___x_1642_, 1);
lean_inc_ref(v_opts_1643_);
lean_dec(v___x_1642_);
v___x_1644_ = l_Lean_Elab_pp_macroStack;
v___x_1645_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(v_opts_1643_, v___x_1644_);
lean_dec_ref(v_opts_1643_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
lean_dec(v_macroStack_1636_);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_msgData_1635_);
return v___x_1646_;
}
else
{
if (lean_obj_tag(v_macroStack_1636_) == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_msgData_1635_);
return v___x_1647_;
}
else
{
lean_object* v_head_1648_; lean_object* v_after_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1664_; 
v_head_1648_ = lean_ctor_get(v_macroStack_1636_, 0);
lean_inc(v_head_1648_);
v_after_1649_ = lean_ctor_get(v_head_1648_, 1);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_head_1648_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; 
v_unused_1665_ = lean_ctor_get(v_head_1648_, 0);
lean_dec(v_unused_1665_);
v___x_1651_ = v_head_1648_;
v_isShared_1652_ = v_isSharedCheck_1664_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_after_1649_);
lean_dec(v_head_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1664_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; lean_object* v___x_1655_; 
v___x_1653_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0);
if (v_isShared_1652_ == 0)
{
lean_ctor_set_tag(v___x_1651_, 7);
lean_ctor_set(v___x_1651_, 1, v___x_1653_);
lean_ctor_set(v___x_1651_, 0, v_msgData_1635_);
v___x_1655_ = v___x_1651_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_msgData_1635_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v_msgData_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1656_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = l_Lean_MessageData_ofSyntax(v_after_1649_);
v___x_1659_ = l_Lean_indentD(v___x_1658_);
v_msgData_1660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1660_, 0, v___x_1657_);
lean_ctor_set(v_msgData_1660_, 1, v___x_1659_);
v___x_1661_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(v_msgData_1660_, v_macroStack_1636_);
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
return v___x_1662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___boxed(lean_object* v_msgData_1666_, lean_object* v_macroStack_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_msgData_1666_, v_macroStack_1667_, v___y_1668_);
lean_dec(v___y_1668_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(lean_object* v_msg_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_Elab_Command_getRef___redArg(v___y_1672_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v_macroStack_1677_; lean_object* v___x_1678_; lean_object* v_a_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1690_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref(v___x_1675_);
v_macroStack_1677_ = lean_ctor_get(v___y_1672_, 4);
v___x_1678_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msg_1671_, v___y_1673_);
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_a_1679_);
lean_dec_ref(v___x_1678_);
lean_inc_n(v_macroStack_1677_, 2);
v___x_1680_ = l_Lean_Elab_getBetterRef(v_a_1676_, v_macroStack_1677_);
lean_dec(v_a_1676_);
v___x_1681_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_a_1679_, v_macroStack_1677_, v___y_1673_);
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1680_);
lean_ctor_set(v___x_1686_, 1, v_a_1682_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set_tag(v___x_1684_, 1);
lean_ctor_set(v___x_1684_, 0, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec_ref(v_msg_1671_);
v_a_1691_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1675_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1675_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg___boxed(lean_object* v_msg_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(lean_object* v_ref_1704_, lean_object* v_msg_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_Elab_Command_getRef___redArg(v___y_1706_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v_fileName_1711_; lean_object* v_fileMap_1712_; lean_object* v_currRecDepth_1713_; lean_object* v_cmdPos_1714_; lean_object* v_macroStack_1715_; lean_object* v_quotContext_x3f_1716_; lean_object* v_currMacroScope_1717_; lean_object* v_snap_x3f_1718_; lean_object* v_cancelTk_x3f_1719_; uint8_t v_suppressElabErrors_1720_; lean_object* v_ref_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref(v___x_1709_);
v_fileName_1711_ = lean_ctor_get(v___y_1706_, 0);
v_fileMap_1712_ = lean_ctor_get(v___y_1706_, 1);
v_currRecDepth_1713_ = lean_ctor_get(v___y_1706_, 2);
v_cmdPos_1714_ = lean_ctor_get(v___y_1706_, 3);
v_macroStack_1715_ = lean_ctor_get(v___y_1706_, 4);
v_quotContext_x3f_1716_ = lean_ctor_get(v___y_1706_, 5);
v_currMacroScope_1717_ = lean_ctor_get(v___y_1706_, 6);
v_snap_x3f_1718_ = lean_ctor_get(v___y_1706_, 8);
v_cancelTk_x3f_1719_ = lean_ctor_get(v___y_1706_, 9);
v_suppressElabErrors_1720_ = lean_ctor_get_uint8(v___y_1706_, sizeof(void*)*10);
v_ref_1721_ = l_Lean_replaceRef(v_ref_1704_, v_a_1710_);
lean_dec(v_a_1710_);
lean_inc(v_cancelTk_x3f_1719_);
lean_inc(v_snap_x3f_1718_);
lean_inc(v_currMacroScope_1717_);
lean_inc(v_quotContext_x3f_1716_);
lean_inc(v_macroStack_1715_);
lean_inc(v_cmdPos_1714_);
lean_inc(v_currRecDepth_1713_);
lean_inc_ref(v_fileMap_1712_);
lean_inc_ref(v_fileName_1711_);
v___x_1722_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1722_, 0, v_fileName_1711_);
lean_ctor_set(v___x_1722_, 1, v_fileMap_1712_);
lean_ctor_set(v___x_1722_, 2, v_currRecDepth_1713_);
lean_ctor_set(v___x_1722_, 3, v_cmdPos_1714_);
lean_ctor_set(v___x_1722_, 4, v_macroStack_1715_);
lean_ctor_set(v___x_1722_, 5, v_quotContext_x3f_1716_);
lean_ctor_set(v___x_1722_, 6, v_currMacroScope_1717_);
lean_ctor_set(v___x_1722_, 7, v_ref_1721_);
lean_ctor_set(v___x_1722_, 8, v_snap_x3f_1718_);
lean_ctor_set(v___x_1722_, 9, v_cancelTk_x3f_1719_);
lean_ctor_set_uint8(v___x_1722_, sizeof(void*)*10, v_suppressElabErrors_1720_);
v___x_1723_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_1705_, v___x_1722_, v___y_1707_);
lean_dec_ref(v___x_1722_);
return v___x_1723_;
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref(v_msg_1705_);
v_a_1724_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1709_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1709_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg___boxed(lean_object* v_ref_1732_, lean_object* v_msg_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_ref_1732_, v_msg_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v_ref_1732_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(lean_object* v_env_1738_, lean_object* v_declName_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v___x_1742_; lean_object* v_env_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; uint8_t v___x_1746_; 
v___x_1742_ = 0;
v_env_1743_ = l_Lean_Environment_setExporting(v_env_1738_, v___x_1742_);
lean_inc(v_declName_1739_);
v___x_1744_ = l_Lean_mkPrivateName(v_env_1743_, v_declName_1739_);
v___x_1745_ = 1;
lean_inc_ref(v_env_1743_);
v___x_1746_ = l_Lean_Environment_contains(v_env_1743_, v___x_1744_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; uint8_t v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1747_ = l_Lean_privateToUserName(v_declName_1739_);
v___x_1748_ = l_Lean_Environment_contains(v_env_1743_, v___x_1747_, v___x_1745_);
v___x_1749_ = lean_box(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v___y_1741_);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec_ref(v_env_1743_);
lean_dec(v_declName_1739_);
v___x_1751_ = lean_box(v___x_1746_);
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
lean_ctor_set(v___x_1752_, 1, v___y_1741_);
return v___x_1752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed(lean_object* v_env_1753_, lean_object* v_declName_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(v_env_1753_, v_declName_1754_, v___y_1755_, v___y_1756_);
lean_dec_ref(v___y_1755_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(lean_object* v_x_1758_, lean_object* v___y_1759_){
_start:
{
if (lean_obj_tag(v_x_1758_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1761_; 
v_a_1760_ = lean_ctor_get(v_x_1758_, 0);
lean_inc(v_a_1760_);
v___x_1761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_a_1760_);
lean_ctor_set(v___x_1761_, 1, v___y_1759_);
return v___x_1761_;
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1763_; 
v_a_1762_ = lean_ctor_get(v_x_1758_, 0);
lean_inc(v_a_1762_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v_a_1762_);
lean_ctor_set(v___x_1763_, 1, v___y_1759_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg___boxed(lean_object* v_x_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v_x_1764_, v___y_1765_);
lean_dec_ref(v_x_1764_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(lean_object* v_env_1767_, lean_object* v_stx_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1767_, v_stx_1768_, v___y_1769_, v___y_1770_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
if (lean_obj_tag(v_a_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1781_; 
v_a_1773_ = lean_ctor_get(v___x_1771_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1781_ == 0)
{
lean_object* v_unused_1782_; 
v_unused_1782_ = lean_ctor_get(v___x_1771_, 0);
lean_dec(v_unused_1782_);
v___x_1775_ = v___x_1771_;
v_isShared_1776_ = v_isSharedCheck_1781_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1771_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1781_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1777_ = lean_box(0);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1777_);
v___x_1779_ = v___x_1775_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_a_1773_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
else
{
lean_object* v_val_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1811_; 
v_val_1783_ = lean_ctor_get(v_a_1772_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_a_1772_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1785_ = v_a_1772_;
v_isShared_1786_ = v_isSharedCheck_1811_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_val_1783_);
lean_dec(v_a_1772_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1811_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v_snd_1787_; 
v_snd_1787_ = lean_ctor_get(v_val_1783_, 1);
lean_inc(v_snd_1787_);
lean_dec(v_val_1783_);
if (lean_obj_tag(v_snd_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1797_; 
lean_del_object(v___x_1785_);
v_a_1788_ = lean_ctor_get(v___x_1771_, 1);
lean_inc(v_a_1788_);
lean_dec_ref(v___x_1771_);
v_a_1789_ = lean_ctor_get(v_snd_1787_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_snd_1787_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1791_ = v_snd_1787_;
v_isShared_1792_ = v_isSharedCheck_1797_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v_snd_1787_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1797_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v___x_1794_, v_a_1788_);
lean_dec_ref(v___x_1794_);
return v___x_1795_;
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1810_; 
v_a_1798_ = lean_ctor_get(v___x_1771_, 1);
lean_inc(v_a_1798_);
lean_dec_ref(v___x_1771_);
v_a_1799_ = lean_ctor_get(v_snd_1787_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_snd_1787_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1801_ = v_snd_1787_;
v_isShared_1802_ = v_isSharedCheck_1810_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v_snd_1787_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1810_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v_a_1799_);
v___x_1804_ = v___x_1785_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1806_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1804_);
v___x_1806_ = v___x_1801_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v___x_1806_, v_a_1798_);
lean_dec_ref(v___x_1806_);
return v___x_1807_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_a_1812_ = lean_ctor_get(v___x_1771_, 0);
v_a_1813_ = lean_ctor_get(v___x_1771_, 1);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1771_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_inc(v_a_1812_);
lean_dec(v___x_1771_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1812_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed(lean_object* v_env_1821_, lean_object* v_stx_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(v_env_1821_, v_stx_1822_, v___y_1823_, v___y_1824_);
lean_dec_ref(v___y_1823_);
return v_res_1825_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = l_Lean_maxRecDepthErrorMessage;
v___x_1832_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
return v___x_1832_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3);
v___x_1834_ = l_Lean_MessageData_ofFormat(v___x_1833_);
return v___x_1834_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4);
v___x_1836_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2));
v___x_1837_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
lean_ctor_set(v___x_1837_, 1, v___x_1835_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(lean_object* v_ref_1838_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_ref_1838_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___boxed(lean_object* v_ref_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_1843_);
return v_res_1845_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(lean_object* v_keys_1846_, lean_object* v_i_1847_, lean_object* v_k_1848_){
_start:
{
lean_object* v___x_1849_; uint8_t v___x_1850_; 
v___x_1849_ = lean_array_get_size(v_keys_1846_);
v___x_1850_ = lean_nat_dec_lt(v_i_1847_, v___x_1849_);
if (v___x_1850_ == 0)
{
lean_dec(v_i_1847_);
return v___x_1850_;
}
else
{
lean_object* v_k_x27_1851_; uint8_t v___x_1852_; 
v_k_x27_1851_ = lean_array_fget_borrowed(v_keys_1846_, v_i_1847_);
v___x_1852_ = l_Lean_instBEqExtraModUse_beq(v_k_1848_, v_k_x27_1851_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_unsigned_to_nat(1u);
v___x_1854_ = lean_nat_add(v_i_1847_, v___x_1853_);
lean_dec(v_i_1847_);
v_i_1847_ = v___x_1854_;
goto _start;
}
else
{
lean_dec(v_i_1847_);
return v___x_1852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg___boxed(lean_object* v_keys_1856_, lean_object* v_i_1857_, lean_object* v_k_1858_){
_start:
{
uint8_t v_res_1859_; lean_object* v_r_1860_; 
v_res_1859_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_1856_, v_i_1857_, v_k_1858_);
lean_dec_ref(v_k_1858_);
lean_dec_ref(v_keys_1856_);
v_r_1860_ = lean_box(v_res_1859_);
return v_r_1860_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__0(void){
_start:
{
size_t v___x_1861_; size_t v___x_1862_; size_t v___x_1863_; 
v___x_1861_ = ((size_t)5ULL);
v___x_1862_ = ((size_t)1ULL);
v___x_1863_ = lean_usize_shift_left(v___x_1862_, v___x_1861_);
return v___x_1863_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__1(void){
_start:
{
size_t v___x_1864_; size_t v___x_1865_; size_t v___x_1866_; 
v___x_1864_ = ((size_t)1ULL);
v___x_1865_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__0);
v___x_1866_ = lean_usize_sub(v___x_1865_, v___x_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(lean_object* v_x_1867_, size_t v_x_1868_, lean_object* v_x_1869_){
_start:
{
if (lean_obj_tag(v_x_1867_) == 0)
{
lean_object* v_es_1870_; lean_object* v___x_1871_; size_t v___x_1872_; size_t v___x_1873_; size_t v___x_1874_; lean_object* v_j_1875_; lean_object* v___x_1876_; 
v_es_1870_ = lean_ctor_get(v_x_1867_, 0);
v___x_1871_ = lean_box(2);
v___x_1872_ = ((size_t)5ULL);
v___x_1873_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__1);
v___x_1874_ = lean_usize_land(v_x_1868_, v___x_1873_);
v_j_1875_ = lean_usize_to_nat(v___x_1874_);
v___x_1876_ = lean_array_get_borrowed(v___x_1871_, v_es_1870_, v_j_1875_);
lean_dec(v_j_1875_);
switch(lean_obj_tag(v___x_1876_))
{
case 0:
{
lean_object* v_key_1877_; uint8_t v___x_1878_; 
v_key_1877_ = lean_ctor_get(v___x_1876_, 0);
v___x_1878_ = l_Lean_instBEqExtraModUse_beq(v_x_1869_, v_key_1877_);
return v___x_1878_;
}
case 1:
{
lean_object* v_node_1879_; size_t v___x_1880_; 
v_node_1879_ = lean_ctor_get(v___x_1876_, 0);
v___x_1880_ = lean_usize_shift_right(v_x_1868_, v___x_1872_);
v_x_1867_ = v_node_1879_;
v_x_1868_ = v___x_1880_;
goto _start;
}
default: 
{
uint8_t v___x_1882_; 
v___x_1882_ = 0;
return v___x_1882_;
}
}
}
else
{
lean_object* v_ks_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v_ks_1883_ = lean_ctor_get(v_x_1867_, 0);
v___x_1884_ = lean_unsigned_to_nat(0u);
v___x_1885_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_ks_1883_, v___x_1884_, v_x_1869_);
return v___x_1885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___boxed(lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
size_t v_x_23530__boxed_1889_; uint8_t v_res_1890_; lean_object* v_r_1891_; 
v_x_23530__boxed_1889_ = lean_unbox_usize(v_x_1887_);
lean_dec(v_x_1887_);
v_res_1890_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_1886_, v_x_23530__boxed_1889_, v_x_1888_);
lean_dec_ref(v_x_1888_);
lean_dec_ref(v_x_1886_);
v_r_1891_ = lean_box(v_res_1890_);
return v_r_1891_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(lean_object* v_x_1892_, lean_object* v_x_1893_){
_start:
{
uint64_t v___x_1894_; size_t v___x_1895_; uint8_t v___x_1896_; 
v___x_1894_ = l_Lean_instHashableExtraModUse_hash(v_x_1893_);
v___x_1895_ = lean_uint64_to_usize(v___x_1894_);
v___x_1896_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_1892_, v___x_1895_, v_x_1893_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg___boxed(lean_object* v_x_1897_, lean_object* v_x_1898_){
_start:
{
uint8_t v_res_1899_; lean_object* v_r_1900_; 
v_res_1899_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_1897_, v_x_1898_);
lean_dec_ref(v_x_1898_);
lean_dec_ref(v_x_1897_);
v_r_1900_ = lean_box(v_res_1899_);
return v_r_1900_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1));
v___x_1904_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0));
v___x_1905_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1904_, v___x_1903_);
return v___x_1905_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5));
v___x_1911_ = l_Lean_stringToMessageData(v___x_1910_);
return v___x_1911_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7));
v___x_1914_ = l_Lean_stringToMessageData(v___x_1913_);
return v___x_1914_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1916_ = l_Lean_stringToMessageData(v___x_1915_);
return v___x_1916_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10(void){
_start:
{
lean_object* v_cls_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_cls_1917_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4));
v___x_1918_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
v___x_1919_ = l_Lean_Name_append(v___x_1918_, v_cls_1917_);
return v___x_1919_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12(void){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11));
v___x_1922_ = l_Lean_stringToMessageData(v___x_1921_);
return v___x_1922_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13));
v___x_1925_ = l_Lean_stringToMessageData(v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(lean_object* v_mod_1930_, uint8_t v_isMeta_1931_, lean_object* v_hint_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v___x_1936_; lean_object* v_env_1937_; uint8_t v_isExporting_1938_; lean_object* v___x_1939_; lean_object* v_env_1940_; lean_object* v___x_1941_; lean_object* v_entry_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___y_1947_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1936_ = lean_st_ref_get(v___y_1934_);
v_env_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc_ref(v_env_1937_);
lean_dec(v___x_1936_);
v_isExporting_1938_ = lean_ctor_get_uint8(v_env_1937_, sizeof(void*)*8);
lean_dec_ref(v_env_1937_);
v___x_1939_ = lean_st_ref_get(v___y_1934_);
v_env_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc_ref(v_env_1940_);
lean_dec(v___x_1939_);
v___x_1941_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2);
lean_inc(v_mod_1930_);
v_entry_1942_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1942_, 0, v_mod_1930_);
lean_ctor_set_uint8(v_entry_1942_, sizeof(void*)*1, v_isExporting_1938_);
lean_ctor_set_uint8(v_entry_1942_, sizeof(void*)*1 + 1, v_isMeta_1931_);
v___x_1943_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1944_ = lean_box(1);
v___x_1945_ = lean_box(0);
v___x_1973_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1941_, v___x_1943_, v_env_1940_, v___x_1944_, v___x_1945_);
v___x_1974_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v___x_1973_, v_entry_1942_);
lean_dec(v___x_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v_scopes_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v_opts_1981_; uint8_t v_hasTrace_1982_; 
v___x_1975_ = l_Lean_inheritedTraceOptions;
v___x_1976_ = lean_st_ref_get(v___x_1975_);
v___x_1977_ = lean_st_ref_get(v___y_1934_);
v_scopes_1978_ = lean_ctor_get(v___x_1977_, 2);
lean_inc(v_scopes_1978_);
lean_dec(v___x_1977_);
v___x_1979_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1980_ = l_List_head_x21___redArg(v___x_1979_, v_scopes_1978_);
lean_dec(v_scopes_1978_);
v_opts_1981_ = lean_ctor_get(v___x_1980_, 1);
lean_inc_ref(v_opts_1981_);
lean_dec(v___x_1980_);
v_hasTrace_1982_ = lean_ctor_get_uint8(v_opts_1981_, sizeof(void*)*1);
if (v_hasTrace_1982_ == 0)
{
lean_dec_ref(v_opts_1981_);
lean_dec(v___x_1976_);
lean_dec(v_hint_1932_);
lean_dec(v_mod_1930_);
v___y_1947_ = v___y_1934_;
goto v___jp_1946_;
}
else
{
lean_object* v_cls_1983_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
v_cls_1983_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4));
v___x_2003_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10);
v___x_2004_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1976_, v_opts_1981_, v___x_2003_);
lean_dec_ref(v_opts_1981_);
lean_dec(v___x_1976_);
if (v___x_2004_ == 0)
{
lean_dec(v_hint_1932_);
lean_dec(v_mod_1930_);
v___y_1947_ = v___y_1934_;
goto v___jp_1946_;
}
else
{
lean_object* v___x_2005_; lean_object* v___y_2007_; 
v___x_2005_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12);
if (v_isExporting_1938_ == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__17));
v___y_2007_ = v___x_2014_;
goto v___jp_2006_;
}
else
{
lean_object* v___x_2015_; 
v___x_2015_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__18));
v___y_2007_ = v___x_2015_;
goto v___jp_2006_;
}
v___jp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
lean_inc_ref(v___y_2007_);
v___x_2008_ = l_Lean_stringToMessageData(v___y_2007_);
v___x_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2005_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2009_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
if (v_isMeta_1931_ == 0)
{
lean_object* v___x_2012_; 
v___x_2012_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15));
v___y_1990_ = v___x_2011_;
v___y_1991_ = v___x_2012_;
goto v___jp_1989_;
}
else
{
lean_object* v___x_2013_; 
v___x_2013_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16));
v___y_1990_ = v___x_2011_;
v___y_1991_ = v___x_2013_;
goto v___jp_1989_;
}
}
}
v___jp_1984_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___y_1985_);
lean_ctor_set(v___x_1987_, 1, v___y_1986_);
v___x_1988_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_1983_, v___x_1987_, v___y_1933_, v___y_1934_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_dec_ref(v___x_1988_);
v___y_1947_ = v___y_1934_;
goto v___jp_1946_;
}
else
{
lean_dec_ref(v_entry_1942_);
return v___x_1988_;
}
}
v___jp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
lean_inc_ref(v___y_1991_);
v___x_1992_ = l_Lean_stringToMessageData(v___y_1991_);
v___x_1993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___y_1990_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6);
v___x_1995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = l_Lean_MessageData_ofName(v_mod_1930_);
v___x_1997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1995_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = l_Lean_Name_isAnonymous(v_hint_1932_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8);
v___x_2000_ = l_Lean_MessageData_ofName(v_hint_1932_);
v___x_2001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___y_1985_ = v___x_1997_;
v___y_1986_ = v___x_2001_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2002_; 
lean_dec(v_hint_1932_);
v___x_2002_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9);
v___y_1985_ = v___x_1997_;
v___y_1986_ = v___x_2002_;
goto v___jp_1984_;
}
}
}
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_dec_ref(v_entry_1942_);
lean_dec(v_hint_1932_);
lean_dec(v_mod_1930_);
v___x_2016_ = lean_box(0);
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
return v___x_2017_;
}
v___jp_1946_:
{
lean_object* v___x_1948_; lean_object* v_toEnvExtension_1949_; lean_object* v_env_1950_; lean_object* v_messages_1951_; lean_object* v_scopes_1952_; lean_object* v_usedQuotCtxts_1953_; lean_object* v_nextMacroScope_1954_; lean_object* v_maxRecDepth_1955_; lean_object* v_ngen_1956_; lean_object* v_auxDeclNGen_1957_; lean_object* v_infoState_1958_; lean_object* v_traceState_1959_; lean_object* v_snapshotTasks_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1972_; 
v___x_1948_ = lean_st_ref_take(v___y_1947_);
v_toEnvExtension_1949_ = lean_ctor_get(v___x_1943_, 0);
v_env_1950_ = lean_ctor_get(v___x_1948_, 0);
v_messages_1951_ = lean_ctor_get(v___x_1948_, 1);
v_scopes_1952_ = lean_ctor_get(v___x_1948_, 2);
v_usedQuotCtxts_1953_ = lean_ctor_get(v___x_1948_, 3);
v_nextMacroScope_1954_ = lean_ctor_get(v___x_1948_, 4);
v_maxRecDepth_1955_ = lean_ctor_get(v___x_1948_, 5);
v_ngen_1956_ = lean_ctor_get(v___x_1948_, 6);
v_auxDeclNGen_1957_ = lean_ctor_get(v___x_1948_, 7);
v_infoState_1958_ = lean_ctor_get(v___x_1948_, 8);
v_traceState_1959_ = lean_ctor_get(v___x_1948_, 9);
v_snapshotTasks_1960_ = lean_ctor_get(v___x_1948_, 10);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1962_ = v___x_1948_;
v_isShared_1963_ = v_isSharedCheck_1972_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_snapshotTasks_1960_);
lean_inc(v_traceState_1959_);
lean_inc(v_infoState_1958_);
lean_inc(v_auxDeclNGen_1957_);
lean_inc(v_ngen_1956_);
lean_inc(v_maxRecDepth_1955_);
lean_inc(v_nextMacroScope_1954_);
lean_inc(v_usedQuotCtxts_1953_);
lean_inc(v_scopes_1952_);
lean_inc(v_messages_1951_);
lean_inc(v_env_1950_);
lean_dec(v___x_1948_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1972_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v_asyncMode_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v_asyncMode_1964_ = lean_ctor_get(v_toEnvExtension_1949_, 2);
v___x_1965_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1943_, v_env_1950_, v_entry_1942_, v_asyncMode_1964_, v___x_1945_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1965_);
v___x_1967_ = v___x_1962_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_messages_1951_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_scopes_1952_);
lean_ctor_set(v_reuseFailAlloc_1971_, 3, v_usedQuotCtxts_1953_);
lean_ctor_set(v_reuseFailAlloc_1971_, 4, v_nextMacroScope_1954_);
lean_ctor_set(v_reuseFailAlloc_1971_, 5, v_maxRecDepth_1955_);
lean_ctor_set(v_reuseFailAlloc_1971_, 6, v_ngen_1956_);
lean_ctor_set(v_reuseFailAlloc_1971_, 7, v_auxDeclNGen_1957_);
lean_ctor_set(v_reuseFailAlloc_1971_, 8, v_infoState_1958_);
lean_ctor_set(v_reuseFailAlloc_1971_, 9, v_traceState_1959_);
lean_ctor_set(v_reuseFailAlloc_1971_, 10, v_snapshotTasks_1960_);
v___x_1967_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = lean_st_ref_set(v___y_1947_, v___x_1967_);
v___x_1969_ = lean_box(0);
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
return v___x_1970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___boxed(lean_object* v_mod_2018_, lean_object* v_isMeta_2019_, lean_object* v_hint_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
uint8_t v_isMeta_boxed_2024_; lean_object* v_res_2025_; 
v_isMeta_boxed_2024_ = lean_unbox(v_isMeta_2019_);
v_res_2025_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_mod_2018_, v_isMeta_boxed_2024_, v_hint_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(lean_object* v___x_2026_, lean_object* v_declName_2027_, lean_object* v_as_2028_, size_t v_sz_2029_, size_t v_i_2030_, lean_object* v_b_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_usize_dec_lt(v_i_2030_, v_sz_2029_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
lean_dec(v_declName_2027_);
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_b_2031_);
return v___x_2036_;
}
else
{
lean_object* v___x_2037_; lean_object* v_modules_2038_; lean_object* v___x_2039_; lean_object* v_a_2040_; lean_object* v___x_2041_; lean_object* v_toImport_2042_; lean_object* v_module_2043_; uint8_t v___x_2044_; lean_object* v___x_2045_; 
v___x_2037_ = l_Lean_Environment_header(v___x_2026_);
v_modules_2038_ = lean_ctor_get(v___x_2037_, 3);
lean_inc_ref(v_modules_2038_);
lean_dec_ref(v___x_2037_);
v___x_2039_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2040_ = lean_array_uget_borrowed(v_as_2028_, v_i_2030_);
v___x_2041_ = lean_array_get(v___x_2039_, v_modules_2038_, v_a_2040_);
lean_dec_ref(v_modules_2038_);
v_toImport_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc_ref(v_toImport_2042_);
lean_dec(v___x_2041_);
v_module_2043_ = lean_ctor_get(v_toImport_2042_, 0);
lean_inc(v_module_2043_);
lean_dec_ref(v_toImport_2042_);
v___x_2044_ = 0;
lean_inc(v_declName_2027_);
v___x_2045_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_module_2043_, v___x_2044_, v_declName_2027_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v___x_2046_; size_t v___x_2047_; size_t v___x_2048_; 
lean_dec_ref(v___x_2045_);
v___x_2046_ = lean_box(0);
v___x_2047_ = ((size_t)1ULL);
v___x_2048_ = lean_usize_add(v_i_2030_, v___x_2047_);
v_i_2030_ = v___x_2048_;
v_b_2031_ = v___x_2046_;
goto _start;
}
else
{
lean_dec(v_declName_2027_);
return v___x_2045_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7___boxed(lean_object* v___x_2050_, lean_object* v_declName_2051_, lean_object* v_as_2052_, lean_object* v_sz_2053_, lean_object* v_i_2054_, lean_object* v_b_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
size_t v_sz_boxed_2059_; size_t v_i_boxed_2060_; lean_object* v_res_2061_; 
v_sz_boxed_2059_ = lean_unbox_usize(v_sz_2053_);
lean_dec(v_sz_2053_);
v_i_boxed_2060_ = lean_unbox_usize(v_i_2054_);
lean_dec(v_i_2054_);
v_res_2061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v___x_2050_, v_declName_2051_, v_as_2052_, v_sz_boxed_2059_, v_i_boxed_2060_, v_b_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec_ref(v_as_2052_);
lean_dec_ref(v___x_2050_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(lean_object* v_a_2062_, lean_object* v_x_2063_){
_start:
{
if (lean_obj_tag(v_x_2063_) == 0)
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_box(0);
return v___x_2064_;
}
else
{
lean_object* v_key_2065_; lean_object* v_value_2066_; lean_object* v_tail_2067_; uint8_t v___x_2068_; 
v_key_2065_ = lean_ctor_get(v_x_2063_, 0);
v_value_2066_ = lean_ctor_get(v_x_2063_, 1);
v_tail_2067_ = lean_ctor_get(v_x_2063_, 2);
v___x_2068_ = lean_name_eq(v_key_2065_, v_a_2062_);
if (v___x_2068_ == 0)
{
v_x_2063_ = v_tail_2067_;
goto _start;
}
else
{
lean_object* v___x_2070_; 
lean_inc(v_value_2066_);
v___x_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2070_, 0, v_value_2066_);
return v___x_2070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg___boxed(lean_object* v_a_2071_, lean_object* v_x_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_2071_, v_x_2072_);
lean_dec(v_x_2072_);
lean_dec(v_a_2071_);
return v_res_2073_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2074_; uint64_t v___x_2075_; 
v___x_2074_ = lean_unsigned_to_nat(1723u);
v___x_2075_ = lean_uint64_of_nat(v___x_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(lean_object* v_m_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v_buckets_2078_; lean_object* v___x_2079_; uint64_t v___y_2081_; 
v_buckets_2078_ = lean_ctor_get(v_m_2076_, 1);
v___x_2079_ = lean_array_get_size(v_buckets_2078_);
if (lean_obj_tag(v_a_2077_) == 0)
{
uint64_t v___x_2095_; 
v___x_2095_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0);
v___y_2081_ = v___x_2095_;
goto v___jp_2080_;
}
else
{
uint64_t v_hash_2096_; 
v_hash_2096_ = lean_ctor_get_uint64(v_a_2077_, sizeof(void*)*2);
v___y_2081_ = v_hash_2096_;
goto v___jp_2080_;
}
v___jp_2080_:
{
uint64_t v___x_2082_; uint64_t v___x_2083_; uint64_t v_fold_2084_; uint64_t v___x_2085_; uint64_t v___x_2086_; uint64_t v___x_2087_; size_t v___x_2088_; size_t v___x_2089_; size_t v___x_2090_; size_t v___x_2091_; size_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2082_ = 32ULL;
v___x_2083_ = lean_uint64_shift_right(v___y_2081_, v___x_2082_);
v_fold_2084_ = lean_uint64_xor(v___y_2081_, v___x_2083_);
v___x_2085_ = 16ULL;
v___x_2086_ = lean_uint64_shift_right(v_fold_2084_, v___x_2085_);
v___x_2087_ = lean_uint64_xor(v_fold_2084_, v___x_2086_);
v___x_2088_ = lean_uint64_to_usize(v___x_2087_);
v___x_2089_ = lean_usize_of_nat(v___x_2079_);
v___x_2090_ = ((size_t)1ULL);
v___x_2091_ = lean_usize_sub(v___x_2089_, v___x_2090_);
v___x_2092_ = lean_usize_land(v___x_2088_, v___x_2091_);
v___x_2093_ = lean_array_uget_borrowed(v_buckets_2078_, v___x_2092_);
v___x_2094_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_2077_, v___x_2093_);
return v___x_2094_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_m_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v_m_2097_, v_a_2098_);
lean_dec(v_a_2098_);
lean_dec_ref(v_m_2097_);
return v_res_2099_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2102_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1));
v___x_2103_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0));
v___x_2104_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2103_, v___x_2102_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(lean_object* v_declName_2107_, uint8_t v_isMeta_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___x_2112_; lean_object* v_env_2116_; lean_object* v___y_2118_; lean_object* v___x_2131_; 
v___x_2112_ = lean_st_ref_get(v___y_2110_);
v_env_2116_ = lean_ctor_get(v___x_2112_, 0);
lean_inc_ref(v_env_2116_);
lean_dec(v___x_2112_);
v___x_2131_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2116_, v_declName_2107_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_dec_ref(v_env_2116_);
lean_dec(v_declName_2107_);
goto v___jp_2113_;
}
else
{
lean_object* v_val_2132_; lean_object* v___x_2133_; lean_object* v_modules_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v_val_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_val_2132_);
lean_dec_ref(v___x_2131_);
v___x_2133_ = l_Lean_Environment_header(v_env_2116_);
v_modules_2134_ = lean_ctor_get(v___x_2133_, 3);
lean_inc_ref(v_modules_2134_);
lean_dec_ref(v___x_2133_);
v___x_2135_ = lean_array_get_size(v_modules_2134_);
v___x_2136_ = lean_nat_dec_lt(v_val_2132_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_dec_ref(v_modules_2134_);
lean_dec(v_val_2132_);
lean_dec_ref(v_env_2116_);
lean_dec(v_declName_2107_);
goto v___jp_2113_;
}
else
{
lean_object* v___x_2137_; lean_object* v_env_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___y_2142_; 
v___x_2137_ = lean_st_ref_get(v___y_2110_);
v_env_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc_ref(v_env_2138_);
lean_dec(v___x_2137_);
v___x_2139_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2);
v___x_2140_ = lean_array_fget(v_modules_2134_, v_val_2132_);
lean_dec(v_val_2132_);
lean_dec_ref(v_modules_2134_);
if (v_isMeta_2108_ == 0)
{
lean_dec_ref(v_env_2138_);
v___y_2142_ = v_isMeta_2108_;
goto v___jp_2141_;
}
else
{
uint8_t v___x_2153_; 
lean_inc(v_declName_2107_);
v___x_2153_ = l_Lean_isMarkedMeta(v_env_2138_, v_declName_2107_);
if (v___x_2153_ == 0)
{
v___y_2142_ = v_isMeta_2108_;
goto v___jp_2141_;
}
else
{
uint8_t v___x_2154_; 
v___x_2154_ = 0;
v___y_2142_ = v___x_2154_;
goto v___jp_2141_;
}
}
v___jp_2141_:
{
lean_object* v_toImport_2143_; lean_object* v_module_2144_; lean_object* v___x_2145_; 
v_toImport_2143_ = lean_ctor_get(v___x_2140_, 0);
lean_inc_ref(v_toImport_2143_);
lean_dec(v___x_2140_);
v_module_2144_ = lean_ctor_get(v_toImport_2143_, 0);
lean_inc(v_module_2144_);
lean_dec_ref(v_toImport_2143_);
lean_inc(v_declName_2107_);
v___x_2145_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_module_2144_, v___y_2142_, v_declName_2107_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_dec_ref(v___x_2145_);
v___x_2146_ = l_Lean_indirectModUseExt;
v___x_2147_ = lean_box(1);
v___x_2148_ = lean_box(0);
lean_inc_ref(v_env_2116_);
v___x_2149_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2139_, v___x_2146_, v_env_2116_, v___x_2147_, v___x_2148_);
v___x_2150_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v___x_2149_, v_declName_2107_);
lean_dec(v___x_2149_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v___x_2151_; 
v___x_2151_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__3));
v___y_2118_ = v___x_2151_;
goto v___jp_2117_;
}
else
{
lean_object* v_val_2152_; 
v_val_2152_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_val_2152_);
lean_dec_ref(v___x_2150_);
v___y_2118_ = v_val_2152_;
goto v___jp_2117_;
}
}
else
{
lean_dec_ref(v_env_2116_);
lean_dec(v_declName_2107_);
return v___x_2145_;
}
}
}
}
v___jp_2113_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_box(0);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
v___jp_2117_:
{
lean_object* v___x_2119_; size_t v_sz_2120_; size_t v___x_2121_; lean_object* v___x_2122_; 
v___x_2119_ = lean_box(0);
v_sz_2120_ = lean_array_size(v___y_2118_);
v___x_2121_ = ((size_t)0ULL);
v___x_2122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v_env_2116_, v_declName_2107_, v___y_2118_, v_sz_2120_, v___x_2121_, v___x_2119_, v___y_2109_, v___y_2110_);
lean_dec_ref(v___y_2118_);
lean_dec_ref(v_env_2116_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; 
v_unused_2130_ = lean_ctor_get(v___x_2122_, 0);
lean_dec(v_unused_2130_);
v___x_2124_ = v___x_2122_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_dec(v___x_2122_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2119_);
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2119_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
else
{
return v___x_2122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___boxed(lean_object* v_declName_2155_, lean_object* v_isMeta_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
uint8_t v_isMeta_boxed_2160_; lean_object* v_res_2161_; 
v_isMeta_boxed_2160_ = lean_unbox(v_isMeta_2156_);
v_res_2161_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_declName_2155_, v_isMeta_boxed_2160_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(lean_object* v_as_x27_2162_, lean_object* v_b_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
if (lean_obj_tag(v_as_x27_2162_) == 0)
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2167_, 0, v_b_2163_);
return v___x_2167_;
}
else
{
lean_object* v_head_2168_; lean_object* v_tail_2169_; uint8_t v___x_2170_; lean_object* v___x_2171_; 
v_head_2168_ = lean_ctor_get(v_as_x27_2162_, 0);
lean_inc(v_head_2168_);
v_tail_2169_ = lean_ctor_get(v_as_x27_2162_, 1);
lean_inc(v_tail_2169_);
lean_dec_ref(v_as_x27_2162_);
v___x_2170_ = 1;
v___x_2171_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_head_2168_, v___x_2170_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v___x_2172_; 
lean_dec_ref(v___x_2171_);
v___x_2172_ = lean_box(0);
v_as_x27_2162_ = v_tail_2169_;
v_b_2163_ = v___x_2172_;
goto _start;
}
else
{
lean_dec(v_tail_2169_);
return v___x_2171_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2174_, lean_object* v_b_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_2174_, v_b_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(lean_object* v_x_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___x_2185_; lean_object* v_env_2186_; lean_object* v___x_2187_; lean_object* v_scopes_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v_opts_2191_; lean_object* v___x_2192_; 
v___x_2185_ = lean_st_ref_get(v___y_2183_);
v_env_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc_ref(v_env_2186_);
lean_dec(v___x_2185_);
v___x_2187_ = lean_st_ref_get(v___y_2183_);
v_scopes_2188_ = lean_ctor_get(v___x_2187_, 2);
lean_inc(v_scopes_2188_);
lean_dec(v___x_2187_);
v___x_2189_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2190_ = l_List_head_x21___redArg(v___x_2189_, v_scopes_2188_);
lean_dec(v_scopes_2188_);
v_opts_2191_ = lean_ctor_get(v___x_2190_, 1);
lean_inc_ref(v_opts_2191_);
lean_dec(v___x_2190_);
v___x_2192_ = l_Lean_Elab_Command_getScope___redArg(v___y_2183_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v_currNamespace_2194_; lean_object* v___x_2195_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref(v___x_2192_);
v_currNamespace_2194_ = lean_ctor_get(v_a_2193_, 2);
lean_inc(v_currNamespace_2194_);
lean_dec(v_a_2193_);
v___x_2195_ = l_Lean_Elab_Command_getScope___redArg(v___y_2183_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v_openDecls_2197_; lean_object* v___x_2198_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2195_);
v_openDecls_2197_ = lean_ctor_get(v_a_2196_, 3);
lean_inc(v_openDecls_2197_);
lean_dec(v_a_2196_);
v___x_2198_ = l_Lean_Elab_Command_getRef___redArg(v___y_2182_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref(v___x_2198_);
v___x_2200_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2182_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v_currRecDepth_2202_; lean_object* v_quotContext_x3f_2203_; lean_object* v___f_2204_; lean_object* v___f_2205_; lean_object* v___f_2206_; lean_object* v___f_2207_; lean_object* v___f_2208_; lean_object* v_methods_2209_; lean_object* v_a_2211_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v___x_2200_);
v_currRecDepth_2202_ = lean_ctor_get(v___y_2182_, 2);
v_quotContext_x3f_2203_ = lean_ctor_get(v___y_2182_, 5);
lean_inc_ref_n(v_env_2186_, 3);
v___f_2204_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2204_, 0, v_env_2186_);
v___f_2205_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2205_, 0, v_env_2186_);
lean_inc_n(v_currNamespace_2194_, 2);
v___f_2206_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2206_, 0, v_currNamespace_2194_);
lean_inc(v_openDecls_2197_);
v___f_2207_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2207_, 0, v_env_2186_);
lean_closure_set(v___f_2207_, 1, v_currNamespace_2194_);
lean_closure_set(v___f_2207_, 2, v_openDecls_2197_);
v___f_2208_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2208_, 0, v_env_2186_);
lean_closure_set(v___f_2208_, 1, v_opts_2191_);
lean_closure_set(v___f_2208_, 2, v_currNamespace_2194_);
lean_closure_set(v___f_2208_, 3, v_openDecls_2197_);
v_methods_2209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2209_, 0, v___f_2205_);
lean_ctor_set(v_methods_2209_, 1, v___f_2206_);
lean_ctor_set(v_methods_2209_, 2, v___f_2204_);
lean_ctor_set(v_methods_2209_, 3, v___f_2207_);
lean_ctor_set(v_methods_2209_, 4, v___f_2208_);
if (lean_obj_tag(v_quotContext_x3f_2203_) == 0)
{
lean_object* v___x_2283_; lean_object* v_a_2284_; 
v___x_2283_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2183_);
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref(v___x_2283_);
v_a_2211_ = v_a_2284_;
goto v___jp_2210_;
}
else
{
lean_object* v_val_2285_; 
v_val_2285_ = lean_ctor_get(v_quotContext_x3f_2203_, 0);
lean_inc(v_val_2285_);
v_a_2211_ = v_val_2285_;
goto v___jp_2210_;
}
v___jp_2210_:
{
lean_object* v___x_2212_; lean_object* v_maxRecDepth_2213_; lean_object* v___x_2214_; lean_object* v_nextMacroScope_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2212_ = lean_st_ref_get(v___y_2183_);
v_maxRecDepth_2213_ = lean_ctor_get(v___x_2212_, 5);
lean_inc(v_maxRecDepth_2213_);
lean_dec(v___x_2212_);
v___x_2214_ = lean_st_ref_get(v___y_2183_);
v_nextMacroScope_2215_ = lean_ctor_get(v___x_2214_, 4);
lean_inc(v_nextMacroScope_2215_);
lean_dec(v___x_2214_);
lean_inc(v_currRecDepth_2202_);
v___x_2216_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2216_, 0, v_methods_2209_);
lean_ctor_set(v___x_2216_, 1, v_a_2211_);
lean_ctor_set(v___x_2216_, 2, v_a_2201_);
lean_ctor_set(v___x_2216_, 3, v_currRecDepth_2202_);
lean_ctor_set(v___x_2216_, 4, v_maxRecDepth_2213_);
lean_ctor_set(v___x_2216_, 5, v_a_2199_);
v___x_2217_ = lean_box(0);
v___x_2218_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2218_, 0, v_nextMacroScope_2215_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
lean_ctor_set(v___x_2218_, 2, v___x_2217_);
v___x_2219_ = lean_apply_2(v_x_2181_, v___x_2216_, v___x_2218_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v_a_2221_; lean_object* v_macroScope_2222_; lean_object* v_traceMsgs_2223_; lean_object* v_expandedMacroDecls_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 1);
lean_inc(v_a_2220_);
v_a_2221_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2221_);
lean_dec_ref(v___x_2219_);
v_macroScope_2222_ = lean_ctor_get(v_a_2220_, 0);
lean_inc(v_macroScope_2222_);
v_traceMsgs_2223_ = lean_ctor_get(v_a_2220_, 1);
lean_inc(v_traceMsgs_2223_);
v_expandedMacroDecls_2224_ = lean_ctor_get(v_a_2220_, 2);
lean_inc(v_expandedMacroDecls_2224_);
lean_dec(v_a_2220_);
v___x_2225_ = lean_box(0);
v___x_2226_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_expandedMacroDecls_2224_, v___x_2225_, v___y_2182_, v___y_2183_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v___x_2227_; lean_object* v_env_2228_; lean_object* v_messages_2229_; lean_object* v_scopes_2230_; lean_object* v_usedQuotCtxts_2231_; lean_object* v_maxRecDepth_2232_; lean_object* v_ngen_2233_; lean_object* v_auxDeclNGen_2234_; lean_object* v_infoState_2235_; lean_object* v_traceState_2236_; lean_object* v_snapshotTasks_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2263_; 
lean_dec_ref(v___x_2226_);
v___x_2227_ = lean_st_ref_take(v___y_2183_);
v_env_2228_ = lean_ctor_get(v___x_2227_, 0);
v_messages_2229_ = lean_ctor_get(v___x_2227_, 1);
v_scopes_2230_ = lean_ctor_get(v___x_2227_, 2);
v_usedQuotCtxts_2231_ = lean_ctor_get(v___x_2227_, 3);
v_maxRecDepth_2232_ = lean_ctor_get(v___x_2227_, 5);
v_ngen_2233_ = lean_ctor_get(v___x_2227_, 6);
v_auxDeclNGen_2234_ = lean_ctor_get(v___x_2227_, 7);
v_infoState_2235_ = lean_ctor_get(v___x_2227_, 8);
v_traceState_2236_ = lean_ctor_get(v___x_2227_, 9);
v_snapshotTasks_2237_ = lean_ctor_get(v___x_2227_, 10);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2263_ == 0)
{
lean_object* v_unused_2264_; 
v_unused_2264_ = lean_ctor_get(v___x_2227_, 4);
lean_dec(v_unused_2264_);
v___x_2239_ = v___x_2227_;
v_isShared_2240_ = v_isSharedCheck_2263_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_snapshotTasks_2237_);
lean_inc(v_traceState_2236_);
lean_inc(v_infoState_2235_);
lean_inc(v_auxDeclNGen_2234_);
lean_inc(v_ngen_2233_);
lean_inc(v_maxRecDepth_2232_);
lean_inc(v_usedQuotCtxts_2231_);
lean_inc(v_scopes_2230_);
lean_inc(v_messages_2229_);
lean_inc(v_env_2228_);
lean_dec(v___x_2227_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2263_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 4, v_macroScope_2222_);
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_env_2228_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_messages_2229_);
lean_ctor_set(v_reuseFailAlloc_2262_, 2, v_scopes_2230_);
lean_ctor_set(v_reuseFailAlloc_2262_, 3, v_usedQuotCtxts_2231_);
lean_ctor_set(v_reuseFailAlloc_2262_, 4, v_macroScope_2222_);
lean_ctor_set(v_reuseFailAlloc_2262_, 5, v_maxRecDepth_2232_);
lean_ctor_set(v_reuseFailAlloc_2262_, 6, v_ngen_2233_);
lean_ctor_set(v_reuseFailAlloc_2262_, 7, v_auxDeclNGen_2234_);
lean_ctor_set(v_reuseFailAlloc_2262_, 8, v_infoState_2235_);
lean_ctor_set(v_reuseFailAlloc_2262_, 9, v_traceState_2236_);
lean_ctor_set(v_reuseFailAlloc_2262_, 10, v_snapshotTasks_2237_);
v___x_2242_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_st_ref_set(v___y_2183_, v___x_2242_);
v___x_2244_ = l_List_reverse___redArg(v_traceMsgs_2223_);
v___x_2245_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v___x_2244_, v___y_2182_, v___y_2183_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2252_ == 0)
{
lean_object* v_unused_2253_; 
v_unused_2253_ = lean_ctor_get(v___x_2245_, 0);
lean_dec(v_unused_2253_);
v___x_2247_ = v___x_2245_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_dec(v___x_2245_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v_a_2221_);
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2221_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v_a_2221_);
v_a_2254_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2245_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2245_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec(v_traceMsgs_2223_);
lean_dec(v_macroScope_2222_);
lean_dec(v_a_2221_);
v_a_2265_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2226_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2226_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
else
{
lean_object* v_a_2273_; 
v_a_2273_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2273_);
lean_dec_ref(v___x_2219_);
if (lean_obj_tag(v_a_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v_a_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
v_a_2274_ = lean_ctor_get(v_a_2273_, 0);
lean_inc(v_a_2274_);
v_a_2275_ = lean_ctor_get(v_a_2273_, 1);
lean_inc_ref(v_a_2275_);
lean_dec_ref(v_a_2273_);
v___x_2276_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0));
v___x_2277_ = lean_string_dec_eq(v_a_2275_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2278_, 0, v_a_2275_);
v___x_2279_ = l_Lean_MessageData_ofFormat(v___x_2278_);
v___x_2280_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_a_2274_, v___x_2279_, v___y_2182_, v___y_2183_);
lean_dec(v_a_2274_);
return v___x_2280_;
}
else
{
lean_object* v___x_2281_; 
lean_dec_ref(v_a_2275_);
v___x_2281_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_a_2274_);
return v___x_2281_;
}
}
else
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2282_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_a_2199_);
lean_dec(v_openDecls_2197_);
lean_dec(v_currNamespace_2194_);
lean_dec_ref(v_opts_2191_);
lean_dec_ref(v_env_2186_);
lean_dec_ref(v_x_2181_);
v_a_2286_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2200_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2200_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec(v_openDecls_2197_);
lean_dec(v_currNamespace_2194_);
lean_dec_ref(v_opts_2191_);
lean_dec_ref(v_env_2186_);
lean_dec_ref(v_x_2181_);
v_a_2294_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2198_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2198_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec(v_currNamespace_2194_);
lean_dec_ref(v_opts_2191_);
lean_dec_ref(v_env_2186_);
lean_dec_ref(v_x_2181_);
v_a_2302_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2195_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2195_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_opts_2191_);
lean_dec_ref(v_env_2186_);
lean_dec_ref(v_x_2181_);
v_a_2310_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2192_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2192_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___boxed(lean_object* v_x_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(lean_object* v_as_2323_, size_t v_i_2324_, size_t v_stop_2325_, lean_object* v_b_2326_){
_start:
{
lean_object* v___y_2328_; uint8_t v___x_2332_; 
v___x_2332_ = lean_usize_dec_eq(v_i_2324_, v_stop_2325_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2333_ = lean_array_uget_borrowed(v_as_2323_, v_i_2324_);
lean_inc(v___x_2333_);
v___x_2334_ = l_Lean_Syntax_getKind(v___x_2333_);
v___x_2335_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
v___x_2336_ = lean_name_eq(v___x_2334_, v___x_2335_);
lean_dec(v___x_2334_);
if (v___x_2336_ == 0)
{
v___y_2328_ = v_b_2326_;
goto v___jp_2327_;
}
else
{
lean_object* v___x_2337_; 
lean_inc(v___x_2333_);
v___x_2337_ = lean_array_push(v_b_2326_, v___x_2333_);
v___y_2328_ = v___x_2337_;
goto v___jp_2327_;
}
}
else
{
return v_b_2326_;
}
v___jp_2327_:
{
size_t v___x_2329_; size_t v___x_2330_; 
v___x_2329_ = ((size_t)1ULL);
v___x_2330_ = lean_usize_add(v_i_2324_, v___x_2329_);
v_i_2324_ = v___x_2330_;
v_b_2326_ = v___y_2328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8___boxed(lean_object* v_as_2338_, lean_object* v_i_2339_, lean_object* v_stop_2340_, lean_object* v_b_2341_){
_start:
{
size_t v_i_boxed_2342_; size_t v_stop_boxed_2343_; lean_object* v_res_2344_; 
v_i_boxed_2342_ = lean_unbox_usize(v_i_2339_);
lean_dec(v_i_2339_);
v_stop_boxed_2343_ = lean_unbox_usize(v_stop_2340_);
lean_dec(v_stop_2340_);
v_res_2344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v_as_2338_, v_i_boxed_2342_, v_stop_boxed_2343_, v_b_2341_);
lean_dec_ref(v_as_2338_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation(lean_object* v_x_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2476_; lean_object* v___y_2477_; uint8_t v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; size_t v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; 
v___x_2418_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0));
v___x_2419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1));
v___x_2420_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
lean_inc(v_x_2387_);
v___x_2421_ = l_Lean_Syntax_isOfKind(v_x_2387_, v___x_2420_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2530_; 
lean_dec(v_x_2387_);
v___x_2530_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2530_;
}
else
{
lean_object* v___x_2531_; lean_object* v___y_2533_; lean_object* v___y_2534_; uint8_t v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; size_t v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2607_; lean_object* v___y_2608_; uint8_t v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; size_t v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2643_; lean_object* v___y_2644_; uint8_t v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; size_t v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2674_; lean_object* v___y_2675_; uint8_t v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; size_t v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2709_; lean_object* v___y_2710_; uint8_t v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; size_t v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v_prio_x3f_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v_name_x3f_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v_prec_x3f_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v_attrs_x3f_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v_doc_x3f_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2531_ = lean_unsigned_to_nat(0u);
v___x_2886_ = l_Lean_Syntax_getArg(v_x_2387_, v___x_2531_);
v___x_2887_ = l_Lean_Syntax_isNone(v___x_2886_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2888_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2886_);
v___x_2889_ = l_Lean_Syntax_matchesNull(v___x_2886_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; 
lean_dec(v___x_2886_);
lean_dec(v_x_2387_);
v___x_2890_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2890_;
}
else
{
lean_object* v_doc_x3f_2891_; lean_object* v___x_2892_; uint8_t v___x_2893_; 
v_doc_x3f_2891_ = l_Lean_Syntax_getArg(v___x_2886_, v___x_2531_);
lean_dec(v___x_2886_);
v___x_2892_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__15));
lean_inc(v_doc_x3f_2891_);
v___x_2893_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2891_, v___x_2892_);
if (v___x_2893_ == 0)
{
lean_object* v___x_2894_; 
lean_dec(v_doc_x3f_2891_);
lean_dec(v_x_2387_);
v___x_2894_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2894_;
}
else
{
lean_object* v___x_2895_; 
v___x_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2895_, 0, v_doc_x3f_2891_);
v_doc_x3f_2870_ = v___x_2895_;
v___y_2871_ = v_a_2388_;
v___y_2872_ = v_a_2389_;
goto v___jp_2869_;
}
}
}
else
{
lean_object* v___x_2896_; 
lean_dec(v___x_2886_);
v___x_2896_ = lean_box(0);
v_doc_x3f_2870_ = v___x_2896_;
v___y_2871_ = v_a_2388_;
v___y_2872_ = v_a_2389_;
goto v___jp_2869_;
}
v___jp_2532_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; size_t v_sz_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_inc_ref_n(v___y_2536_, 2);
v___x_2553_ = l_Array_append___redArg(v___y_2536_, v___y_2552_);
lean_dec_ref(v___y_2552_);
lean_inc_n(v___y_2540_, 3);
lean_inc_n(v___y_2538_, 9);
v___x_2554_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2554_, 0, v___y_2538_);
lean_ctor_set(v___x_2554_, 1, v___y_2540_);
lean_ctor_set(v___x_2554_, 2, v___x_2553_);
v___x_2555_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
v___x_2556_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
v___x_2557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___y_2538_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__8));
v___x_2559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___y_2538_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_2561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___y_2538_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = l_Nat_reprFast(v___y_2533_);
v___x_2563_ = lean_box(2);
v___x_2564_ = l_Lean_Syntax_mkNumLit(v___x_2562_, v___x_2563_);
v___x_2565_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_2566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___y_2538_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = l_Lean_Syntax_node5(v___y_2538_, v___x_2555_, v___x_2557_, v___x_2559_, v___x_2561_, v___x_2564_, v___x_2566_);
v___x_2568_ = l_Lean_Syntax_node1(v___y_2538_, v___y_2540_, v___x_2567_);
v_sz_2569_ = lean_array_size(v___y_2548_);
v___x_2570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_2569_, v___y_2543_, v___y_2548_);
v___x_2571_ = l_Array_append___redArg(v___y_2536_, v___x_2570_);
lean_dec_ref(v___x_2570_);
v___x_2572_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2572_, 0, v___y_2538_);
lean_ctor_set(v___x_2572_, 1, v___y_2540_);
lean_ctor_set(v___x_2572_, 2, v___x_2571_);
v___x_2573_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
v___x_2574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___y_2538_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = lean_unsigned_to_nat(10u);
v___x_2576_ = lean_mk_empty_array_with_capacity(v___x_2575_);
v___x_2577_ = lean_array_push(v___x_2576_, v___y_2547_);
v___x_2578_ = lean_array_push(v___x_2577_, v___y_2549_);
lean_inc(v___y_2551_);
v___x_2579_ = lean_array_push(v___x_2578_, v___y_2551_);
v___x_2580_ = lean_array_push(v___x_2579_, v___y_2537_);
v___x_2581_ = lean_array_push(v___x_2580_, v___y_2541_);
v___x_2582_ = lean_array_push(v___x_2581_, v___x_2554_);
v___x_2583_ = lean_array_push(v___x_2582_, v___x_2568_);
v___x_2584_ = lean_array_push(v___x_2583_, v___x_2572_);
v___x_2585_ = lean_array_push(v___x_2584_, v___x_2574_);
v___x_2586_ = lean_array_push(v___x_2585_, v___y_2550_);
lean_inc(v___y_2545_);
v___x_2587_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2587_, 0, v___y_2538_);
lean_ctor_set(v___x_2587_, 1, v___y_2545_);
lean_ctor_set(v___x_2587_, 2, v___x_2586_);
v___x_2588_ = l_Lean_Elab_Command_elabSyntax(v___x_2587_, v___y_2542_, v___y_2544_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref(v___x_2588_);
v___x_2590_ = lean_array_get_size(v___y_2546_);
v___x_2591_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__68));
v___x_2592_ = lean_nat_dec_lt(v___x_2531_, v___x_2590_);
if (v___x_2592_ == 0)
{
v___y_2476_ = v_a_2589_;
v___y_2477_ = v___y_2534_;
v___y_2478_ = v___y_2535_;
v___y_2479_ = v___y_2536_;
v___y_2480_ = v___x_2565_;
v___y_2481_ = v___y_2540_;
v___y_2482_ = v___y_2539_;
v___y_2483_ = v___x_2563_;
v___y_2484_ = v___y_2542_;
v___y_2485_ = v___y_2543_;
v___y_2486_ = v___y_2544_;
v___y_2487_ = v___y_2546_;
v___y_2488_ = v___y_2551_;
v___y_2489_ = v___x_2591_;
goto v___jp_2475_;
}
else
{
uint8_t v___x_2593_; 
v___x_2593_ = lean_nat_dec_le(v___x_2590_, v___x_2590_);
if (v___x_2593_ == 0)
{
if (v___x_2592_ == 0)
{
v___y_2476_ = v_a_2589_;
v___y_2477_ = v___y_2534_;
v___y_2478_ = v___y_2535_;
v___y_2479_ = v___y_2536_;
v___y_2480_ = v___x_2565_;
v___y_2481_ = v___y_2540_;
v___y_2482_ = v___y_2539_;
v___y_2483_ = v___x_2563_;
v___y_2484_ = v___y_2542_;
v___y_2485_ = v___y_2543_;
v___y_2486_ = v___y_2544_;
v___y_2487_ = v___y_2546_;
v___y_2488_ = v___y_2551_;
v___y_2489_ = v___x_2591_;
goto v___jp_2475_;
}
else
{
size_t v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = lean_usize_of_nat(v___x_2590_);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2546_, v___y_2543_, v___x_2594_, v___x_2591_);
v___y_2476_ = v_a_2589_;
v___y_2477_ = v___y_2534_;
v___y_2478_ = v___y_2535_;
v___y_2479_ = v___y_2536_;
v___y_2480_ = v___x_2565_;
v___y_2481_ = v___y_2540_;
v___y_2482_ = v___y_2539_;
v___y_2483_ = v___x_2563_;
v___y_2484_ = v___y_2542_;
v___y_2485_ = v___y_2543_;
v___y_2486_ = v___y_2544_;
v___y_2487_ = v___y_2546_;
v___y_2488_ = v___y_2551_;
v___y_2489_ = v___x_2595_;
goto v___jp_2475_;
}
}
else
{
size_t v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_usize_of_nat(v___x_2590_);
v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2546_, v___y_2543_, v___x_2596_, v___x_2591_);
v___y_2476_ = v_a_2589_;
v___y_2477_ = v___y_2534_;
v___y_2478_ = v___y_2535_;
v___y_2479_ = v___y_2536_;
v___y_2480_ = v___x_2565_;
v___y_2481_ = v___y_2540_;
v___y_2482_ = v___y_2539_;
v___y_2483_ = v___x_2563_;
v___y_2484_ = v___y_2542_;
v___y_2485_ = v___y_2543_;
v___y_2486_ = v___y_2544_;
v___y_2487_ = v___y_2546_;
v___y_2488_ = v___y_2551_;
v___y_2489_ = v___x_2597_;
goto v___jp_2475_;
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2539_);
v_a_2598_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2588_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2588_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
v___jp_2606_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
lean_inc_ref(v___y_2610_);
v___x_2627_ = l_Array_append___redArg(v___y_2610_, v___y_2626_);
lean_dec_ref(v___y_2626_);
lean_inc(v___y_2613_);
lean_inc(v___y_2612_);
v___x_2628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2628_, 0, v___y_2612_);
lean_ctor_set(v___x_2628_, 1, v___y_2613_);
lean_ctor_set(v___x_2628_, 2, v___x_2627_);
if (lean_obj_tag(v___y_2617_) == 1)
{
lean_object* v_val_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v_val_2629_ = lean_ctor_get(v___y_2617_, 0);
lean_inc(v_val_2629_);
lean_dec_ref(v___y_2617_);
v___x_2630_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
v___x_2631_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc_n(v___y_2612_, 5);
v___x_2632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___y_2612_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__11));
v___x_2634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___y_2612_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_2636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___y_2612_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
v___x_2637_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_2638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___y_2612_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = l_Lean_Syntax_node5(v___y_2612_, v___x_2630_, v___x_2632_, v___x_2634_, v___x_2636_, v_val_2629_, v___x_2638_);
v___x_2640_ = l_Array_mkArray1___redArg(v___x_2639_);
v___y_2533_ = v___y_2607_;
v___y_2534_ = v___y_2608_;
v___y_2535_ = v___y_2609_;
v___y_2536_ = v___y_2610_;
v___y_2537_ = v___y_2611_;
v___y_2538_ = v___y_2612_;
v___y_2539_ = v___y_2614_;
v___y_2540_ = v___y_2613_;
v___y_2541_ = v___x_2628_;
v___y_2542_ = v___y_2615_;
v___y_2543_ = v___y_2616_;
v___y_2544_ = v___y_2618_;
v___y_2545_ = v___y_2619_;
v___y_2546_ = v___y_2620_;
v___y_2547_ = v___y_2621_;
v___y_2548_ = v___y_2624_;
v___y_2549_ = v___y_2623_;
v___y_2550_ = v___y_2622_;
v___y_2551_ = v___y_2625_;
v___y_2552_ = v___x_2640_;
goto v___jp_2532_;
}
else
{
lean_object* v___x_2641_; 
lean_dec(v___y_2617_);
v___x_2641_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2533_ = v___y_2607_;
v___y_2534_ = v___y_2608_;
v___y_2535_ = v___y_2609_;
v___y_2536_ = v___y_2610_;
v___y_2537_ = v___y_2611_;
v___y_2538_ = v___y_2612_;
v___y_2539_ = v___y_2614_;
v___y_2540_ = v___y_2613_;
v___y_2541_ = v___x_2628_;
v___y_2542_ = v___y_2615_;
v___y_2543_ = v___y_2616_;
v___y_2544_ = v___y_2618_;
v___y_2545_ = v___y_2619_;
v___y_2546_ = v___y_2620_;
v___y_2547_ = v___y_2621_;
v___y_2548_ = v___y_2624_;
v___y_2549_ = v___y_2623_;
v___y_2550_ = v___y_2622_;
v___y_2551_ = v___y_2625_;
v___y_2552_ = v___x_2641_;
goto v___jp_2532_;
}
}
v___jp_2642_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
lean_inc_ref(v___y_2646_);
v___x_2663_ = l_Array_append___redArg(v___y_2646_, v___y_2662_);
lean_dec_ref(v___y_2662_);
lean_inc(v___y_2649_);
lean_inc_n(v___y_2648_, 2);
v___x_2664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2664_, 0, v___y_2648_);
lean_ctor_set(v___x_2664_, 1, v___y_2649_);
lean_ctor_set(v___x_2664_, 2, v___x_2663_);
lean_inc_ref(v___y_2653_);
v___x_2665_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___y_2648_);
lean_ctor_set(v___x_2665_, 1, v___y_2653_);
if (lean_obj_tag(v___y_2647_) == 1)
{
lean_object* v_val_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_val_2666_ = lean_ctor_get(v___y_2647_, 0);
lean_inc(v_val_2666_);
lean_dec_ref(v___y_2647_);
v___x_2667_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
v___x_2668_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc_n(v___y_2648_, 2);
v___x_2669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___y_2648_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = l_Lean_Syntax_node2(v___y_2648_, v___x_2667_, v___x_2669_, v_val_2666_);
v___x_2671_ = l_Array_mkArray1___redArg(v___x_2670_);
v___y_2607_ = v___y_2643_;
v___y_2608_ = v___y_2644_;
v___y_2609_ = v___y_2645_;
v___y_2610_ = v___y_2646_;
v___y_2611_ = v___x_2665_;
v___y_2612_ = v___y_2648_;
v___y_2613_ = v___y_2649_;
v___y_2614_ = v___y_2650_;
v___y_2615_ = v___y_2651_;
v___y_2616_ = v___y_2652_;
v___y_2617_ = v___y_2655_;
v___y_2618_ = v___y_2656_;
v___y_2619_ = v___y_2654_;
v___y_2620_ = v___y_2657_;
v___y_2621_ = v___y_2658_;
v___y_2622_ = v___y_2660_;
v___y_2623_ = v___x_2664_;
v___y_2624_ = v___y_2659_;
v___y_2625_ = v___y_2661_;
v___y_2626_ = v___x_2671_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2672_; 
lean_dec(v___y_2647_);
v___x_2672_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2607_ = v___y_2643_;
v___y_2608_ = v___y_2644_;
v___y_2609_ = v___y_2645_;
v___y_2610_ = v___y_2646_;
v___y_2611_ = v___x_2665_;
v___y_2612_ = v___y_2648_;
v___y_2613_ = v___y_2649_;
v___y_2614_ = v___y_2650_;
v___y_2615_ = v___y_2651_;
v___y_2616_ = v___y_2652_;
v___y_2617_ = v___y_2655_;
v___y_2618_ = v___y_2656_;
v___y_2619_ = v___y_2654_;
v___y_2620_ = v___y_2657_;
v___y_2621_ = v___y_2658_;
v___y_2622_ = v___y_2660_;
v___y_2623_ = v___x_2664_;
v___y_2624_ = v___y_2659_;
v___y_2625_ = v___y_2661_;
v___y_2626_ = v___x_2672_;
goto v___jp_2606_;
}
}
v___jp_2673_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
lean_inc_ref(v___y_2677_);
v___x_2694_ = l_Array_append___redArg(v___y_2677_, v___y_2693_);
lean_dec_ref(v___y_2693_);
lean_inc(v___y_2681_);
lean_inc(v___y_2679_);
v___x_2695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2695_, 0, v___y_2679_);
lean_ctor_set(v___x_2695_, 1, v___y_2681_);
lean_ctor_set(v___x_2695_, 2, v___x_2694_);
if (lean_obj_tag(v___y_2678_) == 1)
{
lean_object* v_val_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v_val_2696_ = lean_ctor_get(v___y_2678_, 0);
lean_inc(v_val_2696_);
lean_dec_ref(v___y_2678_);
v___x_2697_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__11));
lean_inc_ref(v___y_2675_);
v___x_2698_ = l_Lean_Name_mkStr4(v___x_2418_, v___x_2419_, v___y_2675_, v___x_2697_);
v___x_2699_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc_n(v___y_2679_, 4);
v___x_2700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___y_2679_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
lean_inc_ref(v___y_2677_);
v___x_2701_ = l_Array_append___redArg(v___y_2677_, v_val_2696_);
lean_dec(v_val_2696_);
lean_inc(v___y_2681_);
v___x_2702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2702_, 0, v___y_2679_);
lean_ctor_set(v___x_2702_, 1, v___y_2681_);
lean_ctor_set(v___x_2702_, 2, v___x_2701_);
v___x_2703_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
v___x_2704_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___y_2679_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = l_Lean_Syntax_node3(v___y_2679_, v___x_2698_, v___x_2700_, v___x_2702_, v___x_2704_);
v___x_2706_ = l_Array_mkArray1___redArg(v___x_2705_);
v___y_2643_ = v___y_2674_;
v___y_2644_ = v___y_2675_;
v___y_2645_ = v___y_2676_;
v___y_2646_ = v___y_2677_;
v___y_2647_ = v___y_2680_;
v___y_2648_ = v___y_2679_;
v___y_2649_ = v___y_2681_;
v___y_2650_ = v___y_2682_;
v___y_2651_ = v___y_2683_;
v___y_2652_ = v___y_2684_;
v___y_2653_ = v___y_2685_;
v___y_2654_ = v___y_2688_;
v___y_2655_ = v___y_2687_;
v___y_2656_ = v___y_2686_;
v___y_2657_ = v___y_2689_;
v___y_2658_ = v___x_2695_;
v___y_2659_ = v___y_2691_;
v___y_2660_ = v___y_2690_;
v___y_2661_ = v___y_2692_;
v___y_2662_ = v___x_2706_;
goto v___jp_2642_;
}
else
{
lean_object* v___x_2707_; 
lean_dec(v___y_2678_);
v___x_2707_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2643_ = v___y_2674_;
v___y_2644_ = v___y_2675_;
v___y_2645_ = v___y_2676_;
v___y_2646_ = v___y_2677_;
v___y_2647_ = v___y_2680_;
v___y_2648_ = v___y_2679_;
v___y_2649_ = v___y_2681_;
v___y_2650_ = v___y_2682_;
v___y_2651_ = v___y_2683_;
v___y_2652_ = v___y_2684_;
v___y_2653_ = v___y_2685_;
v___y_2654_ = v___y_2688_;
v___y_2655_ = v___y_2687_;
v___y_2656_ = v___y_2686_;
v___y_2657_ = v___y_2689_;
v___y_2658_ = v___x_2695_;
v___y_2659_ = v___y_2691_;
v___y_2660_ = v___y_2690_;
v___y_2661_ = v___y_2692_;
v___y_2662_ = v___x_2707_;
goto v___jp_2642_;
}
}
v___jp_2708_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2725_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__12));
v___x_2726_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__13));
v___x_2727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_2728_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
if (lean_obj_tag(v___y_2713_) == 1)
{
lean_object* v_val_2729_; lean_object* v___x_2730_; 
v_val_2729_ = lean_ctor_get(v___y_2713_, 0);
lean_inc(v_val_2729_);
lean_dec_ref(v___y_2713_);
v___x_2730_ = l_Array_mkArray1___redArg(v_val_2729_);
v___y_2674_ = v___y_2709_;
v___y_2675_ = v___y_2710_;
v___y_2676_ = v___y_2711_;
v___y_2677_ = v___x_2728_;
v___y_2678_ = v___y_2712_;
v___y_2679_ = v___y_2714_;
v___y_2680_ = v___y_2715_;
v___y_2681_ = v___x_2727_;
v___y_2682_ = v___y_2716_;
v___y_2683_ = v___y_2717_;
v___y_2684_ = v___y_2718_;
v___y_2685_ = v___x_2725_;
v___y_2686_ = v___y_2719_;
v___y_2687_ = v___y_2720_;
v___y_2688_ = v___x_2726_;
v___y_2689_ = v___y_2721_;
v___y_2690_ = v___y_2723_;
v___y_2691_ = v___y_2722_;
v___y_2692_ = v___y_2724_;
v___y_2693_ = v___x_2730_;
goto v___jp_2673_;
}
else
{
lean_object* v___x_2731_; 
lean_dec(v___y_2713_);
v___x_2731_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2674_ = v___y_2709_;
v___y_2675_ = v___y_2710_;
v___y_2676_ = v___y_2711_;
v___y_2677_ = v___x_2728_;
v___y_2678_ = v___y_2712_;
v___y_2679_ = v___y_2714_;
v___y_2680_ = v___y_2715_;
v___y_2681_ = v___x_2727_;
v___y_2682_ = v___y_2716_;
v___y_2683_ = v___y_2717_;
v___y_2684_ = v___y_2718_;
v___y_2685_ = v___x_2725_;
v___y_2686_ = v___y_2719_;
v___y_2687_ = v___y_2720_;
v___y_2688_ = v___x_2726_;
v___y_2689_ = v___y_2721_;
v___y_2690_ = v___y_2723_;
v___y_2691_ = v___y_2722_;
v___y_2692_ = v___y_2724_;
v___y_2693_ = v___x_2731_;
goto v___jp_2673_;
}
}
v___jp_2732_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_2742_, 0, v_prio_x3f_2739_);
v___x_2743_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2742_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v_items_2747_; size_t v_sz_2748_; size_t v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec_ref(v___x_2743_);
v___x_2745_ = lean_unsigned_to_nat(7u);
v___x_2746_ = l_Lean_Syntax_getArg(v_x_2387_, v___x_2745_);
v_items_2747_ = l_Lean_Syntax_getArgs(v___x_2746_);
lean_dec(v___x_2746_);
v_sz_2748_ = lean_array_size(v_items_2747_);
v___x_2749_ = ((size_t)0ULL);
v___x_2750_ = lean_box_usize(v_sz_2748_);
v___x_2751_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___boxed__const__1));
lean_inc_ref(v_items_2747_);
v___x_2752_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed), 5, 3);
lean_closure_set(v___x_2752_, 0, v___x_2750_);
lean_closure_set(v___x_2752_, 1, v___x_2751_);
lean_closure_set(v___x_2752_, 2, v_items_2747_);
v___x_2753_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2752_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2755_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref(v___x_2753_);
v___x_2755_ = l_Lean_Elab_Command_getRef___redArg(v___y_2740_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2757_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref(v___x_2755_);
v___x_2757_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2740_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_quotContext_x3f_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v_rhs_2763_; lean_object* v_attrs_x3f_2764_; lean_object* v___x_2765_; 
lean_dec_ref(v___x_2757_);
v_quotContext_x3f_2758_ = lean_ctor_get(v___y_2740_, 5);
v___x_2759_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
v___x_2760_ = 0;
v___x_2761_ = l_Lean_mkIdentFrom(v_x_2387_, v___x_2759_, v___x_2760_);
v___x_2762_ = lean_unsigned_to_nat(9u);
v_rhs_2763_ = l_Lean_Syntax_getArg(v_x_2387_, v___x_2762_);
lean_dec(v_x_2387_);
lean_inc(v_rhs_2763_);
v_attrs_x3f_2764_ = l_Lean_Elab_Command_addInheritDocDefault(v_rhs_2763_, v___y_2738_);
v___x_2765_ = l_Lean_SourceInfo_fromRef(v_a_2756_, v___x_2760_);
lean_dec(v_a_2756_);
if (lean_obj_tag(v_quotContext_x3f_2758_) == 0)
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2741_);
lean_dec_ref(v___x_2766_);
v___y_2709_ = v_a_2744_;
v___y_2710_ = v___y_2734_;
v___y_2711_ = v___x_2760_;
v___y_2712_ = v_attrs_x3f_2764_;
v___y_2713_ = v___y_2736_;
v___y_2714_ = v___x_2765_;
v___y_2715_ = v___y_2735_;
v___y_2716_ = v_rhs_2763_;
v___y_2717_ = v___y_2740_;
v___y_2718_ = v___x_2749_;
v___y_2719_ = v___y_2741_;
v___y_2720_ = v___y_2733_;
v___y_2721_ = v_items_2747_;
v___y_2722_ = v_a_2754_;
v___y_2723_ = v___x_2761_;
v___y_2724_ = v___y_2737_;
goto v___jp_2708_;
}
else
{
v___y_2709_ = v_a_2744_;
v___y_2710_ = v___y_2734_;
v___y_2711_ = v___x_2760_;
v___y_2712_ = v_attrs_x3f_2764_;
v___y_2713_ = v___y_2736_;
v___y_2714_ = v___x_2765_;
v___y_2715_ = v___y_2735_;
v___y_2716_ = v_rhs_2763_;
v___y_2717_ = v___y_2740_;
v___y_2718_ = v___x_2749_;
v___y_2719_ = v___y_2741_;
v___y_2720_ = v___y_2733_;
v___y_2721_ = v_items_2747_;
v___y_2722_ = v_a_2754_;
v___y_2723_ = v___x_2761_;
v___y_2724_ = v___y_2737_;
goto v___jp_2708_;
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v_a_2756_);
lean_dec(v_a_2754_);
lean_dec_ref(v_items_2747_);
lean_dec(v_a_2744_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v___y_2733_);
lean_dec(v_x_2387_);
v_a_2767_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2757_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2757_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec(v_a_2754_);
lean_dec_ref(v_items_2747_);
lean_dec(v_a_2744_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v___y_2733_);
lean_dec(v_x_2387_);
v_a_2775_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2755_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2755_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_dec_ref(v_items_2747_);
lean_dec(v_a_2744_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v___y_2733_);
lean_dec(v_x_2387_);
v_a_2783_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2753_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2753_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
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
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v___y_2733_);
lean_dec(v_x_2387_);
v_a_2791_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2743_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2743_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
v___jp_2799_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2810_ = lean_unsigned_to_nat(6u);
v___x_2811_ = l_Lean_Syntax_getArg(v_x_2387_, v___x_2810_);
v___x_2812_ = l_Lean_Syntax_isNone(v___x_2811_);
if (v___x_2812_ == 0)
{
uint8_t v___x_2813_; 
lean_inc(v___x_2811_);
v___x_2813_ = l_Lean_Syntax_matchesNull(v___x_2811_, v___y_2804_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; 
lean_dec(v___x_2811_);
lean_dec(v_name_x3f_2807_);
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec(v_x_2387_);
v___x_2814_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2814_;
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2815_ = l_Lean_Syntax_getArg(v___x_2811_, v___x_2531_);
lean_dec(v___x_2811_);
v___x_2816_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
lean_inc(v___x_2815_);
v___x_2817_ = l_Lean_Syntax_isOfKind(v___x_2815_, v___x_2816_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; 
lean_dec(v___x_2815_);
lean_dec(v_name_x3f_2807_);
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec(v_x_2387_);
v___x_2818_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2818_;
}
else
{
lean_object* v_prio_x3f_2819_; lean_object* v___x_2820_; 
v_prio_x3f_2819_ = l_Lean_Syntax_getArg(v___x_2815_, v___y_2800_);
lean_dec(v___x_2815_);
v___x_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2820_, 0, v_prio_x3f_2819_);
v___y_2733_ = v_name_x3f_2807_;
v___y_2734_ = v___y_2801_;
v___y_2735_ = v___y_2803_;
v___y_2736_ = v___y_2802_;
v___y_2737_ = v___y_2805_;
v___y_2738_ = v___y_2806_;
v_prio_x3f_2739_ = v___x_2820_;
v___y_2740_ = v___y_2808_;
v___y_2741_ = v___y_2809_;
goto v___jp_2732_;
}
}
}
else
{
lean_object* v___x_2821_; 
lean_dec(v___x_2811_);
v___x_2821_ = lean_box(0);
v___y_2733_ = v_name_x3f_2807_;
v___y_2734_ = v___y_2801_;
v___y_2735_ = v___y_2803_;
v___y_2736_ = v___y_2802_;
v___y_2737_ = v___y_2805_;
v___y_2738_ = v___y_2806_;
v_prio_x3f_2739_ = v___x_2821_;
v___y_2740_ = v___y_2808_;
v___y_2741_ = v___y_2809_;
goto v___jp_2732_;
}
}
v___jp_2822_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
v___x_2832_ = lean_unsigned_to_nat(5u);
v___x_2833_ = l_Lean_Syntax_getArg(v_x_2387_, v___x_2832_);
v___x_2834_ = l_Lean_Syntax_isNone(v___x_2833_);
if (v___x_2834_ == 0)
{
uint8_t v___x_2835_; 
lean_inc(v___x_2833_);
v___x_2835_ = l_Lean_Syntax_matchesNull(v___x_2833_, v___y_2827_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; 
lean_dec(v___x_2833_);
lean_dec(v_prec_x3f_2829_);
lean_dec(v___y_2828_);
lean_dec(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec(v_x_2387_);
v___x_2836_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2836_;
}
else
{
lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2837_ = l_Lean_Syntax_getArg(v___x_2833_, v___x_2531_);
lean_dec(v___x_2833_);
v___x_2838_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
lean_inc(v___x_2837_);
v___x_2839_ = l_Lean_Syntax_isOfKind(v___x_2837_, v___x_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; 
lean_dec(v___x_2837_);
lean_dec(v_prec_x3f_2829_);
lean_dec(v___y_2828_);
lean_dec(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec(v_x_2387_);
v___x_2840_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2840_;
}
else
{
lean_object* v_name_x3f_2841_; lean_object* v___x_2842_; 
v_name_x3f_2841_ = l_Lean_Syntax_getArg(v___x_2837_, v___y_2823_);
lean_dec(v___x_2837_);
v___x_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_name_x3f_2841_);
v___y_2800_ = v___y_2823_;
v___y_2801_ = v___y_2824_;
v___y_2802_ = v___y_2825_;
v___y_2803_ = v_prec_x3f_2829_;
v___y_2804_ = v___y_2827_;
v___y_2805_ = v___y_2826_;
v___y_2806_ = v___y_2828_;
v_name_x3f_2807_ = v___x_2842_;
v___y_2808_ = v___y_2830_;
v___y_2809_ = v___y_2831_;
goto v___jp_2799_;
}
}
}
else
{
lean_object* v___x_2843_; 
lean_dec(v___x_2833_);
v___x_2843_ = lean_box(0);
v___y_2800_ = v___y_2823_;
v___y_2801_ = v___y_2824_;
v___y_2802_ = v___y_2825_;
v___y_2803_ = v_prec_x3f_2829_;
v___y_2804_ = v___y_2827_;
v___y_2805_ = v___y_2826_;
v___y_2806_ = v___y_2828_;
v_name_x3f_2807_ = v___x_2843_;
v___y_2808_ = v___y_2830_;
v___y_2809_ = v___y_2831_;
goto v___jp_2799_;
}
}
v___jp_2844_:
{
lean_object* v___x_2850_; lean_object* v_attrKind_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v___x_2850_ = lean_unsigned_to_nat(2u);
v_attrKind_2851_ = l_Lean_Syntax_getArg(v_x_2387_, v___x_2850_);
v___x_2852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2));
v___x_2853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(v_attrKind_2851_);
v___x_2854_ = l_Lean_Syntax_isOfKind(v_attrKind_2851_, v___x_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_dec(v_attrKind_2851_);
lean_dec(v_attrs_x3f_2847_);
lean_dec(v___y_2845_);
lean_dec(v_x_2387_);
v___x_2855_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2855_;
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2856_ = lean_unsigned_to_nat(3u);
v___x_2857_ = lean_unsigned_to_nat(4u);
v___x_2858_ = l_Lean_Syntax_getArg(v_x_2387_, v___x_2857_);
v___x_2859_ = l_Lean_Syntax_isNone(v___x_2858_);
if (v___x_2859_ == 0)
{
uint8_t v___x_2860_; 
lean_inc(v___x_2858_);
v___x_2860_ = l_Lean_Syntax_matchesNull(v___x_2858_, v___y_2846_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; 
lean_dec(v___x_2858_);
lean_dec(v_attrKind_2851_);
lean_dec(v_attrs_x3f_2847_);
lean_dec(v___y_2845_);
lean_dec(v_x_2387_);
v___x_2861_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2861_;
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; 
v___x_2862_ = l_Lean_Syntax_getArg(v___x_2858_, v___x_2531_);
lean_dec(v___x_2858_);
v___x_2863_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
lean_inc(v___x_2862_);
v___x_2864_ = l_Lean_Syntax_isOfKind(v___x_2862_, v___x_2863_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; 
lean_dec(v___x_2862_);
lean_dec(v_attrKind_2851_);
lean_dec(v_attrs_x3f_2847_);
lean_dec(v___y_2845_);
lean_dec(v_x_2387_);
v___x_2865_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2865_;
}
else
{
lean_object* v_prec_x3f_2866_; lean_object* v___x_2867_; 
v_prec_x3f_2866_ = l_Lean_Syntax_getArg(v___x_2862_, v___y_2846_);
lean_dec(v___x_2862_);
v___x_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2867_, 0, v_prec_x3f_2866_);
v___y_2823_ = v___x_2856_;
v___y_2824_ = v___x_2852_;
v___y_2825_ = v___y_2845_;
v___y_2826_ = v_attrKind_2851_;
v___y_2827_ = v___y_2846_;
v___y_2828_ = v_attrs_x3f_2847_;
v_prec_x3f_2829_ = v___x_2867_;
v___y_2830_ = v___y_2848_;
v___y_2831_ = v___y_2849_;
goto v___jp_2822_;
}
}
}
else
{
lean_object* v___x_2868_; 
lean_dec(v___x_2858_);
v___x_2868_ = lean_box(0);
v___y_2823_ = v___x_2856_;
v___y_2824_ = v___x_2852_;
v___y_2825_ = v___y_2845_;
v___y_2826_ = v_attrKind_2851_;
v___y_2827_ = v___y_2846_;
v___y_2828_ = v_attrs_x3f_2847_;
v_prec_x3f_2829_ = v___x_2868_;
v___y_2830_ = v___y_2848_;
v___y_2831_ = v___y_2849_;
goto v___jp_2822_;
}
}
}
v___jp_2869_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2873_ = lean_unsigned_to_nat(1u);
v___x_2874_ = l_Lean_Syntax_getArg(v_x_2387_, v___x_2873_);
v___x_2875_ = l_Lean_Syntax_isNone(v___x_2874_);
if (v___x_2875_ == 0)
{
uint8_t v___x_2876_; 
lean_inc(v___x_2874_);
v___x_2876_ = l_Lean_Syntax_matchesNull(v___x_2874_, v___x_2873_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; 
lean_dec(v___x_2874_);
lean_dec(v_doc_x3f_2870_);
lean_dec(v_x_2387_);
v___x_2877_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2877_;
}
else
{
lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2878_ = l_Lean_Syntax_getArg(v___x_2874_, v___x_2531_);
lean_dec(v___x_2874_);
v___x_2879_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
lean_inc(v___x_2878_);
v___x_2880_ = l_Lean_Syntax_isOfKind(v___x_2878_, v___x_2879_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; 
lean_dec(v___x_2878_);
lean_dec(v_doc_x3f_2870_);
lean_dec(v_x_2387_);
v___x_2881_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2881_;
}
else
{
lean_object* v___x_2882_; lean_object* v_attrs_x3f_2883_; lean_object* v___x_2884_; 
v___x_2882_ = l_Lean_Syntax_getArg(v___x_2878_, v___x_2873_);
lean_dec(v___x_2878_);
v_attrs_x3f_2883_ = l_Lean_Syntax_getArgs(v___x_2882_);
lean_dec(v___x_2882_);
v___x_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2884_, 0, v_attrs_x3f_2883_);
v___y_2845_ = v_doc_x3f_2870_;
v___y_2846_ = v___x_2873_;
v_attrs_x3f_2847_ = v___x_2884_;
v___y_2848_ = v___y_2871_;
v___y_2849_ = v___y_2872_;
goto v___jp_2844_;
}
}
}
else
{
lean_object* v___x_2885_; 
lean_dec(v___x_2874_);
v___x_2885_ = lean_box(0);
v___y_2845_ = v_doc_x3f_2870_;
v___y_2846_ = v___x_2873_;
v_attrs_x3f_2847_ = v___x_2885_;
v___y_2848_ = v___y_2871_;
v___y_2849_ = v___y_2872_;
goto v___jp_2844_;
}
}
}
v___jp_2391_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkUnexpander___boxed), 5, 3);
lean_closure_set(v___x_2397_, 0, v___y_2394_);
lean_closure_set(v___x_2397_, 1, v___y_2393_);
lean_closure_set(v___x_2397_, 2, v___y_2392_);
v___x_2398_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2397_, v___y_2395_, v___y_2396_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2409_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2401_ = v___x_2398_;
v_isShared_2402_ = v_isSharedCheck_2409_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2398_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2409_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
if (lean_obj_tag(v_a_2399_) == 1)
{
lean_object* v_val_2403_; lean_object* v___x_2404_; 
lean_del_object(v___x_2401_);
v_val_2403_ = lean_ctor_get(v_a_2399_, 0);
lean_inc(v_val_2403_);
lean_dec_ref(v_a_2399_);
v___x_2404_ = l_Lean_Elab_Command_elabCommand(v_val_2403_, v___y_2395_, v___y_2396_);
return v___x_2404_;
}
else
{
lean_object* v___x_2405_; lean_object* v___x_2407_; 
lean_dec(v_a_2399_);
v___x_2405_ = lean_box(0);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v___x_2405_);
v___x_2407_ = v___x_2401_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
v_a_2410_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2398_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2398_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
v___jp_2422_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2433_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__2));
v___x_2434_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__3));
lean_inc_ref(v___y_2426_);
lean_inc_n(v___y_2429_, 4);
lean_inc_n(v___y_2427_, 15);
v___x_2435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2435_, 0, v___y_2427_);
lean_ctor_set(v___x_2435_, 1, v___y_2429_);
lean_ctor_set(v___x_2435_, 2, v___y_2426_);
v___x_2436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___y_2427_);
lean_ctor_set(v___x_2436_, 1, v___x_2433_);
v___x_2437_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__29));
lean_inc_ref_n(v___y_2424_, 4);
v___x_2438_ = l_Lean_Name_mkStr4(v___x_2418_, v___x_2419_, v___y_2424_, v___x_2437_);
v___x_2439_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__31));
v___x_2440_ = l_Lean_Name_mkStr4(v___x_2418_, v___x_2419_, v___y_2424_, v___x_2439_);
v___x_2441_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
v___x_2442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___y_2427_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__34));
v___x_2444_ = l_Lean_Name_mkStr4(v___x_2418_, v___x_2419_, v___y_2424_, v___x_2443_);
v___x_2445_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
v___x_2446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___y_2427_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
lean_inc_ref(v___y_2428_);
v___x_2447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___y_2427_);
lean_ctor_set(v___x_2447_, 1, v___y_2428_);
lean_inc_ref(v___x_2447_);
lean_inc(v___y_2430_);
lean_inc_ref(v___x_2446_);
lean_inc(v___x_2444_);
v___x_2448_ = l_Lean_Syntax_node3(v___y_2427_, v___x_2444_, v___x_2446_, v___y_2430_, v___x_2447_);
v___x_2449_ = l_Lean_Syntax_node1(v___y_2427_, v___y_2429_, v___x_2448_);
v___x_2450_ = l_Lean_Syntax_node1(v___y_2427_, v___y_2429_, v___x_2449_);
v___x_2451_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
v___x_2452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___y_2427_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__4));
v___x_2454_ = l_Lean_Name_mkStr4(v___x_2418_, v___x_2419_, v___y_2424_, v___x_2453_);
v___x_2455_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__5));
v___x_2456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___y_2427_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
lean_inc(v___y_2425_);
v___x_2457_ = l_Lean_Syntax_node3(v___y_2427_, v___x_2444_, v___x_2446_, v___y_2425_, v___x_2447_);
v___x_2458_ = l_Lean_Syntax_node2(v___y_2427_, v___x_2454_, v___x_2456_, v___x_2457_);
v___x_2459_ = l_Lean_Syntax_node4(v___y_2427_, v___x_2440_, v___x_2442_, v___x_2450_, v___x_2452_, v___x_2458_);
v___x_2460_ = l_Lean_Syntax_node1(v___y_2427_, v___y_2429_, v___x_2459_);
v___x_2461_ = l_Lean_Syntax_node1(v___y_2427_, v___x_2438_, v___x_2460_);
lean_inc_n(v___y_2431_, 2);
lean_inc_ref_n(v___x_2435_, 2);
v___x_2462_ = l_Lean_Syntax_node6(v___y_2427_, v___x_2434_, v___x_2435_, v___x_2435_, v___y_2431_, v___x_2436_, v___x_2435_, v___x_2461_);
v___x_2463_ = l_Lean_Elab_Command_isLocalAttrKind(v___y_2431_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_Elab_Command_elabCommand(v___x_2462_, v___y_2432_, v___y_2423_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_dec_ref(v___x_2464_);
v___y_2392_ = v___y_2425_;
v___y_2393_ = v___y_2430_;
v___y_2394_ = v___y_2431_;
v___y_2395_ = v___y_2432_;
v___y_2396_ = v___y_2423_;
goto v___jp_2391_;
}
else
{
lean_dec(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec(v___y_2425_);
return v___x_2464_;
}
}
else
{
lean_object* v___x_2465_; lean_object* v_scopes_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v_opts_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___f_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2465_ = lean_st_ref_get(v___y_2423_);
v_scopes_2466_ = lean_ctor_get(v___x_2465_, 2);
lean_inc(v_scopes_2466_);
lean_dec(v___x_2465_);
v___x_2467_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2468_ = l_List_head_x21___redArg(v___x_2467_, v_scopes_2466_);
lean_dec(v_scopes_2466_);
v_opts_2469_ = lean_ctor_get(v___x_2468_, 1);
lean_inc_ref(v_opts_2469_);
lean_dec(v___x_2468_);
v___x_2470_ = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
v___x_2471_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_2469_, v___x_2470_, v___x_2421_);
v___f_2472_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___lam__0), 2, 1);
lean_closure_set(v___f_2472_, 0, v___x_2471_);
v___x_2473_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_2473_, 0, v___x_2462_);
v___x_2474_ = l_Lean_Elab_Command_withScope___redArg(v___f_2472_, v___x_2473_, v___y_2432_, v___y_2423_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_dec_ref(v___x_2474_);
v___y_2392_ = v___y_2425_;
v___y_2393_ = v___y_2430_;
v___y_2394_ = v___y_2431_;
v___y_2395_ = v___y_2432_;
v___y_2396_ = v___y_2423_;
goto v___jp_2391_;
}
else
{
lean_dec(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec(v___y_2425_);
return v___x_2474_;
}
}
}
v___jp_2475_:
{
size_t v_sz_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v_sz_2490_ = lean_array_size(v___y_2487_);
v___x_2491_ = lean_box_usize(v_sz_2490_);
v___x_2492_ = lean_box_usize(v___y_2485_);
v___x_2493_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed), 5, 3);
lean_closure_set(v___x_2493_, 0, v___x_2491_);
lean_closure_set(v___x_2493_, 1, v___x_2492_);
lean_closure_set(v___x_2493_, 2, v___y_2487_);
v___x_2494_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2493_, v___y_2484_, v___y_2486_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2496_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = l_Lean_Elab_Command_getRef___redArg(v___y_2484_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; lean_object* v___x_2498_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref(v___x_2496_);
v___x_2498_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2484_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_quotContext_x3f_2499_; size_t v_sz_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec_ref(v___x_2498_);
v_quotContext_x3f_2499_ = lean_ctor_get(v___y_2484_, 5);
v_sz_2500_ = lean_array_size(v___y_2489_);
v___x_2501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_2500_, v___y_2485_, v___y_2489_);
v___x_2502_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(v___x_2501_, v___y_2482_);
lean_dec_ref(v___x_2501_);
v___x_2503_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2503_, 0, v___y_2483_);
lean_ctor_set(v___x_2503_, 1, v___y_2476_);
lean_ctor_set(v___x_2503_, 2, v_a_2495_);
v___x_2504_ = l_Lean_SourceInfo_fromRef(v_a_2497_, v___y_2478_);
lean_dec(v_a_2497_);
if (lean_obj_tag(v_quotContext_x3f_2499_) == 0)
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2486_);
lean_dec_ref(v___x_2505_);
v___y_2423_ = v___y_2486_;
v___y_2424_ = v___y_2477_;
v___y_2425_ = v___x_2502_;
v___y_2426_ = v___y_2479_;
v___y_2427_ = v___x_2504_;
v___y_2428_ = v___y_2480_;
v___y_2429_ = v___y_2481_;
v___y_2430_ = v___x_2503_;
v___y_2431_ = v___y_2488_;
v___y_2432_ = v___y_2484_;
goto v___jp_2422_;
}
else
{
v___y_2423_ = v___y_2486_;
v___y_2424_ = v___y_2477_;
v___y_2425_ = v___x_2502_;
v___y_2426_ = v___y_2479_;
v___y_2427_ = v___x_2504_;
v___y_2428_ = v___y_2480_;
v___y_2429_ = v___y_2481_;
v___y_2430_ = v___x_2503_;
v___y_2431_ = v___y_2488_;
v___y_2432_ = v___y_2484_;
goto v___jp_2422_;
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec(v___y_2476_);
v_a_2506_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2498_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2498_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v_a_2495_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec(v___y_2476_);
v_a_2514_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2496_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2496_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec(v___y_2476_);
v_a_2522_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2494_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2494_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___boxed(lean_object* v_x_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_Elab_Command_elabNotation(v_x_2897_, v_a_2898_, v_a_2899_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(lean_object* v_00_u03b1_2902_, lean_object* v_x_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v_x_2903_, v___y_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2907_, lean_object* v_x_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(v_00_u03b1_2907_, v_x_2908_, v___y_2909_, v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec_ref(v_x_2908_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(lean_object* v_00_u03b1_2912_, lean_object* v_ref_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_2913_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___boxed(lean_object* v_00_u03b1_2918_, lean_object* v_ref_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(v_00_u03b1_2918_, v_ref_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(lean_object* v_00_u03b1_2924_, lean_object* v_x_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2925_, v___y_2926_, v___y_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___boxed(lean_object* v_00_u03b1_2930_, lean_object* v_x_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(v_00_u03b1_2930_, v_x_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(lean_object* v_msgData_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msgData_2936_, v___y_2938_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(v_msgData_2941_, v___y_2942_, v___y_2943_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(lean_object* v_as_2946_, lean_object* v_as_x27_2947_, lean_object* v_b_2948_, lean_object* v_a_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_2947_, v_b_2948_, v___y_2950_, v___y_2951_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___boxed(lean_object* v_as_2954_, lean_object* v_as_x27_2955_, lean_object* v_b_2956_, lean_object* v_a_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(v_as_2954_, v_as_x27_2955_, v_b_2956_, v_a_2957_, v___y_2958_, v___y_2959_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v_as_2954_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(lean_object* v_00_u03b1_2962_, lean_object* v_ref_2963_, lean_object* v_msg_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_ref_2963_, v_msg_2964_, v___y_2965_, v___y_2966_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___boxed(lean_object* v_00_u03b1_2969_, lean_object* v_ref_2970_, lean_object* v_msg_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(v_00_u03b1_2969_, v_ref_2970_, v_msg_2971_, v___y_2972_, v___y_2973_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v_ref_2970_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2976_, lean_object* v_m_2977_, lean_object* v_a_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v_m_2977_, v_a_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_2980_, lean_object* v_m_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(v_00_u03b2_2980_, v_m_2981_, v_a_2982_);
lean_dec(v_a_2982_);
lean_dec_ref(v_m_2981_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(lean_object* v_00_u03b1_2984_, lean_object* v_msg_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_2985_, v___y_2986_, v___y_2987_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___boxed(lean_object* v_00_u03b1_2990_, lean_object* v_msg_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(v_00_u03b1_2990_, v_msg_2991_, v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
return v_res_2995_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(lean_object* v_00_u03b2_2996_, lean_object* v_x_2997_, lean_object* v_x_2998_){
_start:
{
uint8_t v___x_2999_; 
v___x_2999_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_2997_, v_x_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3000_, lean_object* v_x_3001_, lean_object* v_x_3002_){
_start:
{
uint8_t v_res_3003_; lean_object* v_r_3004_; 
v_res_3003_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(v_00_u03b2_3000_, v_x_3001_, v_x_3002_);
lean_dec_ref(v_x_3002_);
lean_dec_ref(v_x_3001_);
v_r_3004_ = lean_box(v_res_3003_);
return v_r_3004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(lean_object* v_00_u03b2_3005_, lean_object* v_a_3006_, lean_object* v_x_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_3006_, v_x_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___boxed(lean_object* v_00_u03b2_3009_, lean_object* v_a_3010_, lean_object* v_x_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(v_00_u03b2_3009_, v_a_3010_, v_x_3011_);
lean_dec(v_x_3011_);
lean_dec(v_a_3010_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(lean_object* v_msgData_3013_, lean_object* v_macroStack_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_msgData_3013_, v_macroStack_3014_, v___y_3016_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___boxed(lean_object* v_msgData_3019_, lean_object* v_macroStack_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(v_msgData_3019_, v_macroStack_3020_, v___y_3021_, v___y_3022_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
return v_res_3024_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(lean_object* v_00_u03b2_3025_, lean_object* v_x_3026_, size_t v_x_3027_, lean_object* v_x_3028_){
_start:
{
uint8_t v___x_3029_; 
v___x_3029_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_3026_, v_x_3027_, v_x_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___boxed(lean_object* v_00_u03b2_3030_, lean_object* v_x_3031_, lean_object* v_x_3032_, lean_object* v_x_3033_){
_start:
{
size_t v_x_25599__boxed_3034_; uint8_t v_res_3035_; lean_object* v_r_3036_; 
v_x_25599__boxed_3034_ = lean_unbox_usize(v_x_3032_);
lean_dec(v_x_3032_);
v_res_3035_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(v_00_u03b2_3030_, v_x_3031_, v_x_25599__boxed_3034_, v_x_3033_);
lean_dec_ref(v_x_3033_);
lean_dec_ref(v_x_3031_);
v_r_3036_ = lean_box(v_res_3035_);
return v_r_3036_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(lean_object* v_00_u03b2_3037_, lean_object* v_keys_3038_, lean_object* v_vals_3039_, lean_object* v_heq_3040_, lean_object* v_i_3041_, lean_object* v_k_3042_){
_start:
{
uint8_t v___x_3043_; 
v___x_3043_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_3038_, v_i_3041_, v_k_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___boxed(lean_object* v_00_u03b2_3044_, lean_object* v_keys_3045_, lean_object* v_vals_3046_, lean_object* v_heq_3047_, lean_object* v_i_3048_, lean_object* v_k_3049_){
_start:
{
uint8_t v_res_3050_; lean_object* v_r_3051_; 
v_res_3050_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(v_00_u03b2_3044_, v_keys_3045_, v_vals_3046_, v_heq_3047_, v_i_3048_, v_k_3049_);
lean_dec_ref(v_k_3049_);
lean_dec_ref(v_vals_3046_);
lean_dec_ref(v_keys_3045_);
v_r_3051_ = lean_box(v_res_3050_);
return v_r_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1(){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3059_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3060_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
v___x_3061_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1));
v___x_3062_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___boxed), 4, 0);
v___x_3063_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3059_, v___x_3060_, v___x_3061_, v___x_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___boxed(lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
return v_res_3065_;
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
