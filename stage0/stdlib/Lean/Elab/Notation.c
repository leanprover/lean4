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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
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
lean_inc_ref(v_a_303_);
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
lean_inc_ref(v_a_303_);
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
lean_inc(v___y_310_);
v___x_314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_314_, 0, v___y_310_);
lean_ctor_set(v___x_314_, 1, v___y_309_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(uint8_t v_firstChoiceOnly_651_, lean_object* v_stx_652_, lean_object* v_b_653_, lean_object* v_inst_654_){
_start:
{
lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_668_; lean_object* v_a_669_; lean_object* v_snd_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_703_; 
v_snd_679_ = lean_ctor_get(v_b_653_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_b_653_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v_b_653_, 0);
lean_dec(v_unused_704_);
v___x_681_ = v_b_653_;
v_isShared_682_ = v_isSharedCheck_703_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_snd_679_);
lean_dec(v_b_653_);
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
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v_firstChoiceOnly_651_, v_inst_654_, v___y_656_, v_sz_660_, v___x_661_, v___x_659_);
lean_dec_ref(v___y_656_);
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
if (lean_obj_tag(v_stx_652_) == 1)
{
lean_dec_ref(v___y_668_);
if (v_firstChoiceOnly_651_ == 0)
{
lean_object* v_args_670_; 
v_args_670_ = lean_ctor_get(v_stx_652_, 2);
lean_inc_ref(v_args_670_);
lean_dec_ref(v_stx_652_);
v___y_656_ = v_args_670_;
v___y_657_ = v_a_669_;
goto v___jp_655_;
}
else
{
lean_object* v_kind_671_; lean_object* v_args_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_kind_671_ = lean_ctor_get(v_stx_652_, 1);
lean_inc(v_kind_671_);
v_args_672_ = lean_ctor_get(v_stx_652_, 2);
lean_inc_ref(v_args_672_);
lean_dec_ref(v_stx_652_);
v___x_673_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1));
v___x_674_ = lean_name_eq(v_kind_671_, v___x_673_);
lean_dec(v_kind_671_);
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
v___x_677_ = lean_array_get(v___x_675_, v_args_672_, v___x_676_);
lean_dec_ref(v_args_672_);
v_stx_652_ = v___x_677_;
v_b_653_ = v_a_669_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_a_669_);
lean_dec(v_stx_652_);
return v___y_668_;
}
}
v_resetjp_680_:
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_box(0);
v___x_684_ = l_Lean_Syntax_isAntiquot(v_stx_652_);
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
v___x_689_ = l_Lean_Syntax_getAntiquotTerm(v_stx_652_);
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
lean_dec(v_stx_652_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(uint8_t v_firstChoiceOnly_705_, lean_object* v_inst_706_, lean_object* v_as_707_, size_t v_sz_708_, size_t v_i_709_, lean_object* v_b_710_){
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
lean_inc(v_a_716_);
v___x_717_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v_firstChoiceOnly_705_, v_a_716_, v_snd_712_, v_inst_706_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0___boxed(lean_object* v_firstChoiceOnly_732_, lean_object* v_inst_733_, lean_object* v_as_734_, lean_object* v_sz_735_, lean_object* v_i_736_, lean_object* v_b_737_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_738_; size_t v_sz_boxed_739_; size_t v_i_boxed_740_; lean_object* v_res_741_; 
v_firstChoiceOnly_boxed_738_ = lean_unbox(v_firstChoiceOnly_732_);
v_sz_boxed_739_ = lean_unbox_usize(v_sz_735_);
lean_dec(v_sz_735_);
v_i_boxed_740_ = lean_unbox_usize(v_i_736_);
lean_dec(v_i_736_);
v_res_741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v_firstChoiceOnly_boxed_738_, v_inst_733_, v_as_734_, v_sz_boxed_739_, v_i_boxed_740_, v_b_737_);
lean_dec_ref(v_as_734_);
lean_dec_ref(v_inst_733_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___boxed(lean_object* v_firstChoiceOnly_742_, lean_object* v_stx_743_, lean_object* v_b_744_, lean_object* v_inst_745_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_746_; lean_object* v_res_747_; 
v_firstChoiceOnly_boxed_746_ = lean_unbox(v_firstChoiceOnly_742_);
v_res_747_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v_firstChoiceOnly_boxed_746_, v_stx_743_, v_b_744_, v_inst_745_);
lean_dec_ref(v_inst_745_);
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
v___x_788_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v_firstChoiceOnly_759_, v_stx_760_, v___x_787_, v___x_787_);
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
lean_inc_ref(v_a_965_);
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
lean_inc_ref(v_a_965_);
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
lean_inc(v_quotContext_999_);
v_currMacroScope_1000_ = lean_ctor_get(v___y_974_, 2);
lean_inc(v_currMacroScope_1000_);
v_ref_1001_ = lean_ctor_get(v___y_974_, 5);
lean_inc(v_ref_1001_);
lean_dec_ref(v___y_974_);
v___x_1002_ = l_Lean_SourceInfo_fromRef(v_ref_1001_, v___x_998_);
lean_dec(v_ref_1001_);
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
lean_inc(v___x_1002_);
v___x_1010_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1002_);
lean_ctor_set(v___x_1010_, 1, v___x_1008_);
lean_ctor_set(v___x_1010_, 2, v___x_1009_);
v___x_1011_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__4, &l_Lean_Elab_Command_mkUnexpander___closed__4_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__4);
v___x_1012_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__5));
lean_inc(v_currMacroScope_1000_);
lean_inc(v_quotContext_999_);
v___x_1013_ = l_Lean_addMacroScope(v_quotContext_999_, v___x_1012_, v_currMacroScope_1000_);
v___x_1014_ = lean_box(0);
lean_inc(v___x_1002_);
v___x_1015_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1002_);
lean_ctor_set(v___x_1015_, 1, v___x_1011_);
lean_ctor_set(v___x_1015_, 2, v___x_1013_);
lean_ctor_set(v___x_1015_, 3, v___x_1014_);
v___x_1016_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__7));
v___x_1017_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc(v___x_1002_);
v___x_1018_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1002_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
lean_inc(v___x_1002_);
v___x_1019_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1002_);
lean_ctor_set(v___x_1019_, 1, v___x_1003_);
lean_inc_ref(v___x_1018_);
lean_inc(v___x_1002_);
v___x_1020_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1016_, v___x_1018_, v___x_1019_);
lean_inc_ref(v___x_1015_);
lean_inc_ref(v___x_1010_);
lean_inc(v___x_1002_);
v___x_1021_ = l_Lean_Syntax_node4(v___x_1002_, v___x_1004_, v___x_1007_, v___x_1010_, v___x_1015_, v___x_1020_);
v___x_1022_ = l_Lean_Syntax_mkApp(v___x_1021_, v_a_993_);
lean_inc(v_attrKind_962_);
v___x_1023_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_962_);
v___x_1024_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__9));
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__10));
v___x_1026_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
v___x_1027_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc(v___x_1002_);
v___x_1028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1002_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
v___x_1030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
v___x_1031_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__15, &l_Lean_Elab_Command_mkUnexpander___closed__15_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__15);
v___x_1032_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__16));
lean_inc(v_currMacroScope_1000_);
lean_inc(v_quotContext_999_);
v___x_1033_ = l_Lean_addMacroScope(v_quotContext_999_, v___x_1032_, v_currMacroScope_1000_);
lean_inc(v___x_1002_);
v___x_1034_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1002_);
lean_ctor_set(v___x_1034_, 1, v___x_1031_);
lean_ctor_set(v___x_1034_, 2, v___x_1033_);
lean_ctor_set(v___x_1034_, 3, v___x_1014_);
v___x_1035_ = lean_mk_syntax_ident(v_fst_986_);
lean_inc(v___x_1035_);
lean_inc(v___x_1002_);
v___x_1036_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1035_);
lean_inc(v___x_1002_);
v___x_1037_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1030_, v___x_1034_, v___x_1036_);
lean_inc(v___x_1002_);
v___x_1038_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1029_, v_attrKind_962_, v___x_1037_);
lean_inc(v___x_1002_);
v___x_1039_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1038_);
v___x_1040_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
lean_inc(v___x_1002_);
v___x_1041_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1002_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
lean_inc(v___x_1002_);
v___x_1042_ = l_Lean_Syntax_node3(v___x_1002_, v___x_1026_, v___x_1028_, v___x_1039_, v___x_1041_);
lean_inc(v___x_1002_);
v___x_1043_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1042_);
lean_inc(v___x_1002_);
v___x_1044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1002_);
lean_ctor_set(v___x_1044_, 1, v___x_1024_);
v___x_1045_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__19, &l_Lean_Elab_Command_mkUnexpander___closed__19_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__19);
v___x_1046_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__20));
lean_inc(v_currMacroScope_1000_);
lean_inc(v_quotContext_999_);
v___x_1047_ = l_Lean_addMacroScope(v_quotContext_999_, v___x_1046_, v_currMacroScope_1000_);
lean_inc(v___x_1002_);
v___x_1048_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1002_);
lean_ctor_set(v___x_1048_, 1, v___x_1045_);
lean_ctor_set(v___x_1048_, 2, v___x_1047_);
lean_ctor_set(v___x_1048_, 3, v___x_1014_);
lean_inc(v___x_1002_);
v___x_1049_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1008_, v___x_1048_, v___x_1035_);
v___x_1050_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__22, &l_Lean_Elab_Command_mkUnexpander___closed__22_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__22);
v___x_1051_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__25));
lean_inc(v_currMacroScope_1000_);
lean_inc(v_quotContext_999_);
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
lean_inc(v___x_1002_);
v___x_1056_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1002_);
lean_ctor_set(v___x_1056_, 1, v___x_1050_);
lean_ctor_set(v___x_1056_, 2, v___x_1052_);
lean_ctor_set(v___x_1056_, 3, v___x_1055_);
v___x_1057_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
lean_inc(v___x_1002_);
v___x_1058_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1002_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__27));
v___x_1060_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__28));
lean_inc(v___x_1002_);
v___x_1061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1002_);
lean_ctor_set(v___x_1061_, 1, v___x_1059_);
v___x_1062_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__30));
v___x_1063_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__32));
v___x_1064_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
lean_inc(v___x_1002_);
v___x_1065_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1002_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__35));
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
lean_inc(v___x_1002_);
v___x_1068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1002_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
lean_inc(v___x_1002_);
v___x_1070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1002_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
lean_inc_ref(v___x_1070_);
lean_inc_ref(v___x_1068_);
lean_inc(v___x_1002_);
v___x_1071_ = l_Lean_Syntax_node3(v___x_1002_, v___x_1066_, v___x_1068_, v___x_1022_, v___x_1070_);
lean_inc(v___x_1002_);
v___x_1072_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1071_);
lean_inc(v___x_1002_);
v___x_1073_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1072_);
v___x_1074_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
lean_inc(v___x_1002_);
v___x_1075_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1002_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
v___x_1077_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__40, &l_Lean_Elab_Command_mkUnexpander___closed__40_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__40);
v___x_1078_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__41));
lean_inc(v_currMacroScope_1000_);
lean_inc(v_quotContext_999_);
v___x_1079_ = l_Lean_addMacroScope(v_quotContext_999_, v___x_1078_, v_currMacroScope_1000_);
v___x_1080_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__42));
v___x_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v_snd_980_);
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v___x_1014_);
lean_inc(v___x_1002_);
v___x_1083_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1002_);
lean_ctor_set(v___x_1083_, 1, v___x_1077_);
lean_ctor_set(v___x_1083_, 2, v___x_1079_);
lean_ctor_set(v___x_1083_, 3, v___x_1082_);
lean_inc_ref(v___x_1070_);
lean_inc(v___x_1002_);
v___x_1084_ = l_Lean_Syntax_node3(v___x_1002_, v___x_1066_, v___x_1068_, v_pat_963_, v___x_1070_);
lean_inc(v___x_1002_);
v___x_1085_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1008_, v___x_1015_, v___x_1084_);
lean_inc(v___x_1002_);
v___x_1086_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1076_, v___x_1083_, v___x_1085_);
lean_inc_ref(v___x_1075_);
lean_inc_ref(v___x_1065_);
lean_inc(v___x_1002_);
v___x_1087_ = l_Lean_Syntax_node4(v___x_1002_, v___x_1063_, v___x_1065_, v___x_1073_, v___x_1075_, v___x_1086_);
v___x_1088_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__44));
v___x_1089_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__45));
lean_inc(v___x_1002_);
v___x_1090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1002_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
lean_inc(v___x_1002_);
v___x_1091_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1088_, v___x_1090_);
lean_inc(v___x_1002_);
v___x_1092_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1091_);
lean_inc(v___x_1002_);
v___x_1093_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1092_);
v___x_1094_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__47, &l_Lean_Elab_Command_mkUnexpander___closed__47_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__47);
v___x_1095_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__48));
lean_inc(v_currMacroScope_1000_);
lean_inc(v_quotContext_999_);
v___x_1096_ = l_Lean_addMacroScope(v_quotContext_999_, v___x_1095_, v_currMacroScope_1000_);
v___x_1097_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__50));
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v_snd_980_);
v___x_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v___x_1014_);
lean_inc(v___x_1002_);
v___x_1100_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1002_);
lean_ctor_set(v___x_1100_, 1, v___x_1094_);
lean_ctor_set(v___x_1100_, 2, v___x_1096_);
lean_ctor_set(v___x_1100_, 3, v___x_1099_);
v___x_1101_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__52));
v___x_1102_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__3));
v___x_1103_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc(v___x_1002_);
v___x_1104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1002_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__5));
v___x_1106_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__55, &l_Lean_Elab_Command_mkUnexpander___closed__55_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__55);
v___x_1107_ = lean_box(0);
v___x_1108_ = l_Lean_addMacroScope(v_quotContext_999_, v___x_1107_, v_currMacroScope_1000_);
v___x_1109_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__67));
lean_inc(v___x_1002_);
v___x_1110_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1002_);
lean_ctor_set(v___x_1110_, 1, v___x_1106_);
lean_ctor_set(v___x_1110_, 2, v___x_1108_);
lean_ctor_set(v___x_1110_, 3, v___x_1109_);
lean_inc(v___x_1002_);
v___x_1111_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1105_, v___x_1110_);
lean_inc(v___x_1002_);
v___x_1112_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1102_, v___x_1104_, v___x_1111_);
lean_inc_ref(v___x_1010_);
lean_inc(v___x_1002_);
v___x_1113_ = l_Lean_Syntax_node3(v___x_1002_, v___x_1101_, v___x_1112_, v___x_1010_, v___x_1070_);
lean_inc(v___x_1002_);
v___x_1114_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1008_, v___x_1113_);
lean_inc(v___x_1002_);
v___x_1115_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1076_, v___x_1100_, v___x_1114_);
lean_inc(v___x_1002_);
v___x_1116_ = l_Lean_Syntax_node4(v___x_1002_, v___x_1063_, v___x_1065_, v___x_1093_, v___x_1075_, v___x_1115_);
lean_inc(v___x_1002_);
v___x_1117_ = l_Lean_Syntax_node2(v___x_1002_, v___x_1008_, v___x_1087_, v___x_1116_);
lean_inc(v___x_1002_);
v___x_1118_ = l_Lean_Syntax_node1(v___x_1002_, v___x_1062_, v___x_1117_);
lean_inc(v___x_1002_);
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
lean_dec_ref(v___y_974_);
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
lean_dec_ref(v___y_974_);
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
lean_dec_ref(v___y_974_);
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
lean_dec_ref(v_a_978_);
lean_dec(v_head_979_);
lean_dec_ref(v___y_974_);
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
lean_dec_ref(v___y_974_);
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
lean_dec_ref(v___y_974_);
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14(lean_object* v_o_1268_, lean_object* v_k_1269_, uint8_t v_v_1270_){
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
v___x_1278_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___boxed(lean_object* v_o_1287_, lean_object* v_k_1288_, lean_object* v_v_1289_){
_start:
{
uint8_t v_v_boxed_1290_; lean_object* v_res_1291_; 
v_v_boxed_1290_ = lean_unbox(v_v_1289_);
v_res_1291_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14(v_o_1287_, v_k_1288_, v_v_boxed_1290_);
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
v___x_1296_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14(v_opts_1292_, v_name_1295_, v_val_1294_);
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
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_box(1);
v___x_1401_ = l_Lean_MessageData_ofFormat(v___x_1400_);
return v___x_1401_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__2));
v___x_1406_ = l_Lean_MessageData_ofFormat(v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27(lean_object* v_x_1407_, lean_object* v_x_1408_){
_start:
{
if (lean_obj_tag(v_x_1408_) == 0)
{
return v_x_1407_;
}
else
{
lean_object* v_head_1409_; lean_object* v_tail_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1432_; 
v_head_1409_ = lean_ctor_get(v_x_1408_, 0);
v_tail_1410_ = lean_ctor_get(v_x_1408_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_x_1408_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1412_ = v_x_1408_;
v_isShared_1413_ = v_isSharedCheck_1432_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_tail_1410_);
lean_inc(v_head_1409_);
lean_dec(v_x_1408_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1432_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v_before_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1430_; 
v_before_1414_ = lean_ctor_get(v_head_1409_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_head_1409_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; 
v_unused_1431_ = lean_ctor_get(v_head_1409_, 1);
lean_dec(v_unused_1431_);
v___x_1416_ = v_head_1409_;
v_isShared_1417_ = v_isSharedCheck_1430_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_before_1414_);
lean_dec(v_head_1409_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1430_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1418_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0);
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 7);
lean_ctor_set(v___x_1416_, 1, v___x_1418_);
lean_ctor_set(v___x_1416_, 0, v_x_1407_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_x_1407_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__3);
if (v_isShared_1413_ == 0)
{
lean_ctor_set_tag(v___x_1412_, 7);
lean_ctor_set(v___x_1412_, 1, v___x_1421_);
lean_ctor_set(v___x_1412_, 0, v___x_1420_);
v___x_1423_ = v___x_1412_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = l_Lean_MessageData_ofSyntax(v_before_1414_);
v___x_1425_ = l_Lean_indentD(v___x_1424_);
v___x_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1423_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v_x_1407_ = v___x_1426_;
v_x_1408_ = v_tail_1410_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26(lean_object* v_opts_1433_, lean_object* v_opt_1434_){
_start:
{
lean_object* v_name_1435_; lean_object* v_defValue_1436_; lean_object* v_map_1437_; lean_object* v___x_1438_; 
v_name_1435_ = lean_ctor_get(v_opt_1434_, 0);
v_defValue_1436_ = lean_ctor_get(v_opt_1434_, 1);
v_map_1437_ = lean_ctor_get(v_opts_1433_, 0);
v___x_1438_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1437_, v_name_1435_);
if (lean_obj_tag(v___x_1438_) == 0)
{
uint8_t v___x_1439_; 
v___x_1439_ = lean_unbox(v_defValue_1436_);
return v___x_1439_;
}
else
{
lean_object* v_val_1440_; 
v_val_1440_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_val_1440_);
lean_dec_ref(v___x_1438_);
if (lean_obj_tag(v_val_1440_) == 1)
{
uint8_t v_v_1441_; 
v_v_1441_ = lean_ctor_get_uint8(v_val_1440_, 0);
lean_dec_ref(v_val_1440_);
return v_v_1441_;
}
else
{
uint8_t v___x_1442_; 
lean_dec(v_val_1440_);
v___x_1442_ = lean_unbox(v_defValue_1436_);
return v___x_1442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26___boxed(lean_object* v_opts_1443_, lean_object* v_opt_1444_){
_start:
{
uint8_t v_res_1445_; lean_object* v_r_1446_; 
v_res_1445_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26(v_opts_1443_, v_opt_1444_);
lean_dec_ref(v_opt_1444_);
lean_dec_ref(v_opts_1443_);
v_r_1446_ = lean_box(v_res_1445_);
return v_r_1446_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__1));
v___x_1451_ = l_Lean_MessageData_ofFormat(v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg(lean_object* v_msgData_1452_, lean_object* v_macroStack_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; lean_object* v_scopes_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v_opts_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v___x_1456_ = lean_st_ref_get(v___y_1454_);
v_scopes_1457_ = lean_ctor_get(v___x_1456_, 2);
lean_inc(v_scopes_1457_);
lean_dec(v___x_1456_);
v___x_1458_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1459_ = l_List_head_x21___redArg(v___x_1458_, v_scopes_1457_);
lean_dec(v_scopes_1457_);
v_opts_1460_ = lean_ctor_get(v___x_1459_, 1);
lean_inc_ref(v_opts_1460_);
lean_dec(v___x_1459_);
v___x_1461_ = l_Lean_Elab_pp_macroStack;
v___x_1462_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__26(v_opts_1460_, v___x_1461_);
lean_dec_ref(v_opts_1460_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
lean_dec(v_macroStack_1453_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_msgData_1452_);
return v___x_1463_;
}
else
{
if (lean_obj_tag(v_macroStack_1453_) == 0)
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_msgData_1452_);
return v___x_1464_;
}
else
{
lean_object* v_head_1465_; lean_object* v_after_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1481_; 
v_head_1465_ = lean_ctor_get(v_macroStack_1453_, 0);
lean_inc(v_head_1465_);
v_after_1466_ = lean_ctor_get(v_head_1465_, 1);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_head_1465_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v_head_1465_, 0);
lean_dec(v_unused_1482_);
v___x_1468_ = v_head_1465_;
v_isShared_1469_ = v_isSharedCheck_1481_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_after_1466_);
lean_dec(v_head_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1481_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27___closed__0);
if (v_isShared_1469_ == 0)
{
lean_ctor_set_tag(v___x_1468_, 7);
lean_ctor_set(v___x_1468_, 1, v___x_1470_);
lean_ctor_set(v___x_1468_, 0, v_msgData_1452_);
v___x_1472_ = v___x_1468_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_msgData_1452_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v_msgData_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1473_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___closed__2);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1472_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = l_Lean_MessageData_ofSyntax(v_after_1466_);
v___x_1476_ = l_Lean_indentD(v___x_1475_);
v_msgData_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1477_, 0, v___x_1474_);
lean_ctor_set(v_msgData_1477_, 1, v___x_1476_);
v___x_1478_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24_spec__27(v_msgData_1477_, v_macroStack_1453_);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
return v___x_1479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg___boxed(lean_object* v_msgData_1483_, lean_object* v_macroStack_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg(v_msgData_1483_, v_macroStack_1484_, v___y_1485_);
lean_dec(v___y_1485_);
return v_res_1487_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1488_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__0);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
lean_ctor_set(v___x_1493_, 2, v___x_1492_);
lean_ctor_set(v___x_1493_, 3, v___x_1491_);
lean_ctor_set(v___x_1493_, 4, v___x_1491_);
lean_ctor_set(v___x_1493_, 5, v___x_1491_);
lean_ctor_set(v___x_1493_, 6, v___x_1491_);
lean_ctor_set(v___x_1493_, 7, v___x_1491_);
lean_ctor_set(v___x_1493_, 8, v___x_1491_);
return v___x_1493_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1494_ = lean_unsigned_to_nat(32u);
v___x_1495_ = lean_mk_empty_array_with_capacity(v___x_1494_);
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
return v___x_1496_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1497_ = ((size_t)5ULL);
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = lean_unsigned_to_nat(32u);
v___x_1500_ = lean_mk_empty_array_with_capacity(v___x_1499_);
v___x_1501_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__3);
v___x_1502_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
lean_ctor_set(v___x_1502_, 1, v___x_1500_);
lean_ctor_set(v___x_1502_, 2, v___x_1498_);
lean_ctor_set(v___x_1502_, 3, v___x_1498_);
lean_ctor_set_usize(v___x_1502_, 4, v___x_1497_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1503_ = lean_box(1);
v___x_1504_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__4);
v___x_1505_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_1506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v___x_1504_);
lean_ctor_set(v___x_1506_, 2, v___x_1503_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(lean_object* v_msgData_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v_env_1511_; lean_object* v___x_1512_; lean_object* v_scopes_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v_opts_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1510_ = lean_st_ref_get(v___y_1508_);
v_env_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc_ref(v_env_1511_);
lean_dec(v___x_1510_);
v___x_1512_ = lean_st_ref_get(v___y_1508_);
v_scopes_1513_ = lean_ctor_get(v___x_1512_, 2);
lean_inc(v_scopes_1513_);
lean_dec(v___x_1512_);
v___x_1514_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1515_ = l_List_head_x21___redArg(v___x_1514_, v_scopes_1513_);
lean_dec(v_scopes_1513_);
v_opts_1516_ = lean_ctor_get(v___x_1515_, 1);
lean_inc_ref(v_opts_1516_);
lean_dec(v___x_1515_);
v___x_1517_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__2);
v___x_1518_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___closed__5);
v___x_1519_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1519_, 0, v_env_1511_);
lean_ctor_set(v___x_1519_, 1, v___x_1517_);
lean_ctor_set(v___x_1519_, 2, v___x_1518_);
lean_ctor_set(v___x_1519_, 3, v_opts_1516_);
v___x_1520_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
lean_ctor_set(v___x_1520_, 1, v_msgData_1507_);
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(v_msgData_1522_, v___y_1523_);
lean_dec(v___y_1523_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(lean_object* v_msg_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Elab_Command_getRef___redArg(v___y_1527_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v_macroStack_1532_; lean_object* v___x_1533_; lean_object* v_a_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1545_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref(v___x_1530_);
v_macroStack_1532_ = lean_ctor_get(v___y_1527_, 4);
lean_inc(v_macroStack_1532_);
lean_dec_ref(v___y_1527_);
v___x_1533_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(v_msg_1526_, v___y_1528_);
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref(v___x_1533_);
lean_inc(v_macroStack_1532_);
v___x_1535_ = l_Lean_Elab_getBetterRef(v_a_1531_, v_macroStack_1532_);
lean_dec(v_a_1531_);
v___x_1536_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg(v_a_1534_, v_macroStack_1532_, v___y_1528_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1535_);
lean_ctor_set(v___x_1541_, 1, v_a_1537_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 1);
lean_ctor_set(v___x_1539_, 0, v___x_1541_);
v___x_1543_ = v___x_1539_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec_ref(v___y_1527_);
lean_dec_ref(v_msg_1526_);
v_a_1546_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1530_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1530_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg___boxed(lean_object* v_msg_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(v_msg_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(lean_object* v_ref_1559_, lean_object* v_msg_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Elab_Command_getRef___redArg(v___y_1561_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v_fileName_1566_; lean_object* v_fileMap_1567_; lean_object* v_currRecDepth_1568_; lean_object* v_cmdPos_1569_; lean_object* v_macroStack_1570_; lean_object* v_quotContext_x3f_1571_; lean_object* v_currMacroScope_1572_; lean_object* v_snap_x3f_1573_; lean_object* v_cancelTk_x3f_1574_; uint8_t v_suppressElabErrors_1575_; lean_object* v_ref_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref(v___x_1564_);
v_fileName_1566_ = lean_ctor_get(v___y_1561_, 0);
v_fileMap_1567_ = lean_ctor_get(v___y_1561_, 1);
v_currRecDepth_1568_ = lean_ctor_get(v___y_1561_, 2);
v_cmdPos_1569_ = lean_ctor_get(v___y_1561_, 3);
v_macroStack_1570_ = lean_ctor_get(v___y_1561_, 4);
v_quotContext_x3f_1571_ = lean_ctor_get(v___y_1561_, 5);
v_currMacroScope_1572_ = lean_ctor_get(v___y_1561_, 6);
v_snap_x3f_1573_ = lean_ctor_get(v___y_1561_, 8);
v_cancelTk_x3f_1574_ = lean_ctor_get(v___y_1561_, 9);
v_suppressElabErrors_1575_ = lean_ctor_get_uint8(v___y_1561_, sizeof(void*)*10);
v_ref_1576_ = l_Lean_replaceRef(v_ref_1559_, v_a_1565_);
lean_dec(v_a_1565_);
lean_inc(v_cancelTk_x3f_1574_);
lean_inc(v_snap_x3f_1573_);
lean_inc(v_currMacroScope_1572_);
lean_inc(v_quotContext_x3f_1571_);
lean_inc(v_macroStack_1570_);
lean_inc(v_cmdPos_1569_);
lean_inc(v_currRecDepth_1568_);
lean_inc_ref(v_fileMap_1567_);
lean_inc_ref(v_fileName_1566_);
v___x_1577_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1577_, 0, v_fileName_1566_);
lean_ctor_set(v___x_1577_, 1, v_fileMap_1567_);
lean_ctor_set(v___x_1577_, 2, v_currRecDepth_1568_);
lean_ctor_set(v___x_1577_, 3, v_cmdPos_1569_);
lean_ctor_set(v___x_1577_, 4, v_macroStack_1570_);
lean_ctor_set(v___x_1577_, 5, v_quotContext_x3f_1571_);
lean_ctor_set(v___x_1577_, 6, v_currMacroScope_1572_);
lean_ctor_set(v___x_1577_, 7, v_ref_1576_);
lean_ctor_set(v___x_1577_, 8, v_snap_x3f_1573_);
lean_ctor_set(v___x_1577_, 9, v_cancelTk_x3f_1574_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*10, v_suppressElabErrors_1575_);
v___x_1578_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(v_msg_1560_, v___x_1577_, v___y_1562_);
return v___x_1578_;
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec_ref(v_msg_1560_);
v_a_1579_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1564_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1564_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___boxed(lean_object* v_ref_1587_, lean_object* v_msg_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_1587_, v_msg_1588_, v___y_1589_, v___y_1590_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v_ref_1587_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(lean_object* v_env_1593_, lean_object* v_currNamespace_1594_, lean_object* v_openDecls_1595_, lean_object* v_n_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = l_Lean_ResolveName_resolveNamespace(v_env_1593_, v_currNamespace_1594_, v_openDecls_1595_, v_n_1596_);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v___y_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed(lean_object* v_env_1601_, lean_object* v_currNamespace_1602_, lean_object* v_openDecls_1603_, lean_object* v_n_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(v_env_1601_, v_currNamespace_1602_, v_openDecls_1603_, v_n_1604_, v___y_1605_, v___y_1606_);
lean_dec_ref(v___y_1605_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(lean_object* v_currNamespace_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v_currNamespace_1608_);
lean_ctor_set(v___x_1611_, 1, v___y_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(v_currNamespace_1612_, v___y_1613_, v___y_1614_);
lean_dec_ref(v___y_1613_);
return v_res_1615_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = l_Lean_maxRecDepthErrorMessage;
v___x_1622_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__3);
v___x_1624_ = l_Lean_MessageData_ofFormat(v___x_1623_);
return v___x_1624_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__4);
v___x_1626_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__2));
v___x_1627_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v___x_1625_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg(lean_object* v_ref_1628_){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___closed__5);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v_ref_1628_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg___boxed(lean_object* v_ref_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg(v_ref_1633_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(lean_object* v_cls_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_scopes_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v_opts_1645_; uint8_t v_hasTrace_1646_; 
v___x_1639_ = l_Lean_inheritedTraceOptions;
v___x_1640_ = lean_st_ref_get(v___x_1639_);
v___x_1641_ = lean_st_ref_get(v___y_1637_);
v_scopes_1642_ = lean_ctor_get(v___x_1641_, 2);
lean_inc(v_scopes_1642_);
lean_dec(v___x_1641_);
v___x_1643_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1644_ = l_List_head_x21___redArg(v___x_1643_, v_scopes_1642_);
lean_dec(v_scopes_1642_);
v_opts_1645_ = lean_ctor_get(v___x_1644_, 1);
lean_inc_ref(v_opts_1645_);
lean_dec(v___x_1644_);
v_hasTrace_1646_ = lean_ctor_get_uint8(v_opts_1645_, sizeof(void*)*1);
if (v_hasTrace_1646_ == 0)
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec_ref(v_opts_1645_);
lean_dec(v___x_1640_);
lean_dec(v_cls_1636_);
v___x_1647_ = lean_box(v_hasTrace_1646_);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
return v___x_1648_;
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1649_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__14___closed__1));
v___x_1650_ = l_Lean_Name_append(v___x_1649_, v_cls_1636_);
v___x_1651_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1640_, v_opts_1645_, v___x_1650_);
lean_dec(v___x_1650_);
lean_dec_ref(v_opts_1645_);
lean_dec(v___x_1640_);
v___x_1652_ = lean_box(v___x_1651_);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg___boxed(lean_object* v_cls_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(v_cls_1654_, v___y_1655_);
lean_dec(v___y_1655_);
return v_res_1657_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1658_; double v___x_1659_; 
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_float_of_nat(v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(lean_object* v_cls_1662_, lean_object* v_msg_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_Elab_Command_getRef___redArg(v___y_1664_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1716_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref(v___x_1667_);
v___x_1669_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(v_msg_1663_, v___y_1665_);
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1716_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1716_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v_traceState_1675_; lean_object* v_env_1676_; lean_object* v_messages_1677_; lean_object* v_scopes_1678_; lean_object* v_usedQuotCtxts_1679_; lean_object* v_nextMacroScope_1680_; lean_object* v_maxRecDepth_1681_; lean_object* v_ngen_1682_; lean_object* v_auxDeclNGen_1683_; lean_object* v_infoState_1684_; lean_object* v_snapshotTasks_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1715_; 
v___x_1674_ = lean_st_ref_take(v___y_1665_);
v_traceState_1675_ = lean_ctor_get(v___x_1674_, 9);
v_env_1676_ = lean_ctor_get(v___x_1674_, 0);
v_messages_1677_ = lean_ctor_get(v___x_1674_, 1);
v_scopes_1678_ = lean_ctor_get(v___x_1674_, 2);
v_usedQuotCtxts_1679_ = lean_ctor_get(v___x_1674_, 3);
v_nextMacroScope_1680_ = lean_ctor_get(v___x_1674_, 4);
v_maxRecDepth_1681_ = lean_ctor_get(v___x_1674_, 5);
v_ngen_1682_ = lean_ctor_get(v___x_1674_, 6);
v_auxDeclNGen_1683_ = lean_ctor_get(v___x_1674_, 7);
v_infoState_1684_ = lean_ctor_get(v___x_1674_, 8);
v_snapshotTasks_1685_ = lean_ctor_get(v___x_1674_, 10);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1687_ = v___x_1674_;
v_isShared_1688_ = v_isSharedCheck_1715_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_snapshotTasks_1685_);
lean_inc(v_traceState_1675_);
lean_inc(v_infoState_1684_);
lean_inc(v_auxDeclNGen_1683_);
lean_inc(v_ngen_1682_);
lean_inc(v_maxRecDepth_1681_);
lean_inc(v_nextMacroScope_1680_);
lean_inc(v_usedQuotCtxts_1679_);
lean_inc(v_scopes_1678_);
lean_inc(v_messages_1677_);
lean_inc(v_env_1676_);
lean_dec(v___x_1674_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1715_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
uint64_t v_tid_1689_; lean_object* v_traces_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1714_; 
v_tid_1689_ = lean_ctor_get_uint64(v_traceState_1675_, sizeof(void*)*1);
v_traces_1690_ = lean_ctor_get(v_traceState_1675_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_traceState_1675_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1692_ = v_traceState_1675_;
v_isShared_1693_ = v_isSharedCheck_1714_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_traces_1690_);
lean_dec(v_traceState_1675_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1714_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; double v___x_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1694_ = lean_box(0);
v___x_1695_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__0);
v___x_1696_ = 0;
v___x_1697_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1698_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1698_, 0, v_cls_1662_);
lean_ctor_set(v___x_1698_, 1, v___x_1694_);
lean_ctor_set(v___x_1698_, 2, v___x_1697_);
lean_ctor_set_float(v___x_1698_, sizeof(void*)*3, v___x_1695_);
lean_ctor_set_float(v___x_1698_, sizeof(void*)*3 + 8, v___x_1695_);
lean_ctor_set_uint8(v___x_1698_, sizeof(void*)*3 + 16, v___x_1696_);
v___x_1699_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___closed__1));
v___x_1700_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v_a_1670_);
lean_ctor_set(v___x_1700_, 2, v___x_1699_);
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_a_1668_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = l_Lean_PersistentArray_push___redArg(v_traces_1690_, v___x_1701_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1702_);
v___x_1704_ = v___x_1692_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1702_);
lean_ctor_set_uint64(v_reuseFailAlloc_1713_, sizeof(void*)*1, v_tid_1689_);
v___x_1704_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1706_; 
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 9, v___x_1704_);
v___x_1706_ = v___x_1687_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_env_1676_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_messages_1677_);
lean_ctor_set(v_reuseFailAlloc_1712_, 2, v_scopes_1678_);
lean_ctor_set(v_reuseFailAlloc_1712_, 3, v_usedQuotCtxts_1679_);
lean_ctor_set(v_reuseFailAlloc_1712_, 4, v_nextMacroScope_1680_);
lean_ctor_set(v_reuseFailAlloc_1712_, 5, v_maxRecDepth_1681_);
lean_ctor_set(v_reuseFailAlloc_1712_, 6, v_ngen_1682_);
lean_ctor_set(v_reuseFailAlloc_1712_, 7, v_auxDeclNGen_1683_);
lean_ctor_set(v_reuseFailAlloc_1712_, 8, v_infoState_1684_);
lean_ctor_set(v_reuseFailAlloc_1712_, 9, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1712_, 10, v_snapshotTasks_1685_);
v___x_1706_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1710_; 
v___x_1707_ = lean_st_ref_set(v___y_1665_, v___x_1706_);
v___x_1708_ = lean_box(0);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1708_);
v___x_1710_ = v___x_1672_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec_ref(v_msg_1663_);
lean_dec(v_cls_1662_);
v_a_1717_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1667_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1667_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___boxed(lean_object* v_cls_1725_, lean_object* v_msg_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(v_cls_1725_, v_msg_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
return v_res_1730_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg(lean_object* v_keys_1731_, lean_object* v_i_1732_, lean_object* v_k_1733_){
_start:
{
lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = lean_array_get_size(v_keys_1731_);
v___x_1735_ = lean_nat_dec_lt(v_i_1732_, v___x_1734_);
if (v___x_1735_ == 0)
{
lean_dec(v_i_1732_);
return v___x_1735_;
}
else
{
lean_object* v_k_x27_1736_; uint8_t v___x_1737_; 
v_k_x27_1736_ = lean_array_fget_borrowed(v_keys_1731_, v_i_1732_);
v___x_1737_ = l_Lean_instBEqExtraModUse_beq(v_k_1733_, v_k_x27_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_add(v_i_1732_, v___x_1738_);
lean_dec(v_i_1732_);
v_i_1732_ = v___x_1739_;
goto _start;
}
else
{
lean_dec(v_i_1732_);
return v___x_1737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg___boxed(lean_object* v_keys_1741_, lean_object* v_i_1742_, lean_object* v_k_1743_){
_start:
{
uint8_t v_res_1744_; lean_object* v_r_1745_; 
v_res_1744_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg(v_keys_1741_, v_i_1742_, v_k_1743_);
lean_dec_ref(v_k_1743_);
lean_dec_ref(v_keys_1741_);
v_r_1745_ = lean_box(v_res_1744_);
return v_r_1745_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0(void){
_start:
{
size_t v___x_1746_; size_t v___x_1747_; size_t v___x_1748_; 
v___x_1746_ = ((size_t)5ULL);
v___x_1747_ = ((size_t)1ULL);
v___x_1748_ = lean_usize_shift_left(v___x_1747_, v___x_1746_);
return v___x_1748_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1(void){
_start:
{
size_t v___x_1749_; size_t v___x_1750_; size_t v___x_1751_; 
v___x_1749_ = ((size_t)1ULL);
v___x_1750_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__0);
v___x_1751_ = lean_usize_sub(v___x_1750_, v___x_1749_);
return v___x_1751_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg(lean_object* v_x_1752_, size_t v_x_1753_, lean_object* v_x_1754_){
_start:
{
if (lean_obj_tag(v_x_1752_) == 0)
{
lean_object* v_es_1755_; lean_object* v___x_1756_; size_t v___x_1757_; size_t v___x_1758_; size_t v___x_1759_; lean_object* v_j_1760_; lean_object* v___x_1761_; 
v_es_1755_ = lean_ctor_get(v_x_1752_, 0);
lean_inc_ref(v_es_1755_);
lean_dec_ref(v_x_1752_);
v___x_1756_ = lean_box(2);
v___x_1757_ = ((size_t)5ULL);
v___x_1758_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___closed__1);
v___x_1759_ = lean_usize_land(v_x_1753_, v___x_1758_);
v_j_1760_ = lean_usize_to_nat(v___x_1759_);
v___x_1761_ = lean_array_get(v___x_1756_, v_es_1755_, v_j_1760_);
lean_dec(v_j_1760_);
lean_dec_ref(v_es_1755_);
switch(lean_obj_tag(v___x_1761_))
{
case 0:
{
lean_object* v_key_1762_; uint8_t v___x_1763_; 
v_key_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_key_1762_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = l_Lean_instBEqExtraModUse_beq(v_x_1754_, v_key_1762_);
lean_dec(v_key_1762_);
return v___x_1763_;
}
case 1:
{
lean_object* v_node_1764_; size_t v___x_1765_; 
v_node_1764_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_node_1764_);
lean_dec_ref(v___x_1761_);
v___x_1765_ = lean_usize_shift_right(v_x_1753_, v___x_1757_);
v_x_1752_ = v_node_1764_;
v_x_1753_ = v___x_1765_;
goto _start;
}
default: 
{
uint8_t v___x_1767_; 
v___x_1767_ = 0;
return v___x_1767_;
}
}
}
else
{
lean_object* v_ks_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v_ks_1768_ = lean_ctor_get(v_x_1752_, 0);
lean_inc_ref(v_ks_1768_);
lean_dec_ref(v_x_1752_);
v___x_1769_ = lean_unsigned_to_nat(0u);
v___x_1770_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg(v_ks_1768_, v___x_1769_, v_x_1754_);
lean_dec_ref(v_ks_1768_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg___boxed(lean_object* v_x_1771_, lean_object* v_x_1772_, lean_object* v_x_1773_){
_start:
{
size_t v_x_22924__boxed_1774_; uint8_t v_res_1775_; lean_object* v_r_1776_; 
v_x_22924__boxed_1774_ = lean_unbox_usize(v_x_1772_);
lean_dec(v_x_1772_);
v_res_1775_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg(v_x_1771_, v_x_22924__boxed_1774_, v_x_1773_);
lean_dec_ref(v_x_1773_);
v_r_1776_ = lean_box(v_res_1775_);
return v_r_1776_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg(lean_object* v_x_1777_, lean_object* v_x_1778_){
_start:
{
uint64_t v___x_1779_; size_t v___x_1780_; uint8_t v___x_1781_; 
v___x_1779_ = l_Lean_instHashableExtraModUse_hash(v_x_1778_);
v___x_1780_ = lean_uint64_to_usize(v___x_1779_);
v___x_1781_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg(v_x_1777_, v___x_1780_, v_x_1778_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg___boxed(lean_object* v_x_1782_, lean_object* v_x_1783_){
_start:
{
uint8_t v_res_1784_; lean_object* v_r_1785_; 
v_res_1784_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg(v_x_1782_, v_x_1783_);
lean_dec_ref(v_x_1783_);
v_r_1785_ = lean_box(v_res_1784_);
return v_r_1785_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__1));
v___x_1789_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__0));
v___x_1790_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1789_, v___x_1788_);
return v___x_1790_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__5));
v___x_1796_ = l_Lean_stringToMessageData(v___x_1795_);
return v___x_1796_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__7));
v___x_1799_ = l_Lean_stringToMessageData(v___x_1798_);
return v___x_1799_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1801_ = l_Lean_stringToMessageData(v___x_1800_);
return v___x_1801_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__10));
v___x_1804_ = l_Lean_stringToMessageData(v___x_1803_);
return v___x_1804_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__12));
v___x_1807_ = l_Lean_stringToMessageData(v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7(lean_object* v_mod_1812_, uint8_t v_isMeta_1813_, lean_object* v_hint_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; lean_object* v_env_1819_; uint8_t v_isExporting_1820_; lean_object* v___x_1821_; lean_object* v_env_1822_; lean_object* v___x_1823_; lean_object* v_entry_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___y_1829_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1818_ = lean_st_ref_get(v___y_1816_);
v_env_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc_ref(v_env_1819_);
lean_dec(v___x_1818_);
v_isExporting_1820_ = lean_ctor_get_uint8(v_env_1819_, sizeof(void*)*8);
lean_dec_ref(v_env_1819_);
v___x_1821_ = lean_st_ref_get(v___y_1816_);
v_env_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc_ref(v_env_1822_);
lean_dec(v___x_1821_);
v___x_1823_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__2);
lean_inc(v_mod_1812_);
v_entry_1824_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1824_, 0, v_mod_1812_);
lean_ctor_set_uint8(v_entry_1824_, sizeof(void*)*1, v_isExporting_1820_);
lean_ctor_set_uint8(v_entry_1824_, sizeof(void*)*1 + 1, v_isMeta_1813_);
v___x_1825_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1826_ = lean_box(1);
v___x_1827_ = lean_box(0);
v___x_1855_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1823_, v___x_1825_, v_env_1822_, v___x_1826_, v___x_1827_);
v___x_1856_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg(v___x_1855_, v_entry_1824_);
if (v___x_1856_ == 0)
{
lean_object* v_cls_1857_; lean_object* v___x_1858_; lean_object* v_a_1859_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1866_; lean_object* v___y_1867_; uint8_t v___x_1879_; 
v_cls_1857_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__4));
v___x_1858_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(v_cls_1857_, v___y_1816_);
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref(v___x_1858_);
v___x_1879_ = lean_unbox(v_a_1859_);
lean_dec(v_a_1859_);
if (v___x_1879_ == 0)
{
lean_dec(v_hint_1814_);
lean_dec(v_mod_1812_);
v___y_1829_ = v___y_1816_;
goto v___jp_1828_;
}
else
{
lean_object* v___x_1880_; lean_object* v___y_1882_; 
v___x_1880_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__11);
if (v_isExporting_1820_ == 0)
{
lean_object* v___x_1889_; 
v___x_1889_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__16));
v___y_1882_ = v___x_1889_;
goto v___jp_1881_;
}
else
{
lean_object* v___x_1890_; 
v___x_1890_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__17));
v___y_1882_ = v___x_1890_;
goto v___jp_1881_;
}
v___jp_1881_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1883_ = l_Lean_stringToMessageData(v___y_1882_);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1880_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__13);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
if (v_isMeta_1813_ == 0)
{
lean_object* v___x_1887_; 
v___x_1887_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__14));
v___y_1866_ = v___x_1886_;
v___y_1867_ = v___x_1887_;
goto v___jp_1865_;
}
else
{
lean_object* v___x_1888_; 
v___x_1888_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__15));
v___y_1866_ = v___x_1886_;
v___y_1867_ = v___x_1888_;
goto v___jp_1865_;
}
}
}
v___jp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___y_1861_);
lean_ctor_set(v___x_1863_, 1, v___y_1862_);
v___x_1864_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(v_cls_1857_, v___x_1863_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_dec_ref(v___x_1864_);
v___y_1829_ = v___y_1816_;
goto v___jp_1828_;
}
else
{
lean_dec_ref(v_entry_1824_);
return v___x_1864_;
}
}
v___jp_1865_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; 
v___x_1868_ = l_Lean_stringToMessageData(v___y_1867_);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___y_1866_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__6);
v___x_1871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1869_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = l_Lean_MessageData_ofName(v_mod_1812_);
v___x_1873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1871_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = l_Lean_Name_isAnonymous(v_hint_1814_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__8);
v___x_1876_ = l_Lean_MessageData_ofName(v_hint_1814_);
v___x_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___y_1861_ = v___x_1873_;
v___y_1862_ = v___x_1877_;
goto v___jp_1860_;
}
else
{
lean_object* v___x_1878_; 
lean_dec(v_hint_1814_);
v___x_1878_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___closed__9);
v___y_1861_ = v___x_1873_;
v___y_1862_ = v___x_1878_;
goto v___jp_1860_;
}
}
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
lean_dec_ref(v_entry_1824_);
lean_dec(v_hint_1814_);
lean_dec(v_mod_1812_);
v___x_1891_ = lean_box(0);
v___x_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
return v___x_1892_;
}
v___jp_1828_:
{
lean_object* v___x_1830_; lean_object* v_toEnvExtension_1831_; lean_object* v_env_1832_; lean_object* v_messages_1833_; lean_object* v_scopes_1834_; lean_object* v_usedQuotCtxts_1835_; lean_object* v_nextMacroScope_1836_; lean_object* v_maxRecDepth_1837_; lean_object* v_ngen_1838_; lean_object* v_auxDeclNGen_1839_; lean_object* v_infoState_1840_; lean_object* v_traceState_1841_; lean_object* v_snapshotTasks_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1854_; 
v___x_1830_ = lean_st_ref_take(v___y_1829_);
v_toEnvExtension_1831_ = lean_ctor_get(v___x_1825_, 0);
lean_inc_ref(v_toEnvExtension_1831_);
v_env_1832_ = lean_ctor_get(v___x_1830_, 0);
v_messages_1833_ = lean_ctor_get(v___x_1830_, 1);
v_scopes_1834_ = lean_ctor_get(v___x_1830_, 2);
v_usedQuotCtxts_1835_ = lean_ctor_get(v___x_1830_, 3);
v_nextMacroScope_1836_ = lean_ctor_get(v___x_1830_, 4);
v_maxRecDepth_1837_ = lean_ctor_get(v___x_1830_, 5);
v_ngen_1838_ = lean_ctor_get(v___x_1830_, 6);
v_auxDeclNGen_1839_ = lean_ctor_get(v___x_1830_, 7);
v_infoState_1840_ = lean_ctor_get(v___x_1830_, 8);
v_traceState_1841_ = lean_ctor_get(v___x_1830_, 9);
v_snapshotTasks_1842_ = lean_ctor_get(v___x_1830_, 10);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1844_ = v___x_1830_;
v_isShared_1845_ = v_isSharedCheck_1854_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_snapshotTasks_1842_);
lean_inc(v_traceState_1841_);
lean_inc(v_infoState_1840_);
lean_inc(v_auxDeclNGen_1839_);
lean_inc(v_ngen_1838_);
lean_inc(v_maxRecDepth_1837_);
lean_inc(v_nextMacroScope_1836_);
lean_inc(v_usedQuotCtxts_1835_);
lean_inc(v_scopes_1834_);
lean_inc(v_messages_1833_);
lean_inc(v_env_1832_);
lean_dec(v___x_1830_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1854_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v_asyncMode_1846_; lean_object* v___x_1847_; lean_object* v___x_1849_; 
v_asyncMode_1846_ = lean_ctor_get(v_toEnvExtension_1831_, 2);
lean_inc(v_asyncMode_1846_);
lean_dec_ref(v_toEnvExtension_1831_);
v___x_1847_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1825_, v_env_1832_, v_entry_1824_, v_asyncMode_1846_, v___x_1827_);
lean_dec(v_asyncMode_1846_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1847_);
v___x_1849_ = v___x_1844_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_messages_1833_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_scopes_1834_);
lean_ctor_set(v_reuseFailAlloc_1853_, 3, v_usedQuotCtxts_1835_);
lean_ctor_set(v_reuseFailAlloc_1853_, 4, v_nextMacroScope_1836_);
lean_ctor_set(v_reuseFailAlloc_1853_, 5, v_maxRecDepth_1837_);
lean_ctor_set(v_reuseFailAlloc_1853_, 6, v_ngen_1838_);
lean_ctor_set(v_reuseFailAlloc_1853_, 7, v_auxDeclNGen_1839_);
lean_ctor_set(v_reuseFailAlloc_1853_, 8, v_infoState_1840_);
lean_ctor_set(v_reuseFailAlloc_1853_, 9, v_traceState_1841_);
lean_ctor_set(v_reuseFailAlloc_1853_, 10, v_snapshotTasks_1842_);
v___x_1849_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = lean_st_ref_set(v___y_1829_, v___x_1849_);
v___x_1851_ = lean_box(0);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7___boxed(lean_object* v_mod_1893_, lean_object* v_isMeta_1894_, lean_object* v_hint_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
uint8_t v_isMeta_boxed_1899_; lean_object* v_res_1900_; 
v_isMeta_boxed_1899_ = lean_unbox(v_isMeta_1894_);
v_res_1900_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7(v_mod_1893_, v_isMeta_boxed_1899_, v_hint_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8(lean_object* v___x_1901_, lean_object* v_declName_1902_, lean_object* v_as_1903_, size_t v_sz_1904_, size_t v_i_1905_, lean_object* v_b_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
uint8_t v___x_1910_; 
v___x_1910_ = lean_usize_dec_lt(v_i_1905_, v_sz_1904_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; 
lean_dec(v_declName_1902_);
v___x_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1911_, 0, v_b_1906_);
return v___x_1911_;
}
else
{
lean_object* v___x_1912_; lean_object* v_modules_1913_; lean_object* v___x_1914_; lean_object* v_a_1915_; lean_object* v___x_1916_; lean_object* v_toImport_1917_; lean_object* v_module_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; 
v___x_1912_ = l_Lean_Environment_header(v___x_1901_);
v_modules_1913_ = lean_ctor_get(v___x_1912_, 3);
lean_inc_ref(v_modules_1913_);
lean_dec_ref(v___x_1912_);
v___x_1914_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1915_ = lean_array_uget_borrowed(v_as_1903_, v_i_1905_);
v___x_1916_ = lean_array_get(v___x_1914_, v_modules_1913_, v_a_1915_);
lean_dec_ref(v_modules_1913_);
v_toImport_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc_ref(v_toImport_1917_);
lean_dec(v___x_1916_);
v_module_1918_ = lean_ctor_get(v_toImport_1917_, 0);
lean_inc(v_module_1918_);
lean_dec_ref(v_toImport_1917_);
v___x_1919_ = 0;
lean_inc(v_declName_1902_);
v___x_1920_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7(v_module_1918_, v___x_1919_, v_declName_1902_, v___y_1907_, v___y_1908_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v___x_1921_; size_t v___x_1922_; size_t v___x_1923_; 
lean_dec_ref(v___x_1920_);
v___x_1921_ = lean_box(0);
v___x_1922_ = ((size_t)1ULL);
v___x_1923_ = lean_usize_add(v_i_1905_, v___x_1922_);
v_i_1905_ = v___x_1923_;
v_b_1906_ = v___x_1921_;
goto _start;
}
else
{
lean_dec(v_declName_1902_);
return v___x_1920_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8___boxed(lean_object* v___x_1925_, lean_object* v_declName_1926_, lean_object* v_as_1927_, lean_object* v_sz_1928_, lean_object* v_i_1929_, lean_object* v_b_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
size_t v_sz_boxed_1934_; size_t v_i_boxed_1935_; lean_object* v_res_1936_; 
v_sz_boxed_1934_ = lean_unbox_usize(v_sz_1928_);
lean_dec(v_sz_1928_);
v_i_boxed_1935_ = lean_unbox_usize(v_i_1929_);
lean_dec(v_i_1929_);
v_res_1936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8(v___x_1925_, v_declName_1926_, v_as_1927_, v_sz_boxed_1934_, v_i_boxed_1935_, v_b_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec_ref(v_as_1927_);
lean_dec_ref(v___x_1925_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg(lean_object* v_a_1937_, lean_object* v_x_1938_){
_start:
{
if (lean_obj_tag(v_x_1938_) == 0)
{
lean_object* v___x_1939_; 
v___x_1939_ = lean_box(0);
return v___x_1939_;
}
else
{
lean_object* v_key_1940_; lean_object* v_value_1941_; lean_object* v_tail_1942_; uint8_t v___x_1943_; 
v_key_1940_ = lean_ctor_get(v_x_1938_, 0);
v_value_1941_ = lean_ctor_get(v_x_1938_, 1);
v_tail_1942_ = lean_ctor_get(v_x_1938_, 2);
v___x_1943_ = lean_name_eq(v_key_1940_, v_a_1937_);
if (v___x_1943_ == 0)
{
v_x_1938_ = v_tail_1942_;
goto _start;
}
else
{
lean_object* v___x_1945_; 
lean_inc(v_value_1941_);
v___x_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1945_, 0, v_value_1941_);
return v___x_1945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg___boxed(lean_object* v_a_1946_, lean_object* v_x_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg(v_a_1946_, v_x_1947_);
lean_dec(v_x_1947_);
lean_dec(v_a_1946_);
return v_res_1948_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1949_; uint64_t v___x_1950_; 
v___x_1949_ = lean_unsigned_to_nat(1723u);
v___x_1950_ = lean_uint64_of_nat(v___x_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg(lean_object* v_m_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v_buckets_1953_; lean_object* v___x_1954_; uint64_t v___y_1956_; 
v_buckets_1953_ = lean_ctor_get(v_m_1951_, 1);
v___x_1954_ = lean_array_get_size(v_buckets_1953_);
if (lean_obj_tag(v_a_1952_) == 0)
{
uint64_t v___x_1970_; 
v___x_1970_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___closed__0);
v___y_1956_ = v___x_1970_;
goto v___jp_1955_;
}
else
{
uint64_t v_hash_1971_; 
v_hash_1971_ = lean_ctor_get_uint64(v_a_1952_, sizeof(void*)*2);
v___y_1956_ = v_hash_1971_;
goto v___jp_1955_;
}
v___jp_1955_:
{
uint64_t v___x_1957_; uint64_t v___x_1958_; uint64_t v_fold_1959_; uint64_t v___x_1960_; uint64_t v___x_1961_; uint64_t v___x_1962_; size_t v___x_1963_; size_t v___x_1964_; size_t v___x_1965_; size_t v___x_1966_; size_t v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1957_ = 32ULL;
v___x_1958_ = lean_uint64_shift_right(v___y_1956_, v___x_1957_);
v_fold_1959_ = lean_uint64_xor(v___y_1956_, v___x_1958_);
v___x_1960_ = 16ULL;
v___x_1961_ = lean_uint64_shift_right(v_fold_1959_, v___x_1960_);
v___x_1962_ = lean_uint64_xor(v_fold_1959_, v___x_1961_);
v___x_1963_ = lean_uint64_to_usize(v___x_1962_);
v___x_1964_ = lean_usize_of_nat(v___x_1954_);
v___x_1965_ = ((size_t)1ULL);
v___x_1966_ = lean_usize_sub(v___x_1964_, v___x_1965_);
v___x_1967_ = lean_usize_land(v___x_1963_, v___x_1966_);
v___x_1968_ = lean_array_uget_borrowed(v_buckets_1953_, v___x_1967_);
v___x_1969_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg(v_a_1952_, v___x_1968_);
return v___x_1969_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg___boxed(lean_object* v_m_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg(v_m_1972_, v_a_1973_);
lean_dec(v_a_1973_);
lean_dec_ref(v_m_1972_);
return v_res_1974_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__1));
v___x_1978_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__0));
v___x_1979_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1978_, v___x_1977_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(lean_object* v_declName_1982_, uint8_t v_isMeta_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; lean_object* v_env_1991_; lean_object* v___y_1993_; lean_object* v___x_2006_; 
v___x_1987_ = lean_st_ref_get(v___y_1985_);
v_env_1991_ = lean_ctor_get(v___x_1987_, 0);
lean_inc_ref(v_env_1991_);
lean_dec(v___x_1987_);
v___x_2006_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1991_, v_declName_1982_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_dec_ref(v_env_1991_);
lean_dec(v_declName_1982_);
goto v___jp_1988_;
}
else
{
lean_object* v_val_2007_; lean_object* v___x_2008_; lean_object* v_modules_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
v_val_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_val_2007_);
lean_dec_ref(v___x_2006_);
v___x_2008_ = l_Lean_Environment_header(v_env_1991_);
v_modules_2009_ = lean_ctor_get(v___x_2008_, 3);
lean_inc_ref(v_modules_2009_);
lean_dec_ref(v___x_2008_);
v___x_2010_ = lean_array_get_size(v_modules_2009_);
v___x_2011_ = lean_nat_dec_lt(v_val_2007_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_dec_ref(v_modules_2009_);
lean_dec(v_val_2007_);
lean_dec_ref(v_env_1991_);
lean_dec(v_declName_1982_);
goto v___jp_1988_;
}
else
{
lean_object* v___x_2012_; lean_object* v_env_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___y_2017_; 
v___x_2012_ = lean_st_ref_get(v___y_1985_);
v_env_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc_ref(v_env_2013_);
lean_dec(v___x_2012_);
v___x_2014_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__2);
v___x_2015_ = lean_array_fget(v_modules_2009_, v_val_2007_);
lean_dec(v_val_2007_);
lean_dec_ref(v_modules_2009_);
if (v_isMeta_1983_ == 0)
{
lean_dec_ref(v_env_2013_);
v___y_2017_ = v_isMeta_1983_;
goto v___jp_2016_;
}
else
{
uint8_t v___x_2028_; 
lean_inc(v_declName_1982_);
v___x_2028_ = l_Lean_isMarkedMeta(v_env_2013_, v_declName_1982_);
if (v___x_2028_ == 0)
{
v___y_2017_ = v_isMeta_1983_;
goto v___jp_2016_;
}
else
{
uint8_t v___x_2029_; 
v___x_2029_ = 0;
v___y_2017_ = v___x_2029_;
goto v___jp_2016_;
}
}
v___jp_2016_:
{
lean_object* v_toImport_2018_; lean_object* v_module_2019_; lean_object* v___x_2020_; 
v_toImport_2018_ = lean_ctor_get(v___x_2015_, 0);
lean_inc_ref(v_toImport_2018_);
lean_dec(v___x_2015_);
v_module_2019_ = lean_ctor_get(v_toImport_2018_, 0);
lean_inc(v_module_2019_);
lean_dec_ref(v_toImport_2018_);
lean_inc(v_declName_1982_);
v___x_2020_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7(v_module_2019_, v___y_2017_, v_declName_1982_, v___y_1984_, v___y_1985_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
lean_dec_ref(v___x_2020_);
v___x_2021_ = l_Lean_indirectModUseExt;
v___x_2022_ = lean_box(1);
v___x_2023_ = lean_box(0);
lean_inc_ref(v_env_1991_);
v___x_2024_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2014_, v___x_2021_, v_env_1991_, v___x_2022_, v___x_2023_);
v___x_2025_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg(v___x_2024_, v_declName_1982_);
lean_dec(v___x_2024_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v___x_2026_; 
v___x_2026_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___closed__3));
v___y_1993_ = v___x_2026_;
goto v___jp_1992_;
}
else
{
lean_object* v_val_2027_; 
v_val_2027_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_val_2027_);
lean_dec_ref(v___x_2025_);
v___y_1993_ = v_val_2027_;
goto v___jp_1992_;
}
}
else
{
lean_dec_ref(v_env_1991_);
lean_dec(v_declName_1982_);
return v___x_2020_;
}
}
}
}
v___jp_1988_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_box(0);
v___x_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
return v___x_1990_;
}
v___jp_1992_:
{
lean_object* v___x_1994_; size_t v_sz_1995_; size_t v___x_1996_; lean_object* v___x_1997_; 
v___x_1994_ = lean_box(0);
v_sz_1995_ = lean_array_size(v___y_1993_);
v___x_1996_ = ((size_t)0ULL);
v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__8(v_env_1991_, v_declName_1982_, v___y_1993_, v_sz_1995_, v___x_1996_, v___x_1994_, v___y_1984_, v___y_1985_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v_env_1991_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; 
v_unused_2005_ = lean_ctor_get(v___x_1997_, 0);
lean_dec(v_unused_2005_);
v___x_1999_ = v___x_1997_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_dec(v___x_1997_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_1994_);
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1994_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
else
{
return v___x_1997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___boxed(lean_object* v_declName_2030_, lean_object* v_isMeta_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
uint8_t v_isMeta_boxed_2035_; lean_object* v_res_2036_; 
v_isMeta_boxed_2035_ = lean_unbox(v_isMeta_2031_);
v_res_2036_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(v_declName_2030_, v_isMeta_boxed_2035_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg(lean_object* v_as_x27_2037_, lean_object* v_b_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
if (lean_obj_tag(v_as_x27_2037_) == 0)
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v_b_2038_);
return v___x_2042_;
}
else
{
lean_object* v_head_2043_; lean_object* v_tail_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; 
v_head_2043_ = lean_ctor_get(v_as_x27_2037_, 0);
lean_inc(v_head_2043_);
v_tail_2044_ = lean_ctor_get(v_as_x27_2037_, 1);
lean_inc(v_tail_2044_);
lean_dec_ref(v_as_x27_2037_);
v___x_2045_ = 1;
v___x_2046_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(v_head_2043_, v___x_2045_, v___y_2039_, v___y_2040_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v___x_2047_; 
lean_dec_ref(v___x_2046_);
v___x_2047_ = lean_box(0);
v_as_x27_2037_ = v_tail_2044_;
v_b_2038_ = v___x_2047_;
goto _start;
}
else
{
lean_dec(v_tail_2044_);
return v___x_2046_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg___boxed(lean_object* v_as_x27_2049_, lean_object* v_b_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg(v_as_x27_2049_, v_b_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(lean_object* v_env_2055_, lean_object* v_opts_2056_, lean_object* v_currNamespace_2057_, lean_object* v_openDecls_2058_, lean_object* v_n_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = l_Lean_ResolveName_resolveGlobalName(v_env_2055_, v_opts_2056_, v_currNamespace_2057_, v_openDecls_2058_, v_n_2059_);
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v___y_2061_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed(lean_object* v_env_2064_, lean_object* v_opts_2065_, lean_object* v_currNamespace_2066_, lean_object* v_openDecls_2067_, lean_object* v_n_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(v_env_2064_, v_opts_2065_, v_currNamespace_2066_, v_openDecls_2067_, v_n_2068_, v___y_2069_, v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec_ref(v_opts_2065_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(lean_object* v_env_2072_, lean_object* v_declName_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
uint8_t v___x_2076_; lean_object* v_env_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; uint8_t v___x_2080_; 
v___x_2076_ = 0;
v_env_2077_ = l_Lean_Environment_setExporting(v_env_2072_, v___x_2076_);
lean_inc(v_declName_2073_);
v___x_2078_ = l_Lean_mkPrivateName(v_env_2077_, v_declName_2073_);
v___x_2079_ = 1;
lean_inc_ref(v_env_2077_);
v___x_2080_ = l_Lean_Environment_contains(v_env_2077_, v___x_2078_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; uint8_t v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2081_ = l_Lean_privateToUserName(v_declName_2073_);
v___x_2082_ = l_Lean_Environment_contains(v_env_2077_, v___x_2081_, v___x_2079_);
v___x_2083_ = lean_box(v___x_2082_);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v___y_2075_);
return v___x_2084_;
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_dec_ref(v_env_2077_);
lean_dec(v_declName_2073_);
v___x_2085_ = lean_box(v___x_2080_);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v___y_2075_);
return v___x_2086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed(lean_object* v_env_2087_, lean_object* v_declName_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(v_env_2087_, v_declName_2088_, v___y_2089_, v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(lean_object* v_x_2092_, lean_object* v___y_2093_){
_start:
{
if (lean_obj_tag(v_x_2092_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2095_; 
v_a_2094_ = lean_ctor_get(v_x_2092_, 0);
lean_inc(v_a_2094_);
v___x_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2095_, 0, v_a_2094_);
lean_ctor_set(v___x_2095_, 1, v___y_2093_);
return v___x_2095_;
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2097_; 
v_a_2096_ = lean_ctor_get(v_x_2092_, 0);
lean_inc(v_a_2096_);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v_a_2096_);
lean_ctor_set(v___x_2097_, 1, v___y_2093_);
return v___x_2097_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg___boxed(lean_object* v_x_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(v_x_2098_, v___y_2099_);
lean_dec_ref(v_x_2098_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(lean_object* v_env_2101_, lean_object* v_stx_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2101_, v_stx_2102_, v___y_2103_, v___y_2104_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
if (lean_obj_tag(v_a_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2115_; 
v_a_2107_ = lean_ctor_get(v___x_2105_, 1);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v___x_2105_, 0);
lean_dec(v_unused_2116_);
v___x_2109_ = v___x_2105_;
v_isShared_2110_ = v_isSharedCheck_2115_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2105_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2115_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_box(0);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2111_);
v___x_2113_ = v___x_2109_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_a_2107_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
else
{
lean_object* v_val_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2145_; 
v_val_2117_ = lean_ctor_get(v_a_2106_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_a_2106_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2119_ = v_a_2106_;
v_isShared_2120_ = v_isSharedCheck_2145_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_val_2117_);
lean_dec(v_a_2106_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2145_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v_snd_2121_; 
v_snd_2121_ = lean_ctor_get(v_val_2117_, 1);
lean_inc(v_snd_2121_);
lean_dec(v_val_2117_);
if (lean_obj_tag(v_snd_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2131_; 
lean_del_object(v___x_2119_);
v_a_2122_ = lean_ctor_get(v___x_2105_, 1);
lean_inc(v_a_2122_);
lean_dec_ref(v___x_2105_);
v_a_2123_ = lean_ctor_get(v_snd_2121_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_snd_2121_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2125_ = v_snd_2121_;
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v_snd_2121_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(v___x_2128_, v_a_2122_);
lean_dec_ref(v___x_2128_);
return v___x_2129_;
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2144_; 
v_a_2132_ = lean_ctor_get(v___x_2105_, 1);
lean_inc(v_a_2132_);
lean_dec_ref(v___x_2105_);
v_a_2133_ = lean_ctor_get(v_snd_2121_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_snd_2121_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2135_ = v_snd_2121_;
v_isShared_2136_ = v_isSharedCheck_2144_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v_snd_2121_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2144_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v_a_2133_);
v___x_2138_ = v___x_2119_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2138_);
v___x_2140_ = v___x_2135_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(v___x_2140_, v_a_2132_);
lean_dec_ref(v___x_2140_);
return v___x_2141_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
v_a_2146_ = lean_ctor_get(v___x_2105_, 0);
v_a_2147_ = lean_ctor_get(v___x_2105_, 1);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2105_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_inc(v_a_2146_);
lean_dec(v___x_2105_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2146_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed(lean_object* v_env_2155_, lean_object* v_stx_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(v_env_2155_, v_stx_2156_, v___y_2157_, v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(lean_object* v_as_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
if (lean_obj_tag(v_as_2160_) == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = lean_box(0);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
return v___x_2165_;
}
else
{
lean_object* v_head_2166_; lean_object* v_tail_2167_; lean_object* v_fst_2168_; lean_object* v_snd_2169_; lean_object* v___x_2170_; lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2183_; 
v_head_2166_ = lean_ctor_get(v_as_2160_, 0);
lean_inc(v_head_2166_);
v_tail_2167_ = lean_ctor_get(v_as_2160_, 1);
lean_inc(v_tail_2167_);
lean_dec_ref(v_as_2160_);
v_fst_2168_ = lean_ctor_get(v_head_2166_, 0);
lean_inc(v_fst_2168_);
v_snd_2169_ = lean_ctor_get(v_head_2166_, 1);
lean_inc(v_snd_2169_);
lean_dec(v_head_2166_);
lean_inc(v_fst_2168_);
v___x_2170_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(v_fst_2168_, v___y_2162_);
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2183_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2183_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
uint8_t v___x_2175_; 
v___x_2175_ = lean_unbox(v_a_2171_);
lean_dec(v_a_2171_);
if (v___x_2175_ == 0)
{
lean_del_object(v___x_2173_);
lean_dec(v_snd_2169_);
lean_dec(v_fst_2168_);
v_as_2160_ = v_tail_2167_;
goto _start;
}
else
{
lean_object* v___x_2178_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set_tag(v___x_2173_, 3);
lean_ctor_set(v___x_2173_, 0, v_snd_2169_);
v___x_2178_ = v___x_2173_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_snd_2169_);
v___x_2178_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = l_Lean_MessageData_ofFormat(v___x_2178_);
v___x_2180_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(v_fst_2168_, v___x_2179_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_dec_ref(v___x_2180_);
v_as_2160_ = v_tail_2167_;
goto _start;
}
else
{
lean_dec(v_tail_2167_);
return v___x_2180_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___boxed(lean_object* v_as_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(v_as_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(lean_object* v_x_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___x_2194_; lean_object* v_env_2195_; lean_object* v___x_2196_; lean_object* v_scopes_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v_opts_2200_; lean_object* v___x_2201_; 
v___x_2194_ = lean_st_ref_get(v___y_2192_);
v_env_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc_ref(v_env_2195_);
lean_dec(v___x_2194_);
v___x_2196_ = lean_st_ref_get(v___y_2192_);
v_scopes_2197_ = lean_ctor_get(v___x_2196_, 2);
lean_inc(v_scopes_2197_);
lean_dec(v___x_2196_);
v___x_2198_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2199_ = l_List_head_x21___redArg(v___x_2198_, v_scopes_2197_);
lean_dec(v_scopes_2197_);
v_opts_2200_ = lean_ctor_get(v___x_2199_, 1);
lean_inc_ref(v_opts_2200_);
lean_dec(v___x_2199_);
v___x_2201_ = l_Lean_Elab_Command_getScope___redArg(v___y_2192_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v_currNamespace_2203_; lean_object* v___x_2204_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref(v___x_2201_);
v_currNamespace_2203_ = lean_ctor_get(v_a_2202_, 2);
lean_inc(v_currNamespace_2203_);
lean_dec(v_a_2202_);
v___x_2204_ = l_Lean_Elab_Command_getScope___redArg(v___y_2192_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v_openDecls_2206_; lean_object* v___x_2207_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref(v___x_2204_);
v_openDecls_2206_ = lean_ctor_get(v_a_2205_, 3);
lean_inc(v_openDecls_2206_);
lean_dec(v_a_2205_);
v___x_2207_ = l_Lean_Elab_Command_getRef___redArg(v___y_2191_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2209_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref(v___x_2207_);
v___x_2209_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2191_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v_currRecDepth_2211_; lean_object* v_quotContext_x3f_2212_; lean_object* v___f_2213_; lean_object* v___f_2214_; lean_object* v___f_2215_; lean_object* v___f_2216_; lean_object* v___f_2217_; lean_object* v_methods_2218_; lean_object* v_a_2220_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref(v___x_2209_);
v_currRecDepth_2211_ = lean_ctor_get(v___y_2191_, 2);
v_quotContext_x3f_2212_ = lean_ctor_get(v___y_2191_, 5);
lean_inc_ref(v_env_2195_);
v___f_2213_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2213_, 0, v_env_2195_);
lean_inc_ref(v_env_2195_);
v___f_2214_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2214_, 0, v_env_2195_);
lean_inc(v_currNamespace_2203_);
v___f_2215_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2215_, 0, v_currNamespace_2203_);
lean_inc(v_openDecls_2206_);
lean_inc(v_currNamespace_2203_);
lean_inc_ref(v_env_2195_);
v___f_2216_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2216_, 0, v_env_2195_);
lean_closure_set(v___f_2216_, 1, v_currNamespace_2203_);
lean_closure_set(v___f_2216_, 2, v_openDecls_2206_);
v___f_2217_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2217_, 0, v_env_2195_);
lean_closure_set(v___f_2217_, 1, v_opts_2200_);
lean_closure_set(v___f_2217_, 2, v_currNamespace_2203_);
lean_closure_set(v___f_2217_, 3, v_openDecls_2206_);
v_methods_2218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2218_, 0, v___f_2214_);
lean_ctor_set(v_methods_2218_, 1, v___f_2215_);
lean_ctor_set(v_methods_2218_, 2, v___f_2213_);
lean_ctor_set(v_methods_2218_, 3, v___f_2216_);
lean_ctor_set(v_methods_2218_, 4, v___f_2217_);
if (lean_obj_tag(v_quotContext_x3f_2212_) == 0)
{
lean_object* v___x_2292_; lean_object* v_a_2293_; 
v___x_2292_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2192_);
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref(v___x_2292_);
v_a_2220_ = v_a_2293_;
goto v___jp_2219_;
}
else
{
lean_object* v_val_2294_; 
v_val_2294_ = lean_ctor_get(v_quotContext_x3f_2212_, 0);
lean_inc(v_val_2294_);
v_a_2220_ = v_val_2294_;
goto v___jp_2219_;
}
v___jp_2219_:
{
lean_object* v___x_2221_; lean_object* v_maxRecDepth_2222_; lean_object* v___x_2223_; lean_object* v_nextMacroScope_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2221_ = lean_st_ref_get(v___y_2192_);
v_maxRecDepth_2222_ = lean_ctor_get(v___x_2221_, 5);
lean_inc(v_maxRecDepth_2222_);
lean_dec(v___x_2221_);
v___x_2223_ = lean_st_ref_get(v___y_2192_);
v_nextMacroScope_2224_ = lean_ctor_get(v___x_2223_, 4);
lean_inc(v_nextMacroScope_2224_);
lean_dec(v___x_2223_);
lean_inc(v_currRecDepth_2211_);
v___x_2225_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2225_, 0, v_methods_2218_);
lean_ctor_set(v___x_2225_, 1, v_a_2220_);
lean_ctor_set(v___x_2225_, 2, v_a_2210_);
lean_ctor_set(v___x_2225_, 3, v_currRecDepth_2211_);
lean_ctor_set(v___x_2225_, 4, v_maxRecDepth_2222_);
lean_ctor_set(v___x_2225_, 5, v_a_2208_);
v___x_2226_ = lean_box(0);
v___x_2227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2227_, 0, v_nextMacroScope_2224_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
lean_ctor_set(v___x_2227_, 2, v___x_2226_);
v___x_2228_ = lean_apply_2(v_x_2190_, v___x_2225_, v___x_2227_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v_a_2230_; lean_object* v_macroScope_2231_; lean_object* v_traceMsgs_2232_; lean_object* v_expandedMacroDecls_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 1);
lean_inc(v_a_2229_);
v_a_2230_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2230_);
lean_dec_ref(v___x_2228_);
v_macroScope_2231_ = lean_ctor_get(v_a_2229_, 0);
lean_inc(v_macroScope_2231_);
v_traceMsgs_2232_ = lean_ctor_get(v_a_2229_, 1);
lean_inc(v_traceMsgs_2232_);
v_expandedMacroDecls_2233_ = lean_ctor_get(v_a_2229_, 2);
lean_inc(v_expandedMacroDecls_2233_);
lean_dec(v_a_2229_);
v___x_2234_ = lean_box(0);
v___x_2235_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg(v_expandedMacroDecls_2233_, v___x_2234_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v___x_2236_; lean_object* v_env_2237_; lean_object* v_messages_2238_; lean_object* v_scopes_2239_; lean_object* v_usedQuotCtxts_2240_; lean_object* v_maxRecDepth_2241_; lean_object* v_ngen_2242_; lean_object* v_auxDeclNGen_2243_; lean_object* v_infoState_2244_; lean_object* v_traceState_2245_; lean_object* v_snapshotTasks_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2272_; 
lean_dec_ref(v___x_2235_);
v___x_2236_ = lean_st_ref_take(v___y_2192_);
v_env_2237_ = lean_ctor_get(v___x_2236_, 0);
v_messages_2238_ = lean_ctor_get(v___x_2236_, 1);
v_scopes_2239_ = lean_ctor_get(v___x_2236_, 2);
v_usedQuotCtxts_2240_ = lean_ctor_get(v___x_2236_, 3);
v_maxRecDepth_2241_ = lean_ctor_get(v___x_2236_, 5);
v_ngen_2242_ = lean_ctor_get(v___x_2236_, 6);
v_auxDeclNGen_2243_ = lean_ctor_get(v___x_2236_, 7);
v_infoState_2244_ = lean_ctor_get(v___x_2236_, 8);
v_traceState_2245_ = lean_ctor_get(v___x_2236_, 9);
v_snapshotTasks_2246_ = lean_ctor_get(v___x_2236_, 10);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2272_ == 0)
{
lean_object* v_unused_2273_; 
v_unused_2273_ = lean_ctor_get(v___x_2236_, 4);
lean_dec(v_unused_2273_);
v___x_2248_ = v___x_2236_;
v_isShared_2249_ = v_isSharedCheck_2272_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_snapshotTasks_2246_);
lean_inc(v_traceState_2245_);
lean_inc(v_infoState_2244_);
lean_inc(v_auxDeclNGen_2243_);
lean_inc(v_ngen_2242_);
lean_inc(v_maxRecDepth_2241_);
lean_inc(v_usedQuotCtxts_2240_);
lean_inc(v_scopes_2239_);
lean_inc(v_messages_2238_);
lean_inc(v_env_2237_);
lean_dec(v___x_2236_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2272_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 4, v_macroScope_2231_);
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_env_2237_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_messages_2238_);
lean_ctor_set(v_reuseFailAlloc_2271_, 2, v_scopes_2239_);
lean_ctor_set(v_reuseFailAlloc_2271_, 3, v_usedQuotCtxts_2240_);
lean_ctor_set(v_reuseFailAlloc_2271_, 4, v_macroScope_2231_);
lean_ctor_set(v_reuseFailAlloc_2271_, 5, v_maxRecDepth_2241_);
lean_ctor_set(v_reuseFailAlloc_2271_, 6, v_ngen_2242_);
lean_ctor_set(v_reuseFailAlloc_2271_, 7, v_auxDeclNGen_2243_);
lean_ctor_set(v_reuseFailAlloc_2271_, 8, v_infoState_2244_);
lean_ctor_set(v_reuseFailAlloc_2271_, 9, v_traceState_2245_);
lean_ctor_set(v_reuseFailAlloc_2271_, 10, v_snapshotTasks_2246_);
v___x_2251_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = lean_st_ref_set(v___y_2192_, v___x_2251_);
v___x_2253_ = l_List_reverse___redArg(v_traceMsgs_2232_);
v___x_2254_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(v___x_2253_, v___y_2191_, v___y_2192_);
lean_dec_ref(v___y_2191_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2261_ == 0)
{
lean_object* v_unused_2262_; 
v_unused_2262_ = lean_ctor_get(v___x_2254_, 0);
lean_dec(v_unused_2262_);
v___x_2256_ = v___x_2254_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_dec(v___x_2254_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v_a_2230_);
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2230_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v_a_2230_);
v_a_2263_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2254_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2254_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v_traceMsgs_2232_);
lean_dec(v_macroScope_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v___y_2191_);
v_a_2274_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2235_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2235_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
else
{
lean_object* v_a_2282_; 
v_a_2282_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2282_);
lean_dec_ref(v___x_2228_);
if (lean_obj_tag(v_a_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v_a_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v_a_2283_ = lean_ctor_get(v_a_2282_, 0);
lean_inc(v_a_2283_);
v_a_2284_ = lean_ctor_get(v_a_2282_, 1);
lean_inc_ref(v_a_2284_);
lean_dec_ref(v_a_2282_);
v___x_2285_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0));
v___x_2286_ = lean_string_dec_eq(v_a_2284_, v___x_2285_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2287_, 0, v_a_2284_);
v___x_2288_ = l_Lean_MessageData_ofFormat(v___x_2287_);
v___x_2289_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_a_2283_, v___x_2288_, v___y_2191_, v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v_a_2283_);
return v___x_2289_;
}
else
{
lean_object* v___x_2290_; 
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___y_2191_);
v___x_2290_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg(v_a_2283_);
return v___x_2290_;
}
}
else
{
lean_object* v___x_2291_; 
lean_dec_ref(v___y_2191_);
v___x_2291_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2291_;
}
}
}
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec(v_a_2208_);
lean_dec(v_openDecls_2206_);
lean_dec(v_currNamespace_2203_);
lean_dec_ref(v_opts_2200_);
lean_dec_ref(v_env_2195_);
lean_dec_ref(v___y_2191_);
lean_dec_ref(v_x_2190_);
v_a_2295_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2209_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2209_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec(v_openDecls_2206_);
lean_dec(v_currNamespace_2203_);
lean_dec_ref(v_opts_2200_);
lean_dec_ref(v_env_2195_);
lean_dec_ref(v___y_2191_);
lean_dec_ref(v_x_2190_);
v_a_2303_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2207_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2207_);
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
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec(v_currNamespace_2203_);
lean_dec_ref(v_opts_2200_);
lean_dec_ref(v_env_2195_);
lean_dec_ref(v___y_2191_);
lean_dec_ref(v_x_2190_);
v_a_2311_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2204_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2204_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec_ref(v_opts_2200_);
lean_dec_ref(v_env_2195_);
lean_dec_ref(v___y_2191_);
lean_dec_ref(v_x_2190_);
v_a_2319_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2201_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2201_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___boxed(lean_object* v_x_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(lean_object* v_as_2332_, size_t v_i_2333_, size_t v_stop_2334_, lean_object* v_b_2335_){
_start:
{
lean_object* v___y_2337_; uint8_t v___x_2341_; 
v___x_2341_ = lean_usize_dec_eq(v_i_2333_, v_stop_2334_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
v___x_2342_ = lean_array_uget_borrowed(v_as_2332_, v_i_2333_);
lean_inc(v___x_2342_);
v___x_2343_ = l_Lean_Syntax_getKind(v___x_2342_);
v___x_2344_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
v___x_2345_ = lean_name_eq(v___x_2343_, v___x_2344_);
lean_dec(v___x_2343_);
if (v___x_2345_ == 0)
{
v___y_2337_ = v_b_2335_;
goto v___jp_2336_;
}
else
{
lean_object* v___x_2346_; 
lean_inc(v___x_2342_);
v___x_2346_ = lean_array_push(v_b_2335_, v___x_2342_);
v___y_2337_ = v___x_2346_;
goto v___jp_2336_;
}
}
else
{
return v_b_2335_;
}
v___jp_2336_:
{
size_t v___x_2338_; size_t v___x_2339_; 
v___x_2338_ = ((size_t)1ULL);
v___x_2339_ = lean_usize_add(v_i_2333_, v___x_2338_);
v_i_2333_ = v___x_2339_;
v_b_2335_ = v___y_2337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8___boxed(lean_object* v_as_2347_, lean_object* v_i_2348_, lean_object* v_stop_2349_, lean_object* v_b_2350_){
_start:
{
size_t v_i_boxed_2351_; size_t v_stop_boxed_2352_; lean_object* v_res_2353_; 
v_i_boxed_2351_ = lean_unbox_usize(v_i_2348_);
lean_dec(v_i_2348_);
v_stop_boxed_2352_ = lean_unbox_usize(v_stop_2349_);
lean_dec(v_stop_2349_);
v_res_2353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v_as_2347_, v_i_boxed_2351_, v_stop_boxed_2352_, v_b_2350_);
lean_dec_ref(v_as_2347_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation(lean_object* v_x_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; uint8_t v___x_2430_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2485_; lean_object* v___y_2486_; uint8_t v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; size_t v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; 
v___x_2427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0));
v___x_2428_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1));
v___x_2429_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
lean_inc(v_x_2396_);
v___x_2430_ = l_Lean_Syntax_isOfKind(v_x_2396_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2539_; 
lean_dec(v_x_2396_);
v___x_2539_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2539_;
}
else
{
lean_object* v___x_2540_; lean_object* v___y_2542_; lean_object* v___y_2543_; uint8_t v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; size_t v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2616_; lean_object* v___y_2617_; uint8_t v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; size_t v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2652_; lean_object* v___y_2653_; uint8_t v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; size_t v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2683_; lean_object* v___y_2684_; uint8_t v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; size_t v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2718_; lean_object* v___y_2719_; uint8_t v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; size_t v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v_prio_x3f_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v_name_x3f_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v_prec_x3f_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v_attrs_x3f_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v_doc_x3f_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___x_2895_; uint8_t v___x_2896_; 
v___x_2540_ = lean_unsigned_to_nat(0u);
v___x_2895_ = l_Lean_Syntax_getArg(v_x_2396_, v___x_2540_);
v___x_2896_ = l_Lean_Syntax_isNone(v___x_2895_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; uint8_t v___x_2898_; 
v___x_2897_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2895_);
v___x_2898_ = l_Lean_Syntax_matchesNull(v___x_2895_, v___x_2897_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; 
lean_dec(v___x_2895_);
lean_dec(v_x_2396_);
v___x_2899_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2899_;
}
else
{
lean_object* v_doc_x3f_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; 
v_doc_x3f_2900_ = l_Lean_Syntax_getArg(v___x_2895_, v___x_2540_);
lean_dec(v___x_2895_);
v___x_2901_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__15));
lean_inc(v_doc_x3f_2900_);
v___x_2902_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2900_, v___x_2901_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; 
lean_dec(v_doc_x3f_2900_);
lean_dec(v_x_2396_);
v___x_2903_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2903_;
}
else
{
lean_object* v___x_2904_; 
v___x_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2904_, 0, v_doc_x3f_2900_);
v_doc_x3f_2879_ = v___x_2904_;
v___y_2880_ = v_a_2397_;
v___y_2881_ = v_a_2398_;
goto v___jp_2878_;
}
}
}
else
{
lean_object* v___x_2905_; 
lean_dec(v___x_2895_);
v___x_2905_ = lean_box(0);
v_doc_x3f_2879_ = v___x_2905_;
v___y_2880_ = v_a_2397_;
v___y_2881_ = v_a_2398_;
goto v___jp_2878_;
}
v___jp_2541_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; size_t v_sz_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
lean_inc_ref(v___y_2545_);
v___x_2562_ = l_Array_append___redArg(v___y_2545_, v___y_2561_);
lean_dec_ref(v___y_2561_);
lean_inc(v___y_2549_);
lean_inc(v___y_2547_);
v___x_2563_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2563_, 0, v___y_2547_);
lean_ctor_set(v___x_2563_, 1, v___y_2549_);
lean_ctor_set(v___x_2563_, 2, v___x_2562_);
v___x_2564_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
v___x_2565_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc(v___y_2547_);
v___x_2566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___y_2547_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__8));
lean_inc(v___y_2547_);
v___x_2568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___y_2547_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
lean_inc(v___y_2547_);
v___x_2570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___y_2547_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = l_Nat_reprFast(v___y_2542_);
v___x_2572_ = lean_box(2);
v___x_2573_ = l_Lean_Syntax_mkNumLit(v___x_2571_, v___x_2572_);
v___x_2574_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
lean_inc(v___y_2547_);
v___x_2575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___y_2547_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
lean_inc(v___y_2547_);
v___x_2576_ = l_Lean_Syntax_node5(v___y_2547_, v___x_2564_, v___x_2566_, v___x_2568_, v___x_2570_, v___x_2573_, v___x_2575_);
lean_inc(v___y_2549_);
lean_inc(v___y_2547_);
v___x_2577_ = l_Lean_Syntax_node1(v___y_2547_, v___y_2549_, v___x_2576_);
v_sz_2578_ = lean_array_size(v___y_2557_);
v___x_2579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_2578_, v___y_2552_, v___y_2557_);
lean_inc_ref(v___y_2545_);
v___x_2580_ = l_Array_append___redArg(v___y_2545_, v___x_2579_);
lean_dec_ref(v___x_2579_);
lean_inc(v___y_2549_);
lean_inc(v___y_2547_);
v___x_2581_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2581_, 0, v___y_2547_);
lean_ctor_set(v___x_2581_, 1, v___y_2549_);
lean_ctor_set(v___x_2581_, 2, v___x_2580_);
v___x_2582_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc(v___y_2547_);
v___x_2583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___y_2547_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = lean_unsigned_to_nat(10u);
v___x_2585_ = lean_mk_empty_array_with_capacity(v___x_2584_);
v___x_2586_ = lean_array_push(v___x_2585_, v___y_2556_);
v___x_2587_ = lean_array_push(v___x_2586_, v___y_2558_);
lean_inc(v___y_2560_);
v___x_2588_ = lean_array_push(v___x_2587_, v___y_2560_);
v___x_2589_ = lean_array_push(v___x_2588_, v___y_2546_);
v___x_2590_ = lean_array_push(v___x_2589_, v___y_2550_);
v___x_2591_ = lean_array_push(v___x_2590_, v___x_2563_);
v___x_2592_ = lean_array_push(v___x_2591_, v___x_2577_);
v___x_2593_ = lean_array_push(v___x_2592_, v___x_2581_);
v___x_2594_ = lean_array_push(v___x_2593_, v___x_2583_);
v___x_2595_ = lean_array_push(v___x_2594_, v___y_2559_);
v___x_2596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2596_, 0, v___y_2547_);
lean_ctor_set(v___x_2596_, 1, v___y_2554_);
lean_ctor_set(v___x_2596_, 2, v___x_2595_);
v___x_2597_ = l_Lean_Elab_Command_elabSyntax(v___x_2596_, v___y_2551_, v___y_2553_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref(v___x_2597_);
v___x_2599_ = lean_array_get_size(v___y_2555_);
v___x_2600_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__68));
v___x_2601_ = lean_nat_dec_lt(v___x_2540_, v___x_2599_);
if (v___x_2601_ == 0)
{
v___y_2485_ = v_a_2598_;
v___y_2486_ = v___y_2543_;
v___y_2487_ = v___y_2544_;
v___y_2488_ = v___y_2545_;
v___y_2489_ = v___x_2574_;
v___y_2490_ = v___y_2549_;
v___y_2491_ = v___y_2548_;
v___y_2492_ = v___x_2572_;
v___y_2493_ = v___y_2551_;
v___y_2494_ = v___y_2552_;
v___y_2495_ = v___y_2553_;
v___y_2496_ = v___y_2555_;
v___y_2497_ = v___y_2560_;
v___y_2498_ = v___x_2600_;
goto v___jp_2484_;
}
else
{
uint8_t v___x_2602_; 
v___x_2602_ = lean_nat_dec_le(v___x_2599_, v___x_2599_);
if (v___x_2602_ == 0)
{
if (v___x_2601_ == 0)
{
v___y_2485_ = v_a_2598_;
v___y_2486_ = v___y_2543_;
v___y_2487_ = v___y_2544_;
v___y_2488_ = v___y_2545_;
v___y_2489_ = v___x_2574_;
v___y_2490_ = v___y_2549_;
v___y_2491_ = v___y_2548_;
v___y_2492_ = v___x_2572_;
v___y_2493_ = v___y_2551_;
v___y_2494_ = v___y_2552_;
v___y_2495_ = v___y_2553_;
v___y_2496_ = v___y_2555_;
v___y_2497_ = v___y_2560_;
v___y_2498_ = v___x_2600_;
goto v___jp_2484_;
}
else
{
size_t v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = lean_usize_of_nat(v___x_2599_);
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2555_, v___y_2552_, v___x_2603_, v___x_2600_);
v___y_2485_ = v_a_2598_;
v___y_2486_ = v___y_2543_;
v___y_2487_ = v___y_2544_;
v___y_2488_ = v___y_2545_;
v___y_2489_ = v___x_2574_;
v___y_2490_ = v___y_2549_;
v___y_2491_ = v___y_2548_;
v___y_2492_ = v___x_2572_;
v___y_2493_ = v___y_2551_;
v___y_2494_ = v___y_2552_;
v___y_2495_ = v___y_2553_;
v___y_2496_ = v___y_2555_;
v___y_2497_ = v___y_2560_;
v___y_2498_ = v___x_2604_;
goto v___jp_2484_;
}
}
else
{
size_t v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = lean_usize_of_nat(v___x_2599_);
v___x_2606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2555_, v___y_2552_, v___x_2605_, v___x_2600_);
v___y_2485_ = v_a_2598_;
v___y_2486_ = v___y_2543_;
v___y_2487_ = v___y_2544_;
v___y_2488_ = v___y_2545_;
v___y_2489_ = v___x_2574_;
v___y_2490_ = v___y_2549_;
v___y_2491_ = v___y_2548_;
v___y_2492_ = v___x_2572_;
v___y_2493_ = v___y_2551_;
v___y_2494_ = v___y_2552_;
v___y_2495_ = v___y_2553_;
v___y_2496_ = v___y_2555_;
v___y_2497_ = v___y_2560_;
v___y_2498_ = v___x_2606_;
goto v___jp_2484_;
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2545_);
lean_dec_ref(v___y_2543_);
v_a_2607_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2597_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2597_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
v___jp_2615_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
lean_inc_ref(v___y_2619_);
v___x_2636_ = l_Array_append___redArg(v___y_2619_, v___y_2635_);
lean_dec_ref(v___y_2635_);
lean_inc(v___y_2622_);
lean_inc(v___y_2621_);
v___x_2637_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2637_, 0, v___y_2621_);
lean_ctor_set(v___x_2637_, 1, v___y_2622_);
lean_ctor_set(v___x_2637_, 2, v___x_2636_);
if (lean_obj_tag(v___y_2626_) == 1)
{
lean_object* v_val_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_val_2638_ = lean_ctor_get(v___y_2626_, 0);
lean_inc(v_val_2638_);
lean_dec_ref(v___y_2626_);
v___x_2639_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
v___x_2640_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc(v___y_2621_);
v___x_2641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___y_2621_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__11));
lean_inc(v___y_2621_);
v___x_2643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___y_2621_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
v___x_2644_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
lean_inc(v___y_2621_);
v___x_2645_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___y_2621_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
lean_inc(v___y_2621_);
v___x_2647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___y_2621_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
lean_inc(v___y_2621_);
v___x_2648_ = l_Lean_Syntax_node5(v___y_2621_, v___x_2639_, v___x_2641_, v___x_2643_, v___x_2645_, v_val_2638_, v___x_2647_);
v___x_2649_ = l_Array_mkArray1___redArg(v___x_2648_);
v___y_2542_ = v___y_2616_;
v___y_2543_ = v___y_2617_;
v___y_2544_ = v___y_2618_;
v___y_2545_ = v___y_2619_;
v___y_2546_ = v___y_2620_;
v___y_2547_ = v___y_2621_;
v___y_2548_ = v___y_2623_;
v___y_2549_ = v___y_2622_;
v___y_2550_ = v___x_2637_;
v___y_2551_ = v___y_2624_;
v___y_2552_ = v___y_2625_;
v___y_2553_ = v___y_2627_;
v___y_2554_ = v___y_2628_;
v___y_2555_ = v___y_2629_;
v___y_2556_ = v___y_2630_;
v___y_2557_ = v___y_2633_;
v___y_2558_ = v___y_2632_;
v___y_2559_ = v___y_2631_;
v___y_2560_ = v___y_2634_;
v___y_2561_ = v___x_2649_;
goto v___jp_2541_;
}
else
{
lean_object* v___x_2650_; 
lean_dec(v___y_2626_);
v___x_2650_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2542_ = v___y_2616_;
v___y_2543_ = v___y_2617_;
v___y_2544_ = v___y_2618_;
v___y_2545_ = v___y_2619_;
v___y_2546_ = v___y_2620_;
v___y_2547_ = v___y_2621_;
v___y_2548_ = v___y_2623_;
v___y_2549_ = v___y_2622_;
v___y_2550_ = v___x_2637_;
v___y_2551_ = v___y_2624_;
v___y_2552_ = v___y_2625_;
v___y_2553_ = v___y_2627_;
v___y_2554_ = v___y_2628_;
v___y_2555_ = v___y_2629_;
v___y_2556_ = v___y_2630_;
v___y_2557_ = v___y_2633_;
v___y_2558_ = v___y_2632_;
v___y_2559_ = v___y_2631_;
v___y_2560_ = v___y_2634_;
v___y_2561_ = v___x_2650_;
goto v___jp_2541_;
}
}
v___jp_2651_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_inc_ref(v___y_2655_);
v___x_2672_ = l_Array_append___redArg(v___y_2655_, v___y_2671_);
lean_dec_ref(v___y_2671_);
lean_inc(v___y_2658_);
lean_inc(v___y_2657_);
v___x_2673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2673_, 0, v___y_2657_);
lean_ctor_set(v___x_2673_, 1, v___y_2658_);
lean_ctor_set(v___x_2673_, 2, v___x_2672_);
lean_inc(v___y_2657_);
v___x_2674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___y_2657_);
lean_ctor_set(v___x_2674_, 1, v___y_2662_);
if (lean_obj_tag(v___y_2656_) == 1)
{
lean_object* v_val_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v_val_2675_ = lean_ctor_get(v___y_2656_, 0);
lean_inc(v_val_2675_);
lean_dec_ref(v___y_2656_);
v___x_2676_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
v___x_2677_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc(v___y_2657_);
v___x_2678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___y_2657_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
lean_inc(v___y_2657_);
v___x_2679_ = l_Lean_Syntax_node2(v___y_2657_, v___x_2676_, v___x_2678_, v_val_2675_);
v___x_2680_ = l_Array_mkArray1___redArg(v___x_2679_);
v___y_2616_ = v___y_2652_;
v___y_2617_ = v___y_2653_;
v___y_2618_ = v___y_2654_;
v___y_2619_ = v___y_2655_;
v___y_2620_ = v___x_2674_;
v___y_2621_ = v___y_2657_;
v___y_2622_ = v___y_2658_;
v___y_2623_ = v___y_2659_;
v___y_2624_ = v___y_2660_;
v___y_2625_ = v___y_2661_;
v___y_2626_ = v___y_2664_;
v___y_2627_ = v___y_2665_;
v___y_2628_ = v___y_2663_;
v___y_2629_ = v___y_2666_;
v___y_2630_ = v___y_2667_;
v___y_2631_ = v___y_2669_;
v___y_2632_ = v___x_2673_;
v___y_2633_ = v___y_2668_;
v___y_2634_ = v___y_2670_;
v___y_2635_ = v___x_2680_;
goto v___jp_2615_;
}
else
{
lean_object* v___x_2681_; 
lean_dec(v___y_2656_);
v___x_2681_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2616_ = v___y_2652_;
v___y_2617_ = v___y_2653_;
v___y_2618_ = v___y_2654_;
v___y_2619_ = v___y_2655_;
v___y_2620_ = v___x_2674_;
v___y_2621_ = v___y_2657_;
v___y_2622_ = v___y_2658_;
v___y_2623_ = v___y_2659_;
v___y_2624_ = v___y_2660_;
v___y_2625_ = v___y_2661_;
v___y_2626_ = v___y_2664_;
v___y_2627_ = v___y_2665_;
v___y_2628_ = v___y_2663_;
v___y_2629_ = v___y_2666_;
v___y_2630_ = v___y_2667_;
v___y_2631_ = v___y_2669_;
v___y_2632_ = v___x_2673_;
v___y_2633_ = v___y_2668_;
v___y_2634_ = v___y_2670_;
v___y_2635_ = v___x_2681_;
goto v___jp_2615_;
}
}
v___jp_2682_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
lean_inc_ref(v___y_2686_);
v___x_2703_ = l_Array_append___redArg(v___y_2686_, v___y_2702_);
lean_dec_ref(v___y_2702_);
lean_inc(v___y_2690_);
lean_inc(v___y_2688_);
v___x_2704_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2704_, 0, v___y_2688_);
lean_ctor_set(v___x_2704_, 1, v___y_2690_);
lean_ctor_set(v___x_2704_, 2, v___x_2703_);
if (lean_obj_tag(v___y_2687_) == 1)
{
lean_object* v_val_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_val_2705_ = lean_ctor_get(v___y_2687_, 0);
lean_inc(v_val_2705_);
lean_dec_ref(v___y_2687_);
v___x_2706_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__11));
lean_inc_ref(v___y_2684_);
v___x_2707_ = l_Lean_Name_mkStr4(v___x_2427_, v___x_2428_, v___y_2684_, v___x_2706_);
v___x_2708_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc(v___y_2688_);
v___x_2709_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___y_2688_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
lean_inc_ref(v___y_2686_);
v___x_2710_ = l_Array_append___redArg(v___y_2686_, v_val_2705_);
lean_dec(v_val_2705_);
lean_inc(v___y_2690_);
lean_inc(v___y_2688_);
v___x_2711_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2711_, 0, v___y_2688_);
lean_ctor_set(v___x_2711_, 1, v___y_2690_);
lean_ctor_set(v___x_2711_, 2, v___x_2710_);
v___x_2712_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
lean_inc(v___y_2688_);
v___x_2713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___y_2688_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
lean_inc(v___y_2688_);
v___x_2714_ = l_Lean_Syntax_node3(v___y_2688_, v___x_2707_, v___x_2709_, v___x_2711_, v___x_2713_);
v___x_2715_ = l_Array_mkArray1___redArg(v___x_2714_);
v___y_2652_ = v___y_2683_;
v___y_2653_ = v___y_2684_;
v___y_2654_ = v___y_2685_;
v___y_2655_ = v___y_2686_;
v___y_2656_ = v___y_2689_;
v___y_2657_ = v___y_2688_;
v___y_2658_ = v___y_2690_;
v___y_2659_ = v___y_2691_;
v___y_2660_ = v___y_2692_;
v___y_2661_ = v___y_2693_;
v___y_2662_ = v___y_2694_;
v___y_2663_ = v___y_2697_;
v___y_2664_ = v___y_2696_;
v___y_2665_ = v___y_2695_;
v___y_2666_ = v___y_2698_;
v___y_2667_ = v___x_2704_;
v___y_2668_ = v___y_2700_;
v___y_2669_ = v___y_2699_;
v___y_2670_ = v___y_2701_;
v___y_2671_ = v___x_2715_;
goto v___jp_2651_;
}
else
{
lean_object* v___x_2716_; 
lean_dec(v___y_2687_);
v___x_2716_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2652_ = v___y_2683_;
v___y_2653_ = v___y_2684_;
v___y_2654_ = v___y_2685_;
v___y_2655_ = v___y_2686_;
v___y_2656_ = v___y_2689_;
v___y_2657_ = v___y_2688_;
v___y_2658_ = v___y_2690_;
v___y_2659_ = v___y_2691_;
v___y_2660_ = v___y_2692_;
v___y_2661_ = v___y_2693_;
v___y_2662_ = v___y_2694_;
v___y_2663_ = v___y_2697_;
v___y_2664_ = v___y_2696_;
v___y_2665_ = v___y_2695_;
v___y_2666_ = v___y_2698_;
v___y_2667_ = v___x_2704_;
v___y_2668_ = v___y_2700_;
v___y_2669_ = v___y_2699_;
v___y_2670_ = v___y_2701_;
v___y_2671_ = v___x_2716_;
goto v___jp_2651_;
}
}
v___jp_2717_:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2734_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__12));
v___x_2735_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__13));
v___x_2736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_2737_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
if (lean_obj_tag(v___y_2722_) == 1)
{
lean_object* v_val_2738_; lean_object* v___x_2739_; 
v_val_2738_ = lean_ctor_get(v___y_2722_, 0);
lean_inc(v_val_2738_);
lean_dec_ref(v___y_2722_);
v___x_2739_ = l_Array_mkArray1___redArg(v_val_2738_);
v___y_2683_ = v___y_2718_;
v___y_2684_ = v___y_2719_;
v___y_2685_ = v___y_2720_;
v___y_2686_ = v___x_2737_;
v___y_2687_ = v___y_2721_;
v___y_2688_ = v___y_2723_;
v___y_2689_ = v___y_2724_;
v___y_2690_ = v___x_2736_;
v___y_2691_ = v___y_2725_;
v___y_2692_ = v___y_2726_;
v___y_2693_ = v___y_2727_;
v___y_2694_ = v___x_2734_;
v___y_2695_ = v___y_2728_;
v___y_2696_ = v___y_2729_;
v___y_2697_ = v___x_2735_;
v___y_2698_ = v___y_2730_;
v___y_2699_ = v___y_2732_;
v___y_2700_ = v___y_2731_;
v___y_2701_ = v___y_2733_;
v___y_2702_ = v___x_2739_;
goto v___jp_2682_;
}
else
{
lean_object* v___x_2740_; 
lean_dec(v___y_2722_);
v___x_2740_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2683_ = v___y_2718_;
v___y_2684_ = v___y_2719_;
v___y_2685_ = v___y_2720_;
v___y_2686_ = v___x_2737_;
v___y_2687_ = v___y_2721_;
v___y_2688_ = v___y_2723_;
v___y_2689_ = v___y_2724_;
v___y_2690_ = v___x_2736_;
v___y_2691_ = v___y_2725_;
v___y_2692_ = v___y_2726_;
v___y_2693_ = v___y_2727_;
v___y_2694_ = v___x_2734_;
v___y_2695_ = v___y_2728_;
v___y_2696_ = v___y_2729_;
v___y_2697_ = v___x_2735_;
v___y_2698_ = v___y_2730_;
v___y_2699_ = v___y_2732_;
v___y_2700_ = v___y_2731_;
v___y_2701_ = v___y_2733_;
v___y_2702_ = v___x_2740_;
goto v___jp_2682_;
}
}
v___jp_2741_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_2751_, 0, v_prio_x3f_2748_);
lean_inc_ref(v___y_2749_);
v___x_2752_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2751_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v_items_2756_; size_t v_sz_2757_; size_t v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref(v___x_2752_);
v___x_2754_ = lean_unsigned_to_nat(7u);
v___x_2755_ = l_Lean_Syntax_getArg(v_x_2396_, v___x_2754_);
v_items_2756_ = l_Lean_Syntax_getArgs(v___x_2755_);
lean_dec(v___x_2755_);
v_sz_2757_ = lean_array_size(v_items_2756_);
v___x_2758_ = ((size_t)0ULL);
v___x_2759_ = lean_box_usize(v_sz_2757_);
v___x_2760_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___boxed__const__1));
lean_inc_ref(v_items_2756_);
v___x_2761_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed), 5, 3);
lean_closure_set(v___x_2761_, 0, v___x_2759_);
lean_closure_set(v___x_2761_, 1, v___x_2760_);
lean_closure_set(v___x_2761_, 2, v_items_2756_);
lean_inc_ref(v___y_2749_);
v___x_2762_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2761_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2764_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref(v___x_2762_);
v___x_2764_ = l_Lean_Elab_Command_getRef___redArg(v___y_2749_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2766_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref(v___x_2764_);
v___x_2766_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2749_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_quotContext_x3f_2767_; lean_object* v___x_2768_; uint8_t v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v_rhs_2772_; lean_object* v_attrs_x3f_2773_; lean_object* v___x_2774_; 
lean_dec_ref(v___x_2766_);
v_quotContext_x3f_2767_ = lean_ctor_get(v___y_2749_, 5);
v___x_2768_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
v___x_2769_ = 0;
v___x_2770_ = l_Lean_mkIdentFrom(v_x_2396_, v___x_2768_, v___x_2769_);
v___x_2771_ = lean_unsigned_to_nat(9u);
v_rhs_2772_ = l_Lean_Syntax_getArg(v_x_2396_, v___x_2771_);
lean_dec(v_x_2396_);
lean_inc(v_rhs_2772_);
v_attrs_x3f_2773_ = l_Lean_Elab_Command_addInheritDocDefault(v_rhs_2772_, v___y_2747_);
v___x_2774_ = l_Lean_SourceInfo_fromRef(v_a_2765_, v___x_2769_);
lean_dec(v_a_2765_);
if (lean_obj_tag(v_quotContext_x3f_2767_) == 0)
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2750_);
lean_dec_ref(v___x_2775_);
v___y_2718_ = v_a_2753_;
v___y_2719_ = v___y_2743_;
v___y_2720_ = v___x_2769_;
v___y_2721_ = v_attrs_x3f_2773_;
v___y_2722_ = v___y_2745_;
v___y_2723_ = v___x_2774_;
v___y_2724_ = v___y_2744_;
v___y_2725_ = v_rhs_2772_;
v___y_2726_ = v___y_2749_;
v___y_2727_ = v___x_2758_;
v___y_2728_ = v___y_2750_;
v___y_2729_ = v___y_2742_;
v___y_2730_ = v_items_2756_;
v___y_2731_ = v_a_2763_;
v___y_2732_ = v___x_2770_;
v___y_2733_ = v___y_2746_;
goto v___jp_2717_;
}
else
{
v___y_2718_ = v_a_2753_;
v___y_2719_ = v___y_2743_;
v___y_2720_ = v___x_2769_;
v___y_2721_ = v_attrs_x3f_2773_;
v___y_2722_ = v___y_2745_;
v___y_2723_ = v___x_2774_;
v___y_2724_ = v___y_2744_;
v___y_2725_ = v_rhs_2772_;
v___y_2726_ = v___y_2749_;
v___y_2727_ = v___x_2758_;
v___y_2728_ = v___y_2750_;
v___y_2729_ = v___y_2742_;
v___y_2730_ = v_items_2756_;
v___y_2731_ = v_a_2763_;
v___y_2732_ = v___x_2770_;
v___y_2733_ = v___y_2746_;
goto v___jp_2717_;
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec(v_a_2765_);
lean_dec(v_a_2763_);
lean_dec_ref(v_items_2756_);
lean_dec(v_a_2753_);
lean_dec(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v_x_2396_);
v_a_2776_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2766_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2766_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec(v_a_2763_);
lean_dec_ref(v_items_2756_);
lean_dec(v_a_2753_);
lean_dec(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v_x_2396_);
v_a_2784_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2764_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2764_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec_ref(v_items_2756_);
lean_dec(v_a_2753_);
lean_dec(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v_x_2396_);
v_a_2792_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2762_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2762_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v_x_2396_);
v_a_2800_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2752_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2752_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
v___jp_2808_:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2819_ = lean_unsigned_to_nat(6u);
v___x_2820_ = l_Lean_Syntax_getArg(v_x_2396_, v___x_2819_);
v___x_2821_ = l_Lean_Syntax_isNone(v___x_2820_);
if (v___x_2821_ == 0)
{
uint8_t v___x_2822_; 
lean_inc(v___x_2820_);
v___x_2822_ = l_Lean_Syntax_matchesNull(v___x_2820_, v___y_2813_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; 
lean_dec(v___x_2820_);
lean_dec(v_name_x3f_2816_);
lean_dec(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v_x_2396_);
v___x_2823_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2823_;
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2824_ = l_Lean_Syntax_getArg(v___x_2820_, v___x_2540_);
lean_dec(v___x_2820_);
v___x_2825_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
lean_inc(v___x_2824_);
v___x_2826_ = l_Lean_Syntax_isOfKind(v___x_2824_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; 
lean_dec(v___x_2824_);
lean_dec(v_name_x3f_2816_);
lean_dec(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v_x_2396_);
v___x_2827_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2827_;
}
else
{
lean_object* v_prio_x3f_2828_; lean_object* v___x_2829_; 
v_prio_x3f_2828_ = l_Lean_Syntax_getArg(v___x_2824_, v___y_2809_);
lean_dec(v___x_2824_);
v___x_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2829_, 0, v_prio_x3f_2828_);
v___y_2742_ = v_name_x3f_2816_;
v___y_2743_ = v___y_2810_;
v___y_2744_ = v___y_2812_;
v___y_2745_ = v___y_2811_;
v___y_2746_ = v___y_2814_;
v___y_2747_ = v___y_2815_;
v_prio_x3f_2748_ = v___x_2829_;
v___y_2749_ = v___y_2817_;
v___y_2750_ = v___y_2818_;
goto v___jp_2741_;
}
}
}
else
{
lean_object* v___x_2830_; 
lean_dec(v___x_2820_);
v___x_2830_ = lean_box(0);
v___y_2742_ = v_name_x3f_2816_;
v___y_2743_ = v___y_2810_;
v___y_2744_ = v___y_2812_;
v___y_2745_ = v___y_2811_;
v___y_2746_ = v___y_2814_;
v___y_2747_ = v___y_2815_;
v_prio_x3f_2748_ = v___x_2830_;
v___y_2749_ = v___y_2817_;
v___y_2750_ = v___y_2818_;
goto v___jp_2741_;
}
}
v___jp_2831_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2841_ = lean_unsigned_to_nat(5u);
v___x_2842_ = l_Lean_Syntax_getArg(v_x_2396_, v___x_2841_);
v___x_2843_ = l_Lean_Syntax_isNone(v___x_2842_);
if (v___x_2843_ == 0)
{
uint8_t v___x_2844_; 
lean_inc(v___x_2842_);
v___x_2844_ = l_Lean_Syntax_matchesNull(v___x_2842_, v___y_2836_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; 
lean_dec(v___x_2842_);
lean_dec(v_prec_x3f_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v_x_2396_);
v___x_2845_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2845_;
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2846_ = l_Lean_Syntax_getArg(v___x_2842_, v___x_2540_);
lean_dec(v___x_2842_);
v___x_2847_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
lean_inc(v___x_2846_);
v___x_2848_ = l_Lean_Syntax_isOfKind(v___x_2846_, v___x_2847_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; 
lean_dec(v___x_2846_);
lean_dec(v_prec_x3f_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v_x_2396_);
v___x_2849_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2849_;
}
else
{
lean_object* v_name_x3f_2850_; lean_object* v___x_2851_; 
v_name_x3f_2850_ = l_Lean_Syntax_getArg(v___x_2846_, v___y_2832_);
lean_dec(v___x_2846_);
v___x_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2851_, 0, v_name_x3f_2850_);
v___y_2809_ = v___y_2832_;
v___y_2810_ = v___y_2833_;
v___y_2811_ = v___y_2834_;
v___y_2812_ = v_prec_x3f_2838_;
v___y_2813_ = v___y_2836_;
v___y_2814_ = v___y_2835_;
v___y_2815_ = v___y_2837_;
v_name_x3f_2816_ = v___x_2851_;
v___y_2817_ = v___y_2839_;
v___y_2818_ = v___y_2840_;
goto v___jp_2808_;
}
}
}
else
{
lean_object* v___x_2852_; 
lean_dec(v___x_2842_);
v___x_2852_ = lean_box(0);
v___y_2809_ = v___y_2832_;
v___y_2810_ = v___y_2833_;
v___y_2811_ = v___y_2834_;
v___y_2812_ = v_prec_x3f_2838_;
v___y_2813_ = v___y_2836_;
v___y_2814_ = v___y_2835_;
v___y_2815_ = v___y_2837_;
v_name_x3f_2816_ = v___x_2852_;
v___y_2817_ = v___y_2839_;
v___y_2818_ = v___y_2840_;
goto v___jp_2808_;
}
}
v___jp_2853_:
{
lean_object* v___x_2859_; lean_object* v_attrKind_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2859_ = lean_unsigned_to_nat(2u);
v_attrKind_2860_ = l_Lean_Syntax_getArg(v_x_2396_, v___x_2859_);
v___x_2861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2));
v___x_2862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(v_attrKind_2860_);
v___x_2863_ = l_Lean_Syntax_isOfKind(v_attrKind_2860_, v___x_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; 
lean_dec(v_attrKind_2860_);
lean_dec(v_attrs_x3f_2856_);
lean_dec(v___y_2854_);
lean_dec(v_x_2396_);
v___x_2864_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2864_;
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; 
v___x_2865_ = lean_unsigned_to_nat(3u);
v___x_2866_ = lean_unsigned_to_nat(4u);
v___x_2867_ = l_Lean_Syntax_getArg(v_x_2396_, v___x_2866_);
v___x_2868_ = l_Lean_Syntax_isNone(v___x_2867_);
if (v___x_2868_ == 0)
{
uint8_t v___x_2869_; 
lean_inc(v___x_2867_);
v___x_2869_ = l_Lean_Syntax_matchesNull(v___x_2867_, v___y_2855_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; 
lean_dec(v___x_2867_);
lean_dec(v_attrKind_2860_);
lean_dec(v_attrs_x3f_2856_);
lean_dec(v___y_2854_);
lean_dec(v_x_2396_);
v___x_2870_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2870_;
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; 
v___x_2871_ = l_Lean_Syntax_getArg(v___x_2867_, v___x_2540_);
lean_dec(v___x_2867_);
v___x_2872_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
lean_inc(v___x_2871_);
v___x_2873_ = l_Lean_Syntax_isOfKind(v___x_2871_, v___x_2872_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; 
lean_dec(v___x_2871_);
lean_dec(v_attrKind_2860_);
lean_dec(v_attrs_x3f_2856_);
lean_dec(v___y_2854_);
lean_dec(v_x_2396_);
v___x_2874_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2874_;
}
else
{
lean_object* v_prec_x3f_2875_; lean_object* v___x_2876_; 
v_prec_x3f_2875_ = l_Lean_Syntax_getArg(v___x_2871_, v___y_2855_);
lean_dec(v___x_2871_);
v___x_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2876_, 0, v_prec_x3f_2875_);
v___y_2832_ = v___x_2865_;
v___y_2833_ = v___x_2861_;
v___y_2834_ = v___y_2854_;
v___y_2835_ = v_attrKind_2860_;
v___y_2836_ = v___y_2855_;
v___y_2837_ = v_attrs_x3f_2856_;
v_prec_x3f_2838_ = v___x_2876_;
v___y_2839_ = v___y_2857_;
v___y_2840_ = v___y_2858_;
goto v___jp_2831_;
}
}
}
else
{
lean_object* v___x_2877_; 
lean_dec(v___x_2867_);
v___x_2877_ = lean_box(0);
v___y_2832_ = v___x_2865_;
v___y_2833_ = v___x_2861_;
v___y_2834_ = v___y_2854_;
v___y_2835_ = v_attrKind_2860_;
v___y_2836_ = v___y_2855_;
v___y_2837_ = v_attrs_x3f_2856_;
v_prec_x3f_2838_ = v___x_2877_;
v___y_2839_ = v___y_2857_;
v___y_2840_ = v___y_2858_;
goto v___jp_2831_;
}
}
}
v___jp_2878_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; 
v___x_2882_ = lean_unsigned_to_nat(1u);
v___x_2883_ = l_Lean_Syntax_getArg(v_x_2396_, v___x_2882_);
v___x_2884_ = l_Lean_Syntax_isNone(v___x_2883_);
if (v___x_2884_ == 0)
{
uint8_t v___x_2885_; 
lean_inc(v___x_2883_);
v___x_2885_ = l_Lean_Syntax_matchesNull(v___x_2883_, v___x_2882_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; 
lean_dec(v___x_2883_);
lean_dec(v_doc_x3f_2879_);
lean_dec(v_x_2396_);
v___x_2886_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2886_;
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2887_ = l_Lean_Syntax_getArg(v___x_2883_, v___x_2540_);
lean_dec(v___x_2883_);
v___x_2888_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
lean_inc(v___x_2887_);
v___x_2889_ = l_Lean_Syntax_isOfKind(v___x_2887_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; 
lean_dec(v___x_2887_);
lean_dec(v_doc_x3f_2879_);
lean_dec(v_x_2396_);
v___x_2890_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2890_;
}
else
{
lean_object* v___x_2891_; lean_object* v_attrs_x3f_2892_; lean_object* v___x_2893_; 
v___x_2891_ = l_Lean_Syntax_getArg(v___x_2887_, v___x_2882_);
lean_dec(v___x_2887_);
v_attrs_x3f_2892_ = l_Lean_Syntax_getArgs(v___x_2891_);
lean_dec(v___x_2891_);
v___x_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2893_, 0, v_attrs_x3f_2892_);
v___y_2854_ = v_doc_x3f_2879_;
v___y_2855_ = v___x_2882_;
v_attrs_x3f_2856_ = v___x_2893_;
v___y_2857_ = v___y_2880_;
v___y_2858_ = v___y_2881_;
goto v___jp_2853_;
}
}
}
else
{
lean_object* v___x_2894_; 
lean_dec(v___x_2883_);
v___x_2894_ = lean_box(0);
v___y_2854_ = v_doc_x3f_2879_;
v___y_2855_ = v___x_2882_;
v_attrs_x3f_2856_ = v___x_2894_;
v___y_2857_ = v___y_2880_;
v___y_2858_ = v___y_2881_;
goto v___jp_2853_;
}
}
}
v___jp_2400_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkUnexpander___boxed), 5, 3);
lean_closure_set(v___x_2406_, 0, v___y_2403_);
lean_closure_set(v___x_2406_, 1, v___y_2402_);
lean_closure_set(v___x_2406_, 2, v___y_2401_);
lean_inc_ref(v___y_2404_);
v___x_2407_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2406_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2418_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2418_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2418_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
if (lean_obj_tag(v_a_2408_) == 1)
{
lean_object* v_val_2412_; lean_object* v___x_2413_; 
lean_del_object(v___x_2410_);
v_val_2412_ = lean_ctor_get(v_a_2408_, 0);
lean_inc(v_val_2412_);
lean_dec_ref(v_a_2408_);
v___x_2413_ = l_Lean_Elab_Command_elabCommand(v_val_2412_, v___y_2404_, v___y_2405_);
return v___x_2413_;
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
lean_dec(v_a_2408_);
v___x_2414_ = lean_box(0);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2414_);
v___x_2416_ = v___x_2410_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
v_a_2419_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2407_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2407_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
v___jp_2431_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2442_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__2));
v___x_2443_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__3));
lean_inc(v___y_2438_);
lean_inc(v___y_2436_);
v___x_2444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2444_, 0, v___y_2436_);
lean_ctor_set(v___x_2444_, 1, v___y_2438_);
lean_ctor_set(v___x_2444_, 2, v___y_2435_);
lean_inc(v___y_2436_);
v___x_2445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___y_2436_);
lean_ctor_set(v___x_2445_, 1, v___x_2442_);
v___x_2446_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__29));
lean_inc_ref(v___y_2433_);
v___x_2447_ = l_Lean_Name_mkStr4(v___x_2427_, v___x_2428_, v___y_2433_, v___x_2446_);
v___x_2448_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__31));
lean_inc_ref(v___y_2433_);
v___x_2449_ = l_Lean_Name_mkStr4(v___x_2427_, v___x_2428_, v___y_2433_, v___x_2448_);
v___x_2450_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
lean_inc(v___y_2436_);
v___x_2451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___y_2436_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__34));
lean_inc_ref(v___y_2433_);
v___x_2453_ = l_Lean_Name_mkStr4(v___x_2427_, v___x_2428_, v___y_2433_, v___x_2452_);
v___x_2454_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
lean_inc(v___y_2436_);
v___x_2455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___y_2436_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
lean_inc(v___y_2436_);
v___x_2456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___y_2436_);
lean_ctor_set(v___x_2456_, 1, v___y_2437_);
lean_inc_ref(v___x_2456_);
lean_inc(v___y_2439_);
lean_inc_ref(v___x_2455_);
lean_inc(v___x_2453_);
lean_inc(v___y_2436_);
v___x_2457_ = l_Lean_Syntax_node3(v___y_2436_, v___x_2453_, v___x_2455_, v___y_2439_, v___x_2456_);
lean_inc(v___y_2438_);
lean_inc(v___y_2436_);
v___x_2458_ = l_Lean_Syntax_node1(v___y_2436_, v___y_2438_, v___x_2457_);
lean_inc(v___y_2438_);
lean_inc(v___y_2436_);
v___x_2459_ = l_Lean_Syntax_node1(v___y_2436_, v___y_2438_, v___x_2458_);
v___x_2460_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
lean_inc(v___y_2436_);
v___x_2461_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___y_2436_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__4));
v___x_2463_ = l_Lean_Name_mkStr4(v___x_2427_, v___x_2428_, v___y_2433_, v___x_2462_);
v___x_2464_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__5));
lean_inc(v___y_2436_);
v___x_2465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___y_2436_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
lean_inc(v___y_2434_);
lean_inc(v___y_2436_);
v___x_2466_ = l_Lean_Syntax_node3(v___y_2436_, v___x_2453_, v___x_2455_, v___y_2434_, v___x_2456_);
lean_inc(v___y_2436_);
v___x_2467_ = l_Lean_Syntax_node2(v___y_2436_, v___x_2463_, v___x_2465_, v___x_2466_);
lean_inc(v___y_2436_);
v___x_2468_ = l_Lean_Syntax_node4(v___y_2436_, v___x_2449_, v___x_2451_, v___x_2459_, v___x_2461_, v___x_2467_);
lean_inc(v___y_2436_);
v___x_2469_ = l_Lean_Syntax_node1(v___y_2436_, v___y_2438_, v___x_2468_);
lean_inc(v___y_2436_);
v___x_2470_ = l_Lean_Syntax_node1(v___y_2436_, v___x_2447_, v___x_2469_);
lean_inc(v___y_2440_);
lean_inc_ref_n(v___x_2444_, 2);
v___x_2471_ = l_Lean_Syntax_node6(v___y_2436_, v___x_2443_, v___x_2444_, v___x_2444_, v___y_2440_, v___x_2445_, v___x_2444_, v___x_2470_);
lean_inc(v___y_2440_);
v___x_2472_ = l_Lean_Elab_Command_isLocalAttrKind(v___y_2440_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_Elab_Command_elabCommand(v___x_2471_, v___y_2441_, v___y_2432_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_dec_ref(v___x_2473_);
v___y_2401_ = v___y_2434_;
v___y_2402_ = v___y_2439_;
v___y_2403_ = v___y_2440_;
v___y_2404_ = v___y_2441_;
v___y_2405_ = v___y_2432_;
goto v___jp_2400_;
}
else
{
lean_dec(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec(v___y_2434_);
return v___x_2473_;
}
}
else
{
lean_object* v___x_2474_; lean_object* v_scopes_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v_opts_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___f_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2474_ = lean_st_ref_get(v___y_2432_);
v_scopes_2475_ = lean_ctor_get(v___x_2474_, 2);
lean_inc(v_scopes_2475_);
lean_dec(v___x_2474_);
v___x_2476_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2477_ = l_List_head_x21___redArg(v___x_2476_, v_scopes_2475_);
lean_dec(v_scopes_2475_);
v_opts_2478_ = lean_ctor_get(v___x_2477_, 1);
lean_inc_ref(v_opts_2478_);
lean_dec(v___x_2477_);
v___x_2479_ = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
v___x_2480_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_2478_, v___x_2479_, v___x_2430_);
v___f_2481_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___lam__0), 2, 1);
lean_closure_set(v___f_2481_, 0, v___x_2480_);
v___x_2482_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_2482_, 0, v___x_2471_);
v___x_2483_ = l_Lean_Elab_Command_withScope___redArg(v___f_2481_, v___x_2482_, v___y_2441_, v___y_2432_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_dec_ref(v___x_2483_);
v___y_2401_ = v___y_2434_;
v___y_2402_ = v___y_2439_;
v___y_2403_ = v___y_2440_;
v___y_2404_ = v___y_2441_;
v___y_2405_ = v___y_2432_;
goto v___jp_2400_;
}
else
{
lean_dec(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec(v___y_2434_);
return v___x_2483_;
}
}
}
v___jp_2484_:
{
size_t v_sz_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v_sz_2499_ = lean_array_size(v___y_2496_);
v___x_2500_ = lean_box_usize(v_sz_2499_);
v___x_2501_ = lean_box_usize(v___y_2494_);
v___x_2502_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed), 5, 3);
lean_closure_set(v___x_2502_, 0, v___x_2500_);
lean_closure_set(v___x_2502_, 1, v___x_2501_);
lean_closure_set(v___x_2502_, 2, v___y_2496_);
lean_inc_ref(v___y_2493_);
v___x_2503_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2502_, v___y_2493_, v___y_2495_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2505_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref(v___x_2503_);
v___x_2505_ = l_Lean_Elab_Command_getRef___redArg(v___y_2493_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2507_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref(v___x_2505_);
v___x_2507_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2493_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_quotContext_x3f_2508_; size_t v_sz_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
lean_dec_ref(v___x_2507_);
v_quotContext_x3f_2508_ = lean_ctor_get(v___y_2493_, 5);
v_sz_2509_ = lean_array_size(v___y_2498_);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_2509_, v___y_2494_, v___y_2498_);
v___x_2511_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(v___x_2510_, v___y_2491_);
lean_dec_ref(v___x_2510_);
v___x_2512_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2512_, 0, v___y_2492_);
lean_ctor_set(v___x_2512_, 1, v___y_2485_);
lean_ctor_set(v___x_2512_, 2, v_a_2504_);
v___x_2513_ = l_Lean_SourceInfo_fromRef(v_a_2506_, v___y_2487_);
lean_dec(v_a_2506_);
if (lean_obj_tag(v_quotContext_x3f_2508_) == 0)
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2495_);
lean_dec_ref(v___x_2514_);
v___y_2432_ = v___y_2495_;
v___y_2433_ = v___y_2486_;
v___y_2434_ = v___x_2511_;
v___y_2435_ = v___y_2488_;
v___y_2436_ = v___x_2513_;
v___y_2437_ = v___y_2489_;
v___y_2438_ = v___y_2490_;
v___y_2439_ = v___x_2512_;
v___y_2440_ = v___y_2497_;
v___y_2441_ = v___y_2493_;
goto v___jp_2431_;
}
else
{
v___y_2432_ = v___y_2495_;
v___y_2433_ = v___y_2486_;
v___y_2434_ = v___x_2511_;
v___y_2435_ = v___y_2488_;
v___y_2436_ = v___x_2513_;
v___y_2437_ = v___y_2489_;
v___y_2438_ = v___y_2490_;
v___y_2439_ = v___x_2512_;
v___y_2440_ = v___y_2497_;
v___y_2441_ = v___y_2493_;
goto v___jp_2431_;
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_dec(v_a_2506_);
lean_dec(v_a_2504_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
v_a_2515_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2507_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2507_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v_a_2504_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
v_a_2523_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2505_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2505_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
v_a_2531_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2503_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2503_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___boxed(lean_object* v_x_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Lean_Elab_Command_elabNotation(v_x_2906_, v_a_2907_, v_a_2908_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(lean_object* v_cls_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___redArg(v_cls_2911_, v___y_2913_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___boxed(lean_object* v_cls_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(lean_object* v_00_u03b1_2921_, lean_object* v_x_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___redArg(v_x_2922_, v___y_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2926_, lean_object* v_x_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_00_u03b1_2926_, v_x_2927_, v___y_2928_, v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec_ref(v_x_2927_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8(lean_object* v_00_u03b1_2931_, lean_object* v_ref_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___redArg(v_ref_2932_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8___boxed(lean_object* v_00_u03b1_2937_, lean_object* v_ref_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__8(v_00_u03b1_2937_, v_ref_2938_, v___y_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(lean_object* v_00_u03b1_2943_, lean_object* v_x_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v___x_2948_; 
lean_inc_ref(v___y_2945_);
v___x_2948_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2944_, v___y_2945_, v___y_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___boxed(lean_object* v_00_u03b1_2949_, lean_object* v_x_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(v_00_u03b1_2949_, v_x_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4(lean_object* v_msgData_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___redArg(v_msgData_2955_, v___y_2957_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2_spec__4(v_msgData_2960_, v___y_2961_, v___y_2962_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(lean_object* v_as_2965_, lean_object* v_as_x27_2966_, lean_object* v_b_2967_, lean_object* v_a_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___redArg(v_as_x27_2966_, v_b_2967_, v___y_2969_, v___y_2970_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___boxed(lean_object* v_as_2973_, lean_object* v_as_x27_2974_, lean_object* v_b_2975_, lean_object* v_a_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v_as_2973_, v_as_x27_2974_, v_b_2975_, v_a_2976_, v___y_2977_, v___y_2978_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v_as_2973_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(lean_object* v_00_u03b1_2981_, lean_object* v_ref_2982_, lean_object* v_msg_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_2982_, v_msg_2983_, v___y_2984_, v___y_2985_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___boxed(lean_object* v_00_u03b1_2988_, lean_object* v_ref_2989_, lean_object* v_msg_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(v_00_u03b1_2988_, v_ref_2989_, v_msg_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v_ref_2989_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_2995_, lean_object* v_m_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___redArg(v_m_2996_, v_a_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9___boxed(lean_object* v_00_u03b2_2999_, lean_object* v_m_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9(v_00_u03b2_2999_, v_m_3000_, v_a_3001_);
lean_dec(v_a_3001_);
lean_dec_ref(v_m_3000_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13(lean_object* v_00_u03b1_3003_, lean_object* v_msg_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v___x_3008_; 
lean_inc_ref(v___y_3005_);
v___x_3008_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___redArg(v_msg_3004_, v___y_3005_, v___y_3006_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13___boxed(lean_object* v_00_u03b1_3009_, lean_object* v_msg_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13(v_00_u03b1_3009_, v_msg_3010_, v___y_3011_, v___y_3012_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
return v_res_3014_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16(lean_object* v_00_u03b2_3015_, lean_object* v_x_3016_, lean_object* v_x_3017_){
_start:
{
uint8_t v___x_3018_; 
v___x_3018_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___redArg(v_x_3016_, v_x_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16___boxed(lean_object* v_00_u03b2_3019_, lean_object* v_x_3020_, lean_object* v_x_3021_){
_start:
{
uint8_t v_res_3022_; lean_object* v_r_3023_; 
v_res_3022_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16(v_00_u03b2_3019_, v_x_3020_, v_x_3021_);
lean_dec_ref(v_x_3021_);
v_r_3023_ = lean_box(v_res_3022_);
return v_r_3023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19(lean_object* v_00_u03b2_3024_, lean_object* v_a_3025_, lean_object* v_x_3026_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___redArg(v_a_3025_, v_x_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19___boxed(lean_object* v_00_u03b2_3028_, lean_object* v_a_3029_, lean_object* v_x_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__9_spec__19(v_00_u03b2_3028_, v_a_3029_, v_x_3030_);
lean_dec(v_x_3030_);
lean_dec(v_a_3029_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24(lean_object* v_msgData_3032_, lean_object* v_macroStack_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___redArg(v_msgData_3032_, v_macroStack_3033_, v___y_3035_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24___boxed(lean_object* v_msgData_3038_, lean_object* v_macroStack_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_spec__13_spec__24(v_msgData_3038_, v_macroStack_3039_, v___y_3040_, v___y_3041_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
return v_res_3043_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20(lean_object* v_00_u03b2_3044_, lean_object* v_x_3045_, size_t v_x_3046_, lean_object* v_x_3047_){
_start:
{
uint8_t v___x_3048_; 
v___x_3048_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___redArg(v_x_3045_, v_x_3046_, v_x_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20___boxed(lean_object* v_00_u03b2_3049_, lean_object* v_x_3050_, lean_object* v_x_3051_, lean_object* v_x_3052_){
_start:
{
size_t v_x_25193__boxed_3053_; uint8_t v_res_3054_; lean_object* v_r_3055_; 
v_x_25193__boxed_3053_ = lean_unbox_usize(v_x_3051_);
lean_dec(v_x_3051_);
v_res_3054_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20(v_00_u03b2_3049_, v_x_3050_, v_x_25193__boxed_3053_, v_x_3052_);
lean_dec_ref(v_x_3052_);
v_r_3055_ = lean_box(v_res_3054_);
return v_r_3055_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24(lean_object* v_00_u03b2_3056_, lean_object* v_keys_3057_, lean_object* v_vals_3058_, lean_object* v_heq_3059_, lean_object* v_i_3060_, lean_object* v_k_3061_){
_start:
{
uint8_t v___x_3062_; 
v___x_3062_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___redArg(v_keys_3057_, v_i_3060_, v_k_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24___boxed(lean_object* v_00_u03b2_3063_, lean_object* v_keys_3064_, lean_object* v_vals_3065_, lean_object* v_heq_3066_, lean_object* v_i_3067_, lean_object* v_k_3068_){
_start:
{
uint8_t v_res_3069_; lean_object* v_r_3070_; 
v_res_3069_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_spec__7_spec__16_spec__20_spec__24(v_00_u03b2_3063_, v_keys_3064_, v_vals_3065_, v_heq_3066_, v_i_3067_, v_k_3068_);
lean_dec_ref(v_k_3068_);
lean_dec_ref(v_vals_3065_);
lean_dec_ref(v_keys_3064_);
v_r_3070_ = lean_box(v_res_3069_);
return v_r_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1(){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3078_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3079_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
v___x_3080_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1));
v___x_3081_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___boxed), 4, 0);
v___x_3082_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3078_, v___x_3079_, v___x_3080_, v___x_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___boxed(lean_object* v_a_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
return v_res_3084_;
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
