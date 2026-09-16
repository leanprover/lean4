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
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "atom"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11_value),LEAN_SCALAR_PTR_LITERAL(144, 22, 146, 169, 39, 242, 124, 88)}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value;
static const lean_string_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unicodeAtom"};
static const lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15 = (const lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15_value),LEAN_SCALAR_PTR_LITERAL(29, 147, 94, 13, 45, 35, 101, 109)}};
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
lean_object* v___x_132_; lean_object* v_attr_133_; 
v___x_132_ = lean_box(0);
v_attr_133_ = l_Lean_Syntax_getArg(v___x_129_, v___x_114_);
if (v___x_106_ == 0)
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_attr_133_);
v___x_150_ = l_Lean_Syntax_isOfKind(v_attr_133_, v___x_149_);
if (v___x_150_ == 0)
{
lean_dec(v_attr_133_);
lean_dec(v___x_129_);
v___y_117_ = v_v_113_;
goto v___jp_116_;
}
else
{
goto v___jp_134_;
}
}
else
{
goto v___jp_134_;
}
v___jp_134_:
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
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v_v_113_);
v___x_141_ = l_Lean_SourceInfo_fromRef(v___x_132_, v___x_106_);
v___x_142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_143_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
lean_inc_n(v___x_141_, 4);
v___x_144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_144_, 0, v___x_141_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
lean_ctor_set(v___x_144_, 2, v___x_143_);
v___x_145_ = l_Lean_Syntax_node1(v___x_141_, v___x_124_, v___x_144_);
lean_inc(v___x_107_);
v___x_146_ = l_Lean_Syntax_node1(v___x_141_, v___x_142_, v___x_107_);
v___x_147_ = l_Lean_Syntax_node2(v___x_141_, v___x_130_, v_attr_133_, v___x_146_);
v___x_148_ = l_Lean_Syntax_node2(v___x_141_, v___x_112_, v___x_145_, v___x_147_);
v___y_117_ = v___x_148_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___boxed(lean_object* v___x_151_, lean_object* v___x_152_, lean_object* v_sz_153_, lean_object* v_i_154_, lean_object* v_bs_155_){
_start:
{
uint8_t v___x_7298__boxed_156_; size_t v_sz_boxed_157_; size_t v_i_boxed_158_; lean_object* v_res_159_; 
v___x_7298__boxed_156_ = lean_unbox(v___x_151_);
v_sz_boxed_157_ = lean_unbox_usize(v_sz_153_);
lean_dec(v_sz_153_);
v_i_boxed_158_ = lean_unbox_usize(v_i_154_);
lean_dec(v_i_154_);
v_res_159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(v___x_7298__boxed_156_, v___x_152_, v_sz_boxed_157_, v_i_boxed_158_, v_bs_155_);
return v_res_159_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0(void){
_start:
{
uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = 0;
v___x_161_ = lean_box(0);
v___x_162_ = l_Lean_SourceInfo_fromRef(v___x_161_, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
v___x_164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_165_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0);
v___x_166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_163_);
return v___x_166_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1);
v___x_168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
v___x_169_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0);
v___x_170_ = l_Lean_Syntax_node1(v___x_169_, v___x_168_, v___x_167_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(lean_object* v___x_171_, size_t v_sz_172_, size_t v_i_173_, lean_object* v_bs_174_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = lean_usize_dec_lt(v_i_173_, v_sz_172_);
if (v___x_175_ == 0)
{
lean_dec(v___x_171_);
return v_bs_174_;
}
else
{
lean_object* v___x_176_; lean_object* v_v_177_; lean_object* v___x_178_; lean_object* v_bs_x27_179_; lean_object* v___y_181_; uint8_t v___x_186_; 
v___x_176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
v_v_177_ = lean_array_uget(v_bs_174_, v_i_173_);
v___x_178_ = lean_unsigned_to_nat(0u);
v_bs_x27_179_ = lean_array_uset(v_bs_174_, v_i_173_, v___x_178_);
lean_inc(v_v_177_);
v___x_186_ = l_Lean_Syntax_isOfKind(v_v_177_, v___x_176_);
if (v___x_186_ == 0)
{
v___y_181_ = v_v_177_;
goto v___jp_180_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_187_ = l_Lean_Syntax_getArg(v_v_177_, v___x_178_);
v___x_188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(v___x_187_);
v___x_189_ = l_Lean_Syntax_isOfKind(v___x_187_, v___x_188_);
if (v___x_189_ == 0)
{
lean_dec(v___x_187_);
v___y_181_ = v_v_177_;
goto v___jp_180_;
}
else
{
lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_190_ = l_Lean_Syntax_getArg(v___x_187_, v___x_178_);
lean_dec(v___x_187_);
v___x_191_ = l_Lean_Syntax_matchesNull(v___x_190_, v___x_178_);
if (v___x_191_ == 0)
{
v___y_181_ = v_v_177_;
goto v___jp_180_;
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = l_Lean_Syntax_getArg(v_v_177_, v___x_192_);
v___x_194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
lean_inc(v___x_193_);
v___x_195_ = l_Lean_Syntax_isOfKind(v___x_193_, v___x_194_);
if (v___x_195_ == 0)
{
lean_dec(v___x_193_);
v___y_181_ = v_v_177_;
goto v___jp_180_;
}
else
{
lean_object* v___x_196_; lean_object* v_attr_197_; uint8_t v___x_198_; 
v___x_196_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
v_attr_197_ = l_Lean_Syntax_getArg(v___x_193_, v___x_178_);
lean_inc(v_attr_197_);
v___x_198_ = l_Lean_Syntax_isOfKind(v_attr_197_, v___x_196_);
if (v___x_198_ == 0)
{
lean_dec(v_attr_197_);
lean_dec(v___x_193_);
v___y_181_ = v_v_177_;
goto v___jp_180_;
}
else
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = l_Lean_Syntax_getArg(v___x_193_, v___x_192_);
lean_dec(v___x_193_);
v___x_200_ = l_Lean_Syntax_matchesNull(v___x_199_, v___x_178_);
if (v___x_200_ == 0)
{
lean_dec(v_attr_197_);
v___y_181_ = v_v_177_;
goto v___jp_180_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_201_ = l_Lean_TSyntax_getId(v_attr_197_);
v___x_202_ = l_Lean_Name_eraseMacroScopes(v___x_201_);
lean_dec(v___x_201_);
v___x_203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11));
v___x_204_ = lean_name_eq(v___x_202_, v___x_203_);
lean_dec(v___x_202_);
if (v___x_204_ == 0)
{
lean_dec(v_attr_197_);
v___y_181_ = v_v_177_;
goto v___jp_180_;
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec(v_v_177_);
v___x_205_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0);
v___x_206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_207_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2);
lean_inc(v___x_171_);
v___x_208_ = l_Lean_Syntax_node1(v___x_205_, v___x_206_, v___x_171_);
v___x_209_ = l_Lean_Syntax_node2(v___x_205_, v___x_194_, v_attr_197_, v___x_208_);
v___x_210_ = l_Lean_Syntax_node2(v___x_205_, v___x_176_, v___x_207_, v___x_209_);
v___y_181_ = v___x_210_;
goto v___jp_180_;
}
}
}
}
}
}
}
v___jp_180_:
{
size_t v___x_182_; size_t v___x_183_; lean_object* v___x_184_; 
v___x_182_ = ((size_t)1ULL);
v___x_183_ = lean_usize_add(v_i_173_, v___x_182_);
v___x_184_ = lean_array_uset(v_bs_x27_179_, v_i_173_, v___y_181_);
v_i_173_ = v___x_183_;
v_bs_174_ = v___x_184_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___boxed(lean_object* v___x_211_, lean_object* v_sz_212_, lean_object* v_i_213_, lean_object* v_bs_214_){
_start:
{
size_t v_sz_boxed_215_; size_t v_i_boxed_216_; lean_object* v_res_217_; 
v_sz_boxed_215_ = lean_unbox_usize(v_sz_212_);
lean_dec(v_sz_212_);
v_i_boxed_216_ = lean_unbox_usize(v_i_213_);
lean_dec(v_i_213_);
v_res_217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(v___x_211_, v_sz_boxed_215_, v_i_boxed_216_, v_bs_214_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addInheritDocDefault(lean_object* v_rhs_225_, lean_object* v_attrs_x3f_226_){
_start:
{
if (lean_obj_tag(v_attrs_x3f_226_) == 0)
{
lean_dec(v_rhs_225_);
return v_attrs_x3f_226_;
}
else
{
lean_object* v_val_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_val_227_ = lean_ctor_get(v_attrs_x3f_226_, 0);
v___x_228_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
lean_inc(v_rhs_225_);
v___x_229_ = l_Lean_Syntax_isOfKind(v_rhs_225_, v___x_228_);
if (v___x_229_ == 0)
{
if (v___x_229_ == 0)
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_rhs_225_);
v___x_239_ = l_Lean_Syntax_isOfKind(v_rhs_225_, v___x_238_);
if (v___x_239_ == 0)
{
lean_dec(v_rhs_225_);
return v_attrs_x3f_226_;
}
else
{
lean_inc(v_val_227_);
lean_dec_ref_known(v_attrs_x3f_226_, 1);
goto v___jp_230_;
}
}
else
{
lean_inc(v_val_227_);
lean_dec_ref_known(v_attrs_x3f_226_, 1);
goto v___jp_230_;
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = l_Lean_Syntax_getArg(v_rhs_225_, v___x_240_);
lean_dec(v_rhs_225_);
v___x_242_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v___x_241_);
v___x_243_ = l_Lean_Syntax_isOfKind(v___x_241_, v___x_242_);
if (v___x_243_ == 0)
{
lean_dec(v___x_241_);
return v_attrs_x3f_226_;
}
else
{
lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_256_; 
lean_inc(v_val_227_);
v_isSharedCheck_256_ = !lean_is_exclusive(v_attrs_x3f_226_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; 
v_unused_257_ = lean_ctor_get(v_attrs_x3f_226_, 0);
lean_dec(v_unused_257_);
v___x_245_ = v_attrs_x3f_226_;
v_isShared_246_ = v_isSharedCheck_256_;
goto v_resetjp_244_;
}
else
{
lean_dec(v_attrs_x3f_226_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_256_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; size_t v_sz_249_; size_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_247_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__2));
v___x_248_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_227_);
lean_dec(v_val_227_);
v_sz_249_ = lean_array_size(v___x_248_);
v___x_250_ = ((size_t)0ULL);
v___x_251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(v___x_241_, v_sz_249_, v___x_250_, v___x_248_);
v___x_252_ = l_Lean_Syntax_SepArray_ofElems(v___x_247_, v___x_251_);
lean_dec_ref(v___x_251_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_252_);
v___x_254_ = v___x_245_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
v___jp_230_:
{
lean_object* v___x_231_; lean_object* v___x_232_; size_t v_sz_233_; size_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_231_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__2));
v___x_232_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_227_);
lean_dec(v_val_227_);
v_sz_233_ = lean_array_size(v___x_232_);
v___x_234_ = ((size_t)0ULL);
v___x_235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(v___x_229_, v_rhs_225_, v_sz_233_, v___x_234_, v___x_232_);
v___x_236_ = l_Lean_Syntax_SepArray_ofElems(v___x_231_, v___x_235_);
lean_dec_ref(v___x_235_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2));
v___x_266_ = l_String_toRawSubstring_x27(v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(lean_object* v_x_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v_prec_x3f_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
lean_inc(v_x_297_);
v___x_337_ = l_Lean_Syntax_isOfKind(v_x_297_, v___x_336_);
if (v___x_337_ == 0)
{
if (v___x_337_ == 0)
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
lean_inc(v_x_297_);
v___x_345_ = l_Lean_Syntax_isOfKind(v_x_297_, v___x_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16));
lean_inc(v_x_297_);
v___x_347_ = l_Lean_Syntax_isOfKind(v_x_297_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
lean_dec(v_x_297_);
v___x_348_ = l_Lean_Macro_throwUnsupported___redArg(v_a_299_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v_x_297_);
lean_ctor_set(v___x_349_, 1, v_a_299_);
return v___x_349_;
}
}
else
{
goto v___jp_338_;
}
}
else
{
goto v___jp_338_;
}
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = l_Lean_Syntax_getArg(v_x_297_, v___x_350_);
v___x_352_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
v___x_353_ = l_Lean_Syntax_isOfKind(v___x_351_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16));
lean_inc(v_x_297_);
v___x_355_ = l_Lean_Syntax_isOfKind(v_x_297_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
lean_dec(v_x_297_);
v___x_356_ = l_Lean_Macro_throwUnsupported___redArg(v_a_299_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v_x_297_);
lean_ctor_set(v___x_357_, 1, v_a_299_);
return v___x_357_;
}
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = l_Lean_Syntax_getArg(v_x_297_, v___x_358_);
v___x_360_ = l_Lean_Syntax_isNone(v___x_359_);
if (v___x_360_ == 0)
{
uint8_t v___x_361_; 
lean_inc(v___x_359_);
v___x_361_ = l_Lean_Syntax_matchesNull(v___x_359_, v___x_358_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; uint8_t v___x_363_; 
lean_dec(v___x_359_);
v___x_362_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16));
lean_inc(v_x_297_);
v___x_363_ = l_Lean_Syntax_isOfKind(v_x_297_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
lean_dec(v_x_297_);
v___x_364_ = l_Lean_Macro_throwUnsupported___redArg(v_a_299_);
return v___x_364_;
}
else
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_x_297_);
lean_ctor_set(v___x_365_, 1, v_a_299_);
return v___x_365_;
}
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_366_ = l_Lean_Syntax_getArg(v___x_359_, v___x_350_);
lean_dec(v___x_359_);
v___x_367_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
lean_inc(v___x_366_);
v___x_368_ = l_Lean_Syntax_isOfKind(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; uint8_t v___x_370_; 
lean_dec(v___x_366_);
v___x_369_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16));
lean_inc(v_x_297_);
v___x_370_ = l_Lean_Syntax_isOfKind(v_x_297_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec(v_x_297_);
v___x_371_ = l_Lean_Macro_throwUnsupported___redArg(v_a_299_);
return v___x_371_;
}
else
{
lean_object* v___x_372_; 
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v_x_297_);
lean_ctor_set(v___x_372_, 1, v_a_299_);
return v___x_372_;
}
}
else
{
lean_object* v_prec_x3f_373_; lean_object* v___x_374_; 
lean_dec(v_x_297_);
v_prec_x3f_373_ = l_Lean_Syntax_getArg(v___x_366_, v___x_358_);
lean_dec(v___x_366_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v_prec_x3f_373_);
v_prec_x3f_313_ = v___x_374_;
v___y_314_ = v_a_298_;
v___y_315_ = v_a_299_;
goto v___jp_312_;
}
}
}
else
{
lean_object* v___x_375_; 
lean_dec(v___x_359_);
lean_dec(v_x_297_);
v___x_375_ = lean_box(0);
v_prec_x3f_313_ = v___x_375_;
v___y_314_ = v_a_298_;
v___y_315_ = v_a_299_;
goto v___jp_312_;
}
}
}
v___jp_300_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
lean_inc_ref(v___y_303_);
v___x_308_ = l_Array_append___redArg(v___y_303_, v___y_307_);
lean_dec_ref(v___y_307_);
lean_inc(v___y_301_);
lean_inc(v___y_304_);
v___x_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_309_, 0, v___y_304_);
lean_ctor_set(v___x_309_, 1, v___y_301_);
lean_ctor_set(v___x_309_, 2, v___x_308_);
lean_inc(v___y_306_);
v___x_310_ = l_Lean_Syntax_node2(v___y_304_, v___y_306_, v___y_302_, v___x_309_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___y_305_);
return v___x_311_;
}
v___jp_312_:
{
lean_object* v_quotContext_316_; lean_object* v_currMacroScope_317_; lean_object* v_ref_318_; uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_quotContext_316_ = lean_ctor_get(v___y_314_, 1);
v_currMacroScope_317_ = lean_ctor_get(v___y_314_, 2);
v_ref_318_ = lean_ctor_get(v___y_314_, 5);
v___x_319_ = 0;
v___x_320_ = l_Lean_SourceInfo_fromRef(v_ref_318_, v___x_319_);
v___x_321_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2));
v___x_322_ = lean_obj_once(&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3, &l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3_once, _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3);
v___x_323_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
lean_inc(v_currMacroScope_317_);
lean_inc(v_quotContext_316_);
v___x_324_ = l_Lean_addMacroScope(v_quotContext_316_, v___x_323_, v_currMacroScope_317_);
v___x_325_ = lean_box(0);
lean_inc(v___x_320_);
v___x_326_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_326_, 0, v___x_320_);
lean_ctor_set(v___x_326_, 1, v___x_322_);
lean_ctor_set(v___x_326_, 2, v___x_324_);
lean_ctor_set(v___x_326_, 3, v___x_325_);
v___x_327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_328_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
if (lean_obj_tag(v_prec_x3f_313_) == 1)
{
lean_object* v_val_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_val_329_ = lean_ctor_get(v_prec_x3f_313_, 0);
lean_inc(v_val_329_);
lean_dec_ref_known(v_prec_x3f_313_, 1);
v___x_330_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
v___x_331_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc_n(v___x_320_, 2);
v___x_332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_320_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = l_Lean_Syntax_node2(v___x_320_, v___x_330_, v___x_332_, v_val_329_);
v___x_334_ = l_Array_mkArray1___redArg(v___x_333_);
v___y_301_ = v___x_327_;
v___y_302_ = v___x_326_;
v___y_303_ = v___x_328_;
v___y_304_ = v___x_320_;
v___y_305_ = v___y_315_;
v___y_306_ = v___x_321_;
v___y_307_ = v___x_334_;
goto v___jp_300_;
}
else
{
lean_object* v___x_335_; 
lean_dec(v_prec_x3f_313_);
v___x_335_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_301_ = v___x_327_;
v___y_302_ = v___x_326_;
v___y_303_ = v___x_328_;
v___y_304_ = v___x_320_;
v___y_305_ = v___y_315_;
v___y_306_ = v___x_321_;
v___y_307_ = v___x_335_;
goto v___jp_300_;
}
}
v___jp_338_:
{
lean_object* v_ref_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_ref_339_ = lean_ctor_get(v_a_298_, 5);
v___x_340_ = l_Lean_SourceInfo_fromRef(v_ref_339_, v___x_337_);
v___x_341_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12));
v___x_342_ = l_Lean_Syntax_node1(v___x_340_, v___x_341_, v_x_297_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v_a_299_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___boxed(lean_object* v_x_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(v_x_376_, v_a_377_, v_a_378_);
lean_dec_ref(v_a_377_);
return v_res_379_;
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
v___x_393_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
v___x_394_ = lean_name_eq(v_k_390_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16));
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
lean_dec_ref_known(v___x_418_, 4);
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
lean_dec_ref_known(v___x_420_, 4);
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
lean_inc(v_e_577_);
v___x_580_ = l_Lean_Elab_Term_expandCDot_x3f(v_e_577_, v___x_579_, v_a_469_, v_a_470_);
lean_dec_ref_known(v___x_579_, 1);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v_a_582_; lean_object* v___y_584_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
v_a_582_ = lean_ctor_get(v___x_580_, 1);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_580_, 2);
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
lean_dec_ref_known(v_a_581_, 1);
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
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_bs_608_);
lean_ctor_set(v___x_612_, 1, v___y_610_);
return v___x_612_;
}
else
{
lean_object* v_v_613_; lean_object* v___x_614_; 
v_v_613_ = lean_array_uget_borrowed(v_bs_608_, v_i_607_);
lean_inc(v_v_613_);
v___x_614_ = l_Lean_Elab_Command_removeParentheses(v_v_613_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v_a_616_; lean_object* v___x_617_; lean_object* v_bs_x27_618_; size_t v___x_619_; size_t v___x_620_; lean_object* v___x_621_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
v_a_616_ = lean_ctor_get(v___x_614_, 1);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_614_, 2);
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
lean_dec_ref(v___y_635_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses___boxed(lean_object* v_stx_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Elab_Command_removeParentheses(v_stx_640_, v_a_641_, v_a_642_);
lean_dec_ref(v_a_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(lean_object* v___x_647_, uint8_t v_firstChoiceOnly_648_, lean_object* v_stx_649_, lean_object* v_b_650_){
_start:
{
lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v_snd_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_699_; 
v_snd_663_ = lean_ctor_get(v_b_650_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_b_650_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v_b_650_, 0);
lean_dec(v_unused_700_);
v___x_665_ = v_b_650_;
v_isShared_666_ = v_isSharedCheck_699_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_snd_663_);
lean_dec(v_b_650_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_699_;
goto v_resetjp_664_;
}
v___jp_651_:
{
lean_object* v___x_654_; lean_object* v___x_655_; size_t v_sz_656_; size_t v___x_657_; lean_object* v___x_658_; lean_object* v_fst_659_; 
v___x_654_ = lean_box(0);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v___y_652_);
v_sz_656_ = lean_array_size(v___y_653_);
v___x_657_ = ((size_t)0ULL);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v___x_647_, v_firstChoiceOnly_648_, v___y_653_, v_sz_656_, v___x_657_, v___x_655_);
v_fst_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_fst_659_);
if (lean_obj_tag(v_fst_659_) == 0)
{
lean_object* v_snd_660_; lean_object* v___x_661_; 
v_snd_660_ = lean_ctor_get(v___x_658_, 1);
lean_inc(v_snd_660_);
lean_dec_ref(v___x_658_);
v___x_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_661_, 0, v_snd_660_);
return v___x_661_;
}
else
{
lean_object* v_val_662_; 
lean_dec_ref(v___x_658_);
v_val_662_ = lean_ctor_get(v_fst_659_, 0);
lean_inc(v_val_662_);
lean_dec_ref_known(v_fst_659_, 1);
return v_val_662_;
}
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___y_670_; lean_object* v_a_671_; uint8_t v___x_680_; 
v___x_667_ = lean_box(0);
v___x_668_ = lean_box(0);
v___x_680_ = l_Lean_Syntax_isAntiquot(v_stx_649_);
if (v___x_680_ == 0)
{
lean_object* v___x_682_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_682_ = v___x_665_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_snd_663_);
v___x_682_ = v_reuseFailAlloc_684_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; 
lean_inc_ref(v___x_682_);
v___x_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
v___y_670_ = v___x_683_;
v_a_671_ = v___x_682_;
goto v___jp_669_;
}
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_685_ = l_Lean_Syntax_getAntiquotTerm(v_stx_649_);
v___x_686_ = l_Lean_Syntax_getId(v___x_685_);
lean_dec(v___x_685_);
v___x_687_ = l_Lean_NameSet_contains(v_snd_663_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = l_Lean_NameSet_insert(v_snd_663_, v___x_686_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_688_);
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_690_ = v___x_665_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_692_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; 
lean_inc_ref(v___x_690_);
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
v___y_670_ = v___x_691_;
v_a_671_ = v___x_690_;
goto v___jp_669_;
}
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
lean_dec(v___x_686_);
v___x_693_ = lean_box(v___x_687_);
v___x_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_694_);
v___x_696_ = v___x_665_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_snd_663_);
v___x_696_ = v_reuseFailAlloc_698_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; 
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
}
v___jp_669_:
{
if (lean_obj_tag(v_stx_649_) == 1)
{
lean_dec_ref(v___y_670_);
if (v_firstChoiceOnly_648_ == 0)
{
lean_object* v_args_672_; 
v_args_672_ = lean_ctor_get(v_stx_649_, 2);
v___y_652_ = v_a_671_;
v___y_653_ = v_args_672_;
goto v___jp_651_;
}
else
{
lean_object* v_kind_673_; lean_object* v_args_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_kind_673_ = lean_ctor_get(v_stx_649_, 1);
v_args_674_ = lean_ctor_get(v_stx_649_, 2);
v___x_675_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1));
v___x_676_ = lean_name_eq(v_kind_673_, v___x_675_);
if (v___x_676_ == 0)
{
v___y_652_ = v_a_671_;
v___y_653_ = v_args_674_;
goto v___jp_651_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_array_get_borrowed(v___x_668_, v_args_674_, v___x_677_);
v_stx_649_ = v___x_678_;
v_b_650_ = v_a_671_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_a_671_);
return v___y_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(lean_object* v___x_701_, uint8_t v_firstChoiceOnly_702_, lean_object* v_as_703_, size_t v_sz_704_, size_t v_i_705_, lean_object* v_b_706_){
_start:
{
uint8_t v___x_707_; 
v___x_707_ = lean_usize_dec_lt(v_i_705_, v_sz_704_);
if (v___x_707_ == 0)
{
return v_b_706_;
}
else
{
lean_object* v_snd_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_726_; 
v_snd_708_ = lean_ctor_get(v_b_706_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_b_706_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v_b_706_, 0);
lean_dec(v_unused_727_);
v___x_710_ = v_b_706_;
v_isShared_711_ = v_isSharedCheck_726_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_snd_708_);
lean_dec(v_b_706_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_726_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v_a_712_; lean_object* v___x_713_; 
v_a_712_ = lean_array_uget_borrowed(v_as_703_, v_i_705_);
lean_inc(v_snd_708_);
v___x_713_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_701_, v_firstChoiceOnly_702_, v_a_712_, v_snd_708_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_714_);
v___x_716_ = v___x_710_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_snd_708_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
lean_dec(v_snd_708_);
v_a_718_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_713_, 1);
v___x_719_ = lean_box(0);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v_a_718_);
lean_ctor_set(v___x_710_, 0, v___x_719_);
v___x_721_ = v___x_710_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_a_718_);
v___x_721_ = v_reuseFailAlloc_725_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
size_t v___x_722_; size_t v___x_723_; 
v___x_722_ = ((size_t)1ULL);
v___x_723_ = lean_usize_add(v_i_705_, v___x_722_);
v_i_705_ = v___x_723_;
v_b_706_ = v___x_721_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0___boxed(lean_object* v___x_728_, lean_object* v_firstChoiceOnly_729_, lean_object* v_as_730_, lean_object* v_sz_731_, lean_object* v_i_732_, lean_object* v_b_733_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_734_; size_t v_sz_boxed_735_; size_t v_i_boxed_736_; lean_object* v_res_737_; 
v_firstChoiceOnly_boxed_734_ = lean_unbox(v_firstChoiceOnly_729_);
v_sz_boxed_735_ = lean_unbox_usize(v_sz_731_);
lean_dec(v_sz_731_);
v_i_boxed_736_ = lean_unbox_usize(v_i_732_);
lean_dec(v_i_732_);
v_res_737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v___x_728_, v_firstChoiceOnly_boxed_734_, v_as_730_, v_sz_boxed_735_, v_i_boxed_736_, v_b_733_);
lean_dec_ref(v_as_730_);
lean_dec_ref(v___x_728_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___boxed(lean_object* v___x_738_, lean_object* v_firstChoiceOnly_739_, lean_object* v_stx_740_, lean_object* v_b_741_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_742_; lean_object* v_res_743_; 
v_firstChoiceOnly_boxed_742_ = lean_unbox(v_firstChoiceOnly_739_);
v_res_743_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_738_, v_firstChoiceOnly_boxed_742_, v_stx_740_, v_b_741_);
lean_dec(v_stx_740_);
lean_dec_ref(v___x_738_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(lean_object* v_as_744_, size_t v_sz_745_, size_t v_i_746_, lean_object* v_b_747_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = lean_usize_dec_lt(v_i_746_, v_sz_745_);
if (v___x_748_ == 0)
{
return v_b_747_;
}
else
{
lean_object* v_snd_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_787_; 
v_snd_749_ = lean_ctor_get(v_b_747_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_b_747_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v_b_747_, 0);
lean_dec(v_unused_788_);
v___x_751_ = v_b_747_;
v_isShared_752_ = v_isSharedCheck_787_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_snd_749_);
lean_dec(v_b_747_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_787_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_a_753_; lean_object* v___x_754_; uint8_t v_firstChoiceOnly_755_; lean_object* v_stx_756_; lean_object* v___x_757_; lean_object* v___y_759_; lean_object* v___x_783_; 
v_a_753_ = lean_array_uget_borrowed(v_as_744_, v_i_746_);
lean_inc(v_a_753_);
v___x_754_ = l_Lean_Syntax_topDown(v_a_753_, v___x_748_);
v_firstChoiceOnly_755_ = lean_ctor_get_uint8(v___x_754_, sizeof(void*)*1);
v_stx_756_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_stx_756_);
lean_dec_ref(v___x_754_);
v___x_757_ = lean_box(0);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_757_);
v___x_783_ = v___x_751_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_snd_749_);
v___x_783_ = v_reuseFailAlloc_786_;
goto v_reusejp_782_;
}
v___jp_758_:
{
lean_object* v_fst_760_; 
v_fst_760_ = lean_ctor_get(v___y_759_, 0);
if (lean_obj_tag(v_fst_760_) == 0)
{
lean_object* v_snd_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_771_; 
v_snd_761_ = lean_ctor_get(v___y_759_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v___y_759_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v___y_759_, 0);
lean_dec(v_unused_772_);
v___x_763_ = v___y_759_;
v_isShared_764_ = v_isSharedCheck_771_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_snd_761_);
lean_dec(v___y_759_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_771_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_757_);
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_snd_761_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
size_t v___x_767_; size_t v___x_768_; 
v___x_767_ = ((size_t)1ULL);
v___x_768_ = lean_usize_add(v_i_746_, v___x_767_);
v_i_746_ = v___x_768_;
v_b_747_ = v___x_766_;
goto _start;
}
}
}
else
{
lean_object* v_snd_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_inc_ref(v_fst_760_);
v_snd_773_ = lean_ctor_get(v___y_759_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v___y_759_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___y_759_, 0);
lean_dec(v_unused_781_);
v___x_775_ = v___y_759_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_snd_773_);
lean_dec(v___y_759_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_fst_760_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_snd_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v_a_785_; 
lean_inc_ref(v___x_783_);
v___x_784_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_783_, v_firstChoiceOnly_755_, v_stx_756_, v___x_783_);
lean_dec(v_stx_756_);
lean_dec_ref(v___x_783_);
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref(v___x_784_);
v___y_759_ = v_a_785_;
goto v___jp_758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1___boxed(lean_object* v_as_789_, lean_object* v_sz_790_, lean_object* v_i_791_, lean_object* v_b_792_){
_start:
{
size_t v_sz_boxed_793_; size_t v_i_boxed_794_; lean_object* v_res_795_; 
v_sz_boxed_793_ = lean_unbox_usize(v_sz_790_);
lean_dec(v_sz_790_);
v_i_boxed_794_ = lean_unbox_usize(v_i_791_);
lean_dec(v_i_791_);
v_res_795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(v_as_789_, v_sz_boxed_793_, v_i_boxed_794_, v_b_792_);
lean_dec_ref(v_as_789_);
return v_res_795_;
}
}
static lean_object* _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0(void){
_start:
{
lean_object* v_seen_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_seen_796_ = l_Lean_NameSet_empty;
v___x_797_ = lean_box(0);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v_seen_796_);
return v___x_798_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_hasDuplicateAntiquot(lean_object* v_stxs_799_){
_start:
{
lean_object* v___x_800_; size_t v_sz_801_; size_t v___x_802_; lean_object* v___x_803_; lean_object* v_fst_804_; 
v___x_800_ = lean_obj_once(&l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0, &l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0_once, _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0);
v_sz_801_ = lean_array_size(v_stxs_799_);
v___x_802_ = ((size_t)0ULL);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(v_stxs_799_, v_sz_801_, v___x_802_, v___x_800_);
v_fst_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_fst_804_);
lean_dec_ref(v___x_803_);
if (lean_obj_tag(v_fst_804_) == 0)
{
uint8_t v___x_805_; 
v___x_805_ = 0;
return v___x_805_;
}
else
{
lean_object* v_val_806_; uint8_t v___x_807_; 
v_val_806_ = lean_ctor_get(v_fst_804_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v_fst_804_, 1);
v___x_807_ = lean_unbox(v_val_806_);
lean_dec(v_val_806_);
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___boxed(lean_object* v_stxs_808_){
_start:
{
uint8_t v_res_809_; lean_object* v_r_810_; 
v_res_809_ = l_Lean_Elab_Command_hasDuplicateAntiquot(v_stxs_808_);
lean_dec_ref(v_stxs_808_);
v_r_810_ = lean_box(v_res_809_);
return v_r_810_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__4(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__3));
v___x_818_ = l_String_toRawSubstring_x27(v___x_817_);
return v___x_818_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__15(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__14));
v___x_840_ = l_String_toRawSubstring_x27(v___x_839_);
return v___x_840_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__19(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__18));
v___x_846_ = l_String_toRawSubstring_x27(v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__22(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__21));
v___x_851_ = l_String_toRawSubstring_x27(v___x_850_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__40(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__39));
v___x_889_ = l_String_toRawSubstring_x27(v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__47(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__46));
v___x_904_ = l_String_toRawSubstring_x27(v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__55(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_920_ = l_String_toRawSubstring_x27(v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander(lean_object* v_attrKind_958_, lean_object* v_pat_959_, lean_object* v_qrhs_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v___y_964_; lean_object* v_fst_968_; lean_object* v_snd_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
lean_inc(v_qrhs_960_);
v___x_1167_ = l_Lean_Syntax_isOfKind(v_qrhs_960_, v___x_1166_);
if (v___x_1167_ == 0)
{
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_qrhs_960_);
v___x_1169_ = l_Lean_Syntax_isOfKind(v_qrhs_960_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_dec(v_qrhs_960_);
lean_dec(v_pat_959_);
lean_dec(v_attrKind_958_);
v___x_1170_ = lean_box(0);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
lean_ctor_set(v___x_1171_, 1, v_a_962_);
return v___x_1171_;
}
else
{
goto v___jp_1164_;
}
}
else
{
goto v___jp_1164_;
}
}
else
{
lean_object* v___x_1172_; lean_object* v_c_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1172_ = lean_unsigned_to_nat(0u);
v_c_1173_ = l_Lean_Syntax_getArg(v_qrhs_960_, v___x_1172_);
v___x_1174_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_c_1173_);
v___x_1175_ = l_Lean_Syntax_isOfKind(v_c_1173_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_dec(v_c_1173_);
lean_dec(v_qrhs_960_);
lean_dec(v_pat_959_);
lean_dec(v_attrKind_958_);
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
lean_ctor_set(v___x_1177_, 1, v_a_962_);
return v___x_1177_;
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v_args_1180_; 
v___x_1178_ = lean_unsigned_to_nat(1u);
v___x_1179_ = l_Lean_Syntax_getArg(v_qrhs_960_, v___x_1178_);
lean_dec(v_qrhs_960_);
v_args_1180_ = l_Lean_Syntax_getArgs(v___x_1179_);
lean_dec(v___x_1179_);
v_fst_968_ = v_c_1173_;
v_snd_969_ = v_args_1180_;
v___y_970_ = v_a_961_;
v___y_971_ = v_a_962_;
goto v___jp_967_;
}
}
v___jp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_box(0);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___y_964_);
return v___x_966_;
}
v___jp_967_:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = l_Lean_TSyntax_getId(v_fst_968_);
lean_dec(v_fst_968_);
v___x_973_ = l_Lean_Macro_resolveGlobalName(v___x_972_, v___y_970_, v___y_971_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
if (lean_obj_tag(v_a_974_) == 1)
{
lean_object* v_head_975_; lean_object* v_snd_976_; 
v_head_975_ = lean_ctor_get(v_a_974_, 0);
lean_inc(v_head_975_);
v_snd_976_ = lean_ctor_get(v_head_975_, 1);
lean_inc(v_snd_976_);
if (lean_obj_tag(v_snd_976_) == 0)
{
lean_object* v_tail_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1151_; 
v_tail_977_ = lean_ctor_get(v_a_974_, 1);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_a_974_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v_a_974_, 0);
lean_dec(v_unused_1152_);
v___x_979_ = v_a_974_;
v_isShared_980_ = v_isSharedCheck_1151_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_tail_977_);
lean_dec(v_a_974_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1151_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
if (lean_obj_tag(v_tail_977_) == 0)
{
lean_object* v_a_981_; lean_object* v_fst_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1148_; 
v_a_981_ = lean_ctor_get(v___x_973_, 1);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_973_, 2);
v_fst_982_ = lean_ctor_get(v_head_975_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_head_975_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v_head_975_, 1);
lean_dec(v_unused_1149_);
v___x_984_ = v_head_975_;
v_isShared_985_ = v_isSharedCheck_1148_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_fst_982_);
lean_dec(v_head_975_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1148_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
size_t v_sz_986_; size_t v___x_987_; lean_object* v___x_988_; 
v_sz_986_ = lean_array_size(v_snd_969_);
v___x_987_ = ((size_t)0ULL);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_986_, v___x_987_, v_snd_969_, v___y_970_, v_a_981_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1138_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_a_990_ = lean_ctor_get(v___x_988_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_992_ = v___x_988_;
v_isShared_993_ = v_isSharedCheck_1138_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1138_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
uint8_t v___x_994_; 
v___x_994_ = l_Lean_Elab_Command_hasDuplicateAntiquot(v_a_989_);
if (v___x_994_ == 0)
{
lean_object* v_quotContext_995_; lean_object* v_currMacroScope_996_; lean_object* v_ref_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v_quotContext_995_ = lean_ctor_get(v___y_970_, 1);
v_currMacroScope_996_ = lean_ctor_get(v___y_970_, 2);
v_ref_997_ = lean_ctor_get(v___y_970_, 5);
v___x_998_ = l_Lean_SourceInfo_fromRef(v_ref_997_, v___x_994_);
v___x_999_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0));
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__1));
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__2));
lean_inc(v___x_998_);
if (v_isShared_985_ == 0)
{
lean_ctor_set_tag(v___x_984_, 2);
lean_ctor_set(v___x_984_, 1, v___x_1001_);
lean_ctor_set(v___x_984_, 0, v___x_998_);
v___x_1003_ = v___x_984_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_1005_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
lean_inc_n(v___x_998_, 18);
v___x_1006_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1006_, 0, v___x_998_);
lean_ctor_set(v___x_1006_, 1, v___x_1004_);
lean_ctor_set(v___x_1006_, 2, v___x_1005_);
v___x_1007_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__4, &l_Lean_Elab_Command_mkUnexpander___closed__4_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__4);
v___x_1008_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__5));
lean_inc_n(v_currMacroScope_996_, 4);
lean_inc_n(v_quotContext_995_, 4);
v___x_1009_ = l_Lean_addMacroScope(v_quotContext_995_, v___x_1008_, v_currMacroScope_996_);
v___x_1010_ = lean_box(0);
v___x_1011_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1011_, 0, v___x_998_);
lean_ctor_set(v___x_1011_, 1, v___x_1007_);
lean_ctor_set(v___x_1011_, 2, v___x_1009_);
lean_ctor_set(v___x_1011_, 3, v___x_1010_);
v___x_1012_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__7));
v___x_1013_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
v___x_1014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_998_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_998_);
lean_ctor_set(v___x_1015_, 1, v___x_999_);
lean_inc_ref(v___x_1014_);
v___x_1016_ = l_Lean_Syntax_node2(v___x_998_, v___x_1012_, v___x_1014_, v___x_1015_);
lean_inc_ref(v___x_1011_);
lean_inc_ref(v___x_1006_);
v___x_1017_ = l_Lean_Syntax_node4(v___x_998_, v___x_1000_, v___x_1003_, v___x_1006_, v___x_1011_, v___x_1016_);
v___x_1018_ = l_Lean_Syntax_mkApp(v___x_1017_, v_a_989_);
lean_inc(v_attrKind_958_);
v___x_1019_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_958_);
v___x_1020_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__9));
v___x_1021_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__10));
v___x_1022_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
v___x_1023_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
v___x_1024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_998_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
v___x_1026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
v___x_1027_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__15, &l_Lean_Elab_Command_mkUnexpander___closed__15_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__15);
v___x_1028_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__16));
v___x_1029_ = l_Lean_addMacroScope(v_quotContext_995_, v___x_1028_, v_currMacroScope_996_);
v___x_1030_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1030_, 0, v___x_998_);
lean_ctor_set(v___x_1030_, 1, v___x_1027_);
lean_ctor_set(v___x_1030_, 2, v___x_1029_);
lean_ctor_set(v___x_1030_, 3, v___x_1010_);
v___x_1031_ = l_Lean_mkIdent(v_fst_982_);
lean_inc(v___x_1031_);
v___x_1032_ = l_Lean_Syntax_node1(v___x_998_, v___x_1004_, v___x_1031_);
v___x_1033_ = l_Lean_Syntax_node2(v___x_998_, v___x_1026_, v___x_1030_, v___x_1032_);
v___x_1034_ = l_Lean_Syntax_node2(v___x_998_, v___x_1025_, v_attrKind_958_, v___x_1033_);
v___x_1035_ = l_Lean_Syntax_node1(v___x_998_, v___x_1004_, v___x_1034_);
v___x_1036_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
v___x_1037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_998_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = l_Lean_Syntax_node3(v___x_998_, v___x_1022_, v___x_1024_, v___x_1035_, v___x_1037_);
v___x_1039_ = l_Lean_Syntax_node1(v___x_998_, v___x_1004_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_998_);
lean_ctor_set(v___x_1040_, 1, v___x_1020_);
v___x_1041_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__19, &l_Lean_Elab_Command_mkUnexpander___closed__19_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__19);
v___x_1042_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__20));
v___x_1043_ = l_Lean_addMacroScope(v_quotContext_995_, v___x_1042_, v_currMacroScope_996_);
v___x_1044_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1044_, 0, v___x_998_);
lean_ctor_set(v___x_1044_, 1, v___x_1041_);
lean_ctor_set(v___x_1044_, 2, v___x_1043_);
lean_ctor_set(v___x_1044_, 3, v___x_1010_);
v___x_1045_ = l_Lean_Syntax_node2(v___x_998_, v___x_1004_, v___x_1044_, v___x_1031_);
v___x_1046_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__22, &l_Lean_Elab_Command_mkUnexpander___closed__22_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__22);
v___x_1047_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__25));
v___x_1048_ = l_Lean_addMacroScope(v_quotContext_995_, v___x_1047_, v_currMacroScope_996_);
v___x_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v_snd_976_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v___x_1010_);
lean_ctor_set(v___x_979_, 0, v___x_1049_);
v___x_1051_ = v___x_979_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v___x_1010_);
v___x_1051_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
lean_inc_n(v___x_998_, 31);
v___x_1052_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1052_, 0, v___x_998_);
lean_ctor_set(v___x_1052_, 1, v___x_1046_);
lean_ctor_set(v___x_1052_, 2, v___x_1048_);
lean_ctor_set(v___x_1052_, 3, v___x_1051_);
v___x_1053_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_1054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_998_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__27));
v___x_1056_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__28));
v___x_1057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_998_);
lean_ctor_set(v___x_1057_, 1, v___x_1055_);
v___x_1058_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__30));
v___x_1059_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__32));
v___x_1060_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
v___x_1061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_998_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__35));
v___x_1063_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
v___x_1064_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_998_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_1066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_998_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
lean_inc_ref_n(v___x_1066_, 2);
lean_inc_ref(v___x_1064_);
v___x_1067_ = l_Lean_Syntax_node3(v___x_998_, v___x_1062_, v___x_1064_, v___x_1018_, v___x_1066_);
v___x_1068_ = l_Lean_Syntax_node1(v___x_998_, v___x_1004_, v___x_1067_);
v___x_1069_ = l_Lean_Syntax_node1(v___x_998_, v___x_1004_, v___x_1068_);
v___x_1070_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
v___x_1071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_998_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
v___x_1073_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__40, &l_Lean_Elab_Command_mkUnexpander___closed__40_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__40);
v___x_1074_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__41));
lean_inc_n(v_currMacroScope_996_, 3);
lean_inc_n(v_quotContext_995_, 3);
v___x_1075_ = l_Lean_addMacroScope(v_quotContext_995_, v___x_1074_, v_currMacroScope_996_);
v___x_1076_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__42));
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v_snd_976_);
v___x_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1010_);
v___x_1079_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1079_, 0, v___x_998_);
lean_ctor_set(v___x_1079_, 1, v___x_1073_);
lean_ctor_set(v___x_1079_, 2, v___x_1075_);
lean_ctor_set(v___x_1079_, 3, v___x_1078_);
v___x_1080_ = l_Lean_Syntax_node3(v___x_998_, v___x_1062_, v___x_1064_, v_pat_959_, v___x_1066_);
v___x_1081_ = l_Lean_Syntax_node2(v___x_998_, v___x_1004_, v___x_1011_, v___x_1080_);
v___x_1082_ = l_Lean_Syntax_node2(v___x_998_, v___x_1072_, v___x_1079_, v___x_1081_);
lean_inc_ref(v___x_1071_);
lean_inc_ref(v___x_1061_);
v___x_1083_ = l_Lean_Syntax_node4(v___x_998_, v___x_1059_, v___x_1061_, v___x_1069_, v___x_1071_, v___x_1082_);
v___x_1084_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__44));
v___x_1085_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__45));
v___x_1086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_998_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = l_Lean_Syntax_node1(v___x_998_, v___x_1084_, v___x_1086_);
v___x_1088_ = l_Lean_Syntax_node1(v___x_998_, v___x_1004_, v___x_1087_);
v___x_1089_ = l_Lean_Syntax_node1(v___x_998_, v___x_1004_, v___x_1088_);
v___x_1090_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__47, &l_Lean_Elab_Command_mkUnexpander___closed__47_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__47);
v___x_1091_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__48));
v___x_1092_ = l_Lean_addMacroScope(v_quotContext_995_, v___x_1091_, v_currMacroScope_996_);
v___x_1093_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__50));
v___x_1094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v_snd_976_);
v___x_1095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v___x_1010_);
v___x_1096_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1096_, 0, v___x_998_);
lean_ctor_set(v___x_1096_, 1, v___x_1090_);
lean_ctor_set(v___x_1096_, 2, v___x_1092_);
lean_ctor_set(v___x_1096_, 3, v___x_1095_);
v___x_1097_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__52));
v___x_1098_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__3));
v___x_1099_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
v___x_1100_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_998_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = ((lean_object*)(l_Lean_Elab_Command_removeParentheses___closed__5));
v___x_1102_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__55, &l_Lean_Elab_Command_mkUnexpander___closed__55_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__55);
v___x_1103_ = lean_box(0);
v___x_1104_ = l_Lean_addMacroScope(v_quotContext_995_, v___x_1103_, v_currMacroScope_996_);
v___x_1105_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__67));
v___x_1106_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1106_, 0, v___x_998_);
lean_ctor_set(v___x_1106_, 1, v___x_1102_);
lean_ctor_set(v___x_1106_, 2, v___x_1104_);
lean_ctor_set(v___x_1106_, 3, v___x_1105_);
v___x_1107_ = l_Lean_Syntax_node1(v___x_998_, v___x_1101_, v___x_1106_);
v___x_1108_ = l_Lean_Syntax_node2(v___x_998_, v___x_1098_, v___x_1100_, v___x_1107_);
lean_inc_ref(v___x_1006_);
v___x_1109_ = l_Lean_Syntax_node3(v___x_998_, v___x_1097_, v___x_1108_, v___x_1006_, v___x_1066_);
v___x_1110_ = l_Lean_Syntax_node1(v___x_998_, v___x_1004_, v___x_1109_);
v___x_1111_ = l_Lean_Syntax_node2(v___x_998_, v___x_1072_, v___x_1096_, v___x_1110_);
v___x_1112_ = l_Lean_Syntax_node4(v___x_998_, v___x_1059_, v___x_1061_, v___x_1089_, v___x_1071_, v___x_1111_);
v___x_1113_ = l_Lean_Syntax_node2(v___x_998_, v___x_1004_, v___x_1083_, v___x_1112_);
v___x_1114_ = l_Lean_Syntax_node1(v___x_998_, v___x_1058_, v___x_1113_);
v___x_1115_ = l_Lean_Syntax_node2(v___x_998_, v___x_1056_, v___x_1057_, v___x_1114_);
v___x_1116_ = lean_unsigned_to_nat(9u);
v___x_1117_ = lean_mk_empty_array_with_capacity(v___x_1116_);
v___x_1118_ = lean_array_push(v___x_1117_, v___x_1006_);
v___x_1119_ = lean_array_push(v___x_1118_, v___x_1039_);
v___x_1120_ = lean_array_push(v___x_1119_, v___x_1019_);
v___x_1121_ = lean_array_push(v___x_1120_, v___x_1040_);
v___x_1122_ = lean_array_push(v___x_1121_, v___x_1045_);
v___x_1123_ = lean_array_push(v___x_1122_, v___x_1014_);
v___x_1124_ = lean_array_push(v___x_1123_, v___x_1052_);
v___x_1125_ = lean_array_push(v___x_1124_, v___x_1054_);
v___x_1126_ = lean_array_push(v___x_1125_, v___x_1115_);
v___x_1127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1127_, 0, v___x_998_);
lean_ctor_set(v___x_1127_, 1, v___x_1021_);
lean_ctor_set(v___x_1127_, 2, v___x_1126_);
v___x_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_1128_);
v___x_1130_ = v___x_992_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_a_990_);
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
lean_object* v___x_1134_; lean_object* v___x_1136_; 
lean_dec(v_a_989_);
lean_del_object(v___x_984_);
lean_dec(v_fst_982_);
lean_del_object(v___x_979_);
lean_dec(v_pat_959_);
lean_dec(v_attrKind_958_);
v___x_1134_ = lean_box(0);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_1134_);
v___x_1136_ = v___x_992_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_a_990_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_del_object(v___x_984_);
lean_dec(v_fst_982_);
lean_del_object(v___x_979_);
lean_dec(v_pat_959_);
lean_dec(v_attrKind_958_);
v_a_1139_ = lean_ctor_get(v___x_988_, 0);
v_a_1140_ = lean_ctor_get(v___x_988_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_988_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_inc(v_a_1139_);
lean_dec(v___x_988_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1139_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
else
{
lean_object* v_a_1150_; 
lean_del_object(v___x_979_);
lean_dec(v_tail_977_);
lean_dec(v_head_975_);
lean_dec_ref(v_snd_969_);
lean_dec(v_pat_959_);
lean_dec(v_attrKind_958_);
v_a_1150_ = lean_ctor_get(v___x_973_, 1);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_973_, 2);
v___y_964_ = v_a_1150_;
goto v___jp_963_;
}
}
}
else
{
lean_object* v_a_1153_; 
lean_dec(v_snd_976_);
lean_dec_ref_known(v_a_974_, 2);
lean_dec(v_head_975_);
lean_dec_ref(v_snd_969_);
lean_dec(v_pat_959_);
lean_dec(v_attrKind_958_);
v_a_1153_ = lean_ctor_get(v___x_973_, 1);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___x_973_, 2);
v___y_964_ = v_a_1153_;
goto v___jp_963_;
}
}
else
{
lean_object* v_a_1154_; 
lean_dec(v_a_974_);
lean_dec_ref(v_snd_969_);
lean_dec(v_pat_959_);
lean_dec(v_attrKind_958_);
v_a_1154_ = lean_ctor_get(v___x_973_, 1);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_973_, 2);
v___y_964_ = v_a_1154_;
goto v___jp_963_;
}
}
else
{
lean_object* v_a_1155_; lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec_ref(v_snd_969_);
lean_dec(v_pat_959_);
lean_dec(v_attrKind_958_);
v_a_1155_ = lean_ctor_get(v___x_973_, 0);
v_a_1156_ = lean_ctor_get(v___x_973_, 1);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_973_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_inc(v_a_1155_);
lean_dec(v___x_973_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1155_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
v___jp_1164_:
{
lean_object* v___x_1165_; 
v___x_1165_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__68));
v_fst_968_ = v_qrhs_960_;
v_snd_969_ = v___x_1165_;
v___y_970_ = v_a_961_;
v___y_971_ = v_a_962_;
goto v___jp_967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander___boxed(lean_object* v_attrKind_1181_, lean_object* v_pat_1182_, lean_object* v_qrhs_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_Elab_Command_mkUnexpander(v_attrKind_1181_, v_pat_1182_, v_qrhs_1183_, v_a_1184_, v_a_1185_);
lean_dec_ref(v_a_1184_);
return v_res_1186_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1187_ = lean_box(0);
v___x_1188_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
lean_ctor_set(v___x_1189_, 1, v___x_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg(){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0);
v___x_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___boxed(lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(lean_object* v_00_u03b1_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___boxed(lean_object* v_00_u03b1_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(v_00_u03b1_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v_env_1208_; lean_object* v___x_1209_; lean_object* v_mainModule_1210_; lean_object* v___x_1211_; 
v___x_1207_ = lean_st_ref_get(v___y_1205_);
v_env_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc_ref(v_env_1208_);
lean_dec(v___x_1207_);
v___x_1209_ = l_Lean_Environment_header(v_env_1208_);
lean_dec_ref(v_env_1208_);
v_mainModule_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_mainModule_1210_);
lean_dec_ref(v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_mainModule_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg___boxed(lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_1212_);
lean_dec(v___y_1212_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_1216_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___boxed(lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___lam__0(lean_object* v___x_1223_, lean_object* v_sc_1224_){
_start:
{
lean_object* v_header_1225_; lean_object* v_currNamespace_1226_; lean_object* v_openDecls_1227_; lean_object* v_levelNames_1228_; lean_object* v_varDecls_1229_; lean_object* v_varUIds_1230_; lean_object* v_includedVars_1231_; lean_object* v_omittedVars_1232_; uint8_t v_isNoncomputable_1233_; uint8_t v_isPublic_1234_; uint8_t v_isMeta_1235_; lean_object* v_attrs_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
v_header_1225_ = lean_ctor_get(v_sc_1224_, 0);
v_currNamespace_1226_ = lean_ctor_get(v_sc_1224_, 2);
v_openDecls_1227_ = lean_ctor_get(v_sc_1224_, 3);
v_levelNames_1228_ = lean_ctor_get(v_sc_1224_, 4);
v_varDecls_1229_ = lean_ctor_get(v_sc_1224_, 5);
v_varUIds_1230_ = lean_ctor_get(v_sc_1224_, 6);
v_includedVars_1231_ = lean_ctor_get(v_sc_1224_, 7);
v_omittedVars_1232_ = lean_ctor_get(v_sc_1224_, 8);
v_isNoncomputable_1233_ = lean_ctor_get_uint8(v_sc_1224_, sizeof(void*)*10);
v_isPublic_1234_ = lean_ctor_get_uint8(v_sc_1224_, sizeof(void*)*10 + 1);
v_isMeta_1235_ = lean_ctor_get_uint8(v_sc_1224_, sizeof(void*)*10 + 2);
v_attrs_1236_ = lean_ctor_get(v_sc_1224_, 9);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_sc_1224_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v_sc_1224_, 1);
lean_dec(v_unused_1244_);
v___x_1238_ = v_sc_1224_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_attrs_1236_);
lean_inc(v_omittedVars_1232_);
lean_inc(v_includedVars_1231_);
lean_inc(v_varUIds_1230_);
lean_inc(v_varDecls_1229_);
lean_inc(v_levelNames_1228_);
lean_inc(v_openDecls_1227_);
lean_inc(v_currNamespace_1226_);
lean_inc(v_header_1225_);
lean_dec(v_sc_1224_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v___x_1223_);
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_header_1225_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_currNamespace_1226_);
lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_openDecls_1227_);
lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_levelNames_1228_);
lean_ctor_set(v_reuseFailAlloc_1242_, 5, v_varDecls_1229_);
lean_ctor_set(v_reuseFailAlloc_1242_, 6, v_varUIds_1230_);
lean_ctor_set(v_reuseFailAlloc_1242_, 7, v_includedVars_1231_);
lean_ctor_set(v_reuseFailAlloc_1242_, 8, v_omittedVars_1232_);
lean_ctor_set(v_reuseFailAlloc_1242_, 9, v_attrs_1236_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*10, v_isNoncomputable_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*10 + 1, v_isPublic_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*10 + 2, v_isMeta_1235_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(size_t v_sz_1245_, size_t v_i_1246_, lean_object* v_bs_1247_){
_start:
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_usize_dec_lt(v_i_1246_, v_sz_1245_);
if (v___x_1248_ == 0)
{
return v_bs_1247_;
}
else
{
lean_object* v_v_1249_; lean_object* v___x_1250_; lean_object* v_bs_x27_1251_; size_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v_v_1249_ = lean_array_uget(v_bs_1247_, v_i_1246_);
v___x_1250_ = lean_unsigned_to_nat(0u);
v_bs_x27_1251_ = lean_array_uset(v_bs_1247_, v_i_1246_, v___x_1250_);
v___x_1252_ = ((size_t)1ULL);
v___x_1253_ = lean_usize_add(v_i_1246_, v___x_1252_);
v___x_1254_ = lean_array_uset(v_bs_x27_1251_, v_i_1246_, v_v_1249_);
v_i_1246_ = v___x_1253_;
v_bs_1247_ = v___x_1254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3___boxed(lean_object* v_sz_1256_, lean_object* v_i_1257_, lean_object* v_bs_1258_){
_start:
{
size_t v_sz_boxed_1259_; size_t v_i_boxed_1260_; lean_object* v_res_1261_; 
v_sz_boxed_1259_ = lean_unbox_usize(v_sz_1256_);
lean_dec(v_sz_1256_);
v_i_boxed_1260_ = lean_unbox_usize(v_i_1257_);
lean_dec(v_i_1257_);
v_res_1261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_boxed_1259_, v_i_boxed_1260_, v_bs_1258_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(lean_object* v_o_1265_, lean_object* v_k_1266_, uint8_t v_v_1267_){
_start:
{
lean_object* v_map_1268_; uint8_t v_hasTrace_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1283_; 
v_map_1268_ = lean_ctor_get(v_o_1265_, 0);
v_hasTrace_1269_ = lean_ctor_get_uint8(v_o_1265_, sizeof(void*)*1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_o_1265_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1271_ = v_o_1265_;
v_isShared_1272_ = v_isSharedCheck_1283_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_map_1268_);
lean_dec(v_o_1265_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1283_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1273_, 0, v_v_1267_);
lean_inc(v_k_1266_);
v___x_1274_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1266_, v___x_1273_, v_map_1268_);
if (v_hasTrace_1269_ == 0)
{
lean_object* v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1278_; 
v___x_1275_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
v___x_1276_ = l_Lean_Name_isPrefixOf(v___x_1275_, v_k_1266_);
lean_dec(v_k_1266_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1274_);
v___x_1278_ = v___x_1271_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1274_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*1, v___x_1276_);
return v___x_1278_;
}
}
else
{
lean_object* v___x_1281_; 
lean_dec(v_k_1266_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1274_);
v___x_1281_ = v___x_1271_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1274_);
lean_ctor_set_uint8(v_reuseFailAlloc_1282_, sizeof(void*)*1, v_hasTrace_1269_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___boxed(lean_object* v_o_1284_, lean_object* v_k_1285_, lean_object* v_v_1286_){
_start:
{
uint8_t v_v_boxed_1287_; lean_object* v_res_1288_; 
v_v_boxed_1287_ = lean_unbox(v_v_1286_);
v_res_1288_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(v_o_1284_, v_k_1285_, v_v_boxed_1287_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(lean_object* v_opts_1289_, lean_object* v_opt_1290_, uint8_t v_val_1291_){
_start:
{
lean_object* v_name_1292_; lean_object* v___x_1293_; 
v_name_1292_ = lean_ctor_get(v_opt_1290_, 0);
lean_inc(v_name_1292_);
lean_dec_ref(v_opt_1290_);
v___x_1293_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(v_opts_1289_, v_name_1292_, v_val_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6___boxed(lean_object* v_opts_1294_, lean_object* v_opt_1295_, lean_object* v_val_1296_){
_start:
{
uint8_t v_val_boxed_1297_; lean_object* v_res_1298_; 
v_val_boxed_1297_ = lean_unbox(v_val_1296_);
v_res_1298_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_1294_, v_opt_1295_, v_val_boxed_1297_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(size_t v_sz_1299_, size_t v_i_1300_, lean_object* v_bs_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
uint8_t v___x_1304_; 
v___x_1304_ = lean_usize_dec_lt(v_i_1300_, v_sz_1299_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v_bs_1301_);
lean_ctor_set(v___x_1305_, 1, v___y_1303_);
return v___x_1305_;
}
else
{
lean_object* v_v_1306_; lean_object* v___x_1307_; 
v_v_1306_ = lean_array_uget_borrowed(v_bs_1301_, v_i_1300_);
lean_inc(v_v_1306_);
v___x_1307_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(v_v_1306_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v_a_1309_; lean_object* v___x_1310_; lean_object* v_bs_x27_1311_; size_t v___x_1312_; size_t v___x_1313_; lean_object* v___x_1314_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
v_a_1309_ = lean_ctor_get(v___x_1307_, 1);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1307_, 2);
v___x_1310_ = lean_unsigned_to_nat(0u);
v_bs_x27_1311_ = lean_array_uset(v_bs_1301_, v_i_1300_, v___x_1310_);
v___x_1312_ = ((size_t)1ULL);
v___x_1313_ = lean_usize_add(v_i_1300_, v___x_1312_);
v___x_1314_ = lean_array_uset(v_bs_x27_1311_, v_i_1300_, v_a_1308_);
v_i_1300_ = v___x_1313_;
v_bs_1301_ = v___x_1314_;
v___y_1303_ = v_a_1309_;
goto _start;
}
else
{
lean_object* v_a_1316_; lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec_ref(v_bs_1301_);
v_a_1316_ = lean_ctor_get(v___x_1307_, 0);
v_a_1317_ = lean_ctor_get(v___x_1307_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1307_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_inc(v_a_1316_);
lean_dec(v___x_1307_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1316_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed(lean_object* v_sz_1325_, lean_object* v_i_1326_, lean_object* v_bs_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
size_t v_sz_boxed_1330_; size_t v_i_boxed_1331_; lean_object* v_res_1332_; 
v_sz_boxed_1330_ = lean_unbox_usize(v_sz_1325_);
lean_dec(v_sz_1325_);
v_i_boxed_1331_ = lean_unbox_usize(v_i_1326_);
lean_dec(v_i_1326_);
v_res_1332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(v_sz_boxed_1330_, v_i_boxed_1331_, v_bs_1327_, v___y_1328_, v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(size_t v_sz_1333_, size_t v_i_1334_, lean_object* v_bs_1335_){
_start:
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_usize_dec_lt(v_i_1334_, v_sz_1333_);
if (v___x_1336_ == 0)
{
return v_bs_1335_;
}
else
{
lean_object* v___x_1337_; lean_object* v_v_1338_; lean_object* v_bs_x27_1339_; lean_object* v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1337_ = lean_unsigned_to_nat(0u);
v_v_1338_ = lean_array_uget(v_bs_1335_, v_i_1334_);
v_bs_x27_1339_ = lean_array_uset(v_bs_1335_, v_i_1334_, v___x_1337_);
v___x_1340_ = l_Lean_Syntax_getArg(v_v_1338_, v___x_1337_);
lean_dec(v_v_1338_);
v___x_1341_ = ((size_t)1ULL);
v___x_1342_ = lean_usize_add(v_i_1334_, v___x_1341_);
v___x_1343_ = lean_array_uset(v_bs_x27_1339_, v_i_1334_, v___x_1340_);
v_i_1334_ = v___x_1342_;
v_bs_1335_ = v___x_1343_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed(lean_object* v_sz_1345_, lean_object* v_i_1346_, lean_object* v_bs_1347_){
_start:
{
size_t v_sz_boxed_1348_; size_t v_i_boxed_1349_; lean_object* v_res_1350_; 
v_sz_boxed_1348_ = lean_unbox_usize(v_sz_1345_);
lean_dec(v_sz_1345_);
v_i_boxed_1349_ = lean_unbox_usize(v_i_1346_);
lean_dec(v_i_1346_);
v_res_1350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_boxed_1348_, v_i_boxed_1349_, v_bs_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(size_t v_sz_1351_, size_t v_i_1352_, lean_object* v_bs_1353_, lean_object* v___y_1354_){
_start:
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_usize_dec_lt(v_i_1352_, v_sz_1351_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_bs_1353_);
lean_ctor_set(v___x_1356_, 1, v___y_1354_);
return v___x_1356_;
}
else
{
lean_object* v_v_1357_; lean_object* v___x_1358_; 
v_v_1357_ = lean_array_uget_borrowed(v_bs_1353_, v_i_1352_);
lean_inc(v_v_1357_);
v___x_1358_ = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(v_v_1357_, v___y_1354_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v_a_1360_; lean_object* v___x_1361_; lean_object* v_bs_x27_1362_; size_t v___x_1363_; size_t v___x_1364_; lean_object* v___x_1365_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
v_a_1360_ = lean_ctor_get(v___x_1358_, 1);
lean_inc(v_a_1360_);
lean_dec_ref_known(v___x_1358_, 2);
v___x_1361_ = lean_unsigned_to_nat(0u);
v_bs_x27_1362_ = lean_array_uset(v_bs_1353_, v_i_1352_, v___x_1361_);
v___x_1363_ = ((size_t)1ULL);
v___x_1364_ = lean_usize_add(v_i_1352_, v___x_1363_);
v___x_1365_ = lean_array_uset(v_bs_x27_1362_, v_i_1352_, v_a_1359_);
v_i_1352_ = v___x_1364_;
v_bs_1353_ = v___x_1365_;
v___y_1354_ = v_a_1360_;
goto _start;
}
else
{
lean_object* v_a_1367_; lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v_bs_1353_);
v_a_1367_ = lean_ctor_get(v___x_1358_, 0);
v_a_1368_ = lean_ctor_get(v___x_1358_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1358_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_inc(v_a_1367_);
lean_dec(v___x_1358_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1367_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg___boxed(lean_object* v_sz_1376_, lean_object* v_i_1377_, lean_object* v_bs_1378_, lean_object* v___y_1379_){
_start:
{
size_t v_sz_boxed_1380_; size_t v_i_boxed_1381_; lean_object* v_res_1382_; 
v_sz_boxed_1380_ = lean_unbox_usize(v_sz_1376_);
lean_dec(v_sz_1376_);
v_i_boxed_1381_ = lean_unbox_usize(v_i_1377_);
lean_dec(v_i_1377_);
v_res_1382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(v_sz_boxed_1380_, v_i_boxed_1381_, v_bs_1378_, v___y_1379_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(size_t v_sz_1383_, size_t v_i_1384_, lean_object* v_bs_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(v_sz_1383_, v_i_1384_, v_bs_1385_, v___y_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed(lean_object* v_sz_1389_, lean_object* v_i_1390_, lean_object* v_bs_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
size_t v_sz_boxed_1394_; size_t v_i_boxed_1395_; lean_object* v_res_1396_; 
v_sz_boxed_1394_ = lean_unbox_usize(v_sz_1389_);
lean_dec(v_sz_1389_);
v_i_boxed_1395_ = lean_unbox_usize(v_i_1390_);
lean_dec(v_i_1390_);
v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(v_sz_boxed_1394_, v_i_boxed_1395_, v_bs_1391_, v___y_1392_, v___y_1393_);
lean_dec_ref(v___y_1392_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(lean_object* v_env_1397_, lean_object* v_currNamespace_1398_, lean_object* v_openDecls_1399_, lean_object* v_n_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = l_Lean_ResolveName_resolveNamespace(v_env_1397_, v_currNamespace_1398_, v_openDecls_1399_, v_n_1400_);
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
lean_ctor_set(v___x_1404_, 1, v___y_1402_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed(lean_object* v_env_1405_, lean_object* v_currNamespace_1406_, lean_object* v_openDecls_1407_, lean_object* v_n_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(v_env_1405_, v_currNamespace_1406_, v_openDecls_1407_, v_n_1408_, v___y_1409_, v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1411_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1412_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
return v___x_1414_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
lean_ctor_set(v___x_1417_, 2, v___x_1416_);
lean_ctor_set(v___x_1417_, 3, v___x_1416_);
lean_ctor_set(v___x_1417_, 4, v___x_1415_);
lean_ctor_set(v___x_1417_, 5, v___x_1415_);
lean_ctor_set(v___x_1417_, 6, v___x_1415_);
lean_ctor_set(v___x_1417_, 7, v___x_1415_);
lean_ctor_set(v___x_1417_, 8, v___x_1415_);
lean_ctor_set(v___x_1417_, 9, v___x_1415_);
lean_ctor_set(v___x_1417_, 10, v___x_1415_);
return v___x_1417_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = lean_unsigned_to_nat(32u);
v___x_1419_ = lean_mk_empty_array_with_capacity(v___x_1418_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
return v___x_1420_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4(void){
_start:
{
size_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1421_ = ((size_t)5ULL);
v___x_1422_ = lean_unsigned_to_nat(0u);
v___x_1423_ = lean_unsigned_to_nat(32u);
v___x_1424_ = lean_mk_empty_array_with_capacity(v___x_1423_);
v___x_1425_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3);
v___x_1426_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
lean_ctor_set(v___x_1426_, 1, v___x_1424_);
lean_ctor_set(v___x_1426_, 2, v___x_1422_);
lean_ctor_set(v___x_1426_, 3, v___x_1422_);
lean_ctor_set_usize(v___x_1426_, 4, v___x_1421_);
return v___x_1426_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1427_ = lean_box(1);
v___x_1428_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4);
v___x_1429_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_1430_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1428_);
lean_ctor_set(v___x_1430_, 2, v___x_1427_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; lean_object* v_env_1435_; lean_object* v___x_1436_; lean_object* v_scopes_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v_opts_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1434_ = lean_st_ref_get(v___y_1432_);
v_env_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc_ref(v_env_1435_);
lean_dec(v___x_1434_);
v___x_1436_ = lean_st_ref_get(v___y_1432_);
v_scopes_1437_ = lean_ctor_get(v___x_1436_, 2);
lean_inc(v_scopes_1437_);
lean_dec(v___x_1436_);
v___x_1438_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1439_ = l_List_head_x21___redArg(v___x_1438_, v_scopes_1437_);
lean_dec(v_scopes_1437_);
v_opts_1440_ = lean_ctor_get(v___x_1439_, 1);
lean_inc_ref(v_opts_1440_);
lean_dec(v___x_1439_);
v___x_1441_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_1442_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5);
v___x_1443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1443_, 0, v_env_1435_);
lean_ctor_set(v___x_1443_, 1, v___x_1441_);
lean_ctor_set(v___x_1443_, 2, v___x_1442_);
lean_ctor_set(v___x_1443_, 3, v_opts_1440_);
v___x_1444_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
lean_ctor_set(v___x_1444_, 1, v_msgData_1431_);
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msgData_1446_, v___y_1447_);
lean_dec(v___y_1447_);
return v_res_1449_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1450_; double v___x_1451_; 
v___x_1450_ = lean_unsigned_to_nat(0u);
v___x_1451_ = lean_float_of_nat(v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(lean_object* v_cls_1454_, lean_object* v_msg_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_Elab_Command_getRef___redArg(v___y_1456_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1461_; lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1509_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___x_1461_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msg_1455_, v___y_1457_);
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1509_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1509_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v_traceState_1467_; lean_object* v_env_1468_; lean_object* v_messages_1469_; lean_object* v_scopes_1470_; lean_object* v_usedQuotCtxts_1471_; lean_object* v_nextMacroScope_1472_; lean_object* v_maxRecDepth_1473_; lean_object* v_ngen_1474_; lean_object* v_auxDeclNGen_1475_; lean_object* v_infoState_1476_; lean_object* v_snapshotTasks_1477_; lean_object* v_prevLinterStates_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1508_; 
v___x_1466_ = lean_st_ref_take(v___y_1457_);
v_traceState_1467_ = lean_ctor_get(v___x_1466_, 9);
v_env_1468_ = lean_ctor_get(v___x_1466_, 0);
v_messages_1469_ = lean_ctor_get(v___x_1466_, 1);
v_scopes_1470_ = lean_ctor_get(v___x_1466_, 2);
v_usedQuotCtxts_1471_ = lean_ctor_get(v___x_1466_, 3);
v_nextMacroScope_1472_ = lean_ctor_get(v___x_1466_, 4);
v_maxRecDepth_1473_ = lean_ctor_get(v___x_1466_, 5);
v_ngen_1474_ = lean_ctor_get(v___x_1466_, 6);
v_auxDeclNGen_1475_ = lean_ctor_get(v___x_1466_, 7);
v_infoState_1476_ = lean_ctor_get(v___x_1466_, 8);
v_snapshotTasks_1477_ = lean_ctor_get(v___x_1466_, 10);
v_prevLinterStates_1478_ = lean_ctor_get(v___x_1466_, 11);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1480_ = v___x_1466_;
v_isShared_1481_ = v_isSharedCheck_1508_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_prevLinterStates_1478_);
lean_inc(v_snapshotTasks_1477_);
lean_inc(v_traceState_1467_);
lean_inc(v_infoState_1476_);
lean_inc(v_auxDeclNGen_1475_);
lean_inc(v_ngen_1474_);
lean_inc(v_maxRecDepth_1473_);
lean_inc(v_nextMacroScope_1472_);
lean_inc(v_usedQuotCtxts_1471_);
lean_inc(v_scopes_1470_);
lean_inc(v_messages_1469_);
lean_inc(v_env_1468_);
lean_dec(v___x_1466_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1508_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
uint64_t v_tid_1482_; lean_object* v_traces_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1507_; 
v_tid_1482_ = lean_ctor_get_uint64(v_traceState_1467_, sizeof(void*)*1);
v_traces_1483_ = lean_ctor_get(v_traceState_1467_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_traceState_1467_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1485_ = v_traceState_1467_;
v_isShared_1486_ = v_isSharedCheck_1507_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_traces_1483_);
lean_dec(v_traceState_1467_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1507_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; double v___x_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1487_ = lean_box(0);
v___x_1488_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0);
v___x_1489_ = 0;
v___x_1490_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1491_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1491_, 0, v_cls_1454_);
lean_ctor_set(v___x_1491_, 1, v___x_1487_);
lean_ctor_set(v___x_1491_, 2, v___x_1490_);
lean_ctor_set_float(v___x_1491_, sizeof(void*)*3, v___x_1488_);
lean_ctor_set_float(v___x_1491_, sizeof(void*)*3 + 8, v___x_1488_);
lean_ctor_set_uint8(v___x_1491_, sizeof(void*)*3 + 16, v___x_1489_);
v___x_1492_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__1));
v___x_1493_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1491_);
lean_ctor_set(v___x_1493_, 1, v_a_1462_);
lean_ctor_set(v___x_1493_, 2, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_a_1460_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = l_Lean_PersistentArray_push___redArg(v_traces_1483_, v___x_1494_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1495_);
v___x_1497_ = v___x_1485_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1495_);
lean_ctor_set_uint64(v_reuseFailAlloc_1506_, sizeof(void*)*1, v_tid_1482_);
v___x_1497_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 9, v___x_1497_);
v___x_1499_ = v___x_1480_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_env_1468_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_messages_1469_);
lean_ctor_set(v_reuseFailAlloc_1505_, 2, v_scopes_1470_);
lean_ctor_set(v_reuseFailAlloc_1505_, 3, v_usedQuotCtxts_1471_);
lean_ctor_set(v_reuseFailAlloc_1505_, 4, v_nextMacroScope_1472_);
lean_ctor_set(v_reuseFailAlloc_1505_, 5, v_maxRecDepth_1473_);
lean_ctor_set(v_reuseFailAlloc_1505_, 6, v_ngen_1474_);
lean_ctor_set(v_reuseFailAlloc_1505_, 7, v_auxDeclNGen_1475_);
lean_ctor_set(v_reuseFailAlloc_1505_, 8, v_infoState_1476_);
lean_ctor_set(v_reuseFailAlloc_1505_, 9, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1505_, 10, v_snapshotTasks_1477_);
lean_ctor_set(v_reuseFailAlloc_1505_, 11, v_prevLinterStates_1478_);
v___x_1499_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1500_ = lean_st_ref_put(v___y_1457_, v___x_1499_);
v___x_1501_ = lean_box(0);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v___x_1501_);
v___x_1503_ = v___x_1464_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v_msg_1455_);
lean_dec(v_cls_1454_);
v_a_1510_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1459_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1459_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___boxed(lean_object* v_cls_1518_, lean_object* v_msg_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_1518_, v_msg_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(lean_object* v_as_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
if (lean_obj_tag(v_as_1524_) == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = lean_box(0);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
else
{
lean_object* v_head_1530_; lean_object* v_tail_1531_; lean_object* v_fst_1532_; lean_object* v_snd_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_scopes_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v_opts_1540_; uint8_t v_hasTrace_1541_; 
v_head_1530_ = lean_ctor_get(v_as_1524_, 0);
lean_inc(v_head_1530_);
v_tail_1531_ = lean_ctor_get(v_as_1524_, 1);
lean_inc(v_tail_1531_);
lean_dec_ref_known(v_as_1524_, 2);
v_fst_1532_ = lean_ctor_get(v_head_1530_, 0);
lean_inc(v_fst_1532_);
v_snd_1533_ = lean_ctor_get(v_head_1530_, 1);
lean_inc(v_snd_1533_);
lean_dec(v_head_1530_);
v___x_1534_ = l_Lean_inheritedTraceOptions;
v___x_1535_ = lean_st_ref_get(v___x_1534_);
v___x_1536_ = lean_st_ref_get(v___y_1526_);
v_scopes_1537_ = lean_ctor_get(v___x_1536_, 2);
lean_inc(v_scopes_1537_);
lean_dec(v___x_1536_);
v___x_1538_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1539_ = l_List_head_x21___redArg(v___x_1538_, v_scopes_1537_);
lean_dec(v_scopes_1537_);
v_opts_1540_ = lean_ctor_get(v___x_1539_, 1);
lean_inc_ref(v_opts_1540_);
lean_dec(v___x_1539_);
v_hasTrace_1541_ = lean_ctor_get_uint8(v_opts_1540_, sizeof(void*)*1);
if (v_hasTrace_1541_ == 0)
{
lean_dec_ref(v_opts_1540_);
lean_dec(v___x_1535_);
lean_dec(v_snd_1533_);
lean_dec(v_fst_1532_);
v_as_1524_ = v_tail_1531_;
goto _start;
}
else
{
lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1543_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
lean_inc(v_fst_1532_);
v___x_1544_ = l_Lean_Name_append(v___x_1543_, v_fst_1532_);
v___x_1545_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1535_, v_opts_1540_, v___x_1544_);
lean_dec(v___x_1544_);
lean_dec_ref(v_opts_1540_);
lean_dec(v___x_1535_);
if (v___x_1545_ == 0)
{
lean_dec(v_snd_1533_);
lean_dec(v_fst_1532_);
v_as_1524_ = v_tail_1531_;
goto _start;
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1547_, 0, v_snd_1533_);
v___x_1548_ = l_Lean_MessageData_ofFormat(v___x_1547_);
v___x_1549_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_fst_1532_, v___x_1548_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_dec_ref_known(v___x_1549_, 1);
v_as_1524_ = v_tail_1531_;
goto _start;
}
else
{
lean_dec(v_tail_1531_);
return v___x_1549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___boxed(lean_object* v_as_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v_as_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(lean_object* v_currNamespace_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v_currNamespace_1556_);
lean_ctor_set(v___x_1559_, 1, v___y_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(v_currNamespace_1560_, v___y_1561_, v___y_1562_);
lean_dec_ref(v___y_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(lean_object* v_env_1564_, lean_object* v_opts_1565_, lean_object* v_currNamespace_1566_, lean_object* v_openDecls_1567_, lean_object* v_n_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = l_Lean_ResolveName_resolveGlobalName(v_env_1564_, v_opts_1565_, v_currNamespace_1566_, v_openDecls_1567_, v_n_1568_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v___y_1570_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed(lean_object* v_env_1573_, lean_object* v_opts_1574_, lean_object* v_currNamespace_1575_, lean_object* v_openDecls_1576_, lean_object* v_n_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(v_env_1573_, v_opts_1574_, v_currNamespace_1575_, v_openDecls_1576_, v_n_1577_, v___y_1578_, v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec_ref(v_opts_1574_);
return v_res_1580_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = lean_box(1);
v___x_1582_ = l_Lean_MessageData_ofFormat(v___x_1581_);
return v___x_1582_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__2));
v___x_1587_ = l_Lean_MessageData_ofFormat(v___x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(lean_object* v_x_1588_, lean_object* v_x_1589_){
_start:
{
if (lean_obj_tag(v_x_1589_) == 0)
{
return v_x_1588_;
}
else
{
lean_object* v_head_1590_; lean_object* v_tail_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1613_; 
v_head_1590_ = lean_ctor_get(v_x_1589_, 0);
v_tail_1591_ = lean_ctor_get(v_x_1589_, 1);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_x_1589_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1593_ = v_x_1589_;
v_isShared_1594_ = v_isSharedCheck_1613_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_tail_1591_);
lean_inc(v_head_1590_);
lean_dec(v_x_1589_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1613_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v_before_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1611_; 
v_before_1595_ = lean_ctor_get(v_head_1590_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_head_1590_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v_head_1590_, 1);
lean_dec(v_unused_1612_);
v___x_1597_ = v_head_1590_;
v_isShared_1598_ = v_isSharedCheck_1611_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_before_1595_);
lean_dec(v_head_1590_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1611_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1599_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0);
if (v_isShared_1598_ == 0)
{
lean_ctor_set_tag(v___x_1597_, 7);
lean_ctor_set(v___x_1597_, 1, v___x_1599_);
lean_ctor_set(v___x_1597_, 0, v_x_1588_);
v___x_1601_ = v___x_1597_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_x_1588_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1602_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3);
if (v_isShared_1594_ == 0)
{
lean_ctor_set_tag(v___x_1593_, 7);
lean_ctor_set(v___x_1593_, 1, v___x_1602_);
lean_ctor_set(v___x_1593_, 0, v___x_1601_);
v___x_1604_ = v___x_1593_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1605_ = l_Lean_MessageData_ofSyntax(v_before_1595_);
v___x_1606_ = l_Lean_indentD(v___x_1605_);
v___x_1607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1604_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v_x_1588_ = v___x_1607_;
v_x_1589_ = v_tail_1591_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(lean_object* v_opts_1614_, lean_object* v_opt_1615_){
_start:
{
lean_object* v_name_1616_; lean_object* v_defValue_1617_; lean_object* v_map_1618_; lean_object* v___x_1619_; 
v_name_1616_ = lean_ctor_get(v_opt_1615_, 0);
v_defValue_1617_ = lean_ctor_get(v_opt_1615_, 1);
v_map_1618_ = lean_ctor_get(v_opts_1614_, 0);
v___x_1619_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1618_, v_name_1616_);
if (lean_obj_tag(v___x_1619_) == 0)
{
uint8_t v___x_1620_; 
v___x_1620_ = lean_unbox(v_defValue_1617_);
return v___x_1620_;
}
else
{
lean_object* v_val_1621_; 
v_val_1621_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_val_1621_);
lean_dec_ref_known(v___x_1619_, 1);
if (lean_obj_tag(v_val_1621_) == 1)
{
uint8_t v_v_1622_; 
v_v_1622_ = lean_ctor_get_uint8(v_val_1621_, 0);
lean_dec_ref_known(v_val_1621_, 0);
return v_v_1622_;
}
else
{
uint8_t v___x_1623_; 
lean_dec(v_val_1621_);
v___x_1623_ = lean_unbox(v_defValue_1617_);
return v___x_1623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25___boxed(lean_object* v_opts_1624_, lean_object* v_opt_1625_){
_start:
{
uint8_t v_res_1626_; lean_object* v_r_1627_; 
v_res_1626_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(v_opts_1624_, v_opt_1625_);
lean_dec_ref(v_opt_1625_);
lean_dec_ref(v_opts_1624_);
v_r_1627_ = lean_box(v_res_1626_);
return v_r_1627_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__1));
v___x_1632_ = l_Lean_MessageData_ofFormat(v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(lean_object* v_msgData_1633_, lean_object* v_macroStack_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; lean_object* v_scopes_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v_opts_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1637_ = lean_st_ref_get(v___y_1635_);
v_scopes_1638_ = lean_ctor_get(v___x_1637_, 2);
lean_inc(v_scopes_1638_);
lean_dec(v___x_1637_);
v___x_1639_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1640_ = l_List_head_x21___redArg(v___x_1639_, v_scopes_1638_);
lean_dec(v_scopes_1638_);
v_opts_1641_ = lean_ctor_get(v___x_1640_, 1);
lean_inc_ref(v_opts_1641_);
lean_dec(v___x_1640_);
v___x_1642_ = l_Lean_Elab_pp_macroStack;
v___x_1643_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(v_opts_1641_, v___x_1642_);
lean_dec_ref(v_opts_1641_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; 
lean_dec(v_macroStack_1634_);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v_msgData_1633_);
return v___x_1644_;
}
else
{
if (lean_obj_tag(v_macroStack_1634_) == 0)
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1645_, 0, v_msgData_1633_);
return v___x_1645_;
}
else
{
lean_object* v_head_1646_; lean_object* v_after_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1662_; 
v_head_1646_ = lean_ctor_get(v_macroStack_1634_, 0);
lean_inc(v_head_1646_);
v_after_1647_ = lean_ctor_get(v_head_1646_, 1);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_head_1646_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; 
v_unused_1663_ = lean_ctor_get(v_head_1646_, 0);
lean_dec(v_unused_1663_);
v___x_1649_ = v_head_1646_;
v_isShared_1650_ = v_isSharedCheck_1662_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_after_1647_);
lean_dec(v_head_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1662_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0);
if (v_isShared_1650_ == 0)
{
lean_ctor_set_tag(v___x_1649_, 7);
lean_ctor_set(v___x_1649_, 1, v___x_1651_);
lean_ctor_set(v___x_1649_, 0, v_msgData_1633_);
v___x_1653_ = v___x_1649_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_msgData_1633_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v_msgData_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1654_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = l_Lean_MessageData_ofSyntax(v_after_1647_);
v___x_1657_ = l_Lean_indentD(v___x_1656_);
v_msgData_1658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1658_, 0, v___x_1655_);
lean_ctor_set(v_msgData_1658_, 1, v___x_1657_);
v___x_1659_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(v_msgData_1658_, v_macroStack_1634_);
v___x_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
return v___x_1660_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___boxed(lean_object* v_msgData_1664_, lean_object* v_macroStack_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_msgData_1664_, v_macroStack_1665_, v___y_1666_);
lean_dec(v___y_1666_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(lean_object* v_msg_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_Elab_Command_getRef___redArg(v___y_1670_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v_macroStack_1675_; lean_object* v___x_1676_; lean_object* v_a_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1688_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v_macroStack_1675_ = lean_ctor_get(v___y_1670_, 4);
v___x_1676_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msg_1669_, v___y_1671_);
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref(v___x_1676_);
v___x_1678_ = l_Lean_Elab_getBetterRef(v_a_1674_, v_macroStack_1675_);
lean_dec(v_a_1674_);
lean_inc(v_macroStack_1675_);
v___x_1679_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_a_1677_, v_macroStack_1675_, v___y_1671_);
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1678_);
lean_ctor_set(v___x_1684_, 1, v_a_1680_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set_tag(v___x_1682_, 1);
lean_ctor_set(v___x_1682_, 0, v___x_1684_);
v___x_1686_ = v___x_1682_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec_ref(v_msg_1669_);
v_a_1689_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1673_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1673_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg___boxed(lean_object* v_msg_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(lean_object* v_ref_1702_, lean_object* v_msg_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Elab_Command_getRef___redArg(v___y_1704_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v_fileName_1709_; lean_object* v_fileMap_1710_; lean_object* v_currRecDepth_1711_; lean_object* v_cmdPos_1712_; lean_object* v_macroStack_1713_; lean_object* v_quotContext_x3f_1714_; lean_object* v_currMacroScope_1715_; lean_object* v_snap_x3f_1716_; lean_object* v_cancelTk_x3f_1717_; uint8_t v_suppressElabErrors_1718_; lean_object* v_ref_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v_fileName_1709_ = lean_ctor_get(v___y_1704_, 0);
v_fileMap_1710_ = lean_ctor_get(v___y_1704_, 1);
v_currRecDepth_1711_ = lean_ctor_get(v___y_1704_, 2);
v_cmdPos_1712_ = lean_ctor_get(v___y_1704_, 3);
v_macroStack_1713_ = lean_ctor_get(v___y_1704_, 4);
v_quotContext_x3f_1714_ = lean_ctor_get(v___y_1704_, 5);
v_currMacroScope_1715_ = lean_ctor_get(v___y_1704_, 6);
v_snap_x3f_1716_ = lean_ctor_get(v___y_1704_, 8);
v_cancelTk_x3f_1717_ = lean_ctor_get(v___y_1704_, 9);
v_suppressElabErrors_1718_ = lean_ctor_get_uint8(v___y_1704_, sizeof(void*)*10);
v_ref_1719_ = l_Lean_replaceRef(v_ref_1702_, v_a_1708_);
lean_dec(v_a_1708_);
lean_inc(v_cancelTk_x3f_1717_);
lean_inc(v_snap_x3f_1716_);
lean_inc(v_currMacroScope_1715_);
lean_inc(v_quotContext_x3f_1714_);
lean_inc(v_macroStack_1713_);
lean_inc(v_cmdPos_1712_);
lean_inc(v_currRecDepth_1711_);
lean_inc_ref(v_fileMap_1710_);
lean_inc_ref(v_fileName_1709_);
v___x_1720_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1720_, 0, v_fileName_1709_);
lean_ctor_set(v___x_1720_, 1, v_fileMap_1710_);
lean_ctor_set(v___x_1720_, 2, v_currRecDepth_1711_);
lean_ctor_set(v___x_1720_, 3, v_cmdPos_1712_);
lean_ctor_set(v___x_1720_, 4, v_macroStack_1713_);
lean_ctor_set(v___x_1720_, 5, v_quotContext_x3f_1714_);
lean_ctor_set(v___x_1720_, 6, v_currMacroScope_1715_);
lean_ctor_set(v___x_1720_, 7, v_ref_1719_);
lean_ctor_set(v___x_1720_, 8, v_snap_x3f_1716_);
lean_ctor_set(v___x_1720_, 9, v_cancelTk_x3f_1717_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*10, v_suppressElabErrors_1718_);
v___x_1721_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_1703_, v___x_1720_, v___y_1705_);
lean_dec_ref_known(v___x_1720_, 10);
return v___x_1721_;
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec_ref(v_msg_1703_);
v_a_1722_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1707_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1707_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg___boxed(lean_object* v_ref_1730_, lean_object* v_msg_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_ref_1730_, v_msg_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v_ref_1730_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(lean_object* v_env_1736_, lean_object* v_declName_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
uint8_t v___x_1740_; lean_object* v_env_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; uint8_t v___x_1744_; 
v___x_1740_ = 0;
v_env_1741_ = l_Lean_Environment_setExporting(v_env_1736_, v___x_1740_);
lean_inc(v_declName_1737_);
v___x_1742_ = l_Lean_mkPrivateName(v_env_1741_, v_declName_1737_);
v___x_1743_ = 1;
lean_inc_ref(v_env_1741_);
v___x_1744_ = l_Lean_Environment_contains(v_env_1741_, v___x_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1745_ = l_Lean_privateToUserName(v_declName_1737_);
v___x_1746_ = l_Lean_Environment_contains(v_env_1741_, v___x_1745_, v___x_1743_);
v___x_1747_ = lean_box(v___x_1746_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v___y_1739_);
return v___x_1748_;
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec_ref(v_env_1741_);
lean_dec(v_declName_1737_);
v___x_1749_ = lean_box(v___x_1744_);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v___y_1739_);
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed(lean_object* v_env_1751_, lean_object* v_declName_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(v_env_1751_, v_declName_1752_, v___y_1753_, v___y_1754_);
lean_dec_ref(v___y_1753_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(lean_object* v_x_1756_, lean_object* v___y_1757_){
_start:
{
if (lean_obj_tag(v_x_1756_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; 
v_a_1758_ = lean_ctor_get(v_x_1756_, 0);
lean_inc(v_a_1758_);
v___x_1759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1759_, 0, v_a_1758_);
lean_ctor_set(v___x_1759_, 1, v___y_1757_);
return v___x_1759_;
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1761_; 
v_a_1760_ = lean_ctor_get(v_x_1756_, 0);
lean_inc(v_a_1760_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_a_1760_);
lean_ctor_set(v___x_1761_, 1, v___y_1757_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg___boxed(lean_object* v_x_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v_x_1762_, v___y_1763_);
lean_dec_ref(v_x_1762_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(lean_object* v_env_1765_, lean_object* v_stx_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1765_, v_stx_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
if (lean_obj_tag(v_a_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1779_; 
v_a_1771_ = lean_ctor_get(v___x_1769_, 1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v___x_1769_, 0);
lean_dec(v_unused_1780_);
v___x_1773_ = v___x_1769_;
v_isShared_1774_ = v_isSharedCheck_1779_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1769_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1779_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = lean_box(0);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1775_);
v___x_1777_ = v___x_1773_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_a_1771_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
else
{
lean_object* v_val_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1809_; 
v_val_1781_ = lean_ctor_get(v_a_1770_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_a_1770_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1783_ = v_a_1770_;
v_isShared_1784_ = v_isSharedCheck_1809_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_val_1781_);
lean_dec(v_a_1770_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1809_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v_snd_1785_; 
v_snd_1785_ = lean_ctor_get(v_val_1781_, 1);
lean_inc(v_snd_1785_);
lean_dec(v_val_1781_);
if (lean_obj_tag(v_snd_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1795_; 
lean_del_object(v___x_1783_);
v_a_1786_ = lean_ctor_get(v___x_1769_, 1);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1769_, 2);
v_a_1787_ = lean_ctor_get(v_snd_1785_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_snd_1785_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1789_ = v_snd_1785_;
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v_snd_1785_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v___x_1792_, v_a_1786_);
lean_dec_ref(v___x_1792_);
return v___x_1793_;
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1808_; 
v_a_1796_ = lean_ctor_get(v___x_1769_, 1);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1769_, 2);
v_a_1797_ = lean_ctor_get(v_snd_1785_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_snd_1785_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1799_ = v_snd_1785_;
v_isShared_1800_ = v_isSharedCheck_1808_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v_snd_1785_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1808_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v_a_1797_);
v___x_1802_ = v___x_1783_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1804_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1802_);
v___x_1804_ = v___x_1799_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v___x_1804_, v_a_1796_);
lean_dec_ref(v___x_1804_);
return v___x_1805_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
v_a_1810_ = lean_ctor_get(v___x_1769_, 0);
v_a_1811_ = lean_ctor_get(v___x_1769_, 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1769_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_inc(v_a_1810_);
lean_dec(v___x_1769_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1810_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed(lean_object* v_env_1819_, lean_object* v_stx_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(v_env_1819_, v_stx_1820_, v___y_1821_, v___y_1822_);
lean_dec_ref(v___y_1821_);
return v_res_1823_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = l_Lean_maxRecDepthErrorMessage;
v___x_1830_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
return v___x_1830_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3);
v___x_1832_ = l_Lean_MessageData_ofFormat(v___x_1831_);
return v___x_1832_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4);
v___x_1834_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2));
v___x_1835_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
lean_ctor_set(v___x_1835_, 1, v___x_1833_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(lean_object* v_ref_1836_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_ref_1836_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___boxed(lean_object* v_ref_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_1841_);
return v_res_1843_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(lean_object* v_keys_1844_, lean_object* v_i_1845_, lean_object* v_k_1846_){
_start:
{
lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1847_ = lean_array_get_size(v_keys_1844_);
v___x_1848_ = lean_nat_dec_lt(v_i_1845_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_dec(v_i_1845_);
return v___x_1848_;
}
else
{
lean_object* v_k_x27_1849_; uint8_t v___x_1850_; 
v_k_x27_1849_ = lean_array_fget_borrowed(v_keys_1844_, v_i_1845_);
v___x_1850_ = l_Lean_instBEqExtraModUse_beq(v_k_1846_, v_k_x27_1849_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_unsigned_to_nat(1u);
v___x_1852_ = lean_nat_add(v_i_1845_, v___x_1851_);
lean_dec(v_i_1845_);
v_i_1845_ = v___x_1852_;
goto _start;
}
else
{
lean_dec(v_i_1845_);
return v___x_1848_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg___boxed(lean_object* v_keys_1854_, lean_object* v_i_1855_, lean_object* v_k_1856_){
_start:
{
uint8_t v_res_1857_; lean_object* v_r_1858_; 
v_res_1857_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_1854_, v_i_1855_, v_k_1856_);
lean_dec_ref(v_k_1856_);
lean_dec_ref(v_keys_1854_);
v_r_1858_ = lean_box(v_res_1857_);
return v_r_1858_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(lean_object* v_x_1859_, size_t v_x_1860_, lean_object* v_x_1861_){
_start:
{
if (lean_obj_tag(v_x_1859_) == 0)
{
lean_object* v_es_1862_; lean_object* v___x_1863_; size_t v___x_1864_; size_t v___x_1865_; lean_object* v_j_1866_; lean_object* v___x_1867_; 
v_es_1862_ = lean_ctor_get(v_x_1859_, 0);
v___x_1863_ = lean_box(2);
v___x_1864_ = ((size_t)31ULL);
v___x_1865_ = lean_usize_land(v_x_1860_, v___x_1864_);
v_j_1866_ = lean_usize_to_nat(v___x_1865_);
v___x_1867_ = lean_array_get_borrowed(v___x_1863_, v_es_1862_, v_j_1866_);
lean_dec(v_j_1866_);
switch(lean_obj_tag(v___x_1867_))
{
case 0:
{
lean_object* v_key_1868_; uint8_t v___x_1869_; 
v_key_1868_ = lean_ctor_get(v___x_1867_, 0);
v___x_1869_ = l_Lean_instBEqExtraModUse_beq(v_x_1861_, v_key_1868_);
return v___x_1869_;
}
case 1:
{
lean_object* v_node_1870_; size_t v___x_1871_; size_t v___x_1872_; 
v_node_1870_ = lean_ctor_get(v___x_1867_, 0);
v___x_1871_ = ((size_t)5ULL);
v___x_1872_ = lean_usize_shift_right(v_x_1860_, v___x_1871_);
v_x_1859_ = v_node_1870_;
v_x_1860_ = v___x_1872_;
goto _start;
}
default: 
{
uint8_t v___x_1874_; 
v___x_1874_ = 0;
return v___x_1874_;
}
}
}
else
{
lean_object* v_ks_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v_ks_1875_ = lean_ctor_get(v_x_1859_, 0);
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_ks_1875_, v___x_1876_, v_x_1861_);
return v___x_1877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___boxed(lean_object* v_x_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_){
_start:
{
size_t v_x_20944__boxed_1881_; uint8_t v_res_1882_; lean_object* v_r_1883_; 
v_x_20944__boxed_1881_ = lean_unbox_usize(v_x_1879_);
lean_dec(v_x_1879_);
v_res_1882_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_1878_, v_x_20944__boxed_1881_, v_x_1880_);
lean_dec_ref(v_x_1880_);
lean_dec_ref(v_x_1878_);
v_r_1883_ = lean_box(v_res_1882_);
return v_r_1883_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(lean_object* v_x_1884_, lean_object* v_x_1885_){
_start:
{
uint64_t v___x_1886_; size_t v___x_1887_; uint8_t v___x_1888_; 
v___x_1886_ = l_Lean_instHashableExtraModUse_hash(v_x_1885_);
v___x_1887_ = lean_uint64_to_usize(v___x_1886_);
v___x_1888_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_1884_, v___x_1887_, v_x_1885_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg___boxed(lean_object* v_x_1889_, lean_object* v_x_1890_){
_start:
{
uint8_t v_res_1891_; lean_object* v_r_1892_; 
v_res_1891_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_1889_, v_x_1890_);
lean_dec_ref(v_x_1890_);
lean_dec_ref(v_x_1889_);
v_r_1892_ = lean_box(v_res_1891_);
return v_r_1892_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1));
v___x_1896_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0));
v___x_1897_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1896_, v___x_1895_);
return v___x_1897_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5));
v___x_1903_ = l_Lean_stringToMessageData(v___x_1902_);
return v___x_1903_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7));
v___x_1906_ = l_Lean_stringToMessageData(v___x_1905_);
return v___x_1906_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1908_ = l_Lean_stringToMessageData(v___x_1907_);
return v___x_1908_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10(void){
_start:
{
lean_object* v_cls_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v_cls_1909_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4));
v___x_1910_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
v___x_1911_ = l_Lean_Name_append(v___x_1910_, v_cls_1909_);
return v___x_1911_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11));
v___x_1914_ = l_Lean_stringToMessageData(v___x_1913_);
return v___x_1914_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13));
v___x_1917_ = l_Lean_stringToMessageData(v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(lean_object* v_mod_1922_, uint8_t v_isMeta_1923_, lean_object* v_hint_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v___x_1928_; lean_object* v_env_1929_; uint8_t v_isExporting_1930_; lean_object* v___x_1931_; lean_object* v_env_1932_; lean_object* v___x_1933_; lean_object* v_entry_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___y_1939_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1928_ = lean_st_ref_get(v___y_1926_);
v_env_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc_ref(v_env_1929_);
lean_dec(v___x_1928_);
v_isExporting_1930_ = lean_ctor_get_uint8(v_env_1929_, sizeof(void*)*8);
lean_dec_ref(v_env_1929_);
v___x_1931_ = lean_st_ref_get(v___y_1926_);
v_env_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc_ref(v_env_1932_);
lean_dec(v___x_1931_);
v___x_1933_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2);
lean_inc(v_mod_1922_);
v_entry_1934_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1934_, 0, v_mod_1922_);
lean_ctor_set_uint8(v_entry_1934_, sizeof(void*)*1, v_isExporting_1930_);
lean_ctor_set_uint8(v_entry_1934_, sizeof(void*)*1 + 1, v_isMeta_1923_);
v___x_1935_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1936_ = lean_box(1);
v___x_1937_ = lean_box(0);
v___x_1966_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1933_, v___x_1935_, v_env_1932_, v___x_1936_, v___x_1937_);
v___x_1967_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v___x_1966_, v_entry_1934_);
lean_dec(v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v_scopes_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_opts_1974_; uint8_t v_hasTrace_1975_; 
v___x_1968_ = l_Lean_inheritedTraceOptions;
v___x_1969_ = lean_st_ref_get(v___x_1968_);
v___x_1970_ = lean_st_ref_get(v___y_1926_);
v_scopes_1971_ = lean_ctor_get(v___x_1970_, 2);
lean_inc(v_scopes_1971_);
lean_dec(v___x_1970_);
v___x_1972_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1973_ = l_List_head_x21___redArg(v___x_1972_, v_scopes_1971_);
lean_dec(v_scopes_1971_);
v_opts_1974_ = lean_ctor_get(v___x_1973_, 1);
lean_inc_ref(v_opts_1974_);
lean_dec(v___x_1973_);
v_hasTrace_1975_ = lean_ctor_get_uint8(v_opts_1974_, sizeof(void*)*1);
if (v_hasTrace_1975_ == 0)
{
lean_dec_ref(v_opts_1974_);
lean_dec(v___x_1969_);
lean_dec(v_hint_1924_);
lean_dec(v_mod_1922_);
v___y_1939_ = v___y_1926_;
goto v___jp_1938_;
}
else
{
lean_object* v_cls_1976_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v_cls_1976_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4));
v___x_1996_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10);
v___x_1997_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1969_, v_opts_1974_, v___x_1996_);
lean_dec_ref(v_opts_1974_);
lean_dec(v___x_1969_);
if (v___x_1997_ == 0)
{
lean_dec(v_hint_1924_);
lean_dec(v_mod_1922_);
v___y_1939_ = v___y_1926_;
goto v___jp_1938_;
}
else
{
lean_object* v___x_1998_; lean_object* v___y_2000_; 
v___x_1998_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12);
if (v_isExporting_1930_ == 0)
{
lean_object* v___x_2007_; 
v___x_2007_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__17));
v___y_2000_ = v___x_2007_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2008_; 
v___x_2008_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__18));
v___y_2000_ = v___x_2008_;
goto v___jp_1999_;
}
v___jp_1999_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
lean_inc_ref(v___y_2000_);
v___x_2001_ = l_Lean_stringToMessageData(v___y_2000_);
v___x_2002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_1998_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14);
v___x_2004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2002_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
if (v_isMeta_1923_ == 0)
{
lean_object* v___x_2005_; 
v___x_2005_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15));
v___y_1983_ = v___x_2004_;
v___y_1984_ = v___x_2005_;
goto v___jp_1982_;
}
else
{
lean_object* v___x_2006_; 
v___x_2006_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16));
v___y_1983_ = v___x_2004_;
v___y_1984_ = v___x_2006_;
goto v___jp_1982_;
}
}
}
v___jp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___y_1978_);
lean_ctor_set(v___x_1980_, 1, v___y_1979_);
v___x_1981_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_1976_, v___x_1980_, v___y_1925_, v___y_1926_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_dec_ref_known(v___x_1981_, 1);
v___y_1939_ = v___y_1926_;
goto v___jp_1938_;
}
else
{
lean_dec_ref_known(v_entry_1934_, 1);
return v___x_1981_;
}
}
v___jp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
lean_inc_ref(v___y_1984_);
v___x_1985_ = l_Lean_stringToMessageData(v___y_1984_);
v___x_1986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___y_1983_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6);
v___x_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = l_Lean_MessageData_ofName(v_mod_1922_);
v___x_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1988_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = l_Lean_Name_isAnonymous(v_hint_1924_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1992_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8);
v___x_1993_ = l_Lean_MessageData_ofName(v_hint_1924_);
v___x_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___y_1978_ = v___x_1990_;
v___y_1979_ = v___x_1994_;
goto v___jp_1977_;
}
else
{
lean_object* v___x_1995_; 
lean_dec(v_hint_1924_);
v___x_1995_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9);
v___y_1978_ = v___x_1990_;
v___y_1979_ = v___x_1995_;
goto v___jp_1977_;
}
}
}
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec_ref_known(v_entry_1934_, 1);
lean_dec(v_hint_1924_);
lean_dec(v_mod_1922_);
v___x_2009_ = lean_box(0);
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
return v___x_2010_;
}
v___jp_1938_:
{
lean_object* v___x_1940_; lean_object* v_toEnvExtension_1941_; lean_object* v_env_1942_; lean_object* v_messages_1943_; lean_object* v_scopes_1944_; lean_object* v_usedQuotCtxts_1945_; lean_object* v_nextMacroScope_1946_; lean_object* v_maxRecDepth_1947_; lean_object* v_ngen_1948_; lean_object* v_auxDeclNGen_1949_; lean_object* v_infoState_1950_; lean_object* v_traceState_1951_; lean_object* v_snapshotTasks_1952_; lean_object* v_prevLinterStates_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1965_; 
v___x_1940_ = lean_st_ref_take(v___y_1939_);
v_toEnvExtension_1941_ = lean_ctor_get(v___x_1935_, 0);
v_env_1942_ = lean_ctor_get(v___x_1940_, 0);
v_messages_1943_ = lean_ctor_get(v___x_1940_, 1);
v_scopes_1944_ = lean_ctor_get(v___x_1940_, 2);
v_usedQuotCtxts_1945_ = lean_ctor_get(v___x_1940_, 3);
v_nextMacroScope_1946_ = lean_ctor_get(v___x_1940_, 4);
v_maxRecDepth_1947_ = lean_ctor_get(v___x_1940_, 5);
v_ngen_1948_ = lean_ctor_get(v___x_1940_, 6);
v_auxDeclNGen_1949_ = lean_ctor_get(v___x_1940_, 7);
v_infoState_1950_ = lean_ctor_get(v___x_1940_, 8);
v_traceState_1951_ = lean_ctor_get(v___x_1940_, 9);
v_snapshotTasks_1952_ = lean_ctor_get(v___x_1940_, 10);
v_prevLinterStates_1953_ = lean_ctor_get(v___x_1940_, 11);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1955_ = v___x_1940_;
v_isShared_1956_ = v_isSharedCheck_1965_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_prevLinterStates_1953_);
lean_inc(v_snapshotTasks_1952_);
lean_inc(v_traceState_1951_);
lean_inc(v_infoState_1950_);
lean_inc(v_auxDeclNGen_1949_);
lean_inc(v_ngen_1948_);
lean_inc(v_maxRecDepth_1947_);
lean_inc(v_nextMacroScope_1946_);
lean_inc(v_usedQuotCtxts_1945_);
lean_inc(v_scopes_1944_);
lean_inc(v_messages_1943_);
lean_inc(v_env_1942_);
lean_dec(v___x_1940_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1965_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v_asyncMode_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
v_asyncMode_1957_ = lean_ctor_get(v_toEnvExtension_1941_, 2);
v___x_1958_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1935_, v_env_1942_, v_entry_1934_, v_asyncMode_1957_, v___x_1937_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 0, v___x_1958_);
v___x_1960_ = v___x_1955_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_messages_1943_);
lean_ctor_set(v_reuseFailAlloc_1964_, 2, v_scopes_1944_);
lean_ctor_set(v_reuseFailAlloc_1964_, 3, v_usedQuotCtxts_1945_);
lean_ctor_set(v_reuseFailAlloc_1964_, 4, v_nextMacroScope_1946_);
lean_ctor_set(v_reuseFailAlloc_1964_, 5, v_maxRecDepth_1947_);
lean_ctor_set(v_reuseFailAlloc_1964_, 6, v_ngen_1948_);
lean_ctor_set(v_reuseFailAlloc_1964_, 7, v_auxDeclNGen_1949_);
lean_ctor_set(v_reuseFailAlloc_1964_, 8, v_infoState_1950_);
lean_ctor_set(v_reuseFailAlloc_1964_, 9, v_traceState_1951_);
lean_ctor_set(v_reuseFailAlloc_1964_, 10, v_snapshotTasks_1952_);
lean_ctor_set(v_reuseFailAlloc_1964_, 11, v_prevLinterStates_1953_);
v___x_1960_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1961_ = lean_st_ref_put(v___y_1939_, v___x_1960_);
v___x_1962_ = lean_box(0);
v___x_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
return v___x_1963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___boxed(lean_object* v_mod_2011_, lean_object* v_isMeta_2012_, lean_object* v_hint_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
uint8_t v_isMeta_boxed_2017_; lean_object* v_res_2018_; 
v_isMeta_boxed_2017_ = lean_unbox(v_isMeta_2012_);
v_res_2018_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_mod_2011_, v_isMeta_boxed_2017_, v_hint_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(lean_object* v___x_2019_, lean_object* v_declName_2020_, lean_object* v_as_2021_, size_t v_sz_2022_, size_t v_i_2023_, lean_object* v_b_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_usize_dec_lt(v_i_2023_, v_sz_2022_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; 
lean_dec(v_declName_2020_);
v___x_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2029_, 0, v_b_2024_);
return v___x_2029_;
}
else
{
lean_object* v___x_2030_; lean_object* v_modules_2031_; lean_object* v___x_2032_; lean_object* v_a_2033_; lean_object* v___x_2034_; lean_object* v_toImport_2035_; lean_object* v_module_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; 
v___x_2030_ = l_Lean_Environment_header(v___x_2019_);
v_modules_2031_ = lean_ctor_get(v___x_2030_, 3);
lean_inc_ref(v_modules_2031_);
lean_dec_ref(v___x_2030_);
v___x_2032_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2033_ = lean_array_uget_borrowed(v_as_2021_, v_i_2023_);
v___x_2034_ = lean_array_get(v___x_2032_, v_modules_2031_, v_a_2033_);
lean_dec_ref(v_modules_2031_);
v_toImport_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc_ref(v_toImport_2035_);
lean_dec(v___x_2034_);
v_module_2036_ = lean_ctor_get(v_toImport_2035_, 0);
lean_inc(v_module_2036_);
lean_dec_ref(v_toImport_2035_);
v___x_2037_ = 0;
lean_inc(v_declName_2020_);
v___x_2038_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_module_2036_, v___x_2037_, v_declName_2020_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v___x_2039_; size_t v___x_2040_; size_t v___x_2041_; 
lean_dec_ref_known(v___x_2038_, 1);
v___x_2039_ = lean_box(0);
v___x_2040_ = ((size_t)1ULL);
v___x_2041_ = lean_usize_add(v_i_2023_, v___x_2040_);
v_i_2023_ = v___x_2041_;
v_b_2024_ = v___x_2039_;
goto _start;
}
else
{
lean_dec(v_declName_2020_);
return v___x_2038_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7___boxed(lean_object* v___x_2043_, lean_object* v_declName_2044_, lean_object* v_as_2045_, lean_object* v_sz_2046_, lean_object* v_i_2047_, lean_object* v_b_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
size_t v_sz_boxed_2052_; size_t v_i_boxed_2053_; lean_object* v_res_2054_; 
v_sz_boxed_2052_ = lean_unbox_usize(v_sz_2046_);
lean_dec(v_sz_2046_);
v_i_boxed_2053_ = lean_unbox_usize(v_i_2047_);
lean_dec(v_i_2047_);
v_res_2054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v___x_2043_, v_declName_2044_, v_as_2045_, v_sz_boxed_2052_, v_i_boxed_2053_, v_b_2048_, v___y_2049_, v___y_2050_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_as_2045_);
lean_dec_ref(v___x_2043_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(lean_object* v_a_2055_, lean_object* v_x_2056_){
_start:
{
if (lean_obj_tag(v_x_2056_) == 0)
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_box(0);
return v___x_2057_;
}
else
{
lean_object* v_key_2058_; lean_object* v_value_2059_; lean_object* v_tail_2060_; uint8_t v___x_2061_; 
v_key_2058_ = lean_ctor_get(v_x_2056_, 0);
v_value_2059_ = lean_ctor_get(v_x_2056_, 1);
v_tail_2060_ = lean_ctor_get(v_x_2056_, 2);
v___x_2061_ = lean_name_eq(v_key_2058_, v_a_2055_);
if (v___x_2061_ == 0)
{
v_x_2056_ = v_tail_2060_;
goto _start;
}
else
{
lean_object* v___x_2063_; 
lean_inc(v_value_2059_);
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_value_2059_);
return v___x_2063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg___boxed(lean_object* v_a_2064_, lean_object* v_x_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_2064_, v_x_2065_);
lean_dec(v_x_2065_);
lean_dec(v_a_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(lean_object* v_m_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_buckets_2069_; lean_object* v___x_2070_; uint64_t v___y_2072_; 
v_buckets_2069_ = lean_ctor_get(v_m_2067_, 1);
v___x_2070_ = lean_array_get_size(v_buckets_2069_);
if (lean_obj_tag(v_a_2068_) == 0)
{
uint64_t v___x_2086_; 
v___x_2086_ = 1723ULL;
v___y_2072_ = v___x_2086_;
goto v___jp_2071_;
}
else
{
uint64_t v_hash_2087_; 
v_hash_2087_ = lean_ctor_get_uint64(v_a_2068_, sizeof(void*)*2);
v___y_2072_ = v_hash_2087_;
goto v___jp_2071_;
}
v___jp_2071_:
{
uint64_t v___x_2073_; uint64_t v___x_2074_; uint64_t v_fold_2075_; uint64_t v___x_2076_; uint64_t v___x_2077_; uint64_t v___x_2078_; size_t v___x_2079_; size_t v___x_2080_; size_t v___x_2081_; size_t v___x_2082_; size_t v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2073_ = 32ULL;
v___x_2074_ = lean_uint64_shift_right(v___y_2072_, v___x_2073_);
v_fold_2075_ = lean_uint64_xor(v___y_2072_, v___x_2074_);
v___x_2076_ = 16ULL;
v___x_2077_ = lean_uint64_shift_right(v_fold_2075_, v___x_2076_);
v___x_2078_ = lean_uint64_xor(v_fold_2075_, v___x_2077_);
v___x_2079_ = lean_uint64_to_usize(v___x_2078_);
v___x_2080_ = lean_usize_of_nat(v___x_2070_);
v___x_2081_ = ((size_t)1ULL);
v___x_2082_ = lean_usize_sub(v___x_2080_, v___x_2081_);
v___x_2083_ = lean_usize_land(v___x_2079_, v___x_2082_);
v___x_2084_ = lean_array_uget_borrowed(v_buckets_2069_, v___x_2083_);
v___x_2085_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_2068_, v___x_2084_);
return v___x_2085_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_m_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v_m_2088_, v_a_2089_);
lean_dec(v_a_2089_);
lean_dec_ref(v_m_2088_);
return v_res_2090_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2093_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1));
v___x_2094_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0));
v___x_2095_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2094_, v___x_2093_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(lean_object* v_declName_2098_, uint8_t v_isMeta_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v___x_2103_; lean_object* v_env_2107_; lean_object* v___y_2109_; lean_object* v___x_2122_; 
v___x_2103_ = lean_st_ref_get(v___y_2101_);
v_env_2107_ = lean_ctor_get(v___x_2103_, 0);
lean_inc_ref(v_env_2107_);
lean_dec(v___x_2103_);
v___x_2122_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2107_, v_declName_2098_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_dec_ref(v_env_2107_);
lean_dec(v_declName_2098_);
goto v___jp_2104_;
}
else
{
lean_object* v_val_2123_; lean_object* v___x_2124_; lean_object* v_modules_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v_val_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_val_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2124_ = l_Lean_Environment_header(v_env_2107_);
v_modules_2125_ = lean_ctor_get(v___x_2124_, 3);
lean_inc_ref(v_modules_2125_);
lean_dec_ref(v___x_2124_);
v___x_2126_ = lean_array_get_size(v_modules_2125_);
v___x_2127_ = lean_nat_dec_lt(v_val_2123_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_dec_ref(v_modules_2125_);
lean_dec(v_val_2123_);
lean_dec_ref(v_env_2107_);
lean_dec(v_declName_2098_);
goto v___jp_2104_;
}
else
{
lean_object* v___x_2128_; lean_object* v_env_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___y_2133_; 
v___x_2128_ = lean_st_ref_get(v___y_2101_);
v_env_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc_ref(v_env_2129_);
lean_dec(v___x_2128_);
v___x_2130_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2);
v___x_2131_ = lean_array_fget(v_modules_2125_, v_val_2123_);
lean_dec(v_val_2123_);
lean_dec_ref(v_modules_2125_);
if (v_isMeta_2099_ == 0)
{
lean_dec_ref(v_env_2129_);
v___y_2133_ = v_isMeta_2099_;
goto v___jp_2132_;
}
else
{
uint8_t v___x_2144_; 
lean_inc(v_declName_2098_);
v___x_2144_ = l_Lean_isMarkedMeta(v_env_2129_, v_declName_2098_);
if (v___x_2144_ == 0)
{
v___y_2133_ = v_isMeta_2099_;
goto v___jp_2132_;
}
else
{
uint8_t v___x_2145_; 
v___x_2145_ = 0;
v___y_2133_ = v___x_2145_;
goto v___jp_2132_;
}
}
v___jp_2132_:
{
lean_object* v_toImport_2134_; lean_object* v_module_2135_; lean_object* v___x_2136_; 
v_toImport_2134_ = lean_ctor_get(v___x_2131_, 0);
lean_inc_ref(v_toImport_2134_);
lean_dec(v___x_2131_);
v_module_2135_ = lean_ctor_get(v_toImport_2134_, 0);
lean_inc(v_module_2135_);
lean_dec_ref(v_toImport_2134_);
lean_inc(v_declName_2098_);
v___x_2136_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_module_2135_, v___y_2133_, v_declName_2098_, v___y_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_dec_ref_known(v___x_2136_, 1);
v___x_2137_ = l_Lean_indirectModUseExt;
v___x_2138_ = lean_box(1);
v___x_2139_ = lean_box(0);
lean_inc_ref(v_env_2107_);
v___x_2140_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2130_, v___x_2137_, v_env_2107_, v___x_2138_, v___x_2139_);
v___x_2141_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v___x_2140_, v_declName_2098_);
lean_dec(v___x_2140_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v___x_2142_; 
v___x_2142_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__3));
v___y_2109_ = v___x_2142_;
goto v___jp_2108_;
}
else
{
lean_object* v_val_2143_; 
v_val_2143_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_val_2143_);
lean_dec_ref_known(v___x_2141_, 1);
v___y_2109_ = v_val_2143_;
goto v___jp_2108_;
}
}
else
{
lean_dec_ref(v_env_2107_);
lean_dec(v_declName_2098_);
return v___x_2136_;
}
}
}
}
v___jp_2104_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
return v___x_2106_;
}
v___jp_2108_:
{
lean_object* v___x_2110_; size_t v_sz_2111_; size_t v___x_2112_; lean_object* v___x_2113_; 
v___x_2110_ = lean_box(0);
v_sz_2111_ = lean_array_size(v___y_2109_);
v___x_2112_ = ((size_t)0ULL);
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v_env_2107_, v_declName_2098_, v___y_2109_, v_sz_2111_, v___x_2112_, v___x_2110_, v___y_2100_, v___y_2101_);
lean_dec_ref(v___y_2109_);
lean_dec_ref(v_env_2107_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; 
v_unused_2121_ = lean_ctor_get(v___x_2113_, 0);
lean_dec(v_unused_2121_);
v___x_2115_ = v___x_2113_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_dec(v___x_2113_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2110_);
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2110_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
else
{
return v___x_2113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___boxed(lean_object* v_declName_2146_, lean_object* v_isMeta_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
uint8_t v_isMeta_boxed_2151_; lean_object* v_res_2152_; 
v_isMeta_boxed_2151_ = lean_unbox(v_isMeta_2147_);
v_res_2152_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_declName_2146_, v_isMeta_boxed_2151_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(lean_object* v_as_x27_2153_, lean_object* v_b_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
if (lean_obj_tag(v_as_x27_2153_) == 0)
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_b_2154_);
return v___x_2158_;
}
else
{
lean_object* v_head_2159_; lean_object* v_tail_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; 
v_head_2159_ = lean_ctor_get(v_as_x27_2153_, 0);
v_tail_2160_ = lean_ctor_get(v_as_x27_2153_, 1);
v___x_2161_ = 1;
lean_inc(v_head_2159_);
v___x_2162_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_head_2159_, v___x_2161_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v___x_2163_; 
lean_dec_ref_known(v___x_2162_, 1);
v___x_2163_ = lean_box(0);
v_as_x27_2153_ = v_tail_2160_;
v_b_2154_ = v___x_2163_;
goto _start;
}
else
{
return v___x_2162_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2165_, lean_object* v_b_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_2165_, v_b_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v_as_x27_2165_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(lean_object* v_x_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; lean_object* v_env_2177_; lean_object* v___x_2178_; lean_object* v_scopes_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v_opts_2182_; lean_object* v___x_2183_; 
v___x_2176_ = lean_st_ref_get(v___y_2174_);
v_env_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc_ref(v_env_2177_);
lean_dec(v___x_2176_);
v___x_2178_ = lean_st_ref_get(v___y_2174_);
v_scopes_2179_ = lean_ctor_get(v___x_2178_, 2);
lean_inc(v_scopes_2179_);
lean_dec(v___x_2178_);
v___x_2180_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2181_ = l_List_head_x21___redArg(v___x_2180_, v_scopes_2179_);
lean_dec(v_scopes_2179_);
v_opts_2182_ = lean_ctor_get(v___x_2181_, 1);
lean_inc_ref(v_opts_2182_);
lean_dec(v___x_2181_);
v___x_2183_ = l_Lean_Elab_Command_getScope___redArg(v___y_2174_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v_currNamespace_2185_; lean_object* v___x_2186_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
v_currNamespace_2185_ = lean_ctor_get(v_a_2184_, 2);
lean_inc(v_currNamespace_2185_);
lean_dec(v_a_2184_);
v___x_2186_ = l_Lean_Elab_Command_getScope___redArg(v___y_2174_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v_openDecls_2188_; lean_object* v___x_2189_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
v_openDecls_2188_ = lean_ctor_get(v_a_2187_, 3);
lean_inc(v_openDecls_2188_);
lean_dec(v_a_2187_);
v___x_2189_ = l_Lean_Elab_Command_getRef___redArg(v___y_2173_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2191_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v___x_2191_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2173_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v_currRecDepth_2193_; lean_object* v_quotContext_x3f_2194_; lean_object* v___f_2195_; lean_object* v___f_2196_; lean_object* v___f_2197_; lean_object* v___f_2198_; lean_object* v___f_2199_; lean_object* v_methods_2200_; lean_object* v_a_2202_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
lean_dec_ref_known(v___x_2191_, 1);
v_currRecDepth_2193_ = lean_ctor_get(v___y_2173_, 2);
v_quotContext_x3f_2194_ = lean_ctor_get(v___y_2173_, 5);
lean_inc_ref_n(v_env_2177_, 3);
v___f_2195_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2195_, 0, v_env_2177_);
v___f_2196_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2196_, 0, v_env_2177_);
lean_inc_n(v_currNamespace_2185_, 2);
v___f_2197_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2197_, 0, v_currNamespace_2185_);
lean_inc(v_openDecls_2188_);
v___f_2198_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2198_, 0, v_env_2177_);
lean_closure_set(v___f_2198_, 1, v_currNamespace_2185_);
lean_closure_set(v___f_2198_, 2, v_openDecls_2188_);
v___f_2199_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2199_, 0, v_env_2177_);
lean_closure_set(v___f_2199_, 1, v_opts_2182_);
lean_closure_set(v___f_2199_, 2, v_currNamespace_2185_);
lean_closure_set(v___f_2199_, 3, v_openDecls_2188_);
v_methods_2200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2200_, 0, v___f_2196_);
lean_ctor_set(v_methods_2200_, 1, v___f_2197_);
lean_ctor_set(v_methods_2200_, 2, v___f_2195_);
lean_ctor_set(v_methods_2200_, 3, v___f_2198_);
lean_ctor_set(v_methods_2200_, 4, v___f_2199_);
if (lean_obj_tag(v_quotContext_x3f_2194_) == 0)
{
lean_object* v___x_2275_; lean_object* v_a_2276_; 
v___x_2275_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2174_);
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref(v___x_2275_);
v_a_2202_ = v_a_2276_;
goto v___jp_2201_;
}
else
{
lean_object* v_val_2277_; 
v_val_2277_ = lean_ctor_get(v_quotContext_x3f_2194_, 0);
lean_inc(v_val_2277_);
v_a_2202_ = v_val_2277_;
goto v___jp_2201_;
}
v___jp_2201_:
{
lean_object* v___x_2203_; lean_object* v_maxRecDepth_2204_; lean_object* v___x_2205_; lean_object* v_nextMacroScope_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2203_ = lean_st_ref_get(v___y_2174_);
v_maxRecDepth_2204_ = lean_ctor_get(v___x_2203_, 5);
lean_inc(v_maxRecDepth_2204_);
lean_dec(v___x_2203_);
v___x_2205_ = lean_st_ref_get(v___y_2174_);
v_nextMacroScope_2206_ = lean_ctor_get(v___x_2205_, 4);
lean_inc(v_nextMacroScope_2206_);
lean_dec(v___x_2205_);
lean_inc(v_currRecDepth_2193_);
v___x_2207_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2207_, 0, v_methods_2200_);
lean_ctor_set(v___x_2207_, 1, v_a_2202_);
lean_ctor_set(v___x_2207_, 2, v_a_2192_);
lean_ctor_set(v___x_2207_, 3, v_currRecDepth_2193_);
lean_ctor_set(v___x_2207_, 4, v_maxRecDepth_2204_);
lean_ctor_set(v___x_2207_, 5, v_a_2190_);
v___x_2208_ = lean_box(0);
v___x_2209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2209_, 0, v_nextMacroScope_2206_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
lean_ctor_set(v___x_2209_, 2, v___x_2208_);
v___x_2210_ = lean_apply_2(v_x_2172_, v___x_2207_, v___x_2209_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v_a_2212_; lean_object* v_macroScope_2213_; lean_object* v_traceMsgs_2214_; lean_object* v_expandedMacroDecls_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 1);
lean_inc(v_a_2211_);
v_a_2212_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2212_);
lean_dec_ref_known(v___x_2210_, 2);
v_macroScope_2213_ = lean_ctor_get(v_a_2211_, 0);
lean_inc(v_macroScope_2213_);
v_traceMsgs_2214_ = lean_ctor_get(v_a_2211_, 1);
lean_inc(v_traceMsgs_2214_);
v_expandedMacroDecls_2215_ = lean_ctor_get(v_a_2211_, 2);
lean_inc(v_expandedMacroDecls_2215_);
lean_dec(v_a_2211_);
v___x_2216_ = lean_box(0);
v___x_2217_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_expandedMacroDecls_2215_, v___x_2216_, v___y_2173_, v___y_2174_);
lean_dec(v_expandedMacroDecls_2215_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v___x_2218_; lean_object* v_env_2219_; lean_object* v_messages_2220_; lean_object* v_scopes_2221_; lean_object* v_usedQuotCtxts_2222_; lean_object* v_maxRecDepth_2223_; lean_object* v_ngen_2224_; lean_object* v_auxDeclNGen_2225_; lean_object* v_infoState_2226_; lean_object* v_traceState_2227_; lean_object* v_snapshotTasks_2228_; lean_object* v_prevLinterStates_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2255_; 
lean_dec_ref_known(v___x_2217_, 1);
v___x_2218_ = lean_st_ref_take(v___y_2174_);
v_env_2219_ = lean_ctor_get(v___x_2218_, 0);
v_messages_2220_ = lean_ctor_get(v___x_2218_, 1);
v_scopes_2221_ = lean_ctor_get(v___x_2218_, 2);
v_usedQuotCtxts_2222_ = lean_ctor_get(v___x_2218_, 3);
v_maxRecDepth_2223_ = lean_ctor_get(v___x_2218_, 5);
v_ngen_2224_ = lean_ctor_get(v___x_2218_, 6);
v_auxDeclNGen_2225_ = lean_ctor_get(v___x_2218_, 7);
v_infoState_2226_ = lean_ctor_get(v___x_2218_, 8);
v_traceState_2227_ = lean_ctor_get(v___x_2218_, 9);
v_snapshotTasks_2228_ = lean_ctor_get(v___x_2218_, 10);
v_prevLinterStates_2229_ = lean_ctor_get(v___x_2218_, 11);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; 
v_unused_2256_ = lean_ctor_get(v___x_2218_, 4);
lean_dec(v_unused_2256_);
v___x_2231_ = v___x_2218_;
v_isShared_2232_ = v_isSharedCheck_2255_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_prevLinterStates_2229_);
lean_inc(v_snapshotTasks_2228_);
lean_inc(v_traceState_2227_);
lean_inc(v_infoState_2226_);
lean_inc(v_auxDeclNGen_2225_);
lean_inc(v_ngen_2224_);
lean_inc(v_maxRecDepth_2223_);
lean_inc(v_usedQuotCtxts_2222_);
lean_inc(v_scopes_2221_);
lean_inc(v_messages_2220_);
lean_inc(v_env_2219_);
lean_dec(v___x_2218_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2255_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 4, v_macroScope_2213_);
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_env_2219_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_messages_2220_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_scopes_2221_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v_usedQuotCtxts_2222_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v_macroScope_2213_);
lean_ctor_set(v_reuseFailAlloc_2254_, 5, v_maxRecDepth_2223_);
lean_ctor_set(v_reuseFailAlloc_2254_, 6, v_ngen_2224_);
lean_ctor_set(v_reuseFailAlloc_2254_, 7, v_auxDeclNGen_2225_);
lean_ctor_set(v_reuseFailAlloc_2254_, 8, v_infoState_2226_);
lean_ctor_set(v_reuseFailAlloc_2254_, 9, v_traceState_2227_);
lean_ctor_set(v_reuseFailAlloc_2254_, 10, v_snapshotTasks_2228_);
lean_ctor_set(v_reuseFailAlloc_2254_, 11, v_prevLinterStates_2229_);
v___x_2234_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = lean_st_ref_put(v___y_2174_, v___x_2234_);
v___x_2236_ = l_List_reverse___redArg(v_traceMsgs_2214_);
v___x_2237_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v___x_2236_, v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2244_ == 0)
{
lean_object* v_unused_2245_; 
v_unused_2245_ = lean_ctor_get(v___x_2237_, 0);
lean_dec(v_unused_2245_);
v___x_2239_ = v___x_2237_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_dec(v___x_2237_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v_a_2212_);
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2212_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec(v_a_2212_);
v_a_2246_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2237_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2237_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_traceMsgs_2214_);
lean_dec(v_macroScope_2213_);
lean_dec(v_a_2212_);
v_a_2257_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2217_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2217_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
else
{
lean_object* v_a_2265_; 
v_a_2265_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2210_, 2);
if (lean_obj_tag(v_a_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v_a_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v_a_2266_ = lean_ctor_get(v_a_2265_, 0);
lean_inc(v_a_2266_);
v_a_2267_ = lean_ctor_get(v_a_2265_, 1);
lean_inc_ref(v_a_2267_);
lean_dec_ref_known(v_a_2265_, 2);
v___x_2268_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0));
v___x_2269_ = lean_string_dec_eq(v_a_2267_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2270_, 0, v_a_2267_);
v___x_2271_ = l_Lean_MessageData_ofFormat(v___x_2270_);
v___x_2272_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_a_2266_, v___x_2271_, v___y_2173_, v___y_2174_);
lean_dec(v_a_2266_);
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; 
lean_dec_ref(v_a_2267_);
v___x_2273_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_a_2266_);
return v___x_2273_;
}
}
else
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2274_;
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_a_2190_);
lean_dec(v_openDecls_2188_);
lean_dec(v_currNamespace_2185_);
lean_dec_ref(v_opts_2182_);
lean_dec_ref(v_env_2177_);
lean_dec_ref(v_x_2172_);
v_a_2278_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2191_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2191_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_openDecls_2188_);
lean_dec(v_currNamespace_2185_);
lean_dec_ref(v_opts_2182_);
lean_dec_ref(v_env_2177_);
lean_dec_ref(v_x_2172_);
v_a_2286_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2189_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2189_);
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
lean_dec(v_currNamespace_2185_);
lean_dec_ref(v_opts_2182_);
lean_dec_ref(v_env_2177_);
lean_dec_ref(v_x_2172_);
v_a_2294_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2186_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2186_);
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
lean_dec_ref(v_opts_2182_);
lean_dec_ref(v_env_2177_);
lean_dec_ref(v_x_2172_);
v_a_2302_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2183_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2183_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___boxed(lean_object* v_x_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(lean_object* v_as_2315_, size_t v_i_2316_, size_t v_stop_2317_, lean_object* v_b_2318_){
_start:
{
lean_object* v___y_2320_; uint8_t v___x_2324_; 
v___x_2324_ = lean_usize_dec_eq(v_i_2316_, v_stop_2317_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2325_ = lean_array_uget_borrowed(v_as_2315_, v_i_2316_);
lean_inc(v___x_2325_);
v___x_2326_ = l_Lean_Syntax_getKind(v___x_2325_);
v___x_2327_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
v___x_2328_ = lean_name_eq(v___x_2326_, v___x_2327_);
lean_dec(v___x_2326_);
if (v___x_2328_ == 0)
{
v___y_2320_ = v_b_2318_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2329_; 
lean_inc(v___x_2325_);
v___x_2329_ = lean_array_push(v_b_2318_, v___x_2325_);
v___y_2320_ = v___x_2329_;
goto v___jp_2319_;
}
}
else
{
return v_b_2318_;
}
v___jp_2319_:
{
size_t v___x_2321_; size_t v___x_2322_; 
v___x_2321_ = ((size_t)1ULL);
v___x_2322_ = lean_usize_add(v_i_2316_, v___x_2321_);
v_i_2316_ = v___x_2322_;
v_b_2318_ = v___y_2320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8___boxed(lean_object* v_as_2330_, lean_object* v_i_2331_, lean_object* v_stop_2332_, lean_object* v_b_2333_){
_start:
{
size_t v_i_boxed_2334_; size_t v_stop_boxed_2335_; lean_object* v_res_2336_; 
v_i_boxed_2334_ = lean_unbox_usize(v_i_2331_);
lean_dec(v_i_2331_);
v_stop_boxed_2335_ = lean_unbox_usize(v_stop_2332_);
lean_dec(v_stop_2332_);
v_res_2336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v_as_2330_, v_i_boxed_2334_, v_stop_boxed_2335_, v_b_2333_);
lean_dec_ref(v_as_2330_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation(lean_object* v_x_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; size_t v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; uint8_t v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; 
v___x_2410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0));
v___x_2411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1));
v___x_2412_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
lean_inc(v_x_2379_);
v___x_2413_ = l_Lean_Syntax_isOfKind(v_x_2379_, v___x_2412_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2522_; 
lean_dec(v_x_2379_);
v___x_2522_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2522_;
}
else
{
lean_object* v___x_2523_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; size_t v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; uint8_t v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; size_t v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; uint8_t v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; size_t v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; uint8_t v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; size_t v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; uint8_t v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; size_t v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; uint8_t v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v_prio_x3f_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v_name_x3f_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v_prec_x3f_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v_attrs_x3f_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v_doc_x3f_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___x_2878_; uint8_t v___x_2879_; 
v___x_2523_ = lean_unsigned_to_nat(0u);
v___x_2878_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2523_);
v___x_2879_ = l_Lean_Syntax_isNone(v___x_2878_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2880_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2878_);
v___x_2881_ = l_Lean_Syntax_matchesNull(v___x_2878_, v___x_2880_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; 
lean_dec(v___x_2878_);
lean_dec(v_x_2379_);
v___x_2882_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2882_;
}
else
{
lean_object* v_doc_x3f_2883_; 
v_doc_x3f_2883_ = l_Lean_Syntax_getArg(v___x_2878_, v___x_2523_);
lean_dec(v___x_2878_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__15));
lean_inc(v_doc_x3f_2883_);
v___x_2887_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2883_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; 
lean_dec(v_doc_x3f_2883_);
lean_dec(v_x_2379_);
v___x_2888_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2888_;
}
else
{
goto v___jp_2884_;
}
}
else
{
goto v___jp_2884_;
}
v___jp_2884_:
{
lean_object* v___x_2885_; 
v___x_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2885_, 0, v_doc_x3f_2883_);
v_doc_x3f_2862_ = v___x_2885_;
v___y_2863_ = v_a_2380_;
v___y_2864_ = v_a_2381_;
goto v___jp_2861_;
}
}
}
else
{
lean_object* v___x_2889_; 
lean_dec(v___x_2878_);
v___x_2889_ = lean_box(0);
v_doc_x3f_2862_ = v___x_2889_;
v___y_2863_ = v_a_2380_;
v___y_2864_ = v_a_2381_;
goto v___jp_2861_;
}
v___jp_2524_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; size_t v_sz_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_inc_ref_n(v___y_2528_, 2);
v___x_2545_ = l_Array_append___redArg(v___y_2528_, v___y_2544_);
lean_dec_ref(v___y_2544_);
lean_inc_n(v___y_2526_, 3);
lean_inc_n(v___y_2531_, 9);
v___x_2546_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2546_, 0, v___y_2531_);
lean_ctor_set(v___x_2546_, 1, v___y_2526_);
lean_ctor_set(v___x_2546_, 2, v___x_2545_);
v___x_2547_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
v___x_2548_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
v___x_2549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___y_2531_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__8));
v___x_2551_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___y_2531_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_2553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___y_2531_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = l_Nat_reprFast(v___y_2534_);
v___x_2555_ = lean_box(2);
v___x_2556_ = l_Lean_Syntax_mkNumLit(v___x_2554_, v___x_2555_);
v___x_2557_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_2558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___y_2531_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = l_Lean_Syntax_node5(v___y_2531_, v___x_2547_, v___x_2549_, v___x_2551_, v___x_2553_, v___x_2556_, v___x_2558_);
v___x_2560_ = l_Lean_Syntax_node1(v___y_2531_, v___y_2526_, v___x_2559_);
v_sz_2561_ = lean_array_size(v___y_2536_);
v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_2561_, v___y_2530_, v___y_2536_);
v___x_2563_ = l_Array_append___redArg(v___y_2528_, v___x_2562_);
lean_dec_ref(v___x_2562_);
v___x_2564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2564_, 0, v___y_2531_);
lean_ctor_set(v___x_2564_, 1, v___y_2526_);
lean_ctor_set(v___x_2564_, 2, v___x_2563_);
v___x_2565_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
v___x_2566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___y_2531_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = lean_unsigned_to_nat(10u);
v___x_2568_ = lean_mk_empty_array_with_capacity(v___x_2567_);
v___x_2569_ = lean_array_push(v___x_2568_, v___y_2532_);
v___x_2570_ = lean_array_push(v___x_2569_, v___y_2542_);
lean_inc(v___y_2539_);
v___x_2571_ = lean_array_push(v___x_2570_, v___y_2539_);
v___x_2572_ = lean_array_push(v___x_2571_, v___y_2543_);
v___x_2573_ = lean_array_push(v___x_2572_, v___y_2535_);
v___x_2574_ = lean_array_push(v___x_2573_, v___x_2546_);
v___x_2575_ = lean_array_push(v___x_2574_, v___x_2560_);
v___x_2576_ = lean_array_push(v___x_2575_, v___x_2564_);
v___x_2577_ = lean_array_push(v___x_2576_, v___x_2566_);
v___x_2578_ = lean_array_push(v___x_2577_, v___y_2525_);
lean_inc(v___y_2540_);
v___x_2579_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2579_, 0, v___y_2531_);
lean_ctor_set(v___x_2579_, 1, v___y_2540_);
lean_ctor_set(v___x_2579_, 2, v___x_2578_);
v___x_2580_ = l_Lean_Elab_Command_elabSyntax(v___x_2579_, v___y_2541_, v___y_2538_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2580_, 1);
v___x_2582_ = lean_array_get_size(v___y_2527_);
v___x_2583_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__68));
v___x_2584_ = lean_nat_dec_lt(v___x_2523_, v___x_2582_);
if (v___x_2584_ == 0)
{
v___y_2468_ = v___y_2526_;
v___y_2469_ = v___y_2527_;
v___y_2470_ = v_a_2581_;
v___y_2471_ = v___y_2528_;
v___y_2472_ = v___y_2529_;
v___y_2473_ = v___y_2530_;
v___y_2474_ = v___x_2557_;
v___y_2475_ = v___y_2533_;
v___y_2476_ = v___y_2537_;
v___y_2477_ = v___y_2538_;
v___y_2478_ = v___x_2555_;
v___y_2479_ = v___y_2539_;
v___y_2480_ = v___y_2541_;
v___y_2481_ = v___x_2583_;
goto v___jp_2467_;
}
else
{
uint8_t v___x_2585_; 
v___x_2585_ = lean_nat_dec_le(v___x_2582_, v___x_2582_);
if (v___x_2585_ == 0)
{
if (v___x_2584_ == 0)
{
v___y_2468_ = v___y_2526_;
v___y_2469_ = v___y_2527_;
v___y_2470_ = v_a_2581_;
v___y_2471_ = v___y_2528_;
v___y_2472_ = v___y_2529_;
v___y_2473_ = v___y_2530_;
v___y_2474_ = v___x_2557_;
v___y_2475_ = v___y_2533_;
v___y_2476_ = v___y_2537_;
v___y_2477_ = v___y_2538_;
v___y_2478_ = v___x_2555_;
v___y_2479_ = v___y_2539_;
v___y_2480_ = v___y_2541_;
v___y_2481_ = v___x_2583_;
goto v___jp_2467_;
}
else
{
size_t v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_usize_of_nat(v___x_2582_);
v___x_2587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2527_, v___y_2530_, v___x_2586_, v___x_2583_);
v___y_2468_ = v___y_2526_;
v___y_2469_ = v___y_2527_;
v___y_2470_ = v_a_2581_;
v___y_2471_ = v___y_2528_;
v___y_2472_ = v___y_2529_;
v___y_2473_ = v___y_2530_;
v___y_2474_ = v___x_2557_;
v___y_2475_ = v___y_2533_;
v___y_2476_ = v___y_2537_;
v___y_2477_ = v___y_2538_;
v___y_2478_ = v___x_2555_;
v___y_2479_ = v___y_2539_;
v___y_2480_ = v___y_2541_;
v___y_2481_ = v___x_2587_;
goto v___jp_2467_;
}
}
else
{
size_t v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = lean_usize_of_nat(v___x_2582_);
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2527_, v___y_2530_, v___x_2588_, v___x_2583_);
v___y_2468_ = v___y_2526_;
v___y_2469_ = v___y_2527_;
v___y_2470_ = v_a_2581_;
v___y_2471_ = v___y_2528_;
v___y_2472_ = v___y_2529_;
v___y_2473_ = v___y_2530_;
v___y_2474_ = v___x_2557_;
v___y_2475_ = v___y_2533_;
v___y_2476_ = v___y_2537_;
v___y_2477_ = v___y_2538_;
v___y_2478_ = v___x_2555_;
v___y_2479_ = v___y_2539_;
v___y_2480_ = v___y_2541_;
v___y_2481_ = v___x_2589_;
goto v___jp_2467_;
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v___y_2539_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2527_);
v_a_2590_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2580_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2580_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
v___jp_2598_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
lean_inc_ref(v___y_2602_);
v___x_2619_ = l_Array_append___redArg(v___y_2602_, v___y_2618_);
lean_dec_ref(v___y_2618_);
lean_inc(v___y_2600_);
lean_inc(v___y_2606_);
v___x_2620_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2620_, 0, v___y_2606_);
lean_ctor_set(v___x_2620_, 1, v___y_2600_);
lean_ctor_set(v___x_2620_, 2, v___x_2619_);
if (lean_obj_tag(v___y_2603_) == 1)
{
lean_object* v_val_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v_val_2621_ = lean_ctor_get(v___y_2603_, 0);
lean_inc(v_val_2621_);
lean_dec_ref_known(v___y_2603_, 1);
v___x_2622_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
v___x_2623_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc_n(v___y_2606_, 5);
v___x_2624_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___y_2606_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
v___x_2625_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__11));
v___x_2626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___y_2606_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_2628_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___y_2606_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_2630_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___y_2606_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = l_Lean_Syntax_node5(v___y_2606_, v___x_2622_, v___x_2624_, v___x_2626_, v___x_2628_, v_val_2621_, v___x_2630_);
v___x_2632_ = l_Array_mkArray1___redArg(v___x_2631_);
v___y_2525_ = v___y_2599_;
v___y_2526_ = v___y_2600_;
v___y_2527_ = v___y_2601_;
v___y_2528_ = v___y_2602_;
v___y_2529_ = v___y_2604_;
v___y_2530_ = v___y_2605_;
v___y_2531_ = v___y_2606_;
v___y_2532_ = v___y_2607_;
v___y_2533_ = v___y_2608_;
v___y_2534_ = v___y_2609_;
v___y_2535_ = v___x_2620_;
v___y_2536_ = v___y_2610_;
v___y_2537_ = v___y_2611_;
v___y_2538_ = v___y_2612_;
v___y_2539_ = v___y_2614_;
v___y_2540_ = v___y_2613_;
v___y_2541_ = v___y_2617_;
v___y_2542_ = v___y_2616_;
v___y_2543_ = v___y_2615_;
v___y_2544_ = v___x_2632_;
goto v___jp_2524_;
}
else
{
lean_object* v___x_2633_; 
lean_dec(v___y_2603_);
v___x_2633_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2525_ = v___y_2599_;
v___y_2526_ = v___y_2600_;
v___y_2527_ = v___y_2601_;
v___y_2528_ = v___y_2602_;
v___y_2529_ = v___y_2604_;
v___y_2530_ = v___y_2605_;
v___y_2531_ = v___y_2606_;
v___y_2532_ = v___y_2607_;
v___y_2533_ = v___y_2608_;
v___y_2534_ = v___y_2609_;
v___y_2535_ = v___x_2620_;
v___y_2536_ = v___y_2610_;
v___y_2537_ = v___y_2611_;
v___y_2538_ = v___y_2612_;
v___y_2539_ = v___y_2614_;
v___y_2540_ = v___y_2613_;
v___y_2541_ = v___y_2617_;
v___y_2542_ = v___y_2616_;
v___y_2543_ = v___y_2615_;
v___y_2544_ = v___x_2633_;
goto v___jp_2524_;
}
}
v___jp_2634_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_inc_ref(v___y_2639_);
v___x_2655_ = l_Array_append___redArg(v___y_2639_, v___y_2654_);
lean_dec_ref(v___y_2654_);
lean_inc(v___y_2637_);
lean_inc_n(v___y_2643_, 2);
v___x_2656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2656_, 0, v___y_2643_);
lean_ctor_set(v___x_2656_, 1, v___y_2637_);
lean_ctor_set(v___x_2656_, 2, v___x_2655_);
lean_inc_ref(v___y_2647_);
v___x_2657_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___y_2643_);
lean_ctor_set(v___x_2657_, 1, v___y_2647_);
if (lean_obj_tag(v___y_2635_) == 1)
{
lean_object* v_val_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v_val_2658_ = lean_ctor_get(v___y_2635_, 0);
lean_inc(v_val_2658_);
lean_dec_ref_known(v___y_2635_, 1);
v___x_2659_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
v___x_2660_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc_n(v___y_2643_, 2);
v___x_2661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___y_2643_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = l_Lean_Syntax_node2(v___y_2643_, v___x_2659_, v___x_2661_, v_val_2658_);
v___x_2663_ = l_Array_mkArray1___redArg(v___x_2662_);
v___y_2599_ = v___y_2636_;
v___y_2600_ = v___y_2637_;
v___y_2601_ = v___y_2638_;
v___y_2602_ = v___y_2639_;
v___y_2603_ = v___y_2640_;
v___y_2604_ = v___y_2641_;
v___y_2605_ = v___y_2642_;
v___y_2606_ = v___y_2643_;
v___y_2607_ = v___y_2644_;
v___y_2608_ = v___y_2645_;
v___y_2609_ = v___y_2646_;
v___y_2610_ = v___y_2648_;
v___y_2611_ = v___y_2649_;
v___y_2612_ = v___y_2650_;
v___y_2613_ = v___y_2652_;
v___y_2614_ = v___y_2651_;
v___y_2615_ = v___x_2657_;
v___y_2616_ = v___x_2656_;
v___y_2617_ = v___y_2653_;
v___y_2618_ = v___x_2663_;
goto v___jp_2598_;
}
else
{
lean_object* v___x_2664_; 
lean_dec(v___y_2635_);
v___x_2664_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2599_ = v___y_2636_;
v___y_2600_ = v___y_2637_;
v___y_2601_ = v___y_2638_;
v___y_2602_ = v___y_2639_;
v___y_2603_ = v___y_2640_;
v___y_2604_ = v___y_2641_;
v___y_2605_ = v___y_2642_;
v___y_2606_ = v___y_2643_;
v___y_2607_ = v___y_2644_;
v___y_2608_ = v___y_2645_;
v___y_2609_ = v___y_2646_;
v___y_2610_ = v___y_2648_;
v___y_2611_ = v___y_2649_;
v___y_2612_ = v___y_2650_;
v___y_2613_ = v___y_2652_;
v___y_2614_ = v___y_2651_;
v___y_2615_ = v___x_2657_;
v___y_2616_ = v___x_2656_;
v___y_2617_ = v___y_2653_;
v___y_2618_ = v___x_2664_;
goto v___jp_2598_;
}
}
v___jp_2665_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_inc_ref(v___y_2670_);
v___x_2686_ = l_Array_append___redArg(v___y_2670_, v___y_2685_);
lean_dec_ref(v___y_2685_);
lean_inc(v___y_2668_);
lean_inc(v___y_2674_);
v___x_2687_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2687_, 0, v___y_2674_);
lean_ctor_set(v___x_2687_, 1, v___y_2668_);
lean_ctor_set(v___x_2687_, 2, v___x_2686_);
if (lean_obj_tag(v___y_2675_) == 1)
{
lean_object* v_val_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_val_2688_ = lean_ctor_get(v___y_2675_, 0);
lean_inc(v_val_2688_);
lean_dec_ref_known(v___y_2675_, 1);
v___x_2689_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__11));
lean_inc_ref(v___y_2676_);
v___x_2690_ = l_Lean_Name_mkStr4(v___x_2410_, v___x_2411_, v___y_2676_, v___x_2689_);
v___x_2691_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc_n(v___y_2674_, 4);
v___x_2692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___y_2674_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
lean_inc_ref(v___y_2670_);
v___x_2693_ = l_Array_append___redArg(v___y_2670_, v_val_2688_);
lean_dec(v_val_2688_);
lean_inc(v___y_2668_);
v___x_2694_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2694_, 0, v___y_2674_);
lean_ctor_set(v___x_2694_, 1, v___y_2668_);
lean_ctor_set(v___x_2694_, 2, v___x_2693_);
v___x_2695_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
v___x_2696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___y_2674_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = l_Lean_Syntax_node3(v___y_2674_, v___x_2690_, v___x_2692_, v___x_2694_, v___x_2696_);
v___x_2698_ = l_Array_mkArray1___redArg(v___x_2697_);
v___y_2635_ = v___y_2666_;
v___y_2636_ = v___y_2667_;
v___y_2637_ = v___y_2668_;
v___y_2638_ = v___y_2669_;
v___y_2639_ = v___y_2670_;
v___y_2640_ = v___y_2671_;
v___y_2641_ = v___y_2672_;
v___y_2642_ = v___y_2673_;
v___y_2643_ = v___y_2674_;
v___y_2644_ = v___x_2687_;
v___y_2645_ = v___y_2676_;
v___y_2646_ = v___y_2677_;
v___y_2647_ = v___y_2678_;
v___y_2648_ = v___y_2679_;
v___y_2649_ = v___y_2680_;
v___y_2650_ = v___y_2681_;
v___y_2651_ = v___y_2683_;
v___y_2652_ = v___y_2682_;
v___y_2653_ = v___y_2684_;
v___y_2654_ = v___x_2698_;
goto v___jp_2634_;
}
else
{
lean_object* v___x_2699_; 
lean_dec(v___y_2675_);
v___x_2699_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2635_ = v___y_2666_;
v___y_2636_ = v___y_2667_;
v___y_2637_ = v___y_2668_;
v___y_2638_ = v___y_2669_;
v___y_2639_ = v___y_2670_;
v___y_2640_ = v___y_2671_;
v___y_2641_ = v___y_2672_;
v___y_2642_ = v___y_2673_;
v___y_2643_ = v___y_2674_;
v___y_2644_ = v___x_2687_;
v___y_2645_ = v___y_2676_;
v___y_2646_ = v___y_2677_;
v___y_2647_ = v___y_2678_;
v___y_2648_ = v___y_2679_;
v___y_2649_ = v___y_2680_;
v___y_2650_ = v___y_2681_;
v___y_2651_ = v___y_2683_;
v___y_2652_ = v___y_2682_;
v___y_2653_ = v___y_2684_;
v___y_2654_ = v___x_2699_;
goto v___jp_2634_;
}
}
v___jp_2700_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2717_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__12));
v___x_2718_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__13));
v___x_2719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_2720_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
if (lean_obj_tag(v___y_2701_) == 1)
{
lean_object* v_val_2721_; lean_object* v___x_2722_; 
v_val_2721_ = lean_ctor_get(v___y_2701_, 0);
lean_inc(v_val_2721_);
lean_dec_ref_known(v___y_2701_, 1);
v___x_2722_ = l_Array_mkArray1___redArg(v_val_2721_);
v___y_2666_ = v___y_2702_;
v___y_2667_ = v___y_2703_;
v___y_2668_ = v___x_2719_;
v___y_2669_ = v___y_2704_;
v___y_2670_ = v___x_2720_;
v___y_2671_ = v___y_2705_;
v___y_2672_ = v___y_2706_;
v___y_2673_ = v___y_2707_;
v___y_2674_ = v___y_2708_;
v___y_2675_ = v___y_2709_;
v___y_2676_ = v___y_2710_;
v___y_2677_ = v___y_2711_;
v___y_2678_ = v___x_2717_;
v___y_2679_ = v___y_2712_;
v___y_2680_ = v___y_2713_;
v___y_2681_ = v___y_2714_;
v___y_2682_ = v___x_2718_;
v___y_2683_ = v___y_2715_;
v___y_2684_ = v___y_2716_;
v___y_2685_ = v___x_2722_;
goto v___jp_2665_;
}
else
{
lean_object* v___x_2723_; 
lean_dec(v___y_2701_);
v___x_2723_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2666_ = v___y_2702_;
v___y_2667_ = v___y_2703_;
v___y_2668_ = v___x_2719_;
v___y_2669_ = v___y_2704_;
v___y_2670_ = v___x_2720_;
v___y_2671_ = v___y_2705_;
v___y_2672_ = v___y_2706_;
v___y_2673_ = v___y_2707_;
v___y_2674_ = v___y_2708_;
v___y_2675_ = v___y_2709_;
v___y_2676_ = v___y_2710_;
v___y_2677_ = v___y_2711_;
v___y_2678_ = v___x_2717_;
v___y_2679_ = v___y_2712_;
v___y_2680_ = v___y_2713_;
v___y_2681_ = v___y_2714_;
v___y_2682_ = v___x_2718_;
v___y_2683_ = v___y_2715_;
v___y_2684_ = v___y_2716_;
v___y_2685_ = v___x_2723_;
goto v___jp_2665_;
}
}
v___jp_2724_:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_2734_, 0, v_prio_x3f_2731_);
v___x_2735_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2734_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v_items_2739_; size_t v_sz_2740_; size_t v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2737_ = lean_unsigned_to_nat(7u);
v___x_2738_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2737_);
v_items_2739_ = l_Lean_Syntax_getArgs(v___x_2738_);
lean_dec(v___x_2738_);
v_sz_2740_ = lean_array_size(v_items_2739_);
v___x_2741_ = ((size_t)0ULL);
v___x_2742_ = lean_box_usize(v_sz_2740_);
v___x_2743_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___boxed__const__1));
lean_inc_ref(v_items_2739_);
v___x_2744_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed), 5, 3);
lean_closure_set(v___x_2744_, 0, v___x_2742_);
lean_closure_set(v___x_2744_, 1, v___x_2743_);
lean_closure_set(v___x_2744_, 2, v_items_2739_);
v___x_2745_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2744_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2747_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___x_2745_, 1);
v___x_2747_ = l_Lean_Elab_Command_getRef___redArg(v___y_2732_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2749_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v___x_2747_, 1);
v___x_2749_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2732_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_quotContext_x3f_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v_rhs_2755_; lean_object* v_attrs_x3f_2756_; lean_object* v___x_2757_; 
lean_dec_ref_known(v___x_2749_, 1);
v_quotContext_x3f_2750_ = lean_ctor_get(v___y_2732_, 5);
v___x_2751_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
v___x_2752_ = 0;
v___x_2753_ = l_Lean_mkIdentFrom(v_x_2379_, v___x_2751_, v___x_2752_);
v___x_2754_ = lean_unsigned_to_nat(9u);
v_rhs_2755_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2754_);
lean_dec(v_x_2379_);
lean_inc(v_rhs_2755_);
v_attrs_x3f_2756_ = l_Lean_Elab_Command_addInheritDocDefault(v_rhs_2755_, v___y_2729_);
v___x_2757_ = l_Lean_SourceInfo_fromRef(v_a_2748_, v___x_2752_);
lean_dec(v_a_2748_);
if (lean_obj_tag(v_quotContext_x3f_2750_) == 0)
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2733_);
lean_dec_ref(v___x_2758_);
v___y_2701_ = v___y_2725_;
v___y_2702_ = v___y_2726_;
v___y_2703_ = v___x_2753_;
v___y_2704_ = v_items_2739_;
v___y_2705_ = v___y_2728_;
v___y_2706_ = v_rhs_2755_;
v___y_2707_ = v___x_2741_;
v___y_2708_ = v___x_2757_;
v___y_2709_ = v_attrs_x3f_2756_;
v___y_2710_ = v___y_2727_;
v___y_2711_ = v_a_2736_;
v___y_2712_ = v_a_2746_;
v___y_2713_ = v___x_2752_;
v___y_2714_ = v___y_2733_;
v___y_2715_ = v___y_2730_;
v___y_2716_ = v___y_2732_;
goto v___jp_2700_;
}
else
{
v___y_2701_ = v___y_2725_;
v___y_2702_ = v___y_2726_;
v___y_2703_ = v___x_2753_;
v___y_2704_ = v_items_2739_;
v___y_2705_ = v___y_2728_;
v___y_2706_ = v_rhs_2755_;
v___y_2707_ = v___x_2741_;
v___y_2708_ = v___x_2757_;
v___y_2709_ = v_attrs_x3f_2756_;
v___y_2710_ = v___y_2727_;
v___y_2711_ = v_a_2736_;
v___y_2712_ = v_a_2746_;
v___y_2713_ = v___x_2752_;
v___y_2714_ = v___y_2733_;
v___y_2715_ = v___y_2730_;
v___y_2716_ = v___y_2732_;
goto v___jp_2700_;
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_dec(v_a_2748_);
lean_dec(v_a_2746_);
lean_dec_ref(v_items_2739_);
lean_dec(v_a_2736_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v_x_2379_);
v_a_2759_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2749_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2749_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v_a_2746_);
lean_dec_ref(v_items_2739_);
lean_dec(v_a_2736_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v_x_2379_);
v_a_2767_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2747_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2747_);
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
lean_dec_ref(v_items_2739_);
lean_dec(v_a_2736_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v_x_2379_);
v_a_2775_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2745_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2745_);
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
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v_x_2379_);
v_a_2783_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2735_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2735_);
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
v___jp_2791_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; 
v___x_2802_ = lean_unsigned_to_nat(6u);
v___x_2803_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2802_);
v___x_2804_ = l_Lean_Syntax_isNone(v___x_2803_);
if (v___x_2804_ == 0)
{
uint8_t v___x_2805_; 
lean_inc(v___x_2803_);
v___x_2805_ = l_Lean_Syntax_matchesNull(v___x_2803_, v___y_2798_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; 
lean_dec(v___x_2803_);
lean_dec(v_name_x3f_2799_);
lean_dec(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec(v___y_2794_);
lean_dec(v___y_2792_);
lean_dec(v_x_2379_);
v___x_2806_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2806_;
}
else
{
lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2807_ = l_Lean_Syntax_getArg(v___x_2803_, v___x_2523_);
lean_dec(v___x_2803_);
v___x_2808_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
lean_inc(v___x_2807_);
v___x_2809_ = l_Lean_Syntax_isOfKind(v___x_2807_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
lean_dec(v___x_2807_);
lean_dec(v_name_x3f_2799_);
lean_dec(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec(v___y_2794_);
lean_dec(v___y_2792_);
lean_dec(v_x_2379_);
v___x_2810_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2810_;
}
else
{
lean_object* v_prio_x3f_2811_; lean_object* v___x_2812_; 
v_prio_x3f_2811_ = l_Lean_Syntax_getArg(v___x_2807_, v___y_2793_);
lean_dec(v___x_2807_);
v___x_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2812_, 0, v_prio_x3f_2811_);
v___y_2725_ = v___y_2792_;
v___y_2726_ = v___y_2794_;
v___y_2727_ = v___y_2795_;
v___y_2728_ = v_name_x3f_2799_;
v___y_2729_ = v___y_2796_;
v___y_2730_ = v___y_2797_;
v_prio_x3f_2731_ = v___x_2812_;
v___y_2732_ = v___y_2800_;
v___y_2733_ = v___y_2801_;
goto v___jp_2724_;
}
}
}
else
{
lean_object* v___x_2813_; 
lean_dec(v___x_2803_);
v___x_2813_ = lean_box(0);
v___y_2725_ = v___y_2792_;
v___y_2726_ = v___y_2794_;
v___y_2727_ = v___y_2795_;
v___y_2728_ = v_name_x3f_2799_;
v___y_2729_ = v___y_2796_;
v___y_2730_ = v___y_2797_;
v_prio_x3f_2731_ = v___x_2813_;
v___y_2732_ = v___y_2800_;
v___y_2733_ = v___y_2801_;
goto v___jp_2724_;
}
}
v___jp_2814_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2824_ = lean_unsigned_to_nat(5u);
v___x_2825_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2824_);
v___x_2826_ = l_Lean_Syntax_isNone(v___x_2825_);
if (v___x_2826_ == 0)
{
uint8_t v___x_2827_; 
lean_inc(v___x_2825_);
v___x_2827_ = l_Lean_Syntax_matchesNull(v___x_2825_, v___y_2820_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; 
lean_dec(v___x_2825_);
lean_dec(v_prec_x3f_2821_);
lean_dec(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec(v___y_2815_);
lean_dec(v_x_2379_);
v___x_2828_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2828_;
}
else
{
lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v___x_2829_ = l_Lean_Syntax_getArg(v___x_2825_, v___x_2523_);
lean_dec(v___x_2825_);
v___x_2830_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
lean_inc(v___x_2829_);
v___x_2831_ = l_Lean_Syntax_isOfKind(v___x_2829_, v___x_2830_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; 
lean_dec(v___x_2829_);
lean_dec(v_prec_x3f_2821_);
lean_dec(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec(v___y_2815_);
lean_dec(v_x_2379_);
v___x_2832_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2832_;
}
else
{
lean_object* v_name_x3f_2833_; lean_object* v___x_2834_; 
v_name_x3f_2833_ = l_Lean_Syntax_getArg(v___x_2829_, v___y_2816_);
lean_dec(v___x_2829_);
v___x_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2834_, 0, v_name_x3f_2833_);
v___y_2792_ = v___y_2815_;
v___y_2793_ = v___y_2816_;
v___y_2794_ = v_prec_x3f_2821_;
v___y_2795_ = v___y_2817_;
v___y_2796_ = v___y_2818_;
v___y_2797_ = v___y_2819_;
v___y_2798_ = v___y_2820_;
v_name_x3f_2799_ = v___x_2834_;
v___y_2800_ = v___y_2822_;
v___y_2801_ = v___y_2823_;
goto v___jp_2791_;
}
}
}
else
{
lean_object* v___x_2835_; 
lean_dec(v___x_2825_);
v___x_2835_ = lean_box(0);
v___y_2792_ = v___y_2815_;
v___y_2793_ = v___y_2816_;
v___y_2794_ = v_prec_x3f_2821_;
v___y_2795_ = v___y_2817_;
v___y_2796_ = v___y_2818_;
v___y_2797_ = v___y_2819_;
v___y_2798_ = v___y_2820_;
v_name_x3f_2799_ = v___x_2835_;
v___y_2800_ = v___y_2822_;
v___y_2801_ = v___y_2823_;
goto v___jp_2791_;
}
}
v___jp_2836_:
{
lean_object* v___x_2842_; lean_object* v_attrKind_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
v___x_2842_ = lean_unsigned_to_nat(2u);
v_attrKind_2843_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2842_);
v___x_2844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2));
v___x_2845_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(v_attrKind_2843_);
v___x_2846_ = l_Lean_Syntax_isOfKind(v_attrKind_2843_, v___x_2845_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; 
lean_dec(v_attrKind_2843_);
lean_dec(v_attrs_x3f_2839_);
lean_dec(v___y_2837_);
lean_dec(v_x_2379_);
v___x_2847_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2847_;
}
else
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2848_ = lean_unsigned_to_nat(3u);
v___x_2849_ = lean_unsigned_to_nat(4u);
v___x_2850_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2849_);
v___x_2851_ = l_Lean_Syntax_isNone(v___x_2850_);
if (v___x_2851_ == 0)
{
uint8_t v___x_2852_; 
lean_inc(v___x_2850_);
v___x_2852_ = l_Lean_Syntax_matchesNull(v___x_2850_, v___y_2838_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; 
lean_dec(v___x_2850_);
lean_dec(v_attrKind_2843_);
lean_dec(v_attrs_x3f_2839_);
lean_dec(v___y_2837_);
lean_dec(v_x_2379_);
v___x_2853_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2853_;
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; 
v___x_2854_ = l_Lean_Syntax_getArg(v___x_2850_, v___x_2523_);
lean_dec(v___x_2850_);
v___x_2855_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
lean_inc(v___x_2854_);
v___x_2856_ = l_Lean_Syntax_isOfKind(v___x_2854_, v___x_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
lean_dec(v___x_2854_);
lean_dec(v_attrKind_2843_);
lean_dec(v_attrs_x3f_2839_);
lean_dec(v___y_2837_);
lean_dec(v_x_2379_);
v___x_2857_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2857_;
}
else
{
lean_object* v_prec_x3f_2858_; lean_object* v___x_2859_; 
v_prec_x3f_2858_ = l_Lean_Syntax_getArg(v___x_2854_, v___y_2838_);
lean_dec(v___x_2854_);
v___x_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2859_, 0, v_prec_x3f_2858_);
v___y_2815_ = v___y_2837_;
v___y_2816_ = v___x_2848_;
v___y_2817_ = v___x_2844_;
v___y_2818_ = v_attrs_x3f_2839_;
v___y_2819_ = v_attrKind_2843_;
v___y_2820_ = v___y_2838_;
v_prec_x3f_2821_ = v___x_2859_;
v___y_2822_ = v___y_2840_;
v___y_2823_ = v___y_2841_;
goto v___jp_2814_;
}
}
}
else
{
lean_object* v___x_2860_; 
lean_dec(v___x_2850_);
v___x_2860_ = lean_box(0);
v___y_2815_ = v___y_2837_;
v___y_2816_ = v___x_2848_;
v___y_2817_ = v___x_2844_;
v___y_2818_ = v_attrs_x3f_2839_;
v___y_2819_ = v_attrKind_2843_;
v___y_2820_ = v___y_2838_;
v_prec_x3f_2821_ = v___x_2860_;
v___y_2822_ = v___y_2840_;
v___y_2823_ = v___y_2841_;
goto v___jp_2814_;
}
}
}
v___jp_2861_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v___x_2865_ = lean_unsigned_to_nat(1u);
v___x_2866_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2865_);
v___x_2867_ = l_Lean_Syntax_isNone(v___x_2866_);
if (v___x_2867_ == 0)
{
uint8_t v___x_2868_; 
lean_inc(v___x_2866_);
v___x_2868_ = l_Lean_Syntax_matchesNull(v___x_2866_, v___x_2865_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; 
lean_dec(v___x_2866_);
lean_dec(v_doc_x3f_2862_);
lean_dec(v_x_2379_);
v___x_2869_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2869_;
}
else
{
lean_object* v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2870_ = l_Lean_Syntax_getArg(v___x_2866_, v___x_2523_);
lean_dec(v___x_2866_);
v___x_2871_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
lean_inc(v___x_2870_);
v___x_2872_ = l_Lean_Syntax_isOfKind(v___x_2870_, v___x_2871_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; 
lean_dec(v___x_2870_);
lean_dec(v_doc_x3f_2862_);
lean_dec(v_x_2379_);
v___x_2873_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2873_;
}
else
{
lean_object* v___x_2874_; lean_object* v_attrs_x3f_2875_; lean_object* v___x_2876_; 
v___x_2874_ = l_Lean_Syntax_getArg(v___x_2870_, v___x_2865_);
lean_dec(v___x_2870_);
v_attrs_x3f_2875_ = l_Lean_Syntax_getArgs(v___x_2874_);
lean_dec(v___x_2874_);
v___x_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2876_, 0, v_attrs_x3f_2875_);
v___y_2837_ = v_doc_x3f_2862_;
v___y_2838_ = v___x_2865_;
v_attrs_x3f_2839_ = v___x_2876_;
v___y_2840_ = v___y_2863_;
v___y_2841_ = v___y_2864_;
goto v___jp_2836_;
}
}
}
else
{
lean_object* v___x_2877_; 
lean_dec(v___x_2866_);
v___x_2877_ = lean_box(0);
v___y_2837_ = v_doc_x3f_2862_;
v___y_2838_ = v___x_2865_;
v_attrs_x3f_2839_ = v___x_2877_;
v___y_2840_ = v___y_2863_;
v___y_2841_ = v___y_2864_;
goto v___jp_2836_;
}
}
}
v___jp_2383_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkUnexpander___boxed), 5, 3);
lean_closure_set(v___x_2389_, 0, v___y_2386_);
lean_closure_set(v___x_2389_, 1, v___y_2384_);
lean_closure_set(v___x_2389_, 2, v___y_2385_);
v___x_2390_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2389_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2401_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2401_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2401_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
if (lean_obj_tag(v_a_2391_) == 1)
{
lean_object* v_val_2395_; lean_object* v___x_2396_; 
lean_del_object(v___x_2393_);
v_val_2395_ = lean_ctor_get(v_a_2391_, 0);
lean_inc(v_val_2395_);
lean_dec_ref_known(v_a_2391_, 1);
v___x_2396_ = l_Lean_Elab_Command_elabCommand(v_val_2395_, v___y_2387_, v___y_2388_);
return v___x_2396_;
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2399_; 
lean_dec(v_a_2391_);
v___x_2397_ = lean_box(0);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2397_);
v___x_2399_ = v___x_2393_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
v_a_2402_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2390_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2390_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
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
v___jp_2414_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2425_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__2));
v___x_2426_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__3));
lean_inc_ref(v___y_2420_);
lean_inc_n(v___y_2418_, 4);
lean_inc_n(v___y_2419_, 15);
v___x_2427_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2427_, 0, v___y_2419_);
lean_ctor_set(v___x_2427_, 1, v___y_2418_);
lean_ctor_set(v___x_2427_, 2, v___y_2420_);
v___x_2428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___y_2419_);
lean_ctor_set(v___x_2428_, 1, v___x_2425_);
v___x_2429_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__29));
lean_inc_ref_n(v___y_2417_, 4);
v___x_2430_ = l_Lean_Name_mkStr4(v___x_2410_, v___x_2411_, v___y_2417_, v___x_2429_);
v___x_2431_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__31));
v___x_2432_ = l_Lean_Name_mkStr4(v___x_2410_, v___x_2411_, v___y_2417_, v___x_2431_);
v___x_2433_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
v___x_2434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___y_2419_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__34));
v___x_2436_ = l_Lean_Name_mkStr4(v___x_2410_, v___x_2411_, v___y_2417_, v___x_2435_);
v___x_2437_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
v___x_2438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___y_2419_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
lean_inc_ref(v___y_2415_);
v___x_2439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___y_2419_);
lean_ctor_set(v___x_2439_, 1, v___y_2415_);
lean_inc_ref(v___x_2439_);
lean_inc(v___y_2416_);
lean_inc_ref(v___x_2438_);
lean_inc(v___x_2436_);
v___x_2440_ = l_Lean_Syntax_node3(v___y_2419_, v___x_2436_, v___x_2438_, v___y_2416_, v___x_2439_);
v___x_2441_ = l_Lean_Syntax_node1(v___y_2419_, v___y_2418_, v___x_2440_);
v___x_2442_ = l_Lean_Syntax_node1(v___y_2419_, v___y_2418_, v___x_2441_);
v___x_2443_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
v___x_2444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___y_2419_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
v___x_2445_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__4));
v___x_2446_ = l_Lean_Name_mkStr4(v___x_2410_, v___x_2411_, v___y_2417_, v___x_2445_);
v___x_2447_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__5));
v___x_2448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___y_2419_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
lean_inc(v___y_2422_);
v___x_2449_ = l_Lean_Syntax_node3(v___y_2419_, v___x_2436_, v___x_2438_, v___y_2422_, v___x_2439_);
v___x_2450_ = l_Lean_Syntax_node2(v___y_2419_, v___x_2446_, v___x_2448_, v___x_2449_);
v___x_2451_ = l_Lean_Syntax_node4(v___y_2419_, v___x_2432_, v___x_2434_, v___x_2442_, v___x_2444_, v___x_2450_);
v___x_2452_ = l_Lean_Syntax_node1(v___y_2419_, v___y_2418_, v___x_2451_);
v___x_2453_ = l_Lean_Syntax_node1(v___y_2419_, v___x_2430_, v___x_2452_);
lean_inc_n(v___y_2423_, 2);
lean_inc_ref_n(v___x_2427_, 2);
v___x_2454_ = l_Lean_Syntax_node6(v___y_2419_, v___x_2426_, v___x_2427_, v___x_2427_, v___y_2423_, v___x_2428_, v___x_2427_, v___x_2453_);
v___x_2455_ = l_Lean_Elab_Command_isLocalAttrKind(v___y_2423_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_Elab_Command_elabCommand(v___x_2454_, v___y_2424_, v___y_2421_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_dec_ref_known(v___x_2456_, 1);
v___y_2384_ = v___y_2416_;
v___y_2385_ = v___y_2422_;
v___y_2386_ = v___y_2423_;
v___y_2387_ = v___y_2424_;
v___y_2388_ = v___y_2421_;
goto v___jp_2383_;
}
else
{
lean_dec(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec(v___y_2416_);
return v___x_2456_;
}
}
else
{
lean_object* v___x_2457_; lean_object* v_scopes_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v_opts_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2457_ = lean_st_ref_get(v___y_2421_);
v_scopes_2458_ = lean_ctor_get(v___x_2457_, 2);
lean_inc(v_scopes_2458_);
lean_dec(v___x_2457_);
v___x_2459_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2460_ = l_List_head_x21___redArg(v___x_2459_, v_scopes_2458_);
lean_dec(v_scopes_2458_);
v_opts_2461_ = lean_ctor_get(v___x_2460_, 1);
lean_inc_ref(v_opts_2461_);
lean_dec(v___x_2460_);
v___x_2462_ = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
v___x_2463_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_2461_, v___x_2462_, v___x_2413_);
v___f_2464_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___lam__0), 2, 1);
lean_closure_set(v___f_2464_, 0, v___x_2463_);
v___x_2465_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_2465_, 0, v___x_2454_);
v___x_2466_ = l_Lean_Elab_Command_withScope___redArg(v___f_2464_, v___x_2465_, v___y_2424_, v___y_2421_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_dec_ref_known(v___x_2466_, 1);
v___y_2384_ = v___y_2416_;
v___y_2385_ = v___y_2422_;
v___y_2386_ = v___y_2423_;
v___y_2387_ = v___y_2424_;
v___y_2388_ = v___y_2421_;
goto v___jp_2383_;
}
else
{
lean_dec(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec(v___y_2416_);
return v___x_2466_;
}
}
}
v___jp_2467_:
{
size_t v_sz_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v_sz_2482_ = lean_array_size(v___y_2469_);
v___x_2483_ = lean_box_usize(v_sz_2482_);
v___x_2484_ = lean_box_usize(v___y_2473_);
v___x_2485_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed), 5, 3);
lean_closure_set(v___x_2485_, 0, v___x_2483_);
lean_closure_set(v___x_2485_, 1, v___x_2484_);
lean_closure_set(v___x_2485_, 2, v___y_2469_);
v___x_2486_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2485_, v___y_2480_, v___y_2477_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2488_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref_known(v___x_2486_, 1);
v___x_2488_ = l_Lean_Elab_Command_getRef___redArg(v___y_2480_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v___x_2490_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v___x_2490_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2480_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_quotContext_x3f_2491_; size_t v_sz_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
lean_dec_ref_known(v___x_2490_, 1);
v_quotContext_x3f_2491_ = lean_ctor_get(v___y_2480_, 5);
v_sz_2492_ = lean_array_size(v___y_2481_);
v___x_2493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_2492_, v___y_2473_, v___y_2481_);
v___x_2494_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(v___x_2493_, v___y_2472_);
lean_dec_ref(v___x_2493_);
v___x_2495_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2495_, 0, v___y_2478_);
lean_ctor_set(v___x_2495_, 1, v___y_2470_);
lean_ctor_set(v___x_2495_, 2, v_a_2487_);
v___x_2496_ = l_Lean_SourceInfo_fromRef(v_a_2489_, v___y_2476_);
lean_dec(v_a_2489_);
if (lean_obj_tag(v_quotContext_x3f_2491_) == 0)
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2477_);
lean_dec_ref(v___x_2497_);
v___y_2415_ = v___y_2474_;
v___y_2416_ = v___x_2495_;
v___y_2417_ = v___y_2475_;
v___y_2418_ = v___y_2468_;
v___y_2419_ = v___x_2496_;
v___y_2420_ = v___y_2471_;
v___y_2421_ = v___y_2477_;
v___y_2422_ = v___x_2494_;
v___y_2423_ = v___y_2479_;
v___y_2424_ = v___y_2480_;
goto v___jp_2414_;
}
else
{
v___y_2415_ = v___y_2474_;
v___y_2416_ = v___x_2495_;
v___y_2417_ = v___y_2475_;
v___y_2418_ = v___y_2468_;
v___y_2419_ = v___x_2496_;
v___y_2420_ = v___y_2471_;
v___y_2421_ = v___y_2477_;
v___y_2422_ = v___x_2494_;
v___y_2423_ = v___y_2479_;
v___y_2424_ = v___y_2480_;
goto v___jp_2414_;
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec(v_a_2489_);
lean_dec(v_a_2487_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec(v___y_2472_);
lean_dec(v___y_2470_);
v_a_2498_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2490_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2490_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_a_2487_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec(v___y_2472_);
lean_dec(v___y_2470_);
v_a_2506_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2488_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2488_);
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
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec(v___y_2472_);
lean_dec(v___y_2470_);
v_a_2514_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2486_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2486_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___boxed(lean_object* v_x_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lean_Elab_Command_elabNotation(v_x_2890_, v_a_2891_, v_a_2892_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(lean_object* v_00_u03b1_2895_, lean_object* v_x_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v_x_2896_, v___y_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2900_, lean_object* v_x_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(v_00_u03b1_2900_, v_x_2901_, v___y_2902_, v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec_ref(v_x_2901_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(lean_object* v_00_u03b1_2905_, lean_object* v_ref_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_2906_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___boxed(lean_object* v_00_u03b1_2911_, lean_object* v_ref_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(v_00_u03b1_2911_, v_ref_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(lean_object* v_00_u03b1_2917_, lean_object* v_x_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2918_, v___y_2919_, v___y_2920_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___boxed(lean_object* v_00_u03b1_2923_, lean_object* v_x_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(v_00_u03b1_2923_, v_x_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(lean_object* v_msgData_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msgData_2929_, v___y_2931_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(v_msgData_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(lean_object* v_as_2939_, lean_object* v_as_x27_2940_, lean_object* v_b_2941_, lean_object* v_a_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_2940_, v_b_2941_, v___y_2943_, v___y_2944_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___boxed(lean_object* v_as_2947_, lean_object* v_as_x27_2948_, lean_object* v_b_2949_, lean_object* v_a_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(v_as_2947_, v_as_x27_2948_, v_b_2949_, v_a_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_as_x27_2948_);
lean_dec(v_as_2947_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(lean_object* v_00_u03b1_2955_, lean_object* v_ref_2956_, lean_object* v_msg_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_ref_2956_, v_msg_2957_, v___y_2958_, v___y_2959_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___boxed(lean_object* v_00_u03b1_2962_, lean_object* v_ref_2963_, lean_object* v_msg_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(v_00_u03b1_2962_, v_ref_2963_, v_msg_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v_ref_2963_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2969_, lean_object* v_m_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v_m_2970_, v_a_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_2973_, lean_object* v_m_2974_, lean_object* v_a_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(v_00_u03b2_2973_, v_m_2974_, v_a_2975_);
lean_dec(v_a_2975_);
lean_dec_ref(v_m_2974_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(lean_object* v_00_u03b1_2977_, lean_object* v_msg_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_2978_, v___y_2979_, v___y_2980_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___boxed(lean_object* v_00_u03b1_2983_, lean_object* v_msg_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(v_00_u03b1_2983_, v_msg_2984_, v___y_2985_, v___y_2986_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
return v_res_2988_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(lean_object* v_00_u03b2_2989_, lean_object* v_x_2990_, lean_object* v_x_2991_){
_start:
{
uint8_t v___x_2992_; 
v___x_2992_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_2990_, v_x_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___boxed(lean_object* v_00_u03b2_2993_, lean_object* v_x_2994_, lean_object* v_x_2995_){
_start:
{
uint8_t v_res_2996_; lean_object* v_r_2997_; 
v_res_2996_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(v_00_u03b2_2993_, v_x_2994_, v_x_2995_);
lean_dec_ref(v_x_2995_);
lean_dec_ref(v_x_2994_);
v_r_2997_ = lean_box(v_res_2996_);
return v_r_2997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(lean_object* v_00_u03b2_2998_, lean_object* v_a_2999_, lean_object* v_x_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_2999_, v_x_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___boxed(lean_object* v_00_u03b2_3002_, lean_object* v_a_3003_, lean_object* v_x_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(v_00_u03b2_3002_, v_a_3003_, v_x_3004_);
lean_dec(v_x_3004_);
lean_dec(v_a_3003_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(lean_object* v_msgData_3006_, lean_object* v_macroStack_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_msgData_3006_, v_macroStack_3007_, v___y_3009_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___boxed(lean_object* v_msgData_3012_, lean_object* v_macroStack_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(v_msgData_3012_, v_macroStack_3013_, v___y_3014_, v___y_3015_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
return v_res_3017_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(lean_object* v_00_u03b2_3018_, lean_object* v_x_3019_, size_t v_x_3020_, lean_object* v_x_3021_){
_start:
{
uint8_t v___x_3022_; 
v___x_3022_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_3019_, v_x_3020_, v_x_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___boxed(lean_object* v_00_u03b2_3023_, lean_object* v_x_3024_, lean_object* v_x_3025_, lean_object* v_x_3026_){
_start:
{
size_t v_x_23003__boxed_3027_; uint8_t v_res_3028_; lean_object* v_r_3029_; 
v_x_23003__boxed_3027_ = lean_unbox_usize(v_x_3025_);
lean_dec(v_x_3025_);
v_res_3028_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(v_00_u03b2_3023_, v_x_3024_, v_x_23003__boxed_3027_, v_x_3026_);
lean_dec_ref(v_x_3026_);
lean_dec_ref(v_x_3024_);
v_r_3029_ = lean_box(v_res_3028_);
return v_r_3029_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(lean_object* v_00_u03b2_3030_, lean_object* v_keys_3031_, lean_object* v_vals_3032_, lean_object* v_heq_3033_, lean_object* v_i_3034_, lean_object* v_k_3035_){
_start:
{
uint8_t v___x_3036_; 
v___x_3036_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_3031_, v_i_3034_, v_k_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___boxed(lean_object* v_00_u03b2_3037_, lean_object* v_keys_3038_, lean_object* v_vals_3039_, lean_object* v_heq_3040_, lean_object* v_i_3041_, lean_object* v_k_3042_){
_start:
{
uint8_t v_res_3043_; lean_object* v_r_3044_; 
v_res_3043_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(v_00_u03b2_3037_, v_keys_3038_, v_vals_3039_, v_heq_3040_, v_i_3041_, v_k_3042_);
lean_dec_ref(v_k_3042_);
lean_dec_ref(v_vals_3039_);
lean_dec_ref(v_keys_3038_);
v_r_3044_ = lean_box(v_res_3043_);
return v_r_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1(){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3052_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3053_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
v___x_3054_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1));
v___x_3055_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___boxed), 4, 0);
v___x_3056_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3052_, v___x_3053_, v___x_3054_, v___x_3055_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___boxed(lean_object* v_a_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
return v_res_3058_;
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
