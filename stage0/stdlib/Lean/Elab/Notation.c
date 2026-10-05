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
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0___redArg();
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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
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
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_evalOptPrio___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1_value;
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
v___x_105_ = l_Array_mkArray0___redArg();
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
uint8_t v___x_7302__boxed_156_; size_t v_sz_boxed_157_; size_t v_i_boxed_158_; lean_object* v_res_159_; 
v___x_7302__boxed_156_ = lean_unbox(v___x_151_);
v_sz_boxed_157_ = lean_unbox_usize(v_sz_153_);
lean_dec(v_sz_153_);
v_i_boxed_158_ = lean_unbox_usize(v_i_154_);
lean_dec(v_i_154_);
v_res_159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(v___x_7302__boxed_156_, v___x_152_, v_sz_boxed_157_, v_i_boxed_158_, v_bs_155_);
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
lean_inc_ref(v___y_305_);
v___x_308_ = l_Array_append___redArg(v___y_305_, v___y_307_);
lean_dec_ref(v___y_307_);
lean_inc(v___y_306_);
lean_inc(v___y_301_);
v___x_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_309_, 0, v___y_301_);
lean_ctor_set(v___x_309_, 1, v___y_306_);
lean_ctor_set(v___x_309_, 2, v___x_308_);
lean_inc(v___y_302_);
v___x_310_ = l_Lean_Syntax_node2(v___y_301_, v___y_302_, v___y_304_, v___x_309_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___y_303_);
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
v___y_301_ = v___x_320_;
v___y_302_ = v___x_321_;
v___y_303_ = v___y_315_;
v___y_304_ = v___x_326_;
v___y_305_ = v___x_328_;
v___y_306_ = v___x_327_;
v___y_307_ = v___x_334_;
goto v___jp_300_;
}
else
{
lean_object* v___x_335_; 
lean_dec(v_prec_x3f_313_);
v___x_335_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_301_ = v___x_320_;
v___y_302_ = v___x_321_;
v___y_303_ = v___y_315_;
v___y_304_ = v___x_326_;
v___y_305_ = v___x_328_;
v___y_306_ = v___x_327_;
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
lean_inc_ref(v_fst_659_);
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
lean_dec(v_head_975_);
lean_dec_ref_known(v_a_974_, 2);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___redArg(size_t v_sz_1333_, size_t v_i_1334_, lean_object* v_bs_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v___x_1337_; 
v___x_1337_ = lean_usize_dec_lt(v_i_1334_, v_sz_1333_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_bs_1335_);
lean_ctor_set(v___x_1338_, 1, v___y_1336_);
return v___x_1338_;
}
else
{
lean_object* v_v_1339_; lean_object* v___x_1340_; 
v_v_1339_ = lean_array_uget_borrowed(v_bs_1335_, v_i_1334_);
lean_inc(v_v_1339_);
v___x_1340_ = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(v_v_1339_, v___y_1336_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v_a_1342_; lean_object* v___x_1343_; lean_object* v_bs_x27_1344_; size_t v___x_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
v_a_1342_ = lean_ctor_get(v___x_1340_, 1);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1340_, 2);
v___x_1343_ = lean_unsigned_to_nat(0u);
v_bs_x27_1344_ = lean_array_uset(v_bs_1335_, v_i_1334_, v___x_1343_);
v___x_1345_ = ((size_t)1ULL);
v___x_1346_ = lean_usize_add(v_i_1334_, v___x_1345_);
v___x_1347_ = lean_array_uset(v_bs_x27_1344_, v_i_1334_, v_a_1341_);
v_i_1334_ = v___x_1346_;
v_bs_1335_ = v___x_1347_;
v___y_1336_ = v_a_1342_;
goto _start;
}
else
{
lean_object* v_a_1349_; lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec_ref(v_bs_1335_);
v_a_1349_ = lean_ctor_get(v___x_1340_, 0);
v_a_1350_ = lean_ctor_get(v___x_1340_, 1);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1340_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_inc(v_a_1349_);
lean_dec(v___x_1340_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1349_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___redArg___boxed(lean_object* v_sz_1358_, lean_object* v_i_1359_, lean_object* v_bs_1360_, lean_object* v___y_1361_){
_start:
{
size_t v_sz_boxed_1362_; size_t v_i_boxed_1363_; lean_object* v_res_1364_; 
v_sz_boxed_1362_ = lean_unbox_usize(v_sz_1358_);
lean_dec(v_sz_1358_);
v_i_boxed_1363_ = lean_unbox_usize(v_i_1359_);
lean_dec(v_i_1359_);
v_res_1364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___redArg(v_sz_boxed_1362_, v_i_boxed_1363_, v_bs_1360_, v___y_1361_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(size_t v_sz_1365_, size_t v_i_1366_, lean_object* v_bs_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___redArg(v_sz_1365_, v_i_1366_, v_bs_1367_, v___y_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed(lean_object* v_sz_1371_, lean_object* v_i_1372_, lean_object* v_bs_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
size_t v_sz_boxed_1376_; size_t v_i_boxed_1377_; lean_object* v_res_1378_; 
v_sz_boxed_1376_ = lean_unbox_usize(v_sz_1371_);
lean_dec(v_sz_1371_);
v_i_boxed_1377_ = lean_unbox_usize(v_i_1372_);
lean_dec(v_i_1372_);
v_res_1378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_boxed_1376_, v_i_boxed_1377_, v_bs_1373_, v___y_1374_, v___y_1375_);
lean_dec_ref(v___y_1374_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(size_t v_sz_1379_, size_t v_i_1380_, lean_object* v_bs_1381_){
_start:
{
uint8_t v___x_1382_; 
v___x_1382_ = lean_usize_dec_lt(v_i_1380_, v_sz_1379_);
if (v___x_1382_ == 0)
{
return v_bs_1381_;
}
else
{
lean_object* v___x_1383_; lean_object* v_v_1384_; lean_object* v_bs_x27_1385_; lean_object* v___x_1386_; size_t v___x_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v___x_1383_ = lean_unsigned_to_nat(0u);
v_v_1384_ = lean_array_uget(v_bs_1381_, v_i_1380_);
v_bs_x27_1385_ = lean_array_uset(v_bs_1381_, v_i_1380_, v___x_1383_);
v___x_1386_ = l_Lean_Syntax_getArg(v_v_1384_, v___x_1383_);
lean_dec(v_v_1384_);
v___x_1387_ = ((size_t)1ULL);
v___x_1388_ = lean_usize_add(v_i_1380_, v___x_1387_);
v___x_1389_ = lean_array_uset(v_bs_x27_1385_, v_i_1380_, v___x_1386_);
v_i_1380_ = v___x_1388_;
v_bs_1381_ = v___x_1389_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed(lean_object* v_sz_1391_, lean_object* v_i_1392_, lean_object* v_bs_1393_){
_start:
{
size_t v_sz_boxed_1394_; size_t v_i_boxed_1395_; lean_object* v_res_1396_; 
v_sz_boxed_1394_ = lean_unbox_usize(v_sz_1391_);
lean_dec(v_sz_1391_);
v_i_boxed_1395_ = lean_unbox_usize(v_i_1392_);
lean_dec(v_i_1392_);
v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(v_sz_boxed_1394_, v_i_boxed_1395_, v_bs_1393_);
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
v___x_1412_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1415_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1416_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_1417_ = lean_unsigned_to_nat(0u);
v___x_1418_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
lean_ctor_set(v___x_1418_, 2, v___x_1417_);
lean_ctor_set(v___x_1418_, 3, v___x_1417_);
lean_ctor_set(v___x_1418_, 4, v___x_1416_);
lean_ctor_set(v___x_1418_, 5, v___x_1416_);
lean_ctor_set(v___x_1418_, 6, v___x_1416_);
lean_ctor_set(v___x_1418_, 7, v___x_1416_);
lean_ctor_set(v___x_1418_, 8, v___x_1416_);
lean_ctor_set(v___x_1418_, 9, v___x_1416_);
lean_ctor_set(v___x_1418_, 10, v___x_1416_);
lean_ctor_set(v___x_1418_, 11, v___x_1415_);
return v___x_1418_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = lean_unsigned_to_nat(32u);
v___x_1420_ = lean_mk_empty_array_with_capacity(v___x_1419_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
return v___x_1421_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4(void){
_start:
{
size_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1422_ = ((size_t)5ULL);
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = lean_unsigned_to_nat(32u);
v___x_1425_ = lean_mk_empty_array_with_capacity(v___x_1424_);
v___x_1426_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3);
v___x_1427_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
lean_ctor_set(v___x_1427_, 1, v___x_1425_);
lean_ctor_set(v___x_1427_, 2, v___x_1423_);
lean_ctor_set(v___x_1427_, 3, v___x_1423_);
lean_ctor_set_usize(v___x_1427_, 4, v___x_1422_);
return v___x_1427_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1428_ = lean_box(1);
v___x_1429_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4);
v___x_1430_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_1431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v___x_1429_);
lean_ctor_set(v___x_1431_, 2, v___x_1428_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; lean_object* v_env_1436_; uint8_t v___x_1437_; lean_object* v_env_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v_scopes_1441_; lean_object* v___x_1442_; lean_object* v_opts_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1435_ = lean_st_ref_get(v___y_1433_);
v_env_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc_ref(v_env_1436_);
lean_dec(v___x_1435_);
v___x_1437_ = 0;
v_env_1438_ = l_Lean_Environment_setRecordingDeps(v_env_1436_, v___x_1437_);
v___x_1439_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1440_ = lean_st_ref_get(v___y_1433_);
v_scopes_1441_ = lean_ctor_get(v___x_1440_, 2);
lean_inc(v_scopes_1441_);
lean_dec(v___x_1440_);
v___x_1442_ = l_List_head_x21___redArg(v___x_1439_, v_scopes_1441_);
lean_dec(v_scopes_1441_);
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
lean_ctor_set(v___x_1447_, 1, v_msgData_1432_);
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
lean_object* v_a_1463_; lean_object* v___x_1464_; lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1513_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v___x_1464_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msg_1458_, v___y_1460_);
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1513_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1513_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v_traceState_1470_; lean_object* v_env_1471_; lean_object* v_messages_1472_; lean_object* v_scopes_1473_; lean_object* v_usedQuotCtxts_1474_; lean_object* v_nextMacroScope_1475_; lean_object* v_maxRecDepth_1476_; lean_object* v_ngen_1477_; lean_object* v_auxDeclNGen_1478_; lean_object* v_infoState_1479_; lean_object* v_snapshotTasks_1480_; lean_object* v_prevLinterStates_1481_; lean_object* v_codeQualityEntryTasks_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1512_; 
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
v_prevLinterStates_1481_ = lean_ctor_get(v___x_1469_, 11);
v_codeQualityEntryTasks_1482_ = lean_ctor_get(v___x_1469_, 12);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1484_ = v___x_1469_;
v_isShared_1485_ = v_isSharedCheck_1512_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1482_);
lean_inc(v_prevLinterStates_1481_);
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
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1512_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
uint64_t v_tid_1486_; lean_object* v_traces_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1511_; 
v_tid_1486_ = lean_ctor_get_uint64(v_traceState_1470_, sizeof(void*)*1);
v_traces_1487_ = lean_ctor_get(v_traceState_1470_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_traceState_1470_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1489_ = v_traceState_1470_;
v_isShared_1490_ = v_isSharedCheck_1511_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_traces_1487_);
lean_dec(v_traceState_1470_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1511_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; double v___x_1493_; uint8_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1491_ = lean_box(0);
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0);
v___x_1494_ = 0;
v___x_1495_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1496_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1496_, 0, v_cls_1457_);
lean_ctor_set(v___x_1496_, 1, v___x_1492_);
lean_ctor_set(v___x_1496_, 2, v___x_1495_);
lean_ctor_set_float(v___x_1496_, sizeof(void*)*3, v___x_1493_);
lean_ctor_set_float(v___x_1496_, sizeof(void*)*3 + 8, v___x_1493_);
lean_ctor_set_uint8(v___x_1496_, sizeof(void*)*3 + 16, v___x_1494_);
v___x_1497_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__1));
v___x_1498_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1496_);
lean_ctor_set(v___x_1498_, 1, v_a_1465_);
lean_ctor_set(v___x_1498_, 2, v___x_1497_);
v___x_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1499_, 0, v_a_1463_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v___x_1500_ = l_Lean_PersistentArray_push___redArg(v_traces_1487_, v___x_1499_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1500_);
v___x_1502_ = v___x_1489_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1500_);
lean_ctor_set_uint64(v_reuseFailAlloc_1510_, sizeof(void*)*1, v_tid_1486_);
v___x_1502_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1504_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 9, v___x_1502_);
v___x_1504_ = v___x_1484_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_env_1471_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_messages_1472_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_scopes_1473_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_usedQuotCtxts_1474_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_nextMacroScope_1475_);
lean_ctor_set(v_reuseFailAlloc_1509_, 5, v_maxRecDepth_1476_);
lean_ctor_set(v_reuseFailAlloc_1509_, 6, v_ngen_1477_);
lean_ctor_set(v_reuseFailAlloc_1509_, 7, v_auxDeclNGen_1478_);
lean_ctor_set(v_reuseFailAlloc_1509_, 8, v_infoState_1479_);
lean_ctor_set(v_reuseFailAlloc_1509_, 9, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1509_, 10, v_snapshotTasks_1480_);
lean_ctor_set(v_reuseFailAlloc_1509_, 11, v_prevLinterStates_1481_);
lean_ctor_set(v_reuseFailAlloc_1509_, 12, v_codeQualityEntryTasks_1482_);
v___x_1504_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1505_ = lean_st_ref_put(v___y_1460_, v___x_1504_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1491_);
v___x_1507_ = v___x_1467_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1491_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref(v_msg_1458_);
lean_dec(v_cls_1457_);
v_a_1514_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1462_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1462_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___boxed(lean_object* v_cls_1522_, lean_object* v_msg_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_1522_, v_msg_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(lean_object* v_as_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
if (lean_obj_tag(v_as_1528_) == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
else
{
lean_object* v_head_1534_; lean_object* v_tail_1535_; lean_object* v_fst_1536_; lean_object* v_snd_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v_scopes_1542_; lean_object* v___x_1543_; lean_object* v_opts_1544_; uint8_t v_hasTrace_1545_; 
v_head_1534_ = lean_ctor_get(v_as_1528_, 0);
lean_inc(v_head_1534_);
v_tail_1535_ = lean_ctor_get(v_as_1528_, 1);
lean_inc(v_tail_1535_);
lean_dec_ref_known(v_as_1528_, 2);
v_fst_1536_ = lean_ctor_get(v_head_1534_, 0);
lean_inc(v_fst_1536_);
v_snd_1537_ = lean_ctor_get(v_head_1534_, 1);
lean_inc(v_snd_1537_);
lean_dec(v_head_1534_);
v___x_1538_ = l_Lean_inheritedTraceOptions;
v___x_1539_ = lean_st_ref_get(v___x_1538_);
v___x_1540_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1541_ = lean_st_ref_get(v___y_1530_);
v_scopes_1542_ = lean_ctor_get(v___x_1541_, 2);
lean_inc(v_scopes_1542_);
lean_dec(v___x_1541_);
v___x_1543_ = l_List_head_x21___redArg(v___x_1540_, v_scopes_1542_);
lean_dec(v_scopes_1542_);
v_opts_1544_ = lean_ctor_get(v___x_1543_, 1);
lean_inc_ref(v_opts_1544_);
lean_dec(v___x_1543_);
v_hasTrace_1545_ = lean_ctor_get_uint8(v_opts_1544_, sizeof(void*)*1);
if (v_hasTrace_1545_ == 0)
{
lean_dec_ref(v_opts_1544_);
lean_dec(v___x_1539_);
lean_dec(v_snd_1537_);
lean_dec(v_fst_1536_);
v_as_1528_ = v_tail_1535_;
goto _start;
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1547_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
lean_inc(v_fst_1536_);
v___x_1548_ = l_Lean_Name_append(v___x_1547_, v_fst_1536_);
v___x_1549_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1539_, v_opts_1544_, v___x_1548_);
lean_dec(v___x_1548_);
lean_dec_ref(v_opts_1544_);
lean_dec(v___x_1539_);
if (v___x_1549_ == 0)
{
lean_dec(v_snd_1537_);
lean_dec(v_fst_1536_);
v_as_1528_ = v_tail_1535_;
goto _start;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1551_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1551_, 0, v_snd_1537_);
v___x_1552_ = l_Lean_MessageData_ofFormat(v___x_1551_);
v___x_1553_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_fst_1536_, v___x_1552_, v___y_1529_, v___y_1530_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_dec_ref_known(v___x_1553_, 1);
v_as_1528_ = v_tail_1535_;
goto _start;
}
else
{
lean_dec(v_tail_1535_);
return v___x_1553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___boxed(lean_object* v_as_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v_as_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(lean_object* v_currNamespace_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_currNamespace_1560_);
lean_ctor_set(v___x_1563_, 1, v___y_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(v_currNamespace_1564_, v___y_1565_, v___y_1566_);
lean_dec_ref(v___y_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(lean_object* v_env_1568_, lean_object* v_opts_1569_, lean_object* v_currNamespace_1570_, lean_object* v_openDecls_1571_, lean_object* v_n_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = l_Lean_ResolveName_resolveGlobalName(v_env_1568_, v_opts_1569_, v_currNamespace_1570_, v_openDecls_1571_, v_n_1572_);
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
lean_ctor_set(v___x_1576_, 1, v___y_1574_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed(lean_object* v_env_1577_, lean_object* v_opts_1578_, lean_object* v_currNamespace_1579_, lean_object* v_openDecls_1580_, lean_object* v_n_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(v_env_1577_, v_opts_1578_, v_currNamespace_1579_, v_openDecls_1580_, v_n_1581_, v___y_1582_, v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec_ref(v_opts_1578_);
return v_res_1584_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_box(1);
v___x_1586_ = l_Lean_MessageData_ofFormat(v___x_1585_);
return v___x_1586_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__2));
v___x_1591_ = l_Lean_MessageData_ofFormat(v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(lean_object* v_x_1592_, lean_object* v_x_1593_){
_start:
{
if (lean_obj_tag(v_x_1593_) == 0)
{
return v_x_1592_;
}
else
{
lean_object* v_head_1594_; lean_object* v_tail_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1617_; 
v_head_1594_ = lean_ctor_get(v_x_1593_, 0);
v_tail_1595_ = lean_ctor_get(v_x_1593_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_x_1593_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1597_ = v_x_1593_;
v_isShared_1598_ = v_isSharedCheck_1617_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_tail_1595_);
lean_inc(v_head_1594_);
lean_dec(v_x_1593_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1617_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v_before_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1615_; 
v_before_1599_ = lean_ctor_get(v_head_1594_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_head_1594_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v_head_1594_, 1);
lean_dec(v_unused_1616_);
v___x_1601_ = v_head_1594_;
v_isShared_1602_ = v_isSharedCheck_1615_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_before_1599_);
lean_dec(v_head_1594_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1615_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0);
if (v_isShared_1602_ == 0)
{
lean_ctor_set_tag(v___x_1601_, 7);
lean_ctor_set(v___x_1601_, 1, v___x_1603_);
lean_ctor_set(v___x_1601_, 0, v_x_1592_);
v___x_1605_ = v___x_1601_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_x_1592_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1606_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3);
if (v_isShared_1598_ == 0)
{
lean_ctor_set_tag(v___x_1597_, 7);
lean_ctor_set(v___x_1597_, 1, v___x_1606_);
lean_ctor_set(v___x_1597_, 0, v___x_1605_);
v___x_1608_ = v___x_1597_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = l_Lean_MessageData_ofSyntax(v_before_1599_);
v___x_1610_ = l_Lean_indentD(v___x_1609_);
v___x_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1608_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v_x_1592_ = v___x_1611_;
v_x_1593_ = v_tail_1595_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(lean_object* v_opts_1618_, lean_object* v_opt_1619_){
_start:
{
lean_object* v_name_1620_; lean_object* v_defValue_1621_; lean_object* v_map_1622_; lean_object* v___x_1623_; 
v_name_1620_ = lean_ctor_get(v_opt_1619_, 0);
v_defValue_1621_ = lean_ctor_get(v_opt_1619_, 1);
v_map_1622_ = lean_ctor_get(v_opts_1618_, 0);
v___x_1623_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1622_, v_name_1620_);
if (lean_obj_tag(v___x_1623_) == 0)
{
uint8_t v___x_1624_; 
v___x_1624_ = lean_unbox(v_defValue_1621_);
return v___x_1624_;
}
else
{
lean_object* v_val_1625_; 
v_val_1625_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_val_1625_);
lean_dec_ref_known(v___x_1623_, 1);
if (lean_obj_tag(v_val_1625_) == 1)
{
uint8_t v_v_1626_; 
v_v_1626_ = lean_ctor_get_uint8(v_val_1625_, 0);
lean_dec_ref_known(v_val_1625_, 0);
return v_v_1626_;
}
else
{
uint8_t v___x_1627_; 
lean_dec(v_val_1625_);
v___x_1627_ = lean_unbox(v_defValue_1621_);
return v___x_1627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25___boxed(lean_object* v_opts_1628_, lean_object* v_opt_1629_){
_start:
{
uint8_t v_res_1630_; lean_object* v_r_1631_; 
v_res_1630_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(v_opts_1628_, v_opt_1629_);
lean_dec_ref(v_opt_1629_);
lean_dec_ref(v_opts_1628_);
v_r_1631_ = lean_box(v_res_1630_);
return v_r_1631_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__1));
v___x_1636_ = l_Lean_MessageData_ofFormat(v___x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(lean_object* v_msgData_1637_, lean_object* v_macroStack_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_scopes_1643_; lean_object* v___x_1644_; lean_object* v_opts_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1641_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1642_ = lean_st_ref_get(v___y_1639_);
v_scopes_1643_ = lean_ctor_get(v___x_1642_, 2);
lean_inc(v_scopes_1643_);
lean_dec(v___x_1642_);
v___x_1644_ = l_List_head_x21___redArg(v___x_1641_, v_scopes_1643_);
lean_dec(v_scopes_1643_);
v_opts_1645_ = lean_ctor_get(v___x_1644_, 1);
lean_inc_ref(v_opts_1645_);
lean_dec(v___x_1644_);
v___x_1646_ = l_Lean_Elab_pp_macroStack;
v___x_1647_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(v_opts_1645_, v___x_1646_);
lean_dec_ref(v_opts_1645_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
lean_dec(v_macroStack_1638_);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v_msgData_1637_);
return v___x_1648_;
}
else
{
if (lean_obj_tag(v_macroStack_1638_) == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_msgData_1637_);
return v___x_1649_;
}
else
{
lean_object* v_head_1650_; lean_object* v_after_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1666_; 
v_head_1650_ = lean_ctor_get(v_macroStack_1638_, 0);
lean_inc(v_head_1650_);
v_after_1651_ = lean_ctor_get(v_head_1650_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_head_1650_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; 
v_unused_1667_ = lean_ctor_get(v_head_1650_, 0);
lean_dec(v_unused_1667_);
v___x_1653_ = v_head_1650_;
v_isShared_1654_ = v_isSharedCheck_1666_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_after_1651_);
lean_dec(v_head_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1666_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0);
if (v_isShared_1654_ == 0)
{
lean_ctor_set_tag(v___x_1653_, 7);
lean_ctor_set(v___x_1653_, 1, v___x_1655_);
lean_ctor_set(v___x_1653_, 0, v_msgData_1637_);
v___x_1657_ = v___x_1653_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_msgData_1637_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v_msgData_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1658_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2);
v___x_1659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = l_Lean_MessageData_ofSyntax(v_after_1651_);
v___x_1661_ = l_Lean_indentD(v___x_1660_);
v_msgData_1662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1662_, 0, v___x_1659_);
lean_ctor_set(v_msgData_1662_, 1, v___x_1661_);
v___x_1663_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(v_msgData_1662_, v_macroStack_1638_);
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
return v___x_1664_;
}
}
}
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
lean_object* v_a_1678_; lean_object* v_macroStack_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v_a_1682_; lean_object* v___x_1683_; lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1692_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref_known(v___x_1677_, 1);
v_macroStack_1679_ = lean_ctor_get(v___y_1674_, 4);
v___x_1680_ = l_Lean_Elab_getBetterRef(v_a_1678_, v_macroStack_1679_);
lean_dec(v_a_1678_);
v___x_1681_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msg_1673_, v___y_1675_);
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref(v___x_1681_);
lean_inc(v_macroStack_1679_);
v___x_1683_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_a_1682_, v_macroStack_1679_, v___y_1675_);
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
lean_ctor_set(v___x_1688_, 0, v___x_1680_);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___lam__0(lean_object* v___x_1848_, lean_object* v_entry_1849_, lean_object* v_s_1850_){
_start:
{
lean_object* v_addEntryFn_1851_; lean_object* v_importedEntries_1852_; lean_object* v_state_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1861_; 
v_addEntryFn_1851_ = lean_ctor_get(v___x_1848_, 3);
lean_inc(v_addEntryFn_1851_);
lean_dec_ref(v___x_1848_);
v_importedEntries_1852_ = lean_ctor_get(v_s_1850_, 0);
v_state_1853_ = lean_ctor_get(v_s_1850_, 1);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_s_1850_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1855_ = v_s_1850_;
v_isShared_1856_ = v_isSharedCheck_1861_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_state_1853_);
lean_inc(v_importedEntries_1852_);
lean_dec(v_s_1850_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1861_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_state_1857_; lean_object* v___x_1859_; 
v_state_1857_ = lean_apply_2(v_addEntryFn_1851_, v_state_1853_, v_entry_1849_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 1, v_state_1857_);
v___x_1859_ = v___x_1855_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_importedEntries_1852_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_state_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(lean_object* v_keys_1862_, lean_object* v_i_1863_, lean_object* v_k_1864_){
_start:
{
lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1865_ = lean_array_get_size(v_keys_1862_);
v___x_1866_ = lean_nat_dec_lt(v_i_1863_, v___x_1865_);
if (v___x_1866_ == 0)
{
lean_dec(v_i_1863_);
return v___x_1866_;
}
else
{
lean_object* v_k_x27_1867_; uint8_t v___x_1868_; 
v_k_x27_1867_ = lean_array_fget_borrowed(v_keys_1862_, v_i_1863_);
v___x_1868_ = l_Lean_instBEqExtraModUse_beq(v_k_1864_, v_k_x27_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_unsigned_to_nat(1u);
v___x_1870_ = lean_nat_add(v_i_1863_, v___x_1869_);
lean_dec(v_i_1863_);
v_i_1863_ = v___x_1870_;
goto _start;
}
else
{
lean_dec(v_i_1863_);
return v___x_1866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg___boxed(lean_object* v_keys_1872_, lean_object* v_i_1873_, lean_object* v_k_1874_){
_start:
{
uint8_t v_res_1875_; lean_object* v_r_1876_; 
v_res_1875_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_1872_, v_i_1873_, v_k_1874_);
lean_dec_ref(v_k_1874_);
lean_dec_ref(v_keys_1872_);
v_r_1876_ = lean_box(v_res_1875_);
return v_r_1876_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(lean_object* v_x_1877_, size_t v_x_1878_, lean_object* v_x_1879_){
_start:
{
if (lean_obj_tag(v_x_1877_) == 0)
{
lean_object* v_es_1880_; lean_object* v___x_1881_; size_t v___x_1882_; size_t v___x_1883_; lean_object* v_j_1884_; lean_object* v___x_1885_; 
v_es_1880_ = lean_ctor_get(v_x_1877_, 0);
v___x_1881_ = lean_box(2);
v___x_1882_ = ((size_t)31ULL);
v___x_1883_ = lean_usize_land(v_x_1878_, v___x_1882_);
v_j_1884_ = lean_usize_to_nat(v___x_1883_);
v___x_1885_ = lean_array_get_borrowed(v___x_1881_, v_es_1880_, v_j_1884_);
lean_dec(v_j_1884_);
switch(lean_obj_tag(v___x_1885_))
{
case 0:
{
lean_object* v_key_1886_; uint8_t v___x_1887_; 
v_key_1886_ = lean_ctor_get(v___x_1885_, 0);
v___x_1887_ = l_Lean_instBEqExtraModUse_beq(v_x_1879_, v_key_1886_);
return v___x_1887_;
}
case 1:
{
lean_object* v_node_1888_; size_t v___x_1889_; size_t v___x_1890_; 
v_node_1888_ = lean_ctor_get(v___x_1885_, 0);
v___x_1889_ = ((size_t)5ULL);
v___x_1890_ = lean_usize_shift_right(v_x_1878_, v___x_1889_);
v_x_1877_ = v_node_1888_;
v_x_1878_ = v___x_1890_;
goto _start;
}
default: 
{
uint8_t v___x_1892_; 
v___x_1892_ = 0;
return v___x_1892_;
}
}
}
else
{
lean_object* v_ks_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v_ks_1893_ = lean_ctor_get(v_x_1877_, 0);
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_ks_1893_, v___x_1894_, v_x_1879_);
return v___x_1895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___boxed(lean_object* v_x_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_){
_start:
{
size_t v_x_21164__boxed_1899_; uint8_t v_res_1900_; lean_object* v_r_1901_; 
v_x_21164__boxed_1899_ = lean_unbox_usize(v_x_1897_);
lean_dec(v_x_1897_);
v_res_1900_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_1896_, v_x_21164__boxed_1899_, v_x_1898_);
lean_dec_ref(v_x_1898_);
lean_dec_ref(v_x_1896_);
v_r_1901_ = lean_box(v_res_1900_);
return v_r_1901_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(lean_object* v_x_1902_, lean_object* v_x_1903_){
_start:
{
uint64_t v___x_1904_; size_t v___x_1905_; uint8_t v___x_1906_; 
v___x_1904_ = l_Lean_instHashableExtraModUse_hash(v_x_1903_);
v___x_1905_ = lean_uint64_to_usize(v___x_1904_);
v___x_1906_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_1902_, v___x_1905_, v_x_1903_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg___boxed(lean_object* v_x_1907_, lean_object* v_x_1908_){
_start:
{
uint8_t v_res_1909_; lean_object* v_r_1910_; 
v_res_1909_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_1907_, v_x_1908_);
lean_dec_ref(v_x_1908_);
lean_dec_ref(v_x_1907_);
v_r_1910_ = lean_box(v_res_1909_);
return v_r_1910_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1911_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__3));
v___x_1917_ = l_Lean_stringToMessageData(v___x_1916_);
return v___x_1917_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5));
v___x_1920_ = l_Lean_stringToMessageData(v___x_1919_);
return v___x_1920_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7(void){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1922_ = l_Lean_stringToMessageData(v___x_1921_);
return v___x_1922_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8(void){
_start:
{
lean_object* v_cls_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_cls_1923_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2));
v___x_1924_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
v___x_1925_ = l_Lean_Name_append(v___x_1924_, v_cls_1923_);
return v___x_1925_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9));
v___x_1928_ = l_Lean_stringToMessageData(v___x_1927_);
return v___x_1928_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11));
v___x_1931_ = l_Lean_stringToMessageData(v___x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(lean_object* v_mod_1936_, uint8_t v_isMeta_1937_, lean_object* v_hint_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v_env_1963_; uint8_t v_isExporting_1964_; lean_object* v_entry_1965_; lean_object* v___x_1966_; lean_object* v_env_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1961_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0);
v___x_1962_ = lean_st_ref_get(v___y_1940_);
v_env_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc_ref(v_env_1963_);
lean_dec(v___x_1962_);
v_isExporting_1964_ = lean_ctor_get_uint8(v_env_1963_, sizeof(void*)*13);
lean_dec_ref(v_env_1963_);
lean_inc(v_mod_1936_);
v_entry_1965_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1965_, 0, v_mod_1936_);
lean_ctor_set_uint8(v_entry_1965_, sizeof(void*)*1, v_isExporting_1964_);
lean_ctor_set_uint8(v_entry_1965_, sizeof(void*)*1 + 1, v_isMeta_1937_);
v___x_1966_ = lean_st_ref_get(v___y_1940_);
v_env_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc_ref(v_env_1967_);
lean_dec(v___x_1966_);
v___x_1968_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1969_ = lean_box(1);
v___x_1970_ = lean_box(0);
v___x_1971_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1961_, v___x_1968_, v_env_1967_, v___x_1969_, v___x_1970_);
v___x_1972_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v___x_1971_, v_entry_1965_);
lean_dec(v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___f_1973_; uint8_t v___x_1974_; lean_object* v___y_1976_; lean_object* v_cls_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v_scopes_2022_; lean_object* v___x_2023_; lean_object* v_opts_2024_; uint8_t v_hasTrace_2025_; 
v___f_1973_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___lam__0), 3, 2);
lean_closure_set(v___f_1973_, 0, v___x_1968_);
lean_closure_set(v___f_1973_, 1, v_entry_1965_);
v___x_1974_ = 1;
v_cls_1998_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2));
v___x_1999_ = l_Lean_inheritedTraceOptions;
v___x_2000_ = lean_st_ref_get(v___x_1999_);
v___x_2001_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2002_ = lean_st_ref_get(v___y_1940_);
v_scopes_2022_ = lean_ctor_get(v___x_2002_, 2);
lean_inc(v_scopes_2022_);
lean_dec(v___x_2002_);
v___x_2023_ = l_List_head_x21___redArg(v___x_2001_, v_scopes_2022_);
lean_dec(v_scopes_2022_);
v_opts_2024_ = lean_ctor_get(v___x_2023_, 1);
lean_inc_ref(v_opts_2024_);
lean_dec(v___x_2023_);
v_hasTrace_2025_ = lean_ctor_get_uint8(v_opts_2024_, sizeof(void*)*1);
if (v_hasTrace_2025_ == 0)
{
lean_dec_ref(v_opts_2024_);
lean_dec(v___x_2000_);
lean_dec(v_hint_1938_);
lean_dec(v_mod_1936_);
v___y_1976_ = v___y_1940_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8);
v___x_2027_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2000_, v_opts_2024_, v___x_2026_);
lean_dec_ref(v_opts_2024_);
lean_dec(v___x_2000_);
if (v___x_2027_ == 0)
{
lean_dec(v_hint_1938_);
lean_dec(v_mod_1936_);
v___y_1976_ = v___y_1940_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2028_; lean_object* v___y_2030_; 
v___x_2028_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10);
if (v_isExporting_1964_ == 0)
{
lean_object* v___x_2037_; 
v___x_2037_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15));
v___y_2030_ = v___x_2037_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2038_; 
v___x_2038_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16));
v___y_2030_ = v___x_2038_;
goto v___jp_2029_;
}
v___jp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_inc_ref(v___y_2030_);
v___x_2031_ = l_Lean_stringToMessageData(v___y_2030_);
v___x_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2028_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12);
v___x_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
if (v_isMeta_1937_ == 0)
{
lean_object* v___x_2035_; 
v___x_2035_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13));
v___y_2009_ = v___x_2034_;
v___y_2010_ = v___x_2035_;
goto v___jp_2008_;
}
else
{
lean_object* v___x_2036_; 
v___x_2036_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14));
v___y_2009_ = v___x_2034_;
v___y_2010_ = v___x_2036_;
goto v___jp_2008_;
}
}
}
}
v___jp_1975_:
{
lean_object* v___x_1977_; lean_object* v_toEnvExtension_1978_; lean_object* v_env_1979_; lean_object* v_messages_1980_; lean_object* v_scopes_1981_; lean_object* v_usedQuotCtxts_1982_; lean_object* v_nextMacroScope_1983_; lean_object* v_maxRecDepth_1984_; lean_object* v_ngen_1985_; lean_object* v_auxDeclNGen_1986_; lean_object* v_infoState_1987_; lean_object* v_traceState_1988_; lean_object* v_snapshotTasks_1989_; lean_object* v_prevLinterStates_1990_; lean_object* v_codeQualityEntryTasks_1991_; lean_object* v_asyncMode_1992_; uint8_t v_logWrites_1993_; lean_object* v___x_1994_; 
v___x_1977_ = lean_st_ref_take(v___y_1976_);
v_toEnvExtension_1978_ = lean_ctor_get(v___x_1968_, 0);
v_env_1979_ = lean_ctor_get(v___x_1977_, 0);
lean_inc_ref(v_env_1979_);
v_messages_1980_ = lean_ctor_get(v___x_1977_, 1);
lean_inc_ref(v_messages_1980_);
v_scopes_1981_ = lean_ctor_get(v___x_1977_, 2);
lean_inc(v_scopes_1981_);
v_usedQuotCtxts_1982_ = lean_ctor_get(v___x_1977_, 3);
lean_inc(v_usedQuotCtxts_1982_);
v_nextMacroScope_1983_ = lean_ctor_get(v___x_1977_, 4);
lean_inc(v_nextMacroScope_1983_);
v_maxRecDepth_1984_ = lean_ctor_get(v___x_1977_, 5);
lean_inc(v_maxRecDepth_1984_);
v_ngen_1985_ = lean_ctor_get(v___x_1977_, 6);
lean_inc_ref(v_ngen_1985_);
v_auxDeclNGen_1986_ = lean_ctor_get(v___x_1977_, 7);
lean_inc_ref(v_auxDeclNGen_1986_);
v_infoState_1987_ = lean_ctor_get(v___x_1977_, 8);
lean_inc_ref(v_infoState_1987_);
v_traceState_1988_ = lean_ctor_get(v___x_1977_, 9);
lean_inc_ref(v_traceState_1988_);
v_snapshotTasks_1989_ = lean_ctor_get(v___x_1977_, 10);
lean_inc_ref(v_snapshotTasks_1989_);
v_prevLinterStates_1990_ = lean_ctor_get(v___x_1977_, 11);
lean_inc(v_prevLinterStates_1990_);
v_codeQualityEntryTasks_1991_ = lean_ctor_get(v___x_1977_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1991_);
lean_dec(v___x_1977_);
v_asyncMode_1992_ = lean_ctor_get(v_toEnvExtension_1978_, 2);
v_logWrites_1993_ = lean_ctor_get_uint8(v_toEnvExtension_1978_, sizeof(void*)*6);
v___x_1994_ = lean_box(0);
if (v_logWrites_1993_ == 0)
{
lean_object* v___x_1995_; 
lean_inc_ref(v_toEnvExtension_1978_);
v___x_1995_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1978_, v_env_1979_, v___f_1973_, v_asyncMode_1992_, v___x_1970_, v___x_1974_);
v___y_1943_ = v_prevLinterStates_1990_;
v___y_1944_ = v_messages_1980_;
v___y_1945_ = v_scopes_1981_;
v___y_1946_ = v_codeQualityEntryTasks_1991_;
v___y_1947_ = v___y_1976_;
v___y_1948_ = v_traceState_1988_;
v___y_1949_ = v_maxRecDepth_1984_;
v___y_1950_ = v_nextMacroScope_1983_;
v___y_1951_ = v_auxDeclNGen_1986_;
v___y_1952_ = v_snapshotTasks_1989_;
v___y_1953_ = v_ngen_1985_;
v___y_1954_ = v___x_1994_;
v___y_1955_ = v_usedQuotCtxts_1982_;
v___y_1956_ = v_infoState_1987_;
v___y_1957_ = v___x_1995_;
goto v___jp_1942_;
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_inc_ref_n(v_toEnvExtension_1978_, 2);
v___x_1996_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1978_, v_env_1979_);
lean_dec_ref(v_env_1979_);
v___x_1997_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1978_, v___x_1996_, v___f_1973_, v_asyncMode_1992_, v___x_1970_, v___x_1974_);
v___y_1943_ = v_prevLinterStates_1990_;
v___y_1944_ = v_messages_1980_;
v___y_1945_ = v_scopes_1981_;
v___y_1946_ = v_codeQualityEntryTasks_1991_;
v___y_1947_ = v___y_1976_;
v___y_1948_ = v_traceState_1988_;
v___y_1949_ = v_maxRecDepth_1984_;
v___y_1950_ = v_nextMacroScope_1983_;
v___y_1951_ = v_auxDeclNGen_1986_;
v___y_1952_ = v_snapshotTasks_1989_;
v___y_1953_ = v_ngen_1985_;
v___y_1954_ = v___x_1994_;
v___y_1955_ = v_usedQuotCtxts_1982_;
v___y_1956_ = v_infoState_1987_;
v___y_1957_ = v___x_1997_;
goto v___jp_1942_;
}
}
v___jp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___y_2004_);
lean_ctor_set(v___x_2006_, 1, v___y_2005_);
v___x_2007_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_1998_, v___x_2006_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_dec_ref_known(v___x_2007_, 1);
v___y_1976_ = v___y_1940_;
goto v___jp_1975_;
}
else
{
lean_dec_ref(v___f_1973_);
return v___x_2007_;
}
}
v___jp_2008_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
lean_inc_ref(v___y_2010_);
v___x_2011_ = l_Lean_stringToMessageData(v___y_2010_);
v___x_2012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___y_2009_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4);
v___x_2014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2012_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = l_Lean_MessageData_ofName(v_mod_1936_);
v___x_2016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2014_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = l_Lean_Name_isAnonymous(v_hint_1938_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6);
v___x_2019_ = l_Lean_MessageData_ofName(v_hint_1938_);
v___x_2020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2018_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___y_2004_ = v___x_2016_;
v___y_2005_ = v___x_2020_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2021_; 
lean_dec(v_hint_1938_);
v___x_2021_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7);
v___y_2004_ = v___x_2016_;
v___y_2005_ = v___x_2021_;
goto v___jp_2003_;
}
}
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec_ref_known(v_entry_1965_, 1);
lean_dec(v_hint_1938_);
lean_dec(v_mod_1936_);
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
return v___x_2040_;
}
v___jp_1942_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1958_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1958_, 0, v___y_1957_);
lean_ctor_set(v___x_1958_, 1, v___y_1944_);
lean_ctor_set(v___x_1958_, 2, v___y_1945_);
lean_ctor_set(v___x_1958_, 3, v___y_1955_);
lean_ctor_set(v___x_1958_, 4, v___y_1950_);
lean_ctor_set(v___x_1958_, 5, v___y_1949_);
lean_ctor_set(v___x_1958_, 6, v___y_1953_);
lean_ctor_set(v___x_1958_, 7, v___y_1951_);
lean_ctor_set(v___x_1958_, 8, v___y_1956_);
lean_ctor_set(v___x_1958_, 9, v___y_1948_);
lean_ctor_set(v___x_1958_, 10, v___y_1952_);
lean_ctor_set(v___x_1958_, 11, v___y_1943_);
lean_ctor_set(v___x_1958_, 12, v___y_1946_);
v___x_1959_ = lean_st_ref_put(v___y_1947_, v___x_1958_);
v___x_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1960_, 0, v___y_1954_);
return v___x_1960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___boxed(lean_object* v_mod_2041_, lean_object* v_isMeta_2042_, lean_object* v_hint_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
uint8_t v_isMeta_boxed_2047_; lean_object* v_res_2048_; 
v_isMeta_boxed_2047_ = lean_unbox(v_isMeta_2042_);
v_res_2048_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_mod_2041_, v_isMeta_boxed_2047_, v_hint_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(lean_object* v___x_2049_, lean_object* v_declName_2050_, lean_object* v_as_2051_, size_t v_sz_2052_, size_t v_i_2053_, lean_object* v_b_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
uint8_t v___x_2058_; 
v___x_2058_ = lean_usize_dec_lt(v_i_2053_, v_sz_2052_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; 
lean_dec(v_declName_2050_);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v_b_2054_);
return v___x_2059_;
}
else
{
lean_object* v___x_2060_; lean_object* v_modules_2061_; lean_object* v___x_2062_; lean_object* v_a_2063_; lean_object* v___x_2064_; lean_object* v_toImport_2065_; lean_object* v_module_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; lean_object* v___x_2069_; 
v___x_2060_ = l_Lean_Environment_header(v___x_2049_);
v_modules_2061_ = lean_ctor_get(v___x_2060_, 3);
lean_inc_ref(v_modules_2061_);
lean_dec_ref(v___x_2060_);
v___x_2062_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2063_ = lean_array_uget_borrowed(v_as_2051_, v_i_2053_);
v___x_2064_ = lean_array_get(v___x_2062_, v_modules_2061_, v_a_2063_);
lean_dec_ref(v_modules_2061_);
v_toImport_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc_ref(v_toImport_2065_);
lean_dec(v___x_2064_);
v_module_2066_ = lean_ctor_get(v_toImport_2065_, 0);
lean_inc(v_module_2066_);
lean_dec_ref(v_toImport_2065_);
v___x_2067_ = lean_box(0);
v___x_2068_ = 0;
lean_inc(v_declName_2050_);
v___x_2069_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_module_2066_, v___x_2068_, v_declName_2050_, v___y_2055_, v___y_2056_);
if (lean_obj_tag(v___x_2069_) == 0)
{
size_t v___x_2070_; size_t v___x_2071_; 
lean_dec_ref_known(v___x_2069_, 1);
v___x_2070_ = ((size_t)1ULL);
v___x_2071_ = lean_usize_add(v_i_2053_, v___x_2070_);
v_i_2053_ = v___x_2071_;
v_b_2054_ = v___x_2067_;
goto _start;
}
else
{
lean_dec(v_declName_2050_);
return v___x_2069_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7___boxed(lean_object* v___x_2073_, lean_object* v_declName_2074_, lean_object* v_as_2075_, lean_object* v_sz_2076_, lean_object* v_i_2077_, lean_object* v_b_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
size_t v_sz_boxed_2082_; size_t v_i_boxed_2083_; lean_object* v_res_2084_; 
v_sz_boxed_2082_ = lean_unbox_usize(v_sz_2076_);
lean_dec(v_sz_2076_);
v_i_boxed_2083_ = lean_unbox_usize(v_i_2077_);
lean_dec(v_i_2077_);
v_res_2084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v___x_2073_, v_declName_2074_, v_as_2075_, v_sz_boxed_2082_, v_i_boxed_2083_, v_b_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec_ref(v_as_2075_);
lean_dec_ref(v___x_2073_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(lean_object* v_a_2085_, lean_object* v_x_2086_){
_start:
{
if (lean_obj_tag(v_x_2086_) == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_box(0);
return v___x_2087_;
}
else
{
lean_object* v_key_2088_; lean_object* v_value_2089_; lean_object* v_tail_2090_; uint8_t v___x_2091_; 
v_key_2088_ = lean_ctor_get(v_x_2086_, 0);
v_value_2089_ = lean_ctor_get(v_x_2086_, 1);
v_tail_2090_ = lean_ctor_get(v_x_2086_, 2);
v___x_2091_ = lean_name_eq(v_key_2088_, v_a_2085_);
if (v___x_2091_ == 0)
{
v_x_2086_ = v_tail_2090_;
goto _start;
}
else
{
lean_object* v___x_2093_; 
lean_inc(v_value_2089_);
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_value_2089_);
return v___x_2093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg___boxed(lean_object* v_a_2094_, lean_object* v_x_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_2094_, v_x_2095_);
lean_dec(v_x_2095_);
lean_dec(v_a_2094_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(lean_object* v_m_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v_buckets_2099_; lean_object* v___x_2100_; uint64_t v___y_2102_; 
v_buckets_2099_ = lean_ctor_get(v_m_2097_, 1);
v___x_2100_ = lean_array_get_size(v_buckets_2099_);
if (lean_obj_tag(v_a_2098_) == 0)
{
uint64_t v___x_2116_; 
v___x_2116_ = 1723ULL;
v___y_2102_ = v___x_2116_;
goto v___jp_2101_;
}
else
{
uint64_t v_hash_2117_; 
v_hash_2117_ = lean_ctor_get_uint64(v_a_2098_, sizeof(void*)*2);
v___y_2102_ = v_hash_2117_;
goto v___jp_2101_;
}
v___jp_2101_:
{
uint64_t v___x_2103_; uint64_t v___x_2104_; uint64_t v_fold_2105_; uint64_t v___x_2106_; uint64_t v___x_2107_; uint64_t v___x_2108_; size_t v___x_2109_; size_t v___x_2110_; size_t v___x_2111_; size_t v___x_2112_; size_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2103_ = 32ULL;
v___x_2104_ = lean_uint64_shift_right(v___y_2102_, v___x_2103_);
v_fold_2105_ = lean_uint64_xor(v___y_2102_, v___x_2104_);
v___x_2106_ = 16ULL;
v___x_2107_ = lean_uint64_shift_right(v_fold_2105_, v___x_2106_);
v___x_2108_ = lean_uint64_xor(v_fold_2105_, v___x_2107_);
v___x_2109_ = lean_uint64_to_usize(v___x_2108_);
v___x_2110_ = lean_usize_of_nat(v___x_2100_);
v___x_2111_ = ((size_t)1ULL);
v___x_2112_ = lean_usize_sub(v___x_2110_, v___x_2111_);
v___x_2113_ = lean_usize_land(v___x_2109_, v___x_2112_);
v___x_2114_ = lean_array_uget_borrowed(v_buckets_2099_, v___x_2113_);
v___x_2115_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_2098_, v___x_2114_);
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_m_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v_m_2118_, v_a_2119_);
lean_dec(v_a_2119_);
lean_dec_ref(v_m_2118_);
return v_res_2120_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(lean_object* v_declName_2124_, uint8_t v_isMeta_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v_env_2134_; lean_object* v___y_2136_; lean_object* v___x_2149_; 
v___x_2129_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0);
v___x_2130_ = lean_st_ref_get(v___y_2127_);
v_env_2134_ = lean_ctor_get(v___x_2130_, 0);
lean_inc_ref(v_env_2134_);
lean_dec(v___x_2130_);
v___x_2149_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2134_, v_declName_2124_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_dec_ref(v_env_2134_);
lean_dec(v_declName_2124_);
goto v___jp_2131_;
}
else
{
lean_object* v_val_2150_; lean_object* v___x_2151_; lean_object* v_modules_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
v_val_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_val_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2151_ = l_Lean_Environment_header(v_env_2134_);
v_modules_2152_ = lean_ctor_get(v___x_2151_, 3);
lean_inc_ref(v_modules_2152_);
lean_dec_ref(v___x_2151_);
v___x_2153_ = lean_array_get_size(v_modules_2152_);
v___x_2154_ = lean_nat_dec_lt(v_val_2150_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_dec_ref(v_modules_2152_);
lean_dec(v_val_2150_);
lean_dec_ref(v_env_2134_);
lean_dec(v_declName_2124_);
goto v___jp_2131_;
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; uint8_t v___y_2158_; 
v___x_2155_ = lean_array_fget(v_modules_2152_, v_val_2150_);
lean_dec(v_val_2150_);
lean_dec_ref(v_modules_2152_);
v___x_2156_ = lean_st_ref_get(v___y_2127_);
if (v_isMeta_2125_ == 0)
{
lean_dec(v___x_2156_);
v___y_2158_ = v_isMeta_2125_;
goto v___jp_2157_;
}
else
{
lean_object* v_env_2169_; uint8_t v___x_2170_; 
v_env_2169_ = lean_ctor_get(v___x_2156_, 0);
lean_inc_ref(v_env_2169_);
lean_dec(v___x_2156_);
lean_inc(v_declName_2124_);
v___x_2170_ = l_Lean_isMarkedMeta(v_env_2169_, v_declName_2124_);
if (v___x_2170_ == 0)
{
v___y_2158_ = v_isMeta_2125_;
goto v___jp_2157_;
}
else
{
uint8_t v___x_2171_; 
v___x_2171_ = 0;
v___y_2158_ = v___x_2171_;
goto v___jp_2157_;
}
}
v___jp_2157_:
{
lean_object* v_toImport_2159_; lean_object* v_module_2160_; lean_object* v___x_2161_; 
v_toImport_2159_ = lean_ctor_get(v___x_2155_, 0);
lean_inc_ref(v_toImport_2159_);
lean_dec(v___x_2155_);
v_module_2160_ = lean_ctor_get(v_toImport_2159_, 0);
lean_inc(v_module_2160_);
lean_dec_ref(v_toImport_2159_);
lean_inc(v_declName_2124_);
v___x_2161_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_module_2160_, v___y_2158_, v_declName_2124_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec_ref_known(v___x_2161_, 1);
v___x_2162_ = l_Lean_indirectModUseExt;
v___x_2163_ = lean_box(1);
v___x_2164_ = lean_box(0);
lean_inc_ref(v_env_2134_);
v___x_2165_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2129_, v___x_2162_, v_env_2134_, v___x_2163_, v___x_2164_);
v___x_2166_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v___x_2165_, v_declName_2124_);
lean_dec(v___x_2165_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v___x_2167_; 
v___x_2167_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1));
v___y_2136_ = v___x_2167_;
goto v___jp_2135_;
}
else
{
lean_object* v_val_2168_; 
v_val_2168_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_val_2168_);
lean_dec_ref_known(v___x_2166_, 1);
v___y_2136_ = v_val_2168_;
goto v___jp_2135_;
}
}
else
{
lean_dec_ref(v_env_2134_);
lean_dec(v_declName_2124_);
return v___x_2161_;
}
}
}
}
v___jp_2131_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = lean_box(0);
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
return v___x_2133_;
}
v___jp_2135_:
{
lean_object* v___x_2137_; size_t v_sz_2138_; size_t v___x_2139_; lean_object* v___x_2140_; 
v___x_2137_ = lean_box(0);
v_sz_2138_ = lean_array_size(v___y_2136_);
v___x_2139_ = ((size_t)0ULL);
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v_env_2134_, v_declName_2124_, v___y_2136_, v_sz_2138_, v___x_2139_, v___x_2137_, v___y_2126_, v___y_2127_);
lean_dec_ref(v___y_2136_);
lean_dec_ref(v_env_2134_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; 
v_unused_2148_ = lean_ctor_get(v___x_2140_, 0);
lean_dec(v_unused_2148_);
v___x_2142_ = v___x_2140_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_dec(v___x_2140_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2137_);
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2137_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
else
{
return v___x_2140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___boxed(lean_object* v_declName_2172_, lean_object* v_isMeta_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
uint8_t v_isMeta_boxed_2177_; lean_object* v_res_2178_; 
v_isMeta_boxed_2177_ = lean_unbox(v_isMeta_2173_);
v_res_2178_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_declName_2172_, v_isMeta_boxed_2177_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(lean_object* v_as_x27_2179_, lean_object* v_b_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
if (lean_obj_tag(v_as_x27_2179_) == 0)
{
lean_object* v___x_2184_; 
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v_b_2180_);
return v___x_2184_;
}
else
{
lean_object* v_head_2185_; lean_object* v_tail_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; lean_object* v___x_2189_; 
v_head_2185_ = lean_ctor_get(v_as_x27_2179_, 0);
v_tail_2186_ = lean_ctor_get(v_as_x27_2179_, 1);
v___x_2187_ = lean_box(0);
v___x_2188_ = 1;
lean_inc(v_head_2185_);
v___x_2189_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_head_2185_, v___x_2188_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_dec_ref_known(v___x_2189_, 1);
v_as_x27_2179_ = v_tail_2186_;
v_b_2180_ = v___x_2187_;
goto _start;
}
else
{
return v___x_2189_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2191_, lean_object* v_b_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_2191_, v_b_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v_as_x27_2191_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(lean_object* v_x_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v___x_2202_; lean_object* v_env_2203_; lean_object* v___f_2204_; lean_object* v___f_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v_scopes_2208_; lean_object* v___x_2209_; lean_object* v_opts_2210_; lean_object* v___x_2211_; 
v___x_2202_ = lean_st_ref_get(v___y_2200_);
v_env_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc_ref_n(v_env_2203_, 3);
lean_dec(v___x_2202_);
v___f_2204_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2204_, 0, v_env_2203_);
v___f_2205_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2205_, 0, v_env_2203_);
v___x_2206_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2207_ = lean_st_ref_get(v___y_2200_);
v_scopes_2208_ = lean_ctor_get(v___x_2207_, 2);
lean_inc(v_scopes_2208_);
lean_dec(v___x_2207_);
v___x_2209_ = l_List_head_x21___redArg(v___x_2206_, v_scopes_2208_);
lean_dec(v_scopes_2208_);
v_opts_2210_ = lean_ctor_get(v___x_2209_, 1);
lean_inc_ref(v_opts_2210_);
lean_dec(v___x_2209_);
v___x_2211_ = l_Lean_Elab_Command_getScope___redArg(v___y_2200_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v_currNamespace_2213_; lean_object* v___f_2214_; lean_object* v___x_2215_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
lean_dec_ref_known(v___x_2211_, 1);
v_currNamespace_2213_ = lean_ctor_get(v_a_2212_, 2);
lean_inc_n(v_currNamespace_2213_, 2);
lean_dec(v_a_2212_);
v___f_2214_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2214_, 0, v_currNamespace_2213_);
v___x_2215_ = l_Lean_Elab_Command_getScope___redArg(v___y_2200_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v_openDecls_2217_; lean_object* v___f_2218_; lean_object* v___f_2219_; lean_object* v_methods_2220_; lean_object* v___x_2221_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v_openDecls_2217_ = lean_ctor_get(v_a_2216_, 3);
lean_inc_n(v_openDecls_2217_, 2);
lean_dec(v_a_2216_);
lean_inc(v_currNamespace_2213_);
lean_inc_ref(v_env_2203_);
v___f_2218_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2218_, 0, v_env_2203_);
lean_closure_set(v___f_2218_, 1, v_currNamespace_2213_);
lean_closure_set(v___f_2218_, 2, v_openDecls_2217_);
v___f_2219_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2219_, 0, v_env_2203_);
lean_closure_set(v___f_2219_, 1, v_opts_2210_);
lean_closure_set(v___f_2219_, 2, v_currNamespace_2213_);
lean_closure_set(v___f_2219_, 3, v_openDecls_2217_);
v_methods_2220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2220_, 0, v___f_2205_);
lean_ctor_set(v_methods_2220_, 1, v___f_2214_);
lean_ctor_set(v_methods_2220_, 2, v___f_2204_);
lean_ctor_set(v_methods_2220_, 3, v___f_2218_);
lean_ctor_set(v_methods_2220_, 4, v___f_2219_);
v___x_2221_ = l_Lean_Elab_Command_getRef___redArg(v___y_2199_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2223_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
v___x_2223_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2199_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v_currRecDepth_2225_; lean_object* v_quotContext_x3f_2226_; lean_object* v_a_2228_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2223_, 1);
v_currRecDepth_2225_ = lean_ctor_get(v___y_2199_, 2);
v_quotContext_x3f_2226_ = lean_ctor_get(v___y_2199_, 5);
if (lean_obj_tag(v_quotContext_x3f_2226_) == 0)
{
lean_object* v___x_2302_; lean_object* v_a_2303_; 
v___x_2302_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2200_);
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref(v___x_2302_);
v_a_2228_ = v_a_2303_;
goto v___jp_2227_;
}
else
{
lean_object* v_val_2304_; 
v_val_2304_ = lean_ctor_get(v_quotContext_x3f_2226_, 0);
lean_inc(v_val_2304_);
v_a_2228_ = v_val_2304_;
goto v___jp_2227_;
}
v___jp_2227_:
{
lean_object* v___x_2229_; lean_object* v_maxRecDepth_2230_; lean_object* v___x_2231_; lean_object* v_nextMacroScope_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2229_ = lean_st_ref_get(v___y_2200_);
v_maxRecDepth_2230_ = lean_ctor_get(v___x_2229_, 5);
lean_inc(v_maxRecDepth_2230_);
lean_dec(v___x_2229_);
v___x_2231_ = lean_st_ref_get(v___y_2200_);
v_nextMacroScope_2232_ = lean_ctor_get(v___x_2231_, 4);
lean_inc(v_nextMacroScope_2232_);
lean_dec(v___x_2231_);
lean_inc(v_currRecDepth_2225_);
v___x_2233_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2233_, 0, v_methods_2220_);
lean_ctor_set(v___x_2233_, 1, v_a_2228_);
lean_ctor_set(v___x_2233_, 2, v_a_2224_);
lean_ctor_set(v___x_2233_, 3, v_currRecDepth_2225_);
lean_ctor_set(v___x_2233_, 4, v_maxRecDepth_2230_);
lean_ctor_set(v___x_2233_, 5, v_a_2222_);
v___x_2234_ = lean_box(0);
v___x_2235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2235_, 0, v_nextMacroScope_2232_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
lean_ctor_set(v___x_2235_, 2, v___x_2234_);
v___x_2236_ = lean_apply_2(v_x_2198_, v___x_2233_, v___x_2235_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v_a_2238_; lean_object* v_macroScope_2239_; lean_object* v_traceMsgs_2240_; lean_object* v_expandedMacroDecls_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 1);
lean_inc(v_a_2237_);
v_a_2238_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2236_, 2);
v_macroScope_2239_ = lean_ctor_get(v_a_2237_, 0);
lean_inc(v_macroScope_2239_);
v_traceMsgs_2240_ = lean_ctor_get(v_a_2237_, 1);
lean_inc(v_traceMsgs_2240_);
v_expandedMacroDecls_2241_ = lean_ctor_get(v_a_2237_, 2);
lean_inc(v_expandedMacroDecls_2241_);
lean_dec(v_a_2237_);
v___x_2242_ = lean_box(0);
v___x_2243_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_expandedMacroDecls_2241_, v___x_2242_, v___y_2199_, v___y_2200_);
lean_dec(v_expandedMacroDecls_2241_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v___x_2244_; lean_object* v_env_2245_; lean_object* v_messages_2246_; lean_object* v_scopes_2247_; lean_object* v_usedQuotCtxts_2248_; lean_object* v_maxRecDepth_2249_; lean_object* v_ngen_2250_; lean_object* v_auxDeclNGen_2251_; lean_object* v_infoState_2252_; lean_object* v_traceState_2253_; lean_object* v_snapshotTasks_2254_; lean_object* v_prevLinterStates_2255_; lean_object* v_codeQualityEntryTasks_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2282_; 
lean_dec_ref_known(v___x_2243_, 1);
v___x_2244_ = lean_st_ref_take(v___y_2200_);
v_env_2245_ = lean_ctor_get(v___x_2244_, 0);
v_messages_2246_ = lean_ctor_get(v___x_2244_, 1);
v_scopes_2247_ = lean_ctor_get(v___x_2244_, 2);
v_usedQuotCtxts_2248_ = lean_ctor_get(v___x_2244_, 3);
v_maxRecDepth_2249_ = lean_ctor_get(v___x_2244_, 5);
v_ngen_2250_ = lean_ctor_get(v___x_2244_, 6);
v_auxDeclNGen_2251_ = lean_ctor_get(v___x_2244_, 7);
v_infoState_2252_ = lean_ctor_get(v___x_2244_, 8);
v_traceState_2253_ = lean_ctor_get(v___x_2244_, 9);
v_snapshotTasks_2254_ = lean_ctor_get(v___x_2244_, 10);
v_prevLinterStates_2255_ = lean_ctor_get(v___x_2244_, 11);
v_codeQualityEntryTasks_2256_ = lean_ctor_get(v___x_2244_, 12);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; 
v_unused_2283_ = lean_ctor_get(v___x_2244_, 4);
lean_dec(v_unused_2283_);
v___x_2258_ = v___x_2244_;
v_isShared_2259_ = v_isSharedCheck_2282_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2256_);
lean_inc(v_prevLinterStates_2255_);
lean_inc(v_snapshotTasks_2254_);
lean_inc(v_traceState_2253_);
lean_inc(v_infoState_2252_);
lean_inc(v_auxDeclNGen_2251_);
lean_inc(v_ngen_2250_);
lean_inc(v_maxRecDepth_2249_);
lean_inc(v_usedQuotCtxts_2248_);
lean_inc(v_scopes_2247_);
lean_inc(v_messages_2246_);
lean_inc(v_env_2245_);
lean_dec(v___x_2244_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2282_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 4, v_macroScope_2239_);
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_env_2245_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_messages_2246_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_scopes_2247_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v_usedQuotCtxts_2248_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v_macroScope_2239_);
lean_ctor_set(v_reuseFailAlloc_2281_, 5, v_maxRecDepth_2249_);
lean_ctor_set(v_reuseFailAlloc_2281_, 6, v_ngen_2250_);
lean_ctor_set(v_reuseFailAlloc_2281_, 7, v_auxDeclNGen_2251_);
lean_ctor_set(v_reuseFailAlloc_2281_, 8, v_infoState_2252_);
lean_ctor_set(v_reuseFailAlloc_2281_, 9, v_traceState_2253_);
lean_ctor_set(v_reuseFailAlloc_2281_, 10, v_snapshotTasks_2254_);
lean_ctor_set(v_reuseFailAlloc_2281_, 11, v_prevLinterStates_2255_);
lean_ctor_set(v_reuseFailAlloc_2281_, 12, v_codeQualityEntryTasks_2256_);
v___x_2261_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2262_ = lean_st_ref_put(v___y_2200_, v___x_2261_);
v___x_2263_ = l_List_reverse___redArg(v_traceMsgs_2240_);
v___x_2264_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v___x_2263_, v___y_2199_, v___y_2200_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2271_ == 0)
{
lean_object* v_unused_2272_; 
v_unused_2272_ = lean_ctor_get(v___x_2264_, 0);
lean_dec(v_unused_2272_);
v___x_2266_ = v___x_2264_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_dec(v___x_2264_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v_a_2238_);
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2238_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec(v_a_2238_);
v_a_2273_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2264_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2264_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec(v_traceMsgs_2240_);
lean_dec(v_macroScope_2239_);
lean_dec(v_a_2238_);
v_a_2284_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2243_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2243_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
lean_object* v_a_2292_; 
v_a_2292_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2236_, 2);
if (lean_obj_tag(v_a_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v_a_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v_a_2293_ = lean_ctor_get(v_a_2292_, 0);
lean_inc(v_a_2293_);
v_a_2294_ = lean_ctor_get(v_a_2292_, 1);
lean_inc_ref(v_a_2294_);
lean_dec_ref_known(v_a_2292_, 2);
v___x_2295_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0));
v___x_2296_ = lean_string_dec_eq(v_a_2294_, v___x_2295_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2297_, 0, v_a_2294_);
v___x_2298_ = l_Lean_MessageData_ofFormat(v___x_2297_);
v___x_2299_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_a_2293_, v___x_2298_, v___y_2199_, v___y_2200_);
lean_dec(v_a_2293_);
return v___x_2299_;
}
else
{
lean_object* v___x_2300_; 
lean_dec_ref(v_a_2294_);
v___x_2300_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_a_2293_);
return v___x_2300_;
}
}
else
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2301_;
}
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v_a_2222_);
lean_dec_ref_known(v_methods_2220_, 5);
lean_dec_ref(v_x_2198_);
v_a_2305_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2223_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2223_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref_known(v_methods_2220_, 5);
lean_dec_ref(v_x_2198_);
v_a_2313_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2221_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2221_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v___f_2214_);
lean_dec(v_currNamespace_2213_);
lean_dec_ref(v_opts_2210_);
lean_dec_ref(v___f_2205_);
lean_dec_ref(v___f_2204_);
lean_dec_ref(v_env_2203_);
lean_dec_ref(v_x_2198_);
v_a_2321_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2215_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2215_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec_ref(v_opts_2210_);
lean_dec_ref(v___f_2205_);
lean_dec_ref(v___f_2204_);
lean_dec_ref(v_env_2203_);
lean_dec_ref(v_x_2198_);
v_a_2329_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2211_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2211_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___boxed(lean_object* v_x_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(lean_object* v_as_2342_, size_t v_i_2343_, size_t v_stop_2344_, lean_object* v_b_2345_){
_start:
{
lean_object* v___y_2347_; uint8_t v___x_2351_; 
v___x_2351_ = lean_usize_dec_eq(v_i_2343_, v_stop_2344_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2352_ = lean_array_uget_borrowed(v_as_2342_, v_i_2343_);
lean_inc(v___x_2352_);
v___x_2353_ = l_Lean_Syntax_getKind(v___x_2352_);
v___x_2354_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
v___x_2355_ = lean_name_eq(v___x_2353_, v___x_2354_);
lean_dec(v___x_2353_);
if (v___x_2355_ == 0)
{
v___y_2347_ = v_b_2345_;
goto v___jp_2346_;
}
else
{
lean_object* v___x_2356_; 
lean_inc(v___x_2352_);
v___x_2356_ = lean_array_push(v_b_2345_, v___x_2352_);
v___y_2347_ = v___x_2356_;
goto v___jp_2346_;
}
}
else
{
return v_b_2345_;
}
v___jp_2346_:
{
size_t v___x_2348_; size_t v___x_2349_; 
v___x_2348_ = ((size_t)1ULL);
v___x_2349_ = lean_usize_add(v_i_2343_, v___x_2348_);
v_i_2343_ = v___x_2349_;
v_b_2345_ = v___y_2347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8___boxed(lean_object* v_as_2357_, lean_object* v_i_2358_, lean_object* v_stop_2359_, lean_object* v_b_2360_){
_start:
{
size_t v_i_boxed_2361_; size_t v_stop_boxed_2362_; lean_object* v_res_2363_; 
v_i_boxed_2361_ = lean_unbox_usize(v_i_2358_);
lean_dec(v_i_2358_);
v_stop_boxed_2362_ = lean_unbox_usize(v_stop_2359_);
lean_dec(v_stop_2359_);
v_res_2363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v_as_2357_, v_i_boxed_2361_, v_stop_boxed_2362_, v_b_2360_);
lean_dec_ref(v_as_2357_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation(lean_object* v_x_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2495_; size_t v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; uint8_t v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; 
v___x_2437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0));
v___x_2438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1));
v___x_2439_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
lean_inc(v_x_2406_);
v___x_2440_ = l_Lean_Syntax_isOfKind(v_x_2406_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2549_; 
lean_dec(v_x_2406_);
v___x_2549_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2549_;
}
else
{
lean_object* v___x_2550_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; size_t v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; uint8_t v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; size_t v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; uint8_t v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; size_t v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; uint8_t v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; size_t v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; uint8_t v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; size_t v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; uint8_t v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v_prio_x3f_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v_name_x3f_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v_prec_x3f_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v_attrs_x3f_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v_doc_x3f_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2550_ = lean_unsigned_to_nat(0u);
v___x_2905_ = l_Lean_Syntax_getArg(v_x_2406_, v___x_2550_);
v___x_2906_ = l_Lean_Syntax_isNone(v___x_2905_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; uint8_t v___x_2908_; 
v___x_2907_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2905_);
v___x_2908_ = l_Lean_Syntax_matchesNull(v___x_2905_, v___x_2907_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; 
lean_dec(v___x_2905_);
lean_dec(v_x_2406_);
v___x_2909_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2909_;
}
else
{
lean_object* v_doc_x3f_2910_; 
v_doc_x3f_2910_ = l_Lean_Syntax_getArg(v___x_2905_, v___x_2550_);
lean_dec(v___x_2905_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2913_; uint8_t v___x_2914_; 
v___x_2913_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__15));
lean_inc(v_doc_x3f_2910_);
v___x_2914_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2910_, v___x_2913_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; 
lean_dec(v_doc_x3f_2910_);
lean_dec(v_x_2406_);
v___x_2915_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2915_;
}
else
{
goto v___jp_2911_;
}
}
else
{
goto v___jp_2911_;
}
v___jp_2911_:
{
lean_object* v___x_2912_; 
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_doc_x3f_2910_);
v_doc_x3f_2889_ = v___x_2912_;
v___y_2890_ = v_a_2407_;
v___y_2891_ = v_a_2408_;
goto v___jp_2888_;
}
}
}
else
{
lean_object* v___x_2916_; 
lean_dec(v___x_2905_);
v___x_2916_ = lean_box(0);
v_doc_x3f_2889_ = v___x_2916_;
v___y_2890_ = v_a_2407_;
v___y_2891_ = v_a_2408_;
goto v___jp_2888_;
}
v___jp_2551_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; size_t v_sz_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_inc_ref_n(v___y_2569_, 2);
v___x_2572_ = l_Array_append___redArg(v___y_2569_, v___y_2571_);
lean_dec_ref(v___y_2571_);
lean_inc_n(v___y_2559_, 3);
lean_inc_n(v___y_2565_, 9);
v___x_2573_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2573_, 0, v___y_2565_);
lean_ctor_set(v___x_2573_, 1, v___y_2559_);
lean_ctor_set(v___x_2573_, 2, v___x_2572_);
v___x_2574_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
v___x_2575_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
v___x_2576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___y_2565_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__8));
v___x_2578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___y_2565_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_2580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___y_2565_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = l_Nat_reprFast(v___y_2564_);
v___x_2582_ = lean_box(2);
v___x_2583_ = l_Lean_Syntax_mkNumLit(v___x_2581_, v___x_2582_);
v___x_2584_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_2585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___y_2565_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
v___x_2586_ = l_Lean_Syntax_node5(v___y_2565_, v___x_2574_, v___x_2576_, v___x_2578_, v___x_2580_, v___x_2583_, v___x_2585_);
v___x_2587_ = l_Lean_Syntax_node1(v___y_2565_, v___y_2559_, v___x_2586_);
v_sz_2588_ = lean_array_size(v___y_2566_);
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_2588_, v___y_2556_, v___y_2566_);
v___x_2590_ = l_Array_append___redArg(v___y_2569_, v___x_2589_);
lean_dec_ref(v___x_2589_);
v___x_2591_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2591_, 0, v___y_2565_);
lean_ctor_set(v___x_2591_, 1, v___y_2559_);
lean_ctor_set(v___x_2591_, 2, v___x_2590_);
v___x_2592_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
v___x_2593_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___y_2565_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___x_2594_ = lean_unsigned_to_nat(10u);
v___x_2595_ = lean_mk_empty_array_with_capacity(v___x_2594_);
v___x_2596_ = lean_array_push(v___x_2595_, v___y_2560_);
v___x_2597_ = lean_array_push(v___x_2596_, v___y_2562_);
lean_inc(v___y_2557_);
v___x_2598_ = lean_array_push(v___x_2597_, v___y_2557_);
v___x_2599_ = lean_array_push(v___x_2598_, v___y_2558_);
v___x_2600_ = lean_array_push(v___x_2599_, v___y_2561_);
v___x_2601_ = lean_array_push(v___x_2600_, v___x_2573_);
v___x_2602_ = lean_array_push(v___x_2601_, v___x_2587_);
v___x_2603_ = lean_array_push(v___x_2602_, v___x_2591_);
v___x_2604_ = lean_array_push(v___x_2603_, v___x_2593_);
v___x_2605_ = lean_array_push(v___x_2604_, v___y_2554_);
lean_inc(v___y_2552_);
v___x_2606_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2606_, 0, v___y_2565_);
lean_ctor_set(v___x_2606_, 1, v___y_2552_);
lean_ctor_set(v___x_2606_, 2, v___x_2605_);
v___x_2607_ = l_Lean_Elab_Command_elabSyntax(v___x_2606_, v___y_2553_, v___y_2567_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2607_, 1);
v___x_2609_ = lean_array_get_size(v___y_2563_);
v___x_2610_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__68));
v___x_2611_ = lean_nat_dec_lt(v___x_2550_, v___x_2609_);
if (v___x_2611_ == 0)
{
v___y_2495_ = v___y_2553_;
v___y_2496_ = v___y_2556_;
v___y_2497_ = v___y_2555_;
v___y_2498_ = v___y_2557_;
v___y_2499_ = v_a_2608_;
v___y_2500_ = v___y_2559_;
v___y_2501_ = v___x_2582_;
v___y_2502_ = v___y_2563_;
v___y_2503_ = v___y_2567_;
v___y_2504_ = v___y_2568_;
v___y_2505_ = v___x_2584_;
v___y_2506_ = v___y_2569_;
v___y_2507_ = v___y_2570_;
v___y_2508_ = v___x_2610_;
goto v___jp_2494_;
}
else
{
uint8_t v___x_2612_; 
v___x_2612_ = lean_nat_dec_le(v___x_2609_, v___x_2609_);
if (v___x_2612_ == 0)
{
if (v___x_2611_ == 0)
{
v___y_2495_ = v___y_2553_;
v___y_2496_ = v___y_2556_;
v___y_2497_ = v___y_2555_;
v___y_2498_ = v___y_2557_;
v___y_2499_ = v_a_2608_;
v___y_2500_ = v___y_2559_;
v___y_2501_ = v___x_2582_;
v___y_2502_ = v___y_2563_;
v___y_2503_ = v___y_2567_;
v___y_2504_ = v___y_2568_;
v___y_2505_ = v___x_2584_;
v___y_2506_ = v___y_2569_;
v___y_2507_ = v___y_2570_;
v___y_2508_ = v___x_2610_;
goto v___jp_2494_;
}
else
{
size_t v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = lean_usize_of_nat(v___x_2609_);
v___x_2614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2563_, v___y_2556_, v___x_2613_, v___x_2610_);
v___y_2495_ = v___y_2553_;
v___y_2496_ = v___y_2556_;
v___y_2497_ = v___y_2555_;
v___y_2498_ = v___y_2557_;
v___y_2499_ = v_a_2608_;
v___y_2500_ = v___y_2559_;
v___y_2501_ = v___x_2582_;
v___y_2502_ = v___y_2563_;
v___y_2503_ = v___y_2567_;
v___y_2504_ = v___y_2568_;
v___y_2505_ = v___x_2584_;
v___y_2506_ = v___y_2569_;
v___y_2507_ = v___y_2570_;
v___y_2508_ = v___x_2614_;
goto v___jp_2494_;
}
}
else
{
size_t v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = lean_usize_of_nat(v___x_2609_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2563_, v___y_2556_, v___x_2615_, v___x_2610_);
v___y_2495_ = v___y_2553_;
v___y_2496_ = v___y_2556_;
v___y_2497_ = v___y_2555_;
v___y_2498_ = v___y_2557_;
v___y_2499_ = v_a_2608_;
v___y_2500_ = v___y_2559_;
v___y_2501_ = v___x_2582_;
v___y_2502_ = v___y_2563_;
v___y_2503_ = v___y_2567_;
v___y_2504_ = v___y_2568_;
v___y_2505_ = v___x_2584_;
v___y_2506_ = v___y_2569_;
v___y_2507_ = v___y_2570_;
v___y_2508_ = v___x_2616_;
goto v___jp_2494_;
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2557_);
v_a_2617_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2607_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2607_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
v___jp_2625_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
lean_inc_ref(v___y_2643_);
v___x_2646_ = l_Array_append___redArg(v___y_2643_, v___y_2645_);
lean_dec_ref(v___y_2645_);
lean_inc(v___y_2634_);
lean_inc(v___y_2640_);
v___x_2647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2647_, 0, v___y_2640_);
lean_ctor_set(v___x_2647_, 1, v___y_2634_);
lean_ctor_set(v___x_2647_, 2, v___x_2646_);
if (lean_obj_tag(v___y_2633_) == 1)
{
lean_object* v_val_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_val_2648_ = lean_ctor_get(v___y_2633_, 0);
lean_inc(v_val_2648_);
lean_dec_ref_known(v___y_2633_, 1);
v___x_2649_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
v___x_2650_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc_n(v___y_2640_, 5);
v___x_2651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___y_2640_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__11));
v___x_2653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___y_2640_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_2655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___y_2640_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_2657_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___y_2640_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = l_Lean_Syntax_node5(v___y_2640_, v___x_2649_, v___x_2651_, v___x_2653_, v___x_2655_, v_val_2648_, v___x_2657_);
v___x_2659_ = l_Array_mkArray1___redArg(v___x_2658_);
v___y_2552_ = v___y_2626_;
v___y_2553_ = v___y_2627_;
v___y_2554_ = v___y_2628_;
v___y_2555_ = v___y_2629_;
v___y_2556_ = v___y_2630_;
v___y_2557_ = v___y_2631_;
v___y_2558_ = v___y_2632_;
v___y_2559_ = v___y_2634_;
v___y_2560_ = v___y_2635_;
v___y_2561_ = v___x_2647_;
v___y_2562_ = v___y_2636_;
v___y_2563_ = v___y_2637_;
v___y_2564_ = v___y_2638_;
v___y_2565_ = v___y_2640_;
v___y_2566_ = v___y_2639_;
v___y_2567_ = v___y_2641_;
v___y_2568_ = v___y_2642_;
v___y_2569_ = v___y_2643_;
v___y_2570_ = v___y_2644_;
v___y_2571_ = v___x_2659_;
goto v___jp_2551_;
}
else
{
lean_object* v___x_2660_; 
lean_dec(v___y_2633_);
v___x_2660_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2552_ = v___y_2626_;
v___y_2553_ = v___y_2627_;
v___y_2554_ = v___y_2628_;
v___y_2555_ = v___y_2629_;
v___y_2556_ = v___y_2630_;
v___y_2557_ = v___y_2631_;
v___y_2558_ = v___y_2632_;
v___y_2559_ = v___y_2634_;
v___y_2560_ = v___y_2635_;
v___y_2561_ = v___x_2647_;
v___y_2562_ = v___y_2636_;
v___y_2563_ = v___y_2637_;
v___y_2564_ = v___y_2638_;
v___y_2565_ = v___y_2640_;
v___y_2566_ = v___y_2639_;
v___y_2567_ = v___y_2641_;
v___y_2568_ = v___y_2642_;
v___y_2569_ = v___y_2643_;
v___y_2570_ = v___y_2644_;
v___y_2571_ = v___x_2660_;
goto v___jp_2551_;
}
}
v___jp_2661_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
lean_inc_ref(v___y_2679_);
v___x_2682_ = l_Array_append___redArg(v___y_2679_, v___y_2681_);
lean_dec_ref(v___y_2681_);
lean_inc(v___y_2670_);
lean_inc_n(v___y_2676_, 2);
v___x_2683_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2683_, 0, v___y_2676_);
lean_ctor_set(v___x_2683_, 1, v___y_2670_);
lean_ctor_set(v___x_2683_, 2, v___x_2682_);
lean_inc_ref(v___y_2672_);
v___x_2684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___y_2676_);
lean_ctor_set(v___x_2684_, 1, v___y_2672_);
if (lean_obj_tag(v___y_2663_) == 1)
{
lean_object* v_val_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_val_2685_ = lean_ctor_get(v___y_2663_, 0);
lean_inc(v_val_2685_);
lean_dec_ref_known(v___y_2663_, 1);
v___x_2686_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
v___x_2687_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc_n(v___y_2676_, 2);
v___x_2688_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___y_2676_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
v___x_2689_ = l_Lean_Syntax_node2(v___y_2676_, v___x_2686_, v___x_2688_, v_val_2685_);
v___x_2690_ = l_Array_mkArray1___redArg(v___x_2689_);
v___y_2626_ = v___y_2662_;
v___y_2627_ = v___y_2664_;
v___y_2628_ = v___y_2665_;
v___y_2629_ = v___y_2666_;
v___y_2630_ = v___y_2667_;
v___y_2631_ = v___y_2668_;
v___y_2632_ = v___x_2684_;
v___y_2633_ = v___y_2669_;
v___y_2634_ = v___y_2670_;
v___y_2635_ = v___y_2671_;
v___y_2636_ = v___x_2683_;
v___y_2637_ = v___y_2673_;
v___y_2638_ = v___y_2674_;
v___y_2639_ = v___y_2675_;
v___y_2640_ = v___y_2676_;
v___y_2641_ = v___y_2677_;
v___y_2642_ = v___y_2678_;
v___y_2643_ = v___y_2679_;
v___y_2644_ = v___y_2680_;
v___y_2645_ = v___x_2690_;
goto v___jp_2625_;
}
else
{
lean_object* v___x_2691_; 
lean_dec(v___y_2663_);
v___x_2691_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2626_ = v___y_2662_;
v___y_2627_ = v___y_2664_;
v___y_2628_ = v___y_2665_;
v___y_2629_ = v___y_2666_;
v___y_2630_ = v___y_2667_;
v___y_2631_ = v___y_2668_;
v___y_2632_ = v___x_2684_;
v___y_2633_ = v___y_2669_;
v___y_2634_ = v___y_2670_;
v___y_2635_ = v___y_2671_;
v___y_2636_ = v___x_2683_;
v___y_2637_ = v___y_2673_;
v___y_2638_ = v___y_2674_;
v___y_2639_ = v___y_2675_;
v___y_2640_ = v___y_2676_;
v___y_2641_ = v___y_2677_;
v___y_2642_ = v___y_2678_;
v___y_2643_ = v___y_2679_;
v___y_2644_ = v___y_2680_;
v___y_2645_ = v___x_2691_;
goto v___jp_2625_;
}
}
v___jp_2692_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_inc_ref(v___y_2709_);
v___x_2713_ = l_Array_append___redArg(v___y_2709_, v___y_2712_);
lean_dec_ref(v___y_2712_);
lean_inc(v___y_2701_);
lean_inc(v___y_2706_);
v___x_2714_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2714_, 0, v___y_2706_);
lean_ctor_set(v___x_2714_, 1, v___y_2701_);
lean_ctor_set(v___x_2714_, 2, v___x_2713_);
if (lean_obj_tag(v___y_2711_) == 1)
{
lean_object* v_val_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v_val_2715_ = lean_ctor_get(v___y_2711_, 0);
lean_inc(v_val_2715_);
lean_dec_ref_known(v___y_2711_, 1);
v___x_2716_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__11));
lean_inc_ref(v___y_2697_);
v___x_2717_ = l_Lean_Name_mkStr4(v___x_2437_, v___x_2438_, v___y_2697_, v___x_2716_);
v___x_2718_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc_n(v___y_2706_, 4);
v___x_2719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___y_2706_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
lean_inc_ref(v___y_2709_);
v___x_2720_ = l_Array_append___redArg(v___y_2709_, v_val_2715_);
lean_dec(v_val_2715_);
lean_inc(v___y_2701_);
v___x_2721_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2721_, 0, v___y_2706_);
lean_ctor_set(v___x_2721_, 1, v___y_2701_);
lean_ctor_set(v___x_2721_, 2, v___x_2720_);
v___x_2722_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
v___x_2723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___y_2706_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___x_2724_ = l_Lean_Syntax_node3(v___y_2706_, v___x_2717_, v___x_2719_, v___x_2721_, v___x_2723_);
v___x_2725_ = l_Array_mkArray1___redArg(v___x_2724_);
v___y_2662_ = v___y_2693_;
v___y_2663_ = v___y_2694_;
v___y_2664_ = v___y_2695_;
v___y_2665_ = v___y_2696_;
v___y_2666_ = v___y_2697_;
v___y_2667_ = v___y_2698_;
v___y_2668_ = v___y_2699_;
v___y_2669_ = v___y_2700_;
v___y_2670_ = v___y_2701_;
v___y_2671_ = v___x_2714_;
v___y_2672_ = v___y_2702_;
v___y_2673_ = v___y_2703_;
v___y_2674_ = v___y_2704_;
v___y_2675_ = v___y_2705_;
v___y_2676_ = v___y_2706_;
v___y_2677_ = v___y_2707_;
v___y_2678_ = v___y_2708_;
v___y_2679_ = v___y_2709_;
v___y_2680_ = v___y_2710_;
v___y_2681_ = v___x_2725_;
goto v___jp_2661_;
}
else
{
lean_object* v___x_2726_; 
lean_dec(v___y_2711_);
v___x_2726_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2662_ = v___y_2693_;
v___y_2663_ = v___y_2694_;
v___y_2664_ = v___y_2695_;
v___y_2665_ = v___y_2696_;
v___y_2666_ = v___y_2697_;
v___y_2667_ = v___y_2698_;
v___y_2668_ = v___y_2699_;
v___y_2669_ = v___y_2700_;
v___y_2670_ = v___y_2701_;
v___y_2671_ = v___x_2714_;
v___y_2672_ = v___y_2702_;
v___y_2673_ = v___y_2703_;
v___y_2674_ = v___y_2704_;
v___y_2675_ = v___y_2705_;
v___y_2676_ = v___y_2706_;
v___y_2677_ = v___y_2707_;
v___y_2678_ = v___y_2708_;
v___y_2679_ = v___y_2709_;
v___y_2680_ = v___y_2710_;
v___y_2681_ = v___x_2726_;
goto v___jp_2661_;
}
}
v___jp_2727_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2744_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__12));
v___x_2745_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__13));
v___x_2746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_2747_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
if (lean_obj_tag(v___y_2735_) == 1)
{
lean_object* v_val_2748_; lean_object* v___x_2749_; 
v_val_2748_ = lean_ctor_get(v___y_2735_, 0);
lean_inc(v_val_2748_);
lean_dec_ref_known(v___y_2735_, 1);
v___x_2749_ = l_Array_mkArray1___redArg(v_val_2748_);
v___y_2693_ = v___x_2745_;
v___y_2694_ = v___y_2728_;
v___y_2695_ = v___y_2729_;
v___y_2696_ = v___y_2730_;
v___y_2697_ = v___y_2731_;
v___y_2698_ = v___y_2732_;
v___y_2699_ = v___y_2733_;
v___y_2700_ = v___y_2734_;
v___y_2701_ = v___x_2746_;
v___y_2702_ = v___x_2744_;
v___y_2703_ = v___y_2736_;
v___y_2704_ = v___y_2737_;
v___y_2705_ = v___y_2738_;
v___y_2706_ = v___y_2739_;
v___y_2707_ = v___y_2740_;
v___y_2708_ = v___y_2741_;
v___y_2709_ = v___x_2747_;
v___y_2710_ = v___y_2742_;
v___y_2711_ = v___y_2743_;
v___y_2712_ = v___x_2749_;
goto v___jp_2692_;
}
else
{
lean_object* v___x_2750_; 
lean_dec(v___y_2735_);
v___x_2750_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2693_ = v___x_2745_;
v___y_2694_ = v___y_2728_;
v___y_2695_ = v___y_2729_;
v___y_2696_ = v___y_2730_;
v___y_2697_ = v___y_2731_;
v___y_2698_ = v___y_2732_;
v___y_2699_ = v___y_2733_;
v___y_2700_ = v___y_2734_;
v___y_2701_ = v___x_2746_;
v___y_2702_ = v___x_2744_;
v___y_2703_ = v___y_2736_;
v___y_2704_ = v___y_2737_;
v___y_2705_ = v___y_2738_;
v___y_2706_ = v___y_2739_;
v___y_2707_ = v___y_2740_;
v___y_2708_ = v___y_2741_;
v___y_2709_ = v___x_2747_;
v___y_2710_ = v___y_2742_;
v___y_2711_ = v___y_2743_;
v___y_2712_ = v___x_2750_;
goto v___jp_2692_;
}
}
v___jp_2751_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v_rhs_2764_; lean_object* v___x_2765_; lean_object* v_items_2766_; lean_object* v_attrs_x3f_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2761_ = lean_unsigned_to_nat(7u);
v___x_2762_ = l_Lean_Syntax_getArg(v_x_2406_, v___x_2761_);
v___x_2763_ = lean_unsigned_to_nat(9u);
v_rhs_2764_ = l_Lean_Syntax_getArg(v_x_2406_, v___x_2763_);
v___x_2765_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
v_items_2766_ = l_Lean_Syntax_getArgs(v___x_2762_);
lean_dec(v___x_2762_);
lean_inc(v_rhs_2764_);
v_attrs_x3f_2767_ = l_Lean_Elab_Command_addInheritDocDefault(v_rhs_2764_, v___y_2757_);
v___x_2768_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_2768_, 0, v_prio_x3f_2758_);
v___x_2769_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2768_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; size_t v_sz_2771_; size_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2769_, 1);
v_sz_2771_ = lean_array_size(v_items_2766_);
v___x_2772_ = ((size_t)0ULL);
v___x_2773_ = lean_box_usize(v_sz_2771_);
v___x_2774_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___boxed__const__1));
lean_inc_ref(v_items_2766_);
v___x_2775_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed), 5, 3);
lean_closure_set(v___x_2775_, 0, v___x_2773_);
lean_closure_set(v___x_2775_, 1, v___x_2774_);
lean_closure_set(v___x_2775_, 2, v_items_2766_);
v___x_2776_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2775_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; uint8_t v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v___x_2778_ = 0;
v___x_2779_ = l_Lean_mkIdentFrom(v_x_2406_, v___x_2765_, v___x_2778_);
lean_dec(v_x_2406_);
v___x_2780_ = l_Lean_Elab_Command_getRef___redArg(v___y_2759_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2782_ = l_Lean_SourceInfo_fromRef(v_a_2781_, v___x_2778_);
lean_dec(v_a_2781_);
v___x_2783_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2759_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_quotContext_x3f_2784_; 
lean_dec_ref_known(v___x_2783_, 1);
v_quotContext_x3f_2784_ = lean_ctor_get(v___y_2759_, 5);
if (lean_obj_tag(v_quotContext_x3f_2784_) == 0)
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2760_);
lean_dec_ref(v___x_2785_);
v___y_2728_ = v___y_2753_;
v___y_2729_ = v___y_2759_;
v___y_2730_ = v___x_2779_;
v___y_2731_ = v___y_2754_;
v___y_2732_ = v___x_2772_;
v___y_2733_ = v___y_2755_;
v___y_2734_ = v___y_2756_;
v___y_2735_ = v___y_2752_;
v___y_2736_ = v_items_2766_;
v___y_2737_ = v_a_2770_;
v___y_2738_ = v_a_2777_;
v___y_2739_ = v___x_2782_;
v___y_2740_ = v___y_2760_;
v___y_2741_ = v___x_2778_;
v___y_2742_ = v_rhs_2764_;
v___y_2743_ = v_attrs_x3f_2767_;
goto v___jp_2727_;
}
else
{
v___y_2728_ = v___y_2753_;
v___y_2729_ = v___y_2759_;
v___y_2730_ = v___x_2779_;
v___y_2731_ = v___y_2754_;
v___y_2732_ = v___x_2772_;
v___y_2733_ = v___y_2755_;
v___y_2734_ = v___y_2756_;
v___y_2735_ = v___y_2752_;
v___y_2736_ = v_items_2766_;
v___y_2737_ = v_a_2770_;
v___y_2738_ = v_a_2777_;
v___y_2739_ = v___x_2782_;
v___y_2740_ = v___y_2760_;
v___y_2741_ = v___x_2778_;
v___y_2742_ = v_rhs_2764_;
v___y_2743_ = v_attrs_x3f_2767_;
goto v___jp_2727_;
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec(v___x_2782_);
lean_dec(v___x_2779_);
lean_dec(v_a_2777_);
lean_dec(v_a_2770_);
lean_dec(v_attrs_x3f_2767_);
lean_dec_ref(v_items_2766_);
lean_dec(v_rhs_2764_);
lean_dec(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
v_a_2786_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2783_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2783_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec(v___x_2779_);
lean_dec(v_a_2777_);
lean_dec(v_a_2770_);
lean_dec(v_attrs_x3f_2767_);
lean_dec_ref(v_items_2766_);
lean_dec(v_rhs_2764_);
lean_dec(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
v_a_2794_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2780_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2780_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v_a_2770_);
lean_dec(v_attrs_x3f_2767_);
lean_dec_ref(v_items_2766_);
lean_dec(v_rhs_2764_);
lean_dec(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec(v_x_2406_);
v_a_2802_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2776_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2776_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_attrs_x3f_2767_);
lean_dec_ref(v_items_2766_);
lean_dec(v_rhs_2764_);
lean_dec(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec(v_x_2406_);
v_a_2810_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2769_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2769_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
v___jp_2818_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v___x_2829_ = lean_unsigned_to_nat(6u);
v___x_2830_ = l_Lean_Syntax_getArg(v_x_2406_, v___x_2829_);
v___x_2831_ = l_Lean_Syntax_isNone(v___x_2830_);
if (v___x_2831_ == 0)
{
uint8_t v___x_2832_; 
lean_inc(v___x_2830_);
v___x_2832_ = l_Lean_Syntax_matchesNull(v___x_2830_, v___y_2824_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; 
lean_dec(v___x_2830_);
lean_dec(v_name_x3f_2826_);
lean_dec(v___y_2825_);
lean_dec(v___y_2822_);
lean_dec(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec(v_x_2406_);
v___x_2833_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2833_;
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2834_ = l_Lean_Syntax_getArg(v___x_2830_, v___x_2550_);
lean_dec(v___x_2830_);
v___x_2835_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
lean_inc(v___x_2834_);
v___x_2836_ = l_Lean_Syntax_isOfKind(v___x_2834_, v___x_2835_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; 
lean_dec(v___x_2834_);
lean_dec(v_name_x3f_2826_);
lean_dec(v___y_2825_);
lean_dec(v___y_2822_);
lean_dec(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec(v_x_2406_);
v___x_2837_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2837_;
}
else
{
lean_object* v_prio_x3f_2838_; lean_object* v___x_2839_; 
v_prio_x3f_2838_ = l_Lean_Syntax_getArg(v___x_2834_, v___y_2823_);
lean_dec(v___x_2834_);
v___x_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2839_, 0, v_prio_x3f_2838_);
v___y_2752_ = v___y_2819_;
v___y_2753_ = v___y_2820_;
v___y_2754_ = v___y_2821_;
v___y_2755_ = v___y_2822_;
v___y_2756_ = v_name_x3f_2826_;
v___y_2757_ = v___y_2825_;
v_prio_x3f_2758_ = v___x_2839_;
v___y_2759_ = v___y_2827_;
v___y_2760_ = v___y_2828_;
goto v___jp_2751_;
}
}
}
else
{
lean_object* v___x_2840_; 
lean_dec(v___x_2830_);
v___x_2840_ = lean_box(0);
v___y_2752_ = v___y_2819_;
v___y_2753_ = v___y_2820_;
v___y_2754_ = v___y_2821_;
v___y_2755_ = v___y_2822_;
v___y_2756_ = v_name_x3f_2826_;
v___y_2757_ = v___y_2825_;
v_prio_x3f_2758_ = v___x_2840_;
v___y_2759_ = v___y_2827_;
v___y_2760_ = v___y_2828_;
goto v___jp_2751_;
}
}
v___jp_2841_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v___x_2851_ = lean_unsigned_to_nat(5u);
v___x_2852_ = l_Lean_Syntax_getArg(v_x_2406_, v___x_2851_);
v___x_2853_ = l_Lean_Syntax_isNone(v___x_2852_);
if (v___x_2853_ == 0)
{
uint8_t v___x_2854_; 
lean_inc(v___x_2852_);
v___x_2854_ = l_Lean_Syntax_matchesNull(v___x_2852_, v___y_2846_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_dec(v___x_2852_);
lean_dec(v_prec_x3f_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2844_);
lean_dec(v___y_2842_);
lean_dec(v_x_2406_);
v___x_2855_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2855_;
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2856_ = l_Lean_Syntax_getArg(v___x_2852_, v___x_2550_);
lean_dec(v___x_2852_);
v___x_2857_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
lean_inc(v___x_2856_);
v___x_2858_ = l_Lean_Syntax_isOfKind(v___x_2856_, v___x_2857_);
if (v___x_2858_ == 0)
{
lean_object* v___x_2859_; 
lean_dec(v___x_2856_);
lean_dec(v_prec_x3f_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2844_);
lean_dec(v___y_2842_);
lean_dec(v_x_2406_);
v___x_2859_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2859_;
}
else
{
lean_object* v_name_x3f_2860_; lean_object* v___x_2861_; 
v_name_x3f_2860_ = l_Lean_Syntax_getArg(v___x_2856_, v___y_2845_);
lean_dec(v___x_2856_);
v___x_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2861_, 0, v_name_x3f_2860_);
v___y_2819_ = v___y_2842_;
v___y_2820_ = v_prec_x3f_2848_;
v___y_2821_ = v___y_2843_;
v___y_2822_ = v___y_2844_;
v___y_2823_ = v___y_2845_;
v___y_2824_ = v___y_2846_;
v___y_2825_ = v___y_2847_;
v_name_x3f_2826_ = v___x_2861_;
v___y_2827_ = v___y_2849_;
v___y_2828_ = v___y_2850_;
goto v___jp_2818_;
}
}
}
else
{
lean_object* v___x_2862_; 
lean_dec(v___x_2852_);
v___x_2862_ = lean_box(0);
v___y_2819_ = v___y_2842_;
v___y_2820_ = v_prec_x3f_2848_;
v___y_2821_ = v___y_2843_;
v___y_2822_ = v___y_2844_;
v___y_2823_ = v___y_2845_;
v___y_2824_ = v___y_2846_;
v___y_2825_ = v___y_2847_;
v_name_x3f_2826_ = v___x_2862_;
v___y_2827_ = v___y_2849_;
v___y_2828_ = v___y_2850_;
goto v___jp_2818_;
}
}
v___jp_2863_:
{
lean_object* v___x_2869_; lean_object* v_attrKind_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; 
v___x_2869_ = lean_unsigned_to_nat(2u);
v_attrKind_2870_ = l_Lean_Syntax_getArg(v_x_2406_, v___x_2869_);
v___x_2871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2));
v___x_2872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(v_attrKind_2870_);
v___x_2873_ = l_Lean_Syntax_isOfKind(v_attrKind_2870_, v___x_2872_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; 
lean_dec(v_attrKind_2870_);
lean_dec(v_attrs_x3f_2866_);
lean_dec(v___y_2864_);
lean_dec(v_x_2406_);
v___x_2874_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2874_;
}
else
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; 
v___x_2875_ = lean_unsigned_to_nat(3u);
v___x_2876_ = lean_unsigned_to_nat(4u);
v___x_2877_ = l_Lean_Syntax_getArg(v_x_2406_, v___x_2876_);
v___x_2878_ = l_Lean_Syntax_isNone(v___x_2877_);
if (v___x_2878_ == 0)
{
uint8_t v___x_2879_; 
lean_inc(v___x_2877_);
v___x_2879_ = l_Lean_Syntax_matchesNull(v___x_2877_, v___y_2865_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; 
lean_dec(v___x_2877_);
lean_dec(v_attrKind_2870_);
lean_dec(v_attrs_x3f_2866_);
lean_dec(v___y_2864_);
lean_dec(v_x_2406_);
v___x_2880_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2880_;
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; 
v___x_2881_ = l_Lean_Syntax_getArg(v___x_2877_, v___x_2550_);
lean_dec(v___x_2877_);
v___x_2882_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
lean_inc(v___x_2881_);
v___x_2883_ = l_Lean_Syntax_isOfKind(v___x_2881_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; 
lean_dec(v___x_2881_);
lean_dec(v_attrKind_2870_);
lean_dec(v_attrs_x3f_2866_);
lean_dec(v___y_2864_);
lean_dec(v_x_2406_);
v___x_2884_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2884_;
}
else
{
lean_object* v_prec_x3f_2885_; lean_object* v___x_2886_; 
v_prec_x3f_2885_ = l_Lean_Syntax_getArg(v___x_2881_, v___y_2865_);
lean_dec(v___x_2881_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v_prec_x3f_2885_);
v___y_2842_ = v___y_2864_;
v___y_2843_ = v___x_2871_;
v___y_2844_ = v_attrKind_2870_;
v___y_2845_ = v___x_2875_;
v___y_2846_ = v___y_2865_;
v___y_2847_ = v_attrs_x3f_2866_;
v_prec_x3f_2848_ = v___x_2886_;
v___y_2849_ = v___y_2867_;
v___y_2850_ = v___y_2868_;
goto v___jp_2841_;
}
}
}
else
{
lean_object* v___x_2887_; 
lean_dec(v___x_2877_);
v___x_2887_ = lean_box(0);
v___y_2842_ = v___y_2864_;
v___y_2843_ = v___x_2871_;
v___y_2844_ = v_attrKind_2870_;
v___y_2845_ = v___x_2875_;
v___y_2846_ = v___y_2865_;
v___y_2847_ = v_attrs_x3f_2866_;
v_prec_x3f_2848_ = v___x_2887_;
v___y_2849_ = v___y_2867_;
v___y_2850_ = v___y_2868_;
goto v___jp_2841_;
}
}
}
v___jp_2888_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; 
v___x_2892_ = lean_unsigned_to_nat(1u);
v___x_2893_ = l_Lean_Syntax_getArg(v_x_2406_, v___x_2892_);
v___x_2894_ = l_Lean_Syntax_isNone(v___x_2893_);
if (v___x_2894_ == 0)
{
uint8_t v___x_2895_; 
lean_inc(v___x_2893_);
v___x_2895_ = l_Lean_Syntax_matchesNull(v___x_2893_, v___x_2892_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; 
lean_dec(v___x_2893_);
lean_dec(v_doc_x3f_2889_);
lean_dec(v_x_2406_);
v___x_2896_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2896_;
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v___x_2897_ = l_Lean_Syntax_getArg(v___x_2893_, v___x_2550_);
lean_dec(v___x_2893_);
v___x_2898_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
lean_inc(v___x_2897_);
v___x_2899_ = l_Lean_Syntax_isOfKind(v___x_2897_, v___x_2898_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; 
lean_dec(v___x_2897_);
lean_dec(v_doc_x3f_2889_);
lean_dec(v_x_2406_);
v___x_2900_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2900_;
}
else
{
lean_object* v___x_2901_; lean_object* v_attrs_x3f_2902_; lean_object* v___x_2903_; 
v___x_2901_ = l_Lean_Syntax_getArg(v___x_2897_, v___x_2892_);
lean_dec(v___x_2897_);
v_attrs_x3f_2902_ = l_Lean_Syntax_getArgs(v___x_2901_);
lean_dec(v___x_2901_);
v___x_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2903_, 0, v_attrs_x3f_2902_);
v___y_2864_ = v_doc_x3f_2889_;
v___y_2865_ = v___x_2892_;
v_attrs_x3f_2866_ = v___x_2903_;
v___y_2867_ = v___y_2890_;
v___y_2868_ = v___y_2891_;
goto v___jp_2863_;
}
}
}
else
{
lean_object* v___x_2904_; 
lean_dec(v___x_2893_);
v___x_2904_ = lean_box(0);
v___y_2864_ = v_doc_x3f_2889_;
v___y_2865_ = v___x_2892_;
v_attrs_x3f_2866_ = v___x_2904_;
v___y_2867_ = v___y_2890_;
v___y_2868_ = v___y_2891_;
goto v___jp_2863_;
}
}
}
v___jp_2410_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkUnexpander___boxed), 5, 3);
lean_closure_set(v___x_2416_, 0, v___y_2412_);
lean_closure_set(v___x_2416_, 1, v___y_2411_);
lean_closure_set(v___x_2416_, 2, v___y_2413_);
v___x_2417_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2416_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2428_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2428_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2428_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
if (lean_obj_tag(v_a_2418_) == 1)
{
lean_object* v_val_2422_; lean_object* v___x_2423_; 
lean_del_object(v___x_2420_);
v_val_2422_ = lean_ctor_get(v_a_2418_, 0);
lean_inc(v_val_2422_);
lean_dec_ref_known(v_a_2418_, 1);
v___x_2423_ = l_Lean_Elab_Command_elabCommand(v_val_2422_, v___y_2414_, v___y_2415_);
return v___x_2423_;
}
else
{
lean_object* v___x_2424_; lean_object* v___x_2426_; 
lean_dec(v_a_2418_);
v___x_2424_ = lean_box(0);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2424_);
v___x_2426_ = v___x_2420_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
v_a_2429_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2417_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2417_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
v___jp_2441_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v___x_2452_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__2));
v___x_2453_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__3));
lean_inc_ref(v___y_2450_);
lean_inc_n(v___y_2451_, 4);
lean_inc_n(v___y_2444_, 15);
v___x_2454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2454_, 0, v___y_2444_);
lean_ctor_set(v___x_2454_, 1, v___y_2451_);
lean_ctor_set(v___x_2454_, 2, v___y_2450_);
v___x_2455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___y_2444_);
lean_ctor_set(v___x_2455_, 1, v___x_2452_);
v___x_2456_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__29));
lean_inc_ref_n(v___y_2446_, 4);
v___x_2457_ = l_Lean_Name_mkStr4(v___x_2437_, v___x_2438_, v___y_2446_, v___x_2456_);
v___x_2458_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__31));
v___x_2459_ = l_Lean_Name_mkStr4(v___x_2437_, v___x_2438_, v___y_2446_, v___x_2458_);
v___x_2460_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
v___x_2461_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___y_2444_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__34));
v___x_2463_ = l_Lean_Name_mkStr4(v___x_2437_, v___x_2438_, v___y_2446_, v___x_2462_);
v___x_2464_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
v___x_2465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___y_2444_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
lean_inc_ref(v___y_2449_);
v___x_2466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___y_2444_);
lean_ctor_set(v___x_2466_, 1, v___y_2449_);
lean_inc_ref(v___x_2466_);
lean_inc(v___y_2442_);
lean_inc_ref(v___x_2465_);
lean_inc(v___x_2463_);
v___x_2467_ = l_Lean_Syntax_node3(v___y_2444_, v___x_2463_, v___x_2465_, v___y_2442_, v___x_2466_);
v___x_2468_ = l_Lean_Syntax_node1(v___y_2444_, v___y_2451_, v___x_2467_);
v___x_2469_ = l_Lean_Syntax_node1(v___y_2444_, v___y_2451_, v___x_2468_);
v___x_2470_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
v___x_2471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___y_2444_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__4));
v___x_2473_ = l_Lean_Name_mkStr4(v___x_2437_, v___x_2438_, v___y_2446_, v___x_2472_);
v___x_2474_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__5));
v___x_2475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___y_2444_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
lean_inc(v___y_2448_);
v___x_2476_ = l_Lean_Syntax_node3(v___y_2444_, v___x_2463_, v___x_2465_, v___y_2448_, v___x_2466_);
v___x_2477_ = l_Lean_Syntax_node2(v___y_2444_, v___x_2473_, v___x_2475_, v___x_2476_);
v___x_2478_ = l_Lean_Syntax_node4(v___y_2444_, v___x_2459_, v___x_2461_, v___x_2469_, v___x_2471_, v___x_2477_);
v___x_2479_ = l_Lean_Syntax_node1(v___y_2444_, v___y_2451_, v___x_2478_);
v___x_2480_ = l_Lean_Syntax_node1(v___y_2444_, v___x_2457_, v___x_2479_);
lean_inc_n(v___y_2447_, 2);
lean_inc_ref_n(v___x_2454_, 2);
v___x_2481_ = l_Lean_Syntax_node6(v___y_2444_, v___x_2453_, v___x_2454_, v___x_2454_, v___y_2447_, v___x_2455_, v___x_2454_, v___x_2480_);
v___x_2482_ = l_Lean_Elab_Command_isLocalAttrKind(v___y_2447_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_Elab_Command_elabCommand(v___x_2481_, v___y_2443_, v___y_2445_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_dec_ref_known(v___x_2483_, 1);
v___y_2411_ = v___y_2442_;
v___y_2412_ = v___y_2447_;
v___y_2413_ = v___y_2448_;
v___y_2414_ = v___y_2443_;
v___y_2415_ = v___y_2445_;
goto v___jp_2410_;
}
else
{
lean_dec(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec(v___y_2442_);
return v___x_2483_;
}
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v_scopes_2486_; lean_object* v___x_2487_; lean_object* v_opts_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2484_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2485_ = lean_st_ref_get(v___y_2445_);
v_scopes_2486_ = lean_ctor_get(v___x_2485_, 2);
lean_inc(v_scopes_2486_);
lean_dec(v___x_2485_);
v___x_2487_ = l_List_head_x21___redArg(v___x_2484_, v_scopes_2486_);
lean_dec(v_scopes_2486_);
v_opts_2488_ = lean_ctor_get(v___x_2487_, 1);
lean_inc_ref(v_opts_2488_);
lean_dec(v___x_2487_);
v___x_2489_ = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
v___x_2490_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_2488_, v___x_2489_, v___x_2440_);
v___f_2491_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___lam__0), 2, 1);
lean_closure_set(v___f_2491_, 0, v___x_2490_);
v___x_2492_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_2492_, 0, v___x_2481_);
v___x_2493_ = l_Lean_Elab_Command_withScope___redArg(v___f_2491_, v___x_2492_, v___y_2443_, v___y_2445_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_dec_ref_known(v___x_2493_, 1);
v___y_2411_ = v___y_2442_;
v___y_2412_ = v___y_2447_;
v___y_2413_ = v___y_2448_;
v___y_2414_ = v___y_2443_;
v___y_2415_ = v___y_2445_;
goto v___jp_2410_;
}
else
{
lean_dec(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec(v___y_2442_);
return v___x_2493_;
}
}
}
v___jp_2494_:
{
size_t v_sz_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; size_t v_sz_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v_sz_2509_ = lean_array_size(v___y_2508_);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(v_sz_2509_, v___y_2496_, v___y_2508_);
v___x_2511_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(v___x_2510_, v___y_2507_);
lean_dec_ref(v___x_2510_);
v_sz_2512_ = lean_array_size(v___y_2502_);
v___x_2513_ = lean_box_usize(v_sz_2512_);
v___x_2514_ = lean_box_usize(v___y_2496_);
v___x_2515_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed), 5, 3);
lean_closure_set(v___x_2515_, 0, v___x_2513_);
lean_closure_set(v___x_2515_, 1, v___x_2514_);
lean_closure_set(v___x_2515_, 2, v___y_2502_);
v___x_2516_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2515_, v___y_2495_, v___y_2503_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v___x_2518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2518_, 0, v___y_2501_);
lean_ctor_set(v___x_2518_, 1, v___y_2499_);
lean_ctor_set(v___x_2518_, 2, v_a_2517_);
v___x_2519_ = l_Lean_Elab_Command_getRef___redArg(v___y_2495_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v___x_2521_ = l_Lean_SourceInfo_fromRef(v_a_2520_, v___y_2504_);
lean_dec(v_a_2520_);
v___x_2522_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2495_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_quotContext_x3f_2523_; 
lean_dec_ref_known(v___x_2522_, 1);
v_quotContext_x3f_2523_ = lean_ctor_get(v___y_2495_, 5);
if (lean_obj_tag(v_quotContext_x3f_2523_) == 0)
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2503_);
lean_dec_ref(v___x_2524_);
v___y_2442_ = v___x_2518_;
v___y_2443_ = v___y_2495_;
v___y_2444_ = v___x_2521_;
v___y_2445_ = v___y_2503_;
v___y_2446_ = v___y_2497_;
v___y_2447_ = v___y_2498_;
v___y_2448_ = v___x_2511_;
v___y_2449_ = v___y_2505_;
v___y_2450_ = v___y_2506_;
v___y_2451_ = v___y_2500_;
goto v___jp_2441_;
}
else
{
v___y_2442_ = v___x_2518_;
v___y_2443_ = v___y_2495_;
v___y_2444_ = v___x_2521_;
v___y_2445_ = v___y_2503_;
v___y_2446_ = v___y_2497_;
v___y_2447_ = v___y_2498_;
v___y_2448_ = v___x_2511_;
v___y_2449_ = v___y_2505_;
v___y_2450_ = v___y_2506_;
v___y_2451_ = v___y_2500_;
goto v___jp_2441_;
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec(v___x_2521_);
lean_dec_ref_known(v___x_2518_, 3);
lean_dec(v___x_2511_);
lean_dec(v___y_2498_);
v_a_2525_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2522_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2522_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec_ref_known(v___x_2518_, 3);
lean_dec(v___x_2511_);
lean_dec(v___y_2498_);
v_a_2533_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2519_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2519_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v___x_2511_);
lean_dec(v___y_2501_);
lean_dec(v___y_2499_);
lean_dec(v___y_2498_);
v_a_2541_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2516_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2516_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___boxed(lean_object* v_x_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lean_Elab_Command_elabNotation(v_x_2917_, v_a_2918_, v_a_2919_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(lean_object* v_00_u03b1_2922_, lean_object* v_x_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v_x_2923_, v___y_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2927_, lean_object* v_x_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(v_00_u03b1_2927_, v_x_2928_, v___y_2929_, v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec_ref(v_x_2928_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(lean_object* v_00_u03b1_2932_, lean_object* v_ref_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_2933_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___boxed(lean_object* v_00_u03b1_2938_, lean_object* v_ref_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(v_00_u03b1_2938_, v_ref_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(lean_object* v_00_u03b1_2944_, lean_object* v_x_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v___x_2949_; 
v___x_2949_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2945_, v___y_2946_, v___y_2947_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___boxed(lean_object* v_00_u03b1_2950_, lean_object* v_x_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(v_00_u03b1_2950_, v_x_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(lean_object* v_msgData_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msgData_2956_, v___y_2958_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(v_msgData_2961_, v___y_2962_, v___y_2963_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(lean_object* v_as_2966_, lean_object* v_as_x27_2967_, lean_object* v_b_2968_, lean_object* v_a_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_2967_, v_b_2968_, v___y_2970_, v___y_2971_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___boxed(lean_object* v_as_2974_, lean_object* v_as_x27_2975_, lean_object* v_b_2976_, lean_object* v_a_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(v_as_2974_, v_as_x27_2975_, v_b_2976_, v_a_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v_as_x27_2975_);
lean_dec(v_as_2974_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(lean_object* v_00_u03b1_2982_, lean_object* v_ref_2983_, lean_object* v_msg_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_ref_2983_, v_msg_2984_, v___y_2985_, v___y_2986_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___boxed(lean_object* v_00_u03b1_2989_, lean_object* v_ref_2990_, lean_object* v_msg_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(v_00_u03b1_2989_, v_ref_2990_, v_msg_2991_, v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v_ref_2990_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2996_, lean_object* v_m_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v_m_2997_, v_a_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_3000_, lean_object* v_m_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(v_00_u03b2_3000_, v_m_3001_, v_a_3002_);
lean_dec(v_a_3002_);
lean_dec_ref(v_m_3001_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(lean_object* v_00_u03b1_3004_, lean_object* v_msg_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_3005_, v___y_3006_, v___y_3007_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___boxed(lean_object* v_00_u03b1_3010_, lean_object* v_msg_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(v_00_u03b1_3010_, v_msg_3011_, v___y_3012_, v___y_3013_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
return v_res_3015_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(lean_object* v_00_u03b2_3016_, lean_object* v_x_3017_, lean_object* v_x_3018_){
_start:
{
uint8_t v___x_3019_; 
v___x_3019_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_3017_, v_x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3020_, lean_object* v_x_3021_, lean_object* v_x_3022_){
_start:
{
uint8_t v_res_3023_; lean_object* v_r_3024_; 
v_res_3023_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(v_00_u03b2_3020_, v_x_3021_, v_x_3022_);
lean_dec_ref(v_x_3022_);
lean_dec_ref(v_x_3021_);
v_r_3024_ = lean_box(v_res_3023_);
return v_r_3024_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(lean_object* v_00_u03b2_3025_, lean_object* v_a_3026_, lean_object* v_x_3027_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_3026_, v_x_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___boxed(lean_object* v_00_u03b2_3029_, lean_object* v_a_3030_, lean_object* v_x_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(v_00_u03b2_3029_, v_a_3030_, v_x_3031_);
lean_dec(v_x_3031_);
lean_dec(v_a_3030_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(lean_object* v_msgData_3033_, lean_object* v_macroStack_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_msgData_3033_, v_macroStack_3034_, v___y_3036_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___boxed(lean_object* v_msgData_3039_, lean_object* v_macroStack_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(v_msgData_3039_, v_macroStack_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
return v_res_3044_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(lean_object* v_00_u03b2_3045_, lean_object* v_x_3046_, size_t v_x_3047_, lean_object* v_x_3048_){
_start:
{
uint8_t v___x_3049_; 
v___x_3049_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_3046_, v_x_3047_, v_x_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___boxed(lean_object* v_00_u03b2_3050_, lean_object* v_x_3051_, lean_object* v_x_3052_, lean_object* v_x_3053_){
_start:
{
size_t v_x_23227__boxed_3054_; uint8_t v_res_3055_; lean_object* v_r_3056_; 
v_x_23227__boxed_3054_ = lean_unbox_usize(v_x_3052_);
lean_dec(v_x_3052_);
v_res_3055_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(v_00_u03b2_3050_, v_x_3051_, v_x_23227__boxed_3054_, v_x_3053_);
lean_dec_ref(v_x_3053_);
lean_dec_ref(v_x_3051_);
v_r_3056_ = lean_box(v_res_3055_);
return v_r_3056_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(lean_object* v_00_u03b2_3057_, lean_object* v_keys_3058_, lean_object* v_vals_3059_, lean_object* v_heq_3060_, lean_object* v_i_3061_, lean_object* v_k_3062_){
_start:
{
uint8_t v___x_3063_; 
v___x_3063_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_3058_, v_i_3061_, v_k_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___boxed(lean_object* v_00_u03b2_3064_, lean_object* v_keys_3065_, lean_object* v_vals_3066_, lean_object* v_heq_3067_, lean_object* v_i_3068_, lean_object* v_k_3069_){
_start:
{
uint8_t v_res_3070_; lean_object* v_r_3071_; 
v_res_3070_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(v_00_u03b2_3064_, v_keys_3065_, v_vals_3066_, v_heq_3067_, v_i_3068_, v_k_3069_);
lean_dec_ref(v_k_3069_);
lean_dec_ref(v_vals_3066_);
lean_dec_ref(v_keys_3065_);
v_r_3071_ = lean_box(v_res_3070_);
return v_r_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1(){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3079_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3080_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
v___x_3081_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1));
v___x_3082_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___boxed), 4, 0);
v___x_3083_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3079_, v___x_3080_, v___x_3081_, v___x_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___boxed(lean_object* v_a_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
return v_res_3085_;
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
