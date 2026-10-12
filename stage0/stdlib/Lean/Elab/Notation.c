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
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(lean_object* v_id_1_, lean_object* v_as_2_, size_t v_i_3_, size_t v_stop_4_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_1_ = stack[0].m_obj;
lean_object* v_as_2_ = stack[1].m_obj;
size_t v_i_3_ = stack[2].m_num;
size_t v_stop_4_ = stack[3].m_num;
uint8_t v_res_14_;
v_res_14_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(v_id_1_, v_as_2_, v_i_3_, v_stop_4_);
stack->m_num = v_res_14_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1___boxed(lean_object* v_id_15_, lean_object* v_as_16_, lean_object* v_i_17_, lean_object* v_stop_18_){
_start:
{
size_t v_i_boxed_19_; size_t v_stop_boxed_20_; uint8_t v_res_21_; lean_object* v_r_22_; 
v_i_boxed_19_ = lean_unbox_usize(v_i_17_);
lean_dec(v_i_17_);
v_stop_boxed_20_ = lean_unbox_usize(v_stop_18_);
lean_dec(v_stop_18_);
v_res_21_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(v_id_15_, v_as_16_, v_i_boxed_19_, v_stop_boxed_20_);
lean_dec_ref(v_as_16_);
lean_dec(v_id_15_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(lean_object* v_vars_29_, lean_object* v_x_30_){
_start:
{
lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_31_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_x_30_);
v___x_32_ = l_Lean_Syntax_isOfKind(v_x_30_, v___x_31_);
if (v___x_32_ == 0)
{
if (lean_obj_tag(v_x_30_) == 1)
{
lean_object* v_info_33_; lean_object* v_kind_34_; lean_object* v_args_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_45_; 
v_info_33_ = lean_ctor_get(v_x_30_, 0);
v_kind_34_ = lean_ctor_get(v_x_30_, 1);
v_args_35_ = lean_ctor_get(v_x_30_, 2);
v_isSharedCheck_45_ = !lean_is_exclusive(v_x_30_);
if (v_isSharedCheck_45_ == 0)
{
v___x_37_ = v_x_30_;
v_isShared_38_ = v_isSharedCheck_45_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_args_35_);
lean_inc(v_kind_34_);
lean_inc(v_info_33_);
lean_dec(v_x_30_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_45_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
size_t v_sz_39_; size_t v___x_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
v_sz_39_ = lean_array_size(v_args_35_);
v___x_40_ = ((size_t)0ULL);
v___x_41_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(v_vars_29_, v_sz_39_, v___x_40_, v_args_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 2, v___x_41_);
v___x_43_ = v___x_37_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_info_33_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_kind_34_);
lean_ctor_set(v_reuseFailAlloc_44_, 2, v___x_41_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
else
{
return v_x_30_;
}
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = lean_array_get_size(v_vars_29_);
v___x_48_ = lean_nat_dec_lt(v___x_46_, v___x_47_);
if (v___x_48_ == 0)
{
return v_x_30_;
}
else
{
if (v___x_48_ == 0)
{
return v_x_30_;
}
else
{
size_t v___x_49_; size_t v___x_50_; uint8_t v___x_51_; 
v___x_49_ = ((size_t)0ULL);
v___x_50_ = lean_usize_of_nat(v___x_47_);
v___x_51_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(v_x_30_, v_vars_29_, v___x_49_, v___x_50_);
if (v___x_51_ == 0)
{
return v_x_30_;
}
else
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
v___x_53_ = lean_box(0);
v___x_54_ = l_Lean_Syntax_mkAntiquotNode(v___x_52_, v_x_30_, v___x_46_, v___x_53_, v___x_32_);
return v___x_54_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(lean_object* v_vars_55_, size_t v_sz_56_, size_t v_i_57_, lean_object* v_bs_58_){
_start:
{
uint8_t v___x_59_; 
v___x_59_ = lean_usize_dec_lt(v_i_57_, v_sz_56_);
if (v___x_59_ == 0)
{
return v_bs_58_;
}
else
{
lean_object* v_v_60_; lean_object* v___x_61_; lean_object* v_bs_x27_62_; lean_object* v___x_63_; size_t v___x_64_; size_t v___x_65_; lean_object* v___x_66_; 
v_v_60_ = lean_array_uget(v_bs_58_, v_i_57_);
v___x_61_ = lean_unsigned_to_nat(0u);
v_bs_x27_62_ = lean_array_uset(v_bs_58_, v_i_57_, v___x_61_);
v___x_63_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(v_vars_55_, v_v_60_);
v___x_64_ = ((size_t)1ULL);
v___x_65_ = lean_usize_add(v_i_57_, v___x_64_);
v___x_66_ = lean_array_uset(v_bs_x27_62_, v_i_57_, v___x_63_);
v_i_57_ = v___x_65_;
v_bs_58_ = v___x_66_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_vars_55_ = stack[0].m_obj;
size_t v_sz_56_ = stack[1].m_num;
size_t v_i_57_ = stack[2].m_num;
lean_object* v_bs_58_ = stack[3].m_obj;
lean_object* v_res_68_;
v_res_68_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(v_vars_55_, v_sz_56_, v_i_57_, v_bs_58_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0___boxed(lean_object* v_vars_69_, lean_object* v_sz_70_, lean_object* v_i_71_, lean_object* v_bs_72_){
_start:
{
size_t v_sz_boxed_73_; size_t v_i_boxed_74_; lean_object* v_res_75_; 
v_sz_boxed_73_ = lean_unbox_usize(v_sz_70_);
lean_dec(v_sz_70_);
v_i_boxed_74_ = lean_unbox_usize(v_i_71_);
lean_dec(v_i_71_);
v_res_75_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(v_vars_69_, v_sz_boxed_73_, v_i_boxed_74_, v_bs_72_);
lean_dec_ref(v_vars_69_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___boxed(lean_object* v_vars_76_, lean_object* v_x_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(v_vars_76_, v_x_77_);
lean_dec_ref(v_vars_76_);
return v_res_78_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14(void){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Array_mkArray0___redArg();
return v___x_107_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(uint8_t v___x_108_, lean_object* v___x_109_, size_t v_sz_110_, size_t v_i_111_, lean_object* v_bs_112_){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = lean_usize_dec_lt(v_i_111_, v_sz_110_);
if (v___x_113_ == 0)
{
lean_dec(v___x_109_);
return v_bs_112_;
}
else
{
lean_object* v___x_114_; lean_object* v_v_115_; lean_object* v___x_116_; lean_object* v_bs_x27_117_; lean_object* v___y_119_; uint8_t v___x_124_; 
v___x_114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
v_v_115_ = lean_array_uget(v_bs_112_, v_i_111_);
v___x_116_ = lean_unsigned_to_nat(0u);
v_bs_x27_117_ = lean_array_uset(v_bs_112_, v_i_111_, v___x_116_);
lean_inc(v_v_115_);
v___x_124_ = l_Lean_Syntax_isOfKind(v_v_115_, v___x_114_);
if (v___x_124_ == 0)
{
v___y_119_ = v_v_115_;
goto v___jp_118_;
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_125_ = l_Lean_Syntax_getArg(v_v_115_, v___x_116_);
v___x_126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(v___x_125_);
v___x_127_ = l_Lean_Syntax_isOfKind(v___x_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_dec(v___x_125_);
v___y_119_ = v_v_115_;
goto v___jp_118_;
}
else
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = l_Lean_Syntax_getArg(v___x_125_, v___x_116_);
lean_dec(v___x_125_);
v___x_129_ = l_Lean_Syntax_matchesNull(v___x_128_, v___x_116_);
if (v___x_129_ == 0)
{
v___y_119_ = v_v_115_;
goto v___jp_118_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = l_Lean_Syntax_getArg(v_v_115_, v___x_130_);
v___x_132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
lean_inc(v___x_131_);
v___x_133_ = l_Lean_Syntax_isOfKind(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_dec(v___x_131_);
v___y_119_ = v_v_115_;
goto v___jp_118_;
}
else
{
lean_object* v___x_134_; lean_object* v_attr_135_; 
v___x_134_ = lean_box(0);
v_attr_135_ = l_Lean_Syntax_getArg(v___x_131_, v___x_116_);
if (v___x_108_ == 0)
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_attr_135_);
v___x_152_ = l_Lean_Syntax_isOfKind(v_attr_135_, v___x_151_);
if (v___x_152_ == 0)
{
lean_dec(v_attr_135_);
lean_dec(v___x_131_);
v___y_119_ = v_v_115_;
goto v___jp_118_;
}
else
{
goto v___jp_136_;
}
}
else
{
goto v___jp_136_;
}
v___jp_136_:
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = l_Lean_Syntax_getArg(v___x_131_, v___x_130_);
lean_dec(v___x_131_);
v___x_138_ = l_Lean_Syntax_matchesNull(v___x_137_, v___x_116_);
if (v___x_138_ == 0)
{
lean_dec(v_attr_135_);
v___y_119_ = v_v_115_;
goto v___jp_118_;
}
else
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_139_ = l_Lean_TSyntax_getId(v_attr_135_);
v___x_140_ = l_Lean_Name_eraseMacroScopes(v___x_139_);
lean_dec(v___x_139_);
v___x_141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11));
v___x_142_ = lean_name_eq(v___x_140_, v___x_141_);
lean_dec(v___x_140_);
if (v___x_142_ == 0)
{
lean_dec(v_attr_135_);
v___y_119_ = v_v_115_;
goto v___jp_118_;
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v_v_115_);
v___x_143_ = l_Lean_SourceInfo_fromRef(v___x_134_, v___x_108_);
v___x_144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_145_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
lean_inc_n(v___x_143_, 4);
v___x_146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_146_, 0, v___x_143_);
lean_ctor_set(v___x_146_, 1, v___x_144_);
lean_ctor_set(v___x_146_, 2, v___x_145_);
v___x_147_ = l_Lean_Syntax_node1(v___x_143_, v___x_126_, v___x_146_);
lean_inc(v___x_109_);
v___x_148_ = l_Lean_Syntax_node1(v___x_143_, v___x_144_, v___x_109_);
v___x_149_ = l_Lean_Syntax_node2(v___x_143_, v___x_132_, v_attr_135_, v___x_148_);
v___x_150_ = l_Lean_Syntax_node2(v___x_143_, v___x_114_, v___x_147_, v___x_149_);
v___y_119_ = v___x_150_;
goto v___jp_118_;
}
}
}
}
}
}
}
v___jp_118_:
{
size_t v___x_120_; size_t v___x_121_; lean_object* v___x_122_; 
v___x_120_ = ((size_t)1ULL);
v___x_121_ = lean_usize_add(v_i_111_, v___x_120_);
v___x_122_ = lean_array_uset(v_bs_x27_117_, v_i_111_, v___y_119_);
v_i_111_ = v___x_121_;
v_bs_112_ = v___x_122_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_108_ = stack[0].m_num;
lean_object* v___x_109_ = stack[1].m_obj;
size_t v_sz_110_ = stack[2].m_num;
size_t v_i_111_ = stack[3].m_num;
lean_object* v_bs_112_ = stack[4].m_obj;
lean_object* v_res_153_;
v_res_153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(v___x_108_, v___x_109_, v_sz_110_, v_i_111_, v_bs_112_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___boxed(lean_object* v___x_154_, lean_object* v___x_155_, lean_object* v_sz_156_, lean_object* v_i_157_, lean_object* v_bs_158_){
_start:
{
uint8_t v___x_7302__boxed_159_; size_t v_sz_boxed_160_; size_t v_i_boxed_161_; lean_object* v_res_162_; 
v___x_7302__boxed_159_ = lean_unbox(v___x_154_);
v_sz_boxed_160_ = lean_unbox_usize(v_sz_156_);
lean_dec(v_sz_156_);
v_i_boxed_161_ = lean_unbox_usize(v_i_157_);
lean_dec(v_i_157_);
v_res_162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(v___x_7302__boxed_159_, v___x_155_, v_sz_boxed_160_, v_i_boxed_161_, v_bs_158_);
return v_res_162_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0(void){
_start:
{
uint8_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = 0;
v___x_164_ = lean_box(0);
v___x_165_ = l_Lean_SourceInfo_fromRef(v___x_164_, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_166_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
v___x_167_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_168_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0);
v___x_169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
lean_ctor_set(v___x_169_, 2, v___x_166_);
return v___x_169_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1);
v___x_171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
v___x_172_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0);
v___x_173_ = l_Lean_Syntax_node1(v___x_172_, v___x_171_, v___x_170_);
return v___x_173_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(lean_object* v___x_174_, size_t v_sz_175_, size_t v_i_176_, lean_object* v_bs_177_){
_start:
{
uint8_t v___x_178_; 
v___x_178_ = lean_usize_dec_lt(v_i_176_, v_sz_175_);
if (v___x_178_ == 0)
{
lean_dec(v___x_174_);
return v_bs_177_;
}
else
{
lean_object* v___x_179_; lean_object* v_v_180_; lean_object* v___x_181_; lean_object* v_bs_x27_182_; lean_object* v___y_184_; uint8_t v___x_189_; 
v___x_179_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4));
v_v_180_ = lean_array_uget(v_bs_177_, v_i_176_);
v___x_181_ = lean_unsigned_to_nat(0u);
v_bs_x27_182_ = lean_array_uset(v_bs_177_, v_i_176_, v___x_181_);
lean_inc(v_v_180_);
v___x_189_ = l_Lean_Syntax_isOfKind(v_v_180_, v___x_179_);
if (v___x_189_ == 0)
{
v___y_184_ = v_v_180_;
goto v___jp_183_;
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_190_ = l_Lean_Syntax_getArg(v_v_180_, v___x_181_);
v___x_191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(v___x_190_);
v___x_192_ = l_Lean_Syntax_isOfKind(v___x_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_dec(v___x_190_);
v___y_184_ = v_v_180_;
goto v___jp_183_;
}
else
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = l_Lean_Syntax_getArg(v___x_190_, v___x_181_);
lean_dec(v___x_190_);
v___x_194_ = l_Lean_Syntax_matchesNull(v___x_193_, v___x_181_);
if (v___x_194_ == 0)
{
v___y_184_ = v_v_180_;
goto v___jp_183_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = l_Lean_Syntax_getArg(v_v_180_, v___x_195_);
v___x_197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9));
lean_inc(v___x_196_);
v___x_198_ = l_Lean_Syntax_isOfKind(v___x_196_, v___x_197_);
if (v___x_198_ == 0)
{
lean_dec(v___x_196_);
v___y_184_ = v_v_180_;
goto v___jp_183_;
}
else
{
lean_object* v___x_199_; lean_object* v_attr_200_; uint8_t v___x_201_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
v_attr_200_ = l_Lean_Syntax_getArg(v___x_196_, v___x_181_);
lean_inc(v_attr_200_);
v___x_201_ = l_Lean_Syntax_isOfKind(v_attr_200_, v___x_199_);
if (v___x_201_ == 0)
{
lean_dec(v_attr_200_);
lean_dec(v___x_196_);
v___y_184_ = v_v_180_;
goto v___jp_183_;
}
else
{
lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_202_ = l_Lean_Syntax_getArg(v___x_196_, v___x_195_);
lean_dec(v___x_196_);
v___x_203_ = l_Lean_Syntax_matchesNull(v___x_202_, v___x_181_);
if (v___x_203_ == 0)
{
lean_dec(v_attr_200_);
v___y_184_ = v_v_180_;
goto v___jp_183_;
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_204_ = l_Lean_TSyntax_getId(v_attr_200_);
v___x_205_ = l_Lean_Name_eraseMacroScopes(v___x_204_);
lean_dec(v___x_204_);
v___x_206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11));
v___x_207_ = lean_name_eq(v___x_205_, v___x_206_);
lean_dec(v___x_205_);
if (v___x_207_ == 0)
{
lean_dec(v_attr_200_);
v___y_184_ = v_v_180_;
goto v___jp_183_;
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v_v_180_);
v___x_208_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0);
v___x_209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_210_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2);
lean_inc(v___x_174_);
v___x_211_ = l_Lean_Syntax_node1(v___x_208_, v___x_209_, v___x_174_);
v___x_212_ = l_Lean_Syntax_node2(v___x_208_, v___x_197_, v_attr_200_, v___x_211_);
v___x_213_ = l_Lean_Syntax_node2(v___x_208_, v___x_179_, v___x_210_, v___x_212_);
v___y_184_ = v___x_213_;
goto v___jp_183_;
}
}
}
}
}
}
}
v___jp_183_:
{
size_t v___x_185_; size_t v___x_186_; lean_object* v___x_187_; 
v___x_185_ = ((size_t)1ULL);
v___x_186_ = lean_usize_add(v_i_176_, v___x_185_);
v___x_187_ = lean_array_uset(v_bs_x27_182_, v_i_176_, v___y_184_);
v_i_176_ = v___x_186_;
v_bs_177_ = v___x_187_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_174_ = stack[0].m_obj;
size_t v_sz_175_ = stack[1].m_num;
size_t v_i_176_ = stack[2].m_num;
lean_object* v_bs_177_ = stack[3].m_obj;
lean_object* v_res_214_;
v_res_214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(v___x_174_, v_sz_175_, v_i_176_, v_bs_177_);
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___boxed(lean_object* v___x_215_, lean_object* v_sz_216_, lean_object* v_i_217_, lean_object* v_bs_218_){
_start:
{
size_t v_sz_boxed_219_; size_t v_i_boxed_220_; lean_object* v_res_221_; 
v_sz_boxed_219_ = lean_unbox_usize(v_sz_216_);
lean_dec(v_sz_216_);
v_i_boxed_220_ = lean_unbox_usize(v_i_217_);
lean_dec(v_i_217_);
v_res_221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(v___x_215_, v_sz_boxed_219_, v_i_boxed_220_, v_bs_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addInheritDocDefault(lean_object* v_rhs_229_, lean_object* v_attrs_x3f_230_){
_start:
{
if (lean_obj_tag(v_attrs_x3f_230_) == 0)
{
lean_dec(v_rhs_229_);
return v_attrs_x3f_230_;
}
else
{
lean_object* v_val_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v_val_231_ = lean_ctor_get(v_attrs_x3f_230_, 0);
v___x_232_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
lean_inc(v_rhs_229_);
v___x_233_ = l_Lean_Syntax_isOfKind(v_rhs_229_, v___x_232_);
if (v___x_233_ == 0)
{
if (v___x_233_ == 0)
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_rhs_229_);
v___x_243_ = l_Lean_Syntax_isOfKind(v_rhs_229_, v___x_242_);
if (v___x_243_ == 0)
{
lean_dec(v_rhs_229_);
return v_attrs_x3f_230_;
}
else
{
lean_inc(v_val_231_);
lean_dec_ref_known(v_attrs_x3f_230_, 1);
goto v___jp_234_;
}
}
else
{
lean_inc(v_val_231_);
lean_dec_ref_known(v_attrs_x3f_230_, 1);
goto v___jp_234_;
}
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = l_Lean_Syntax_getArg(v_rhs_229_, v___x_244_);
lean_dec(v_rhs_229_);
v___x_246_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v___x_245_);
v___x_247_ = l_Lean_Syntax_isOfKind(v___x_245_, v___x_246_);
if (v___x_247_ == 0)
{
lean_dec(v___x_245_);
return v_attrs_x3f_230_;
}
else
{
lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_260_; 
lean_inc(v_val_231_);
v_isSharedCheck_260_ = !lean_is_exclusive(v_attrs_x3f_230_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; 
v_unused_261_ = lean_ctor_get(v_attrs_x3f_230_, 0);
lean_dec(v_unused_261_);
v___x_249_ = v_attrs_x3f_230_;
v_isShared_250_ = v_isSharedCheck_260_;
goto v_resetjp_248_;
}
else
{
lean_dec(v_attrs_x3f_230_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_260_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_252_; size_t v_sz_253_; size_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_251_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__2));
v___x_252_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_231_);
lean_dec(v_val_231_);
v_sz_253_ = lean_array_size(v___x_252_);
v___x_254_ = ((size_t)0ULL);
v___x_255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(v___x_245_, v_sz_253_, v___x_254_, v___x_252_);
v___x_256_ = l_Lean_Syntax_SepArray_ofElems(v___x_251_, v___x_255_);
lean_dec_ref(v___x_255_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_256_);
v___x_258_ = v___x_249_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
v___jp_234_:
{
lean_object* v___x_235_; lean_object* v___x_236_; size_t v_sz_237_; size_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_235_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__2));
v___x_236_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_231_);
lean_dec(v_val_231_);
v_sz_237_ = lean_array_size(v___x_236_);
v___x_238_ = ((size_t)0ULL);
v___x_239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(v___x_233_, v_rhs_229_, v_sz_237_, v___x_238_, v___x_236_);
v___x_240_ = l_Lean_Syntax_SepArray_ofElems(v___x_235_, v___x_239_);
lean_dec_ref(v___x_239_);
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2));
v___x_270_ = l_String_toRawSubstring_x27(v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(lean_object* v_x_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v_prec_x3f_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
lean_inc(v_x_301_);
v___x_341_ = l_Lean_Syntax_isOfKind(v_x_301_, v___x_340_);
if (v___x_341_ == 0)
{
if (v___x_341_ == 0)
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
lean_inc(v_x_301_);
v___x_349_ = l_Lean_Syntax_isOfKind(v_x_301_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16));
lean_inc(v_x_301_);
v___x_351_ = l_Lean_Syntax_isOfKind(v_x_301_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
lean_dec(v_x_301_);
v___x_352_ = l_Lean_Macro_throwUnsupported___redArg(v_a_303_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; 
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v_x_301_);
lean_ctor_set(v___x_353_, 1, v_a_303_);
return v___x_353_;
}
}
else
{
goto v___jp_342_;
}
}
else
{
goto v___jp_342_;
}
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = l_Lean_Syntax_getArg(v_x_301_, v___x_354_);
v___x_356_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
v___x_357_ = l_Lean_Syntax_isOfKind(v___x_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16));
lean_inc(v_x_301_);
v___x_359_ = l_Lean_Syntax_isOfKind(v_x_301_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
lean_dec(v_x_301_);
v___x_360_ = l_Lean_Macro_throwUnsupported___redArg(v_a_303_);
return v___x_360_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_x_301_);
lean_ctor_set(v___x_361_, 1, v_a_303_);
return v___x_361_;
}
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = l_Lean_Syntax_getArg(v_x_301_, v___x_362_);
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
v___x_366_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16));
lean_inc(v_x_301_);
v___x_367_ = l_Lean_Syntax_isOfKind(v_x_301_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
lean_dec(v_x_301_);
v___x_368_ = l_Lean_Macro_throwUnsupported___redArg(v_a_303_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; 
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_x_301_);
lean_ctor_set(v___x_369_, 1, v_a_303_);
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
v___x_373_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16));
lean_inc(v_x_301_);
v___x_374_ = l_Lean_Syntax_isOfKind(v_x_301_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; 
lean_dec(v_x_301_);
v___x_375_ = l_Lean_Macro_throwUnsupported___redArg(v_a_303_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; 
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v_x_301_);
lean_ctor_set(v___x_376_, 1, v_a_303_);
return v___x_376_;
}
}
else
{
lean_object* v_prec_x3f_377_; lean_object* v___x_378_; 
lean_dec(v_x_301_);
v_prec_x3f_377_ = l_Lean_Syntax_getArg(v___x_370_, v___x_362_);
lean_dec(v___x_370_);
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v_prec_x3f_377_);
v_prec_x3f_317_ = v___x_378_;
v___y_318_ = v_a_302_;
v___y_319_ = v_a_303_;
goto v___jp_316_;
}
}
}
else
{
lean_object* v___x_379_; 
lean_dec(v___x_363_);
lean_dec(v_x_301_);
v___x_379_ = lean_box(0);
v_prec_x3f_317_ = v___x_379_;
v___y_318_ = v_a_302_;
v___y_319_ = v_a_303_;
goto v___jp_316_;
}
}
}
v___jp_304_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_inc_ref(v___y_310_);
v___x_312_ = l_Array_append___redArg(v___y_310_, v___y_311_);
lean_dec_ref(v___y_311_);
lean_inc(v___y_308_);
lean_inc(v___y_309_);
v___x_313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_313_, 0, v___y_309_);
lean_ctor_set(v___x_313_, 1, v___y_308_);
lean_ctor_set(v___x_313_, 2, v___x_312_);
lean_inc(v___y_306_);
v___x_314_ = l_Lean_Syntax_node2(v___y_309_, v___y_306_, v___y_307_, v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___y_305_);
return v___x_315_;
}
v___jp_316_:
{
lean_object* v_quotContext_320_; lean_object* v_currMacroScope_321_; lean_object* v_ref_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_quotContext_320_ = lean_ctor_get(v___y_318_, 1);
v_currMacroScope_321_ = lean_ctor_get(v___y_318_, 2);
v_ref_322_ = lean_ctor_get(v___y_318_, 5);
v___x_323_ = 0;
v___x_324_ = l_Lean_SourceInfo_fromRef(v_ref_322_, v___x_323_);
v___x_325_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2));
v___x_326_ = lean_obj_once(&l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3, &l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3_once, _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3);
v___x_327_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
lean_inc(v_currMacroScope_321_);
lean_inc(v_quotContext_320_);
v___x_328_ = l_Lean_addMacroScope(v_quotContext_320_, v___x_327_, v_currMacroScope_321_);
v___x_329_ = lean_box(0);
lean_inc(v___x_324_);
v___x_330_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_330_, 0, v___x_324_);
lean_ctor_set(v___x_330_, 1, v___x_326_);
lean_ctor_set(v___x_330_, 2, v___x_328_);
lean_ctor_set(v___x_330_, 3, v___x_329_);
v___x_331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_332_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
if (lean_obj_tag(v_prec_x3f_317_) == 1)
{
lean_object* v_val_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_val_333_ = lean_ctor_get(v_prec_x3f_317_, 0);
lean_inc(v_val_333_);
lean_dec_ref_known(v_prec_x3f_317_, 1);
v___x_334_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
v___x_335_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc_n(v___x_324_, 2);
v___x_336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_324_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = l_Lean_Syntax_node2(v___x_324_, v___x_334_, v___x_336_, v_val_333_);
v___x_338_ = l_Array_mkArray1___redArg(v___x_337_);
v___y_305_ = v___y_319_;
v___y_306_ = v___x_325_;
v___y_307_ = v___x_330_;
v___y_308_ = v___x_331_;
v___y_309_ = v___x_324_;
v___y_310_ = v___x_332_;
v___y_311_ = v___x_338_;
goto v___jp_304_;
}
else
{
lean_object* v___x_339_; 
lean_dec(v_prec_x3f_317_);
v___x_339_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_305_ = v___y_319_;
v___y_306_ = v___x_325_;
v___y_307_ = v___x_330_;
v___y_308_ = v___x_331_;
v___y_309_ = v___x_324_;
v___y_310_ = v___x_332_;
v___y_311_ = v___x_339_;
goto v___jp_304_;
}
}
v___jp_342_:
{
lean_object* v_ref_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_ref_343_ = lean_ctor_get(v_a_302_, 5);
v___x_344_ = l_Lean_SourceInfo_fromRef(v_ref_343_, v___x_341_);
v___x_345_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12));
v___x_346_ = l_Lean_Syntax_node1(v___x_344_, v___x_345_, v_x_301_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v_a_303_);
return v___x_347_;
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
v___x_397_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14));
v___x_398_ = lean_name_eq(v_k_394_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16));
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(size_t v_sz_610_, size_t v_i_611_, lean_object* v_bs_612_, lean_object* v___y_613_, lean_object* v___y_614_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_610_ = stack[0].m_num;
size_t v_i_611_ = stack[1].m_num;
lean_object* v_bs_612_ = stack[2].m_obj;
lean_object* v___y_613_ = stack[3].m_obj;
lean_object* v___y_614_ = stack[4].m_obj;
lean_object* v_res_636_;
v_res_636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_610_, v_i_611_, v_bs_612_, v___y_613_, v___y_614_);
stack->m_obj
 = v_res_636_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0___boxed(lean_object* v_sz_637_, lean_object* v_i_638_, lean_object* v_bs_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
size_t v_sz_boxed_642_; size_t v_i_boxed_643_; lean_object* v_res_644_; 
v_sz_boxed_642_ = lean_unbox_usize(v_sz_637_);
lean_dec(v_sz_637_);
v_i_boxed_643_ = lean_unbox_usize(v_i_638_);
lean_dec(v_i_638_);
v_res_644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_boxed_642_, v_i_boxed_643_, v_bs_639_, v___y_640_, v___y_641_);
lean_dec_ref(v___y_640_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses___boxed(lean_object* v_stx_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_Elab_Command_removeParentheses(v_stx_645_, v_a_646_, v_a_647_);
lean_dec_ref(v_a_646_);
return v_res_648_;
}
}
lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(lean_object* v___x_652_, uint8_t v_firstChoiceOnly_653_, lean_object* v_stx_654_, lean_object* v_b_655_){
_start:
{
lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v_snd_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_704_; 
v_snd_668_ = lean_ctor_get(v_b_655_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_b_655_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v_b_655_, 0);
lean_dec(v_unused_705_);
v___x_670_ = v_b_655_;
v_isShared_671_ = v_isSharedCheck_704_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_snd_668_);
lean_dec(v_b_655_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_704_;
goto v_resetjp_669_;
}
v___jp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; size_t v_sz_661_; size_t v___x_662_; lean_object* v___x_663_; lean_object* v_fst_664_; 
v___x_659_ = lean_box(0);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v___y_657_);
v_sz_661_ = lean_array_size(v___y_658_);
v___x_662_ = ((size_t)0ULL);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v___x_652_, v_firstChoiceOnly_653_, v___y_658_, v_sz_661_, v___x_662_, v___x_660_);
v_fst_664_ = lean_ctor_get(v___x_663_, 0);
if (lean_obj_tag(v_fst_664_) == 0)
{
lean_object* v_snd_665_; lean_object* v___x_666_; 
v_snd_665_ = lean_ctor_get(v___x_663_, 1);
lean_inc(v_snd_665_);
lean_dec_ref(v___x_663_);
v___x_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_666_, 0, v_snd_665_);
return v___x_666_;
}
else
{
lean_object* v_val_667_; 
lean_inc_ref(v_fst_664_);
lean_dec_ref(v___x_663_);
v_val_667_ = lean_ctor_get(v_fst_664_, 0);
lean_inc(v_val_667_);
lean_dec_ref_known(v_fst_664_, 1);
return v_val_667_;
}
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___y_675_; lean_object* v_a_676_; uint8_t v___x_685_; 
v___x_672_ = lean_box(0);
v___x_673_ = lean_box(0);
v___x_685_ = l_Lean_Syntax_isAntiquot(v_stx_654_);
if (v___x_685_ == 0)
{
lean_object* v___x_687_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_672_);
v___x_687_ = v___x_670_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_snd_668_);
v___x_687_ = v_reuseFailAlloc_689_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_688_; 
lean_inc_ref(v___x_687_);
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
v___y_675_ = v___x_688_;
v_a_676_ = v___x_687_;
goto v___jp_674_;
}
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = l_Lean_Syntax_getAntiquotTerm(v_stx_654_);
v___x_691_ = l_Lean_Syntax_getId(v___x_690_);
lean_dec(v___x_690_);
v___x_692_ = l_Lean_NameSet_contains(v_snd_668_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_693_ = l_Lean_NameSet_insert(v_snd_668_, v___x_691_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___x_693_);
lean_ctor_set(v___x_670_, 0, v___x_672_);
v___x_695_ = v___x_670_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_693_);
v___x_695_ = v_reuseFailAlloc_697_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; 
lean_inc_ref(v___x_695_);
v___x_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
v___y_675_ = v___x_696_;
v_a_676_ = v___x_695_;
goto v___jp_674_;
}
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
lean_dec(v___x_691_);
v___x_698_ = lean_box(v___x_692_);
v___x_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_699_);
v___x_701_ = v___x_670_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_snd_668_);
v___x_701_ = v_reuseFailAlloc_703_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
}
}
v___jp_674_:
{
if (lean_obj_tag(v_stx_654_) == 1)
{
lean_dec_ref(v___y_675_);
if (v_firstChoiceOnly_653_ == 0)
{
lean_object* v_args_677_; 
v_args_677_ = lean_ctor_get(v_stx_654_, 2);
v___y_657_ = v_a_676_;
v___y_658_ = v_args_677_;
goto v___jp_656_;
}
else
{
lean_object* v_kind_678_; lean_object* v_args_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_kind_678_ = lean_ctor_get(v_stx_654_, 1);
v_args_679_ = lean_ctor_get(v_stx_654_, 2);
v___x_680_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1));
v___x_681_ = lean_name_eq(v_kind_678_, v___x_680_);
if (v___x_681_ == 0)
{
v___y_657_ = v_a_676_;
v___y_658_ = v_args_679_;
goto v___jp_656_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_array_get_borrowed(v___x_673_, v_args_679_, v___x_682_);
v_stx_654_ = v___x_683_;
v_b_655_ = v_a_676_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_a_676_);
return v___y_675_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_652_ = stack[0].m_obj;
uint8_t v_firstChoiceOnly_653_ = stack[1].m_num;
lean_object* v_stx_654_ = stack[2].m_obj;
lean_object* v_b_655_ = stack[3].m_obj;
lean_object* v_res_706_;
v_res_706_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_652_, v_firstChoiceOnly_653_, v_stx_654_, v_b_655_);
stack->m_obj
 = v_res_706_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(lean_object* v___x_707_, uint8_t v_firstChoiceOnly_708_, lean_object* v_as_709_, size_t v_sz_710_, size_t v_i_711_, lean_object* v_b_712_){
_start:
{
uint8_t v___x_713_; 
v___x_713_ = lean_usize_dec_lt(v_i_711_, v_sz_710_);
if (v___x_713_ == 0)
{
return v_b_712_;
}
else
{
lean_object* v_snd_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_732_; 
v_snd_714_ = lean_ctor_get(v_b_712_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_b_712_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v_b_712_, 0);
lean_dec(v_unused_733_);
v___x_716_ = v_b_712_;
v_isShared_717_ = v_isSharedCheck_732_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_snd_714_);
lean_dec(v_b_712_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_732_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_a_718_; lean_object* v___x_719_; 
v_a_718_ = lean_array_uget_borrowed(v_as_709_, v_i_711_);
lean_inc(v_snd_714_);
v___x_719_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_707_, v_firstChoiceOnly_708_, v_a_718_, v_snd_714_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_720_);
v___x_722_ = v___x_716_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_snd_714_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
lean_dec(v_snd_714_);
v_a_724_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_719_, 1);
v___x_725_ = lean_box(0);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v_a_724_);
lean_ctor_set(v___x_716_, 0, v___x_725_);
v___x_727_ = v___x_716_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_a_724_);
v___x_727_ = v_reuseFailAlloc_731_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
size_t v___x_728_; size_t v___x_729_; 
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_add(v_i_711_, v___x_728_);
v_i_711_ = v___x_729_;
v_b_712_ = v___x_727_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_707_ = stack[0].m_obj;
uint8_t v_firstChoiceOnly_708_ = stack[1].m_num;
lean_object* v_as_709_ = stack[2].m_obj;
size_t v_sz_710_ = stack[3].m_num;
size_t v_i_711_ = stack[4].m_num;
lean_object* v_b_712_ = stack[5].m_obj;
lean_object* v_res_734_;
v_res_734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v___x_707_, v_firstChoiceOnly_708_, v_as_709_, v_sz_710_, v_i_711_, v_b_712_);
stack->m_obj
 = v_res_734_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0___boxed(lean_object* v___x_735_, lean_object* v_firstChoiceOnly_736_, lean_object* v_as_737_, lean_object* v_sz_738_, lean_object* v_i_739_, lean_object* v_b_740_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_741_; size_t v_sz_boxed_742_; size_t v_i_boxed_743_; lean_object* v_res_744_; 
v_firstChoiceOnly_boxed_741_ = lean_unbox(v_firstChoiceOnly_736_);
v_sz_boxed_742_ = lean_unbox_usize(v_sz_738_);
lean_dec(v_sz_738_);
v_i_boxed_743_ = lean_unbox_usize(v_i_739_);
lean_dec(v_i_739_);
v_res_744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v___x_735_, v_firstChoiceOnly_boxed_741_, v_as_737_, v_sz_boxed_742_, v_i_boxed_743_, v_b_740_);
lean_dec_ref(v_as_737_);
lean_dec_ref(v___x_735_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___boxed(lean_object* v___x_745_, lean_object* v_firstChoiceOnly_746_, lean_object* v_stx_747_, lean_object* v_b_748_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_749_; lean_object* v_res_750_; 
v_firstChoiceOnly_boxed_749_ = lean_unbox(v_firstChoiceOnly_746_);
v_res_750_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_745_, v_firstChoiceOnly_boxed_749_, v_stx_747_, v_b_748_);
lean_dec(v_stx_747_);
lean_dec_ref(v___x_745_);
return v_res_750_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(lean_object* v_as_751_, size_t v_sz_752_, size_t v_i_753_, lean_object* v_b_754_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = lean_usize_dec_lt(v_i_753_, v_sz_752_);
if (v___x_755_ == 0)
{
return v_b_754_;
}
else
{
lean_object* v_snd_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_794_; 
v_snd_756_ = lean_ctor_get(v_b_754_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_b_754_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v_b_754_, 0);
lean_dec(v_unused_795_);
v___x_758_ = v_b_754_;
v_isShared_759_ = v_isSharedCheck_794_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_snd_756_);
lean_dec(v_b_754_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_794_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v_a_760_; lean_object* v___x_761_; uint8_t v_firstChoiceOnly_762_; lean_object* v_stx_763_; lean_object* v___x_764_; lean_object* v___y_766_; lean_object* v___x_790_; 
v_a_760_ = lean_array_uget_borrowed(v_as_751_, v_i_753_);
lean_inc(v_a_760_);
v___x_761_ = l_Lean_Syntax_topDown(v_a_760_, v___x_755_);
v_firstChoiceOnly_762_ = lean_ctor_get_uint8(v___x_761_, sizeof(void*)*1);
v_stx_763_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_stx_763_);
lean_dec_ref(v___x_761_);
v___x_764_ = lean_box(0);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_764_);
v___x_790_ = v___x_758_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_snd_756_);
v___x_790_ = v_reuseFailAlloc_793_;
goto v_reusejp_789_;
}
v___jp_765_:
{
lean_object* v_fst_767_; 
v_fst_767_ = lean_ctor_get(v___y_766_, 0);
if (lean_obj_tag(v_fst_767_) == 0)
{
lean_object* v_snd_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_778_; 
v_snd_768_ = lean_ctor_get(v___y_766_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v___y_766_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v___y_766_, 0);
lean_dec(v_unused_779_);
v___x_770_ = v___y_766_;
v_isShared_771_ = v_isSharedCheck_778_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_snd_768_);
lean_dec(v___y_766_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_778_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_764_);
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_snd_768_);
v___x_773_ = v_reuseFailAlloc_777_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
size_t v___x_774_; size_t v___x_775_; 
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_753_, v___x_774_);
v_i_753_ = v___x_775_;
v_b_754_ = v___x_773_;
goto _start;
}
}
}
else
{
lean_object* v_snd_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_inc_ref(v_fst_767_);
v_snd_780_ = lean_ctor_get(v___y_766_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v___y_766_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v___y_766_, 0);
lean_dec(v_unused_788_);
v___x_782_ = v___y_766_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_snd_780_);
lean_dec(v___y_766_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_fst_767_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_snd_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
v_reusejp_789_:
{
lean_object* v___x_791_; lean_object* v_a_792_; 
lean_inc_ref(v___x_790_);
v___x_791_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_790_, v_firstChoiceOnly_762_, v_stx_763_, v___x_790_);
lean_dec(v_stx_763_);
lean_dec_ref(v___x_790_);
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref(v___x_791_);
v___y_766_ = v_a_792_;
goto v___jp_765_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_751_ = stack[0].m_obj;
size_t v_sz_752_ = stack[1].m_num;
size_t v_i_753_ = stack[2].m_num;
lean_object* v_b_754_ = stack[3].m_obj;
lean_object* v_res_796_;
v_res_796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(v_as_751_, v_sz_752_, v_i_753_, v_b_754_);
stack->m_obj
 = v_res_796_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1___boxed(lean_object* v_as_797_, lean_object* v_sz_798_, lean_object* v_i_799_, lean_object* v_b_800_){
_start:
{
size_t v_sz_boxed_801_; size_t v_i_boxed_802_; lean_object* v_res_803_; 
v_sz_boxed_801_ = lean_unbox_usize(v_sz_798_);
lean_dec(v_sz_798_);
v_i_boxed_802_ = lean_unbox_usize(v_i_799_);
lean_dec(v_i_799_);
v_res_803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(v_as_797_, v_sz_boxed_801_, v_i_boxed_802_, v_b_800_);
lean_dec_ref(v_as_797_);
return v_res_803_;
}
}
static lean_object* _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0(void){
_start:
{
lean_object* v_seen_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_seen_804_ = l_Lean_NameSet_empty;
v___x_805_ = lean_box(0);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v_seen_804_);
return v___x_806_;
}
}
uint8_t l_Lean_Elab_Command_hasDuplicateAntiquot(lean_object* v_stxs_807_){
_start:
{
lean_object* v___x_808_; size_t v_sz_809_; size_t v___x_810_; lean_object* v___x_811_; lean_object* v_fst_812_; 
v___x_808_ = lean_obj_once(&l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0, &l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0_once, _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0);
v_sz_809_ = lean_array_size(v_stxs_807_);
v___x_810_ = ((size_t)0ULL);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(v_stxs_807_, v_sz_809_, v___x_810_, v___x_808_);
v_fst_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_fst_812_);
lean_dec_ref(v___x_811_);
if (lean_obj_tag(v_fst_812_) == 0)
{
uint8_t v___x_813_; 
v___x_813_ = 0;
return v___x_813_;
}
else
{
lean_object* v_val_814_; uint8_t v___x_815_; 
v_val_814_ = lean_ctor_get(v_fst_812_, 0);
lean_inc(v_val_814_);
lean_dec_ref_known(v_fst_812_, 1);
v___x_815_ = lean_unbox(v_val_814_);
lean_dec(v_val_814_);
return v___x_815_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_hasDuplicateAntiquot_0interp(lean_interpreter_value* stack)
{
lean_object* v_stxs_807_ = stack[0].m_obj;
uint8_t v_res_816_;
v_res_816_ = l_Lean_Elab_Command_hasDuplicateAntiquot(v_stxs_807_);
stack->m_num = v_res_816_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___boxed(lean_object* v_stxs_817_){
_start:
{
uint8_t v_res_818_; lean_object* v_r_819_; 
v_res_818_ = l_Lean_Elab_Command_hasDuplicateAntiquot(v_stxs_817_);
lean_dec_ref(v_stxs_817_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__4(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__3));
v___x_827_ = l_String_toRawSubstring_x27(v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__15(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__14));
v___x_849_ = l_String_toRawSubstring_x27(v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__19(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__18));
v___x_855_ = l_String_toRawSubstring_x27(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__22(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__21));
v___x_860_ = l_String_toRawSubstring_x27(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__40(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__39));
v___x_898_ = l_String_toRawSubstring_x27(v___x_897_);
return v___x_898_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__47(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__46));
v___x_913_ = l_String_toRawSubstring_x27(v___x_912_);
return v___x_913_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__55(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_929_ = l_String_toRawSubstring_x27(v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander(lean_object* v_attrKind_967_, lean_object* v_pat_968_, lean_object* v_qrhs_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v___y_973_; lean_object* v_fst_977_; lean_object* v_snd_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = ((lean_object*)(l_Lean_Elab_Command_addInheritDocDefault___closed__1));
lean_inc(v_qrhs_969_);
v___x_1176_ = l_Lean_Syntax_isOfKind(v_qrhs_969_, v___x_1175_);
if (v___x_1176_ == 0)
{
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_qrhs_969_);
v___x_1178_ = l_Lean_Syntax_isOfKind(v_qrhs_969_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec(v_qrhs_969_);
lean_dec(v_pat_968_);
lean_dec(v_attrKind_967_);
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v_a_971_);
return v___x_1180_;
}
else
{
goto v___jp_1173_;
}
}
else
{
goto v___jp_1173_;
}
}
else
{
lean_object* v___x_1181_; lean_object* v_c_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1181_ = lean_unsigned_to_nat(0u);
v_c_1182_ = l_Lean_Syntax_getArg(v_qrhs_969_, v___x_1181_);
v___x_1183_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1));
lean_inc(v_c_1182_);
v___x_1184_ = l_Lean_Syntax_isOfKind(v_c_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec(v_c_1182_);
lean_dec(v_qrhs_969_);
lean_dec(v_pat_968_);
lean_dec(v_attrKind_967_);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v_a_971_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v_args_1189_; 
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = l_Lean_Syntax_getArg(v_qrhs_969_, v___x_1187_);
lean_dec(v_qrhs_969_);
v_args_1189_ = l_Lean_Syntax_getArgs(v___x_1188_);
lean_dec(v___x_1188_);
v_fst_977_ = v_c_1182_;
v_snd_978_ = v_args_1189_;
v___y_979_ = v_a_970_;
v___y_980_ = v_a_971_;
goto v___jp_976_;
}
}
v___jp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_box(0);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___y_973_);
return v___x_975_;
}
v___jp_976_:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = l_Lean_TSyntax_getId(v_fst_977_);
lean_dec(v_fst_977_);
v___x_982_ = l_Lean_Macro_resolveGlobalName(v___x_981_, v___y_979_, v___y_980_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
if (lean_obj_tag(v_a_983_) == 1)
{
lean_object* v_head_984_; lean_object* v_snd_985_; 
v_head_984_ = lean_ctor_get(v_a_983_, 0);
lean_inc(v_head_984_);
v_snd_985_ = lean_ctor_get(v_head_984_, 1);
lean_inc(v_snd_985_);
if (lean_obj_tag(v_snd_985_) == 0)
{
lean_object* v_tail_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1160_; 
v_tail_986_ = lean_ctor_get(v_a_983_, 1);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_a_983_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v_a_983_, 0);
lean_dec(v_unused_1161_);
v___x_988_ = v_a_983_;
v_isShared_989_ = v_isSharedCheck_1160_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_tail_986_);
lean_dec(v_a_983_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1160_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
if (lean_obj_tag(v_tail_986_) == 0)
{
lean_object* v_a_990_; lean_object* v_fst_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1157_; 
v_a_990_ = lean_ctor_get(v___x_982_, 1);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_982_, 2);
v_fst_991_ = lean_ctor_get(v_head_984_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_head_984_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; 
v_unused_1158_ = lean_ctor_get(v_head_984_, 1);
lean_dec(v_unused_1158_);
v___x_993_ = v_head_984_;
v_isShared_994_ = v_isSharedCheck_1157_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_fst_991_);
lean_dec(v_head_984_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1157_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
size_t v_sz_995_; size_t v___x_996_; lean_object* v___x_997_; 
v_sz_995_ = lean_array_size(v_snd_978_);
v___x_996_ = ((size_t)0ULL);
v___x_997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_995_, v___x_996_, v_snd_978_, v___y_979_, v_a_990_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1147_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_a_999_ = lean_ctor_get(v___x_997_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1001_ = v___x_997_;
v_isShared_1002_ = v_isSharedCheck_1147_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1147_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
uint8_t v___x_1003_; 
v___x_1003_ = l_Lean_Elab_Command_hasDuplicateAntiquot(v_a_998_);
if (v___x_1003_ == 0)
{
lean_object* v_quotContext_1004_; lean_object* v_currMacroScope_1005_; lean_object* v_ref_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v_quotContext_1004_ = lean_ctor_get(v___y_979_, 1);
v_currMacroScope_1005_ = lean_ctor_get(v___y_979_, 2);
v_ref_1006_ = lean_ctor_get(v___y_979_, 5);
v___x_1007_ = l_Lean_SourceInfo_fromRef(v_ref_1006_, v___x_1003_);
v___x_1008_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0));
v___x_1009_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__1));
v___x_1010_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__2));
lean_inc(v___x_1007_);
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 2);
lean_ctor_set(v___x_993_, 1, v___x_1010_);
lean_ctor_set(v___x_993_, 0, v___x_1007_);
v___x_1012_ = v___x_993_;
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
lean_inc_n(v_currMacroScope_1005_, 4);
lean_inc_n(v_quotContext_1004_, 4);
v___x_1018_ = l_Lean_addMacroScope(v_quotContext_1004_, v___x_1017_, v_currMacroScope_1005_);
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
v___x_1027_ = l_Lean_Syntax_mkApp(v___x_1026_, v_a_998_);
lean_inc(v_attrKind_967_);
v___x_1028_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_967_);
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
v___x_1038_ = l_Lean_addMacroScope(v_quotContext_1004_, v___x_1037_, v_currMacroScope_1005_);
v___x_1039_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1007_);
lean_ctor_set(v___x_1039_, 1, v___x_1036_);
lean_ctor_set(v___x_1039_, 2, v___x_1038_);
lean_ctor_set(v___x_1039_, 3, v___x_1019_);
v___x_1040_ = l_Lean_mkIdent(v_fst_991_);
lean_inc(v___x_1040_);
v___x_1041_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1013_, v___x_1040_);
v___x_1042_ = l_Lean_Syntax_node2(v___x_1007_, v___x_1035_, v___x_1039_, v___x_1041_);
v___x_1043_ = l_Lean_Syntax_node2(v___x_1007_, v___x_1034_, v_attrKind_967_, v___x_1042_);
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
v___x_1052_ = l_Lean_addMacroScope(v_quotContext_1004_, v___x_1051_, v_currMacroScope_1005_);
v___x_1053_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1007_);
lean_ctor_set(v___x_1053_, 1, v___x_1050_);
lean_ctor_set(v___x_1053_, 2, v___x_1052_);
lean_ctor_set(v___x_1053_, 3, v___x_1019_);
v___x_1054_ = l_Lean_Syntax_node2(v___x_1007_, v___x_1013_, v___x_1053_, v___x_1040_);
v___x_1055_ = lean_obj_once(&l_Lean_Elab_Command_mkUnexpander___closed__22, &l_Lean_Elab_Command_mkUnexpander___closed__22_once, _init_l_Lean_Elab_Command_mkUnexpander___closed__22);
v___x_1056_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__25));
v___x_1057_ = l_Lean_addMacroScope(v_quotContext_1004_, v___x_1056_, v_currMacroScope_1005_);
v___x_1058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v_snd_985_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 1, v___x_1019_);
lean_ctor_set(v___x_988_, 0, v___x_1058_);
v___x_1060_ = v___x_988_;
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
lean_inc_n(v_currMacroScope_1005_, 3);
lean_inc_n(v_quotContext_1004_, 3);
v___x_1084_ = l_Lean_addMacroScope(v_quotContext_1004_, v___x_1083_, v_currMacroScope_1005_);
v___x_1085_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__42));
v___x_1086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v_snd_985_);
v___x_1087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v___x_1019_);
v___x_1088_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1007_);
lean_ctor_set(v___x_1088_, 1, v___x_1082_);
lean_ctor_set(v___x_1088_, 2, v___x_1084_);
lean_ctor_set(v___x_1088_, 3, v___x_1087_);
v___x_1089_ = l_Lean_Syntax_node3(v___x_1007_, v___x_1071_, v___x_1073_, v_pat_968_, v___x_1075_);
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
v___x_1101_ = l_Lean_addMacroScope(v_quotContext_1004_, v___x_1100_, v_currMacroScope_1005_);
v___x_1102_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__50));
v___x_1103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v_snd_985_);
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
v___x_1113_ = l_Lean_addMacroScope(v_quotContext_1004_, v___x_1112_, v_currMacroScope_1005_);
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
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1137_);
v___x_1139_ = v___x_1001_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_a_999_);
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
else
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
lean_dec(v_a_998_);
lean_del_object(v___x_993_);
lean_dec(v_fst_991_);
lean_del_object(v___x_988_);
lean_dec(v_pat_968_);
lean_dec(v_attrKind_967_);
v___x_1143_ = lean_box(0);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1143_);
v___x_1145_ = v___x_1001_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_a_999_);
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
else
{
lean_object* v_a_1148_; lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_del_object(v___x_993_);
lean_dec(v_fst_991_);
lean_del_object(v___x_988_);
lean_dec(v_pat_968_);
lean_dec(v_attrKind_967_);
v_a_1148_ = lean_ctor_get(v___x_997_, 0);
v_a_1149_ = lean_ctor_get(v___x_997_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_997_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_inc(v_a_1148_);
lean_dec(v___x_997_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1148_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
else
{
lean_object* v_a_1159_; 
lean_del_object(v___x_988_);
lean_dec(v_tail_986_);
lean_dec(v_head_984_);
lean_dec_ref(v_snd_978_);
lean_dec(v_pat_968_);
lean_dec(v_attrKind_967_);
v_a_1159_ = lean_ctor_get(v___x_982_, 1);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_982_, 2);
v___y_973_ = v_a_1159_;
goto v___jp_972_;
}
}
}
else
{
lean_object* v_a_1162_; 
lean_dec(v_snd_985_);
lean_dec_ref_known(v_a_983_, 2);
lean_dec(v_head_984_);
lean_dec_ref(v_snd_978_);
lean_dec(v_pat_968_);
lean_dec(v_attrKind_967_);
v_a_1162_ = lean_ctor_get(v___x_982_, 1);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_982_, 2);
v___y_973_ = v_a_1162_;
goto v___jp_972_;
}
}
else
{
lean_object* v_a_1163_; 
lean_dec(v_a_983_);
lean_dec_ref(v_snd_978_);
lean_dec(v_pat_968_);
lean_dec(v_attrKind_967_);
v_a_1163_ = lean_ctor_get(v___x_982_, 1);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_982_, 2);
v___y_973_ = v_a_1163_;
goto v___jp_972_;
}
}
else
{
lean_object* v_a_1164_; lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec_ref(v_snd_978_);
lean_dec(v_pat_968_);
lean_dec(v_attrKind_967_);
v_a_1164_ = lean_ctor_get(v___x_982_, 0);
v_a_1165_ = lean_ctor_get(v___x_982_, 1);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_982_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_inc(v_a_1164_);
lean_dec(v___x_982_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1164_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
v___jp_1173_:
{
lean_object* v___x_1174_; 
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__68));
v_fst_977_ = v_qrhs_969_;
v_snd_978_ = v___x_1174_;
v___y_979_ = v_a_970_;
v___y_980_ = v_a_971_;
goto v___jp_976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander___boxed(lean_object* v_attrKind_1190_, lean_object* v_pat_1191_, lean_object* v_qrhs_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Elab_Command_mkUnexpander(v_attrKind_1190_, v_pat_1191_, v_qrhs_1192_, v_a_1193_, v_a_1194_);
lean_dec_ref(v_a_1193_);
return v_res_1195_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_box(0);
v___x_1197_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v___x_1196_);
return v___x_1198_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg(){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0);
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1202_;
v_res_1202_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
stack->m_obj
 = v_res_1202_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___boxed(lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v_res_1204_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(lean_object* v_00_u03b1_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_1209_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1206_ = stack[1].m_obj;
lean_object* v___y_1207_ = stack[2].m_obj;
lean_object* v_res_1210_;
v_res_1210_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(lean_box(0), v___y_1206_, v___y_1207_);
stack->m_obj
 = v_res_1210_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___boxed(lean_object* v_00_u03b1_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(v_00_u03b1_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
return v_res_1215_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; lean_object* v_env_1219_; lean_object* v___x_1220_; lean_object* v_mainModule_1221_; lean_object* v___x_1222_; 
v___x_1218_ = lean_st_ref_get(v___y_1216_);
v_env_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc_ref(v_env_1219_);
lean_dec(v___x_1218_);
v___x_1220_ = l_Lean_Environment_header(v_env_1219_);
lean_dec_ref(v_env_1219_);
v_mainModule_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_mainModule_1221_);
lean_dec_ref(v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v_mainModule_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1216_ = stack[0].m_obj;
lean_object* v_res_1223_;
v_res_1223_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_1216_);
stack->m_obj
 = v_res_1223_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg___boxed(lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_1224_);
lean_dec(v___y_1224_);
return v_res_1226_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1227_ = stack[0].m_obj;
lean_object* v___y_1228_ = stack[1].m_obj;
lean_object* v_res_1231_;
v_res_1231_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(v___y_1227_, v___y_1228_);
stack->m_obj
 = v_res_1231_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___boxed(lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___lam__0(lean_object* v___x_1236_, lean_object* v_sc_1237_){
_start:
{
lean_object* v_header_1238_; lean_object* v_currNamespace_1239_; lean_object* v_openDecls_1240_; lean_object* v_levelNames_1241_; lean_object* v_varDecls_1242_; lean_object* v_varUIds_1243_; lean_object* v_includedVars_1244_; lean_object* v_omittedVars_1245_; uint8_t v_isNoncomputable_1246_; uint8_t v_isPublic_1247_; uint8_t v_isMeta_1248_; lean_object* v_attrs_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
v_header_1238_ = lean_ctor_get(v_sc_1237_, 0);
v_currNamespace_1239_ = lean_ctor_get(v_sc_1237_, 2);
v_openDecls_1240_ = lean_ctor_get(v_sc_1237_, 3);
v_levelNames_1241_ = lean_ctor_get(v_sc_1237_, 4);
v_varDecls_1242_ = lean_ctor_get(v_sc_1237_, 5);
v_varUIds_1243_ = lean_ctor_get(v_sc_1237_, 6);
v_includedVars_1244_ = lean_ctor_get(v_sc_1237_, 7);
v_omittedVars_1245_ = lean_ctor_get(v_sc_1237_, 8);
v_isNoncomputable_1246_ = lean_ctor_get_uint8(v_sc_1237_, sizeof(void*)*10);
v_isPublic_1247_ = lean_ctor_get_uint8(v_sc_1237_, sizeof(void*)*10 + 1);
v_isMeta_1248_ = lean_ctor_get_uint8(v_sc_1237_, sizeof(void*)*10 + 2);
v_attrs_1249_ = lean_ctor_get(v_sc_1237_, 9);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_sc_1237_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v_sc_1237_, 1);
lean_dec(v_unused_1257_);
v___x_1251_ = v_sc_1237_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_attrs_1249_);
lean_inc(v_omittedVars_1245_);
lean_inc(v_includedVars_1244_);
lean_inc(v_varUIds_1243_);
lean_inc(v_varDecls_1242_);
lean_inc(v_levelNames_1241_);
lean_inc(v_openDecls_1240_);
lean_inc(v_currNamespace_1239_);
lean_inc(v_header_1238_);
lean_dec(v_sc_1237_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v___x_1236_);
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_header_1238_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v_currNamespace_1239_);
lean_ctor_set(v_reuseFailAlloc_1255_, 3, v_openDecls_1240_);
lean_ctor_set(v_reuseFailAlloc_1255_, 4, v_levelNames_1241_);
lean_ctor_set(v_reuseFailAlloc_1255_, 5, v_varDecls_1242_);
lean_ctor_set(v_reuseFailAlloc_1255_, 6, v_varUIds_1243_);
lean_ctor_set(v_reuseFailAlloc_1255_, 7, v_includedVars_1244_);
lean_ctor_set(v_reuseFailAlloc_1255_, 8, v_omittedVars_1245_);
lean_ctor_set(v_reuseFailAlloc_1255_, 9, v_attrs_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1255_, sizeof(void*)*10, v_isNoncomputable_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1255_, sizeof(void*)*10 + 1, v_isPublic_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1255_, sizeof(void*)*10 + 2, v_isMeta_1248_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(size_t v_sz_1258_, size_t v_i_1259_, lean_object* v_bs_1260_){
_start:
{
uint8_t v___x_1261_; 
v___x_1261_ = lean_usize_dec_lt(v_i_1259_, v_sz_1258_);
if (v___x_1261_ == 0)
{
return v_bs_1260_;
}
else
{
lean_object* v_v_1262_; lean_object* v___x_1263_; lean_object* v_bs_x27_1264_; size_t v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; 
v_v_1262_ = lean_array_uget(v_bs_1260_, v_i_1259_);
v___x_1263_ = lean_unsigned_to_nat(0u);
v_bs_x27_1264_ = lean_array_uset(v_bs_1260_, v_i_1259_, v___x_1263_);
v___x_1265_ = ((size_t)1ULL);
v___x_1266_ = lean_usize_add(v_i_1259_, v___x_1265_);
v___x_1267_ = lean_array_uset(v_bs_x27_1264_, v_i_1259_, v_v_1262_);
v_i_1259_ = v___x_1266_;
v_bs_1260_ = v___x_1267_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1258_ = stack[0].m_num;
size_t v_i_1259_ = stack[1].m_num;
lean_object* v_bs_1260_ = stack[2].m_obj;
lean_object* v_res_1269_;
v_res_1269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_1258_, v_i_1259_, v_bs_1260_);
stack->m_obj
 = v_res_1269_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3___boxed(lean_object* v_sz_1270_, lean_object* v_i_1271_, lean_object* v_bs_1272_){
_start:
{
size_t v_sz_boxed_1273_; size_t v_i_boxed_1274_; lean_object* v_res_1275_; 
v_sz_boxed_1273_ = lean_unbox_usize(v_sz_1270_);
lean_dec(v_sz_1270_);
v_i_boxed_1274_ = lean_unbox_usize(v_i_1271_);
lean_dec(v_i_1271_);
v_res_1275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_boxed_1273_, v_i_boxed_1274_, v_bs_1272_);
return v_res_1275_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(lean_object* v_o_1279_, lean_object* v_k_1280_, uint8_t v_v_1281_){
_start:
{
lean_object* v_map_1282_; uint8_t v_hasTrace_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1297_; 
v_map_1282_ = lean_ctor_get(v_o_1279_, 0);
v_hasTrace_1283_ = lean_ctor_get_uint8(v_o_1279_, sizeof(void*)*1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_o_1279_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1285_ = v_o_1279_;
v_isShared_1286_ = v_isSharedCheck_1297_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_map_1282_);
lean_dec(v_o_1279_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1297_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1287_, 0, v_v_1281_);
lean_inc(v_k_1280_);
v___x_1288_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1280_, v___x_1287_, v_map_1282_);
if (v_hasTrace_1283_ == 0)
{
lean_object* v___x_1289_; uint8_t v___x_1290_; lean_object* v___x_1292_; 
v___x_1289_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
v___x_1290_ = l_Lean_Name_isPrefixOf(v___x_1289_, v_k_1280_);
lean_dec(v_k_1280_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1288_);
v___x_1292_ = v___x_1285_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1288_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*1, v___x_1290_);
return v___x_1292_;
}
}
else
{
lean_object* v___x_1295_; 
lean_dec(v_k_1280_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1288_);
v___x_1295_ = v___x_1285_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*1, v_hasTrace_1283_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_1279_ = stack[0].m_obj;
lean_object* v_k_1280_ = stack[1].m_obj;
uint8_t v_v_1281_ = stack[2].m_num;
lean_object* v_res_1298_;
v_res_1298_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(v_o_1279_, v_k_1280_, v_v_1281_);
stack->m_obj
 = v_res_1298_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___boxed(lean_object* v_o_1299_, lean_object* v_k_1300_, lean_object* v_v_1301_){
_start:
{
uint8_t v_v_boxed_1302_; lean_object* v_res_1303_; 
v_v_boxed_1302_ = lean_unbox(v_v_1301_);
v_res_1303_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(v_o_1299_, v_k_1300_, v_v_boxed_1302_);
return v_res_1303_;
}
}
lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(lean_object* v_opts_1304_, lean_object* v_opt_1305_, uint8_t v_val_1306_){
_start:
{
lean_object* v_name_1307_; lean_object* v___x_1308_; 
v_name_1307_ = lean_ctor_get(v_opt_1305_, 0);
lean_inc(v_name_1307_);
lean_dec_ref(v_opt_1305_);
v___x_1308_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(v_opts_1304_, v_name_1307_, v_val_1306_);
return v___x_1308_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1304_ = stack[0].m_obj;
lean_object* v_opt_1305_ = stack[1].m_obj;
uint8_t v_val_1306_ = stack[2].m_num;
lean_object* v_res_1309_;
v_res_1309_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_1304_, v_opt_1305_, v_val_1306_);
stack->m_obj
 = v_res_1309_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6___boxed(lean_object* v_opts_1310_, lean_object* v_opt_1311_, lean_object* v_val_1312_){
_start:
{
uint8_t v_val_boxed_1313_; lean_object* v_res_1314_; 
v_val_boxed_1313_ = lean_unbox(v_val_1312_);
v_res_1314_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_1310_, v_opt_1311_, v_val_boxed_1313_);
return v_res_1314_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(size_t v_sz_1315_, size_t v_i_1316_, lean_object* v_bs_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
uint8_t v___x_1320_; 
v___x_1320_ = lean_usize_dec_lt(v_i_1316_, v_sz_1315_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v_bs_1317_);
lean_ctor_set(v___x_1321_, 1, v___y_1319_);
return v___x_1321_;
}
else
{
lean_object* v_v_1322_; lean_object* v___x_1323_; 
v_v_1322_ = lean_array_uget_borrowed(v_bs_1317_, v_i_1316_);
lean_inc(v_v_1322_);
v___x_1323_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(v_v_1322_, v___y_1318_, v___y_1319_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v_a_1325_; lean_object* v___x_1326_; lean_object* v_bs_x27_1327_; size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
v_a_1325_ = lean_ctor_get(v___x_1323_, 1);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1323_, 2);
v___x_1326_ = lean_unsigned_to_nat(0u);
v_bs_x27_1327_ = lean_array_uset(v_bs_1317_, v_i_1316_, v___x_1326_);
v___x_1328_ = ((size_t)1ULL);
v___x_1329_ = lean_usize_add(v_i_1316_, v___x_1328_);
v___x_1330_ = lean_array_uset(v_bs_x27_1327_, v_i_1316_, v_a_1324_);
v_i_1316_ = v___x_1329_;
v_bs_1317_ = v___x_1330_;
v___y_1319_ = v_a_1325_;
goto _start;
}
else
{
lean_object* v_a_1332_; lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v_bs_1317_);
v_a_1332_ = lean_ctor_get(v___x_1323_, 0);
v_a_1333_ = lean_ctor_get(v___x_1323_, 1);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1323_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_inc(v_a_1332_);
lean_dec(v___x_1323_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1332_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1315_ = stack[0].m_num;
size_t v_i_1316_ = stack[1].m_num;
lean_object* v_bs_1317_ = stack[2].m_obj;
lean_object* v___y_1318_ = stack[3].m_obj;
lean_object* v___y_1319_ = stack[4].m_obj;
lean_object* v_res_1341_;
v_res_1341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(v_sz_1315_, v_i_1316_, v_bs_1317_, v___y_1318_, v___y_1319_);
stack->m_obj
 = v_res_1341_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed(lean_object* v_sz_1342_, lean_object* v_i_1343_, lean_object* v_bs_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
size_t v_sz_boxed_1347_; size_t v_i_boxed_1348_; lean_object* v_res_1349_; 
v_sz_boxed_1347_ = lean_unbox_usize(v_sz_1342_);
lean_dec(v_sz_1342_);
v_i_boxed_1348_ = lean_unbox_usize(v_i_1343_);
lean_dec(v_i_1343_);
v_res_1349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(v_sz_boxed_1347_, v_i_boxed_1348_, v_bs_1344_, v___y_1345_, v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1349_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___redArg(size_t v_sz_1350_, size_t v_i_1351_, lean_object* v_bs_1352_, lean_object* v___y_1353_){
_start:
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_usize_dec_lt(v_i_1351_, v_sz_1350_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_bs_1352_);
lean_ctor_set(v___x_1355_, 1, v___y_1353_);
return v___x_1355_;
}
else
{
lean_object* v_v_1356_; lean_object* v___x_1357_; 
v_v_1356_ = lean_array_uget_borrowed(v_bs_1352_, v_i_1351_);
lean_inc(v_v_1356_);
v___x_1357_ = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(v_v_1356_, v___y_1353_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v_a_1359_; lean_object* v___x_1360_; lean_object* v_bs_x27_1361_; size_t v___x_1362_; size_t v___x_1363_; lean_object* v___x_1364_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
v_a_1359_ = lean_ctor_get(v___x_1357_, 1);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1357_, 2);
v___x_1360_ = lean_unsigned_to_nat(0u);
v_bs_x27_1361_ = lean_array_uset(v_bs_1352_, v_i_1351_, v___x_1360_);
v___x_1362_ = ((size_t)1ULL);
v___x_1363_ = lean_usize_add(v_i_1351_, v___x_1362_);
v___x_1364_ = lean_array_uset(v_bs_x27_1361_, v_i_1351_, v_a_1358_);
v_i_1351_ = v___x_1363_;
v_bs_1352_ = v___x_1364_;
v___y_1353_ = v_a_1359_;
goto _start;
}
else
{
lean_object* v_a_1366_; lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec_ref(v_bs_1352_);
v_a_1366_ = lean_ctor_get(v___x_1357_, 0);
v_a_1367_ = lean_ctor_get(v___x_1357_, 1);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1357_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_inc(v_a_1366_);
lean_dec(v___x_1357_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1366_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1350_ = stack[0].m_num;
size_t v_i_1351_ = stack[1].m_num;
lean_object* v_bs_1352_ = stack[2].m_obj;
lean_object* v___y_1353_ = stack[3].m_obj;
lean_object* v_res_1375_;
v_res_1375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___redArg(v_sz_1350_, v_i_1351_, v_bs_1352_, v___y_1353_);
stack->m_obj
 = v_res_1375_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___redArg___boxed(lean_object* v_sz_1376_, lean_object* v_i_1377_, lean_object* v_bs_1378_, lean_object* v___y_1379_){
_start:
{
size_t v_sz_boxed_1380_; size_t v_i_boxed_1381_; lean_object* v_res_1382_; 
v_sz_boxed_1380_ = lean_unbox_usize(v_sz_1376_);
lean_dec(v_sz_1376_);
v_i_boxed_1381_ = lean_unbox_usize(v_i_1377_);
lean_dec(v_i_1377_);
v_res_1382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___redArg(v_sz_boxed_1380_, v_i_boxed_1381_, v_bs_1378_, v___y_1379_);
return v_res_1382_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(size_t v_sz_1383_, size_t v_i_1384_, lean_object* v_bs_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___redArg(v_sz_1383_, v_i_1384_, v_bs_1385_, v___y_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1383_ = stack[0].m_num;
size_t v_i_1384_ = stack[1].m_num;
lean_object* v_bs_1385_ = stack[2].m_obj;
lean_object* v___y_1386_ = stack[3].m_obj;
lean_object* v___y_1387_ = stack[4].m_obj;
lean_object* v_res_1389_;
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_1383_, v_i_1384_, v_bs_1385_, v___y_1386_, v___y_1387_);
stack->m_obj
 = v_res_1389_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed(lean_object* v_sz_1390_, lean_object* v_i_1391_, lean_object* v_bs_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
size_t v_sz_boxed_1395_; size_t v_i_boxed_1396_; lean_object* v_res_1397_; 
v_sz_boxed_1395_ = lean_unbox_usize(v_sz_1390_);
lean_dec(v_sz_1390_);
v_i_boxed_1396_ = lean_unbox_usize(v_i_1391_);
lean_dec(v_i_1391_);
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_boxed_1395_, v_i_boxed_1396_, v_bs_1392_, v___y_1393_, v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1397_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(size_t v_sz_1398_, size_t v_i_1399_, lean_object* v_bs_1400_){
_start:
{
uint8_t v___x_1401_; 
v___x_1401_ = lean_usize_dec_lt(v_i_1399_, v_sz_1398_);
if (v___x_1401_ == 0)
{
return v_bs_1400_;
}
else
{
lean_object* v___x_1402_; lean_object* v_v_1403_; lean_object* v_bs_x27_1404_; lean_object* v___x_1405_; size_t v___x_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1402_ = lean_unsigned_to_nat(0u);
v_v_1403_ = lean_array_uget(v_bs_1400_, v_i_1399_);
v_bs_x27_1404_ = lean_array_uset(v_bs_1400_, v_i_1399_, v___x_1402_);
v___x_1405_ = l_Lean_Syntax_getArg(v_v_1403_, v___x_1402_);
lean_dec(v_v_1403_);
v___x_1406_ = ((size_t)1ULL);
v___x_1407_ = lean_usize_add(v_i_1399_, v___x_1406_);
v___x_1408_ = lean_array_uset(v_bs_x27_1404_, v_i_1399_, v___x_1405_);
v_i_1399_ = v___x_1407_;
v_bs_1400_ = v___x_1408_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1398_ = stack[0].m_num;
size_t v_i_1399_ = stack[1].m_num;
lean_object* v_bs_1400_ = stack[2].m_obj;
lean_object* v_res_1410_;
v_res_1410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(v_sz_1398_, v_i_1399_, v_bs_1400_);
stack->m_obj
 = v_res_1410_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed(lean_object* v_sz_1411_, lean_object* v_i_1412_, lean_object* v_bs_1413_){
_start:
{
size_t v_sz_boxed_1414_; size_t v_i_boxed_1415_; lean_object* v_res_1416_; 
v_sz_boxed_1414_ = lean_unbox_usize(v_sz_1411_);
lean_dec(v_sz_1411_);
v_i_boxed_1415_ = lean_unbox_usize(v_i_1412_);
lean_dec(v_i_1412_);
v_res_1416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(v_sz_boxed_1414_, v_i_boxed_1415_, v_bs_1413_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(lean_object* v_env_1417_, lean_object* v_currNamespace_1418_, lean_object* v_openDecls_1419_, lean_object* v_n_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = l_Lean_ResolveName_resolveNamespace(v_env_1417_, v_currNamespace_1418_, v_openDecls_1419_, v_n_1420_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v___y_1422_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed(lean_object* v_env_1425_, lean_object* v_currNamespace_1426_, lean_object* v_openDecls_1427_, lean_object* v_n_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(v_env_1425_, v_currNamespace_1426_, v_openDecls_1427_, v_n_1428_, v___y_1429_, v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1431_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1432_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
return v___x_1434_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1435_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1436_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
lean_ctor_set(v___x_1438_, 2, v___x_1437_);
lean_ctor_set(v___x_1438_, 3, v___x_1437_);
lean_ctor_set(v___x_1438_, 4, v___x_1436_);
lean_ctor_set(v___x_1438_, 5, v___x_1436_);
lean_ctor_set(v___x_1438_, 6, v___x_1436_);
lean_ctor_set(v___x_1438_, 7, v___x_1436_);
lean_ctor_set(v___x_1438_, 8, v___x_1436_);
lean_ctor_set(v___x_1438_, 9, v___x_1436_);
lean_ctor_set(v___x_1438_, 10, v___x_1436_);
lean_ctor_set(v___x_1438_, 11, v___x_1435_);
return v___x_1438_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1439_ = lean_unsigned_to_nat(32u);
v___x_1440_ = lean_mk_empty_array_with_capacity(v___x_1439_);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
return v___x_1441_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4(void){
_start:
{
size_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1442_ = ((size_t)5ULL);
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = lean_unsigned_to_nat(32u);
v___x_1445_ = lean_mk_empty_array_with_capacity(v___x_1444_);
v___x_1446_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3);
v___x_1447_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
lean_ctor_set(v___x_1447_, 1, v___x_1445_);
lean_ctor_set(v___x_1447_, 2, v___x_1443_);
lean_ctor_set(v___x_1447_, 3, v___x_1443_);
lean_ctor_set_usize(v___x_1447_, 4, v___x_1442_);
return v___x_1447_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1448_ = lean_box(1);
v___x_1449_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4);
v___x_1450_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_1451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
lean_ctor_set(v___x_1451_, 1, v___x_1449_);
lean_ctor_set(v___x_1451_, 2, v___x_1448_);
return v___x_1451_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; lean_object* v_env_1456_; uint8_t v___x_1457_; lean_object* v_env_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v_scopes_1461_; lean_object* v___x_1462_; lean_object* v_opts_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1455_ = lean_st_ref_get(v___y_1453_);
v_env_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc_ref(v_env_1456_);
lean_dec(v___x_1455_);
v___x_1457_ = 0;
v_env_1458_ = l_Lean_Environment_setRecordingDeps(v_env_1456_, v___x_1457_);
v___x_1459_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1460_ = lean_st_ref_get(v___y_1453_);
v_scopes_1461_ = lean_ctor_get(v___x_1460_, 2);
lean_inc(v_scopes_1461_);
lean_dec(v___x_1460_);
v___x_1462_ = l_List_head_x21___redArg(v___x_1459_, v_scopes_1461_);
lean_dec(v_scopes_1461_);
v_opts_1463_ = lean_ctor_get(v___x_1462_, 1);
lean_inc_ref(v_opts_1463_);
lean_dec(v___x_1462_);
v___x_1464_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_1465_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5);
v___x_1466_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1466_, 0, v_env_1458_);
lean_ctor_set(v___x_1466_, 1, v___x_1464_);
lean_ctor_set(v___x_1466_, 2, v___x_1465_);
lean_ctor_set(v___x_1466_, 3, v_opts_1463_);
v___x_1467_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v_msgData_1452_);
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1452_ = stack[0].m_obj;
lean_object* v___y_1453_ = stack[1].m_obj;
lean_object* v_res_1469_;
v_res_1469_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msgData_1452_, v___y_1453_);
stack->m_obj
 = v_res_1469_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msgData_1470_, v___y_1471_);
lean_dec(v___y_1471_);
return v_res_1473_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1474_; double v___x_1475_; 
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = lean_float_of_nat(v___x_1474_);
return v___x_1475_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(lean_object* v_cls_1478_, lean_object* v_msg_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_Elab_Command_getRef___redArg(v___y_1480_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1485_; lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1534_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1485_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msg_1479_, v___y_1481_);
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1534_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1534_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v_traceState_1491_; lean_object* v_env_1492_; lean_object* v_messages_1493_; lean_object* v_scopes_1494_; lean_object* v_usedQuotCtxts_1495_; lean_object* v_nextMacroScope_1496_; lean_object* v_maxRecDepth_1497_; lean_object* v_ngen_1498_; lean_object* v_auxDeclNGen_1499_; lean_object* v_infoState_1500_; lean_object* v_snapshotTasks_1501_; lean_object* v_prevLinterStates_1502_; lean_object* v_codeQualityEntryTasks_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1533_; 
v___x_1490_ = lean_st_ref_take(v___y_1481_);
v_traceState_1491_ = lean_ctor_get(v___x_1490_, 9);
v_env_1492_ = lean_ctor_get(v___x_1490_, 0);
v_messages_1493_ = lean_ctor_get(v___x_1490_, 1);
v_scopes_1494_ = lean_ctor_get(v___x_1490_, 2);
v_usedQuotCtxts_1495_ = lean_ctor_get(v___x_1490_, 3);
v_nextMacroScope_1496_ = lean_ctor_get(v___x_1490_, 4);
v_maxRecDepth_1497_ = lean_ctor_get(v___x_1490_, 5);
v_ngen_1498_ = lean_ctor_get(v___x_1490_, 6);
v_auxDeclNGen_1499_ = lean_ctor_get(v___x_1490_, 7);
v_infoState_1500_ = lean_ctor_get(v___x_1490_, 8);
v_snapshotTasks_1501_ = lean_ctor_get(v___x_1490_, 10);
v_prevLinterStates_1502_ = lean_ctor_get(v___x_1490_, 11);
v_codeQualityEntryTasks_1503_ = lean_ctor_get(v___x_1490_, 12);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1505_ = v___x_1490_;
v_isShared_1506_ = v_isSharedCheck_1533_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1503_);
lean_inc(v_prevLinterStates_1502_);
lean_inc(v_snapshotTasks_1501_);
lean_inc(v_traceState_1491_);
lean_inc(v_infoState_1500_);
lean_inc(v_auxDeclNGen_1499_);
lean_inc(v_ngen_1498_);
lean_inc(v_maxRecDepth_1497_);
lean_inc(v_nextMacroScope_1496_);
lean_inc(v_usedQuotCtxts_1495_);
lean_inc(v_scopes_1494_);
lean_inc(v_messages_1493_);
lean_inc(v_env_1492_);
lean_dec(v___x_1490_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1533_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
uint64_t v_tid_1507_; lean_object* v_traces_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1532_; 
v_tid_1507_ = lean_ctor_get_uint64(v_traceState_1491_, sizeof(void*)*1);
v_traces_1508_ = lean_ctor_get(v_traceState_1491_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_traceState_1491_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1510_ = v_traceState_1491_;
v_isShared_1511_ = v_isSharedCheck_1532_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_traces_1508_);
lean_dec(v_traceState_1491_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1532_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; double v___x_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1512_ = lean_box(0);
v___x_1513_ = lean_box(0);
v___x_1514_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0);
v___x_1515_ = 0;
v___x_1516_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1517_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1517_, 0, v_cls_1478_);
lean_ctor_set(v___x_1517_, 1, v___x_1513_);
lean_ctor_set(v___x_1517_, 2, v___x_1516_);
lean_ctor_set_float(v___x_1517_, sizeof(void*)*3, v___x_1514_);
lean_ctor_set_float(v___x_1517_, sizeof(void*)*3 + 8, v___x_1514_);
lean_ctor_set_uint8(v___x_1517_, sizeof(void*)*3 + 16, v___x_1515_);
v___x_1518_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__1));
v___x_1519_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v_a_1486_);
lean_ctor_set(v___x_1519_, 2, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1520_, 0, v_a_1484_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = l_Lean_PersistentArray_push___redArg(v_traces_1508_, v___x_1520_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1521_);
v___x_1523_ = v___x_1510_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1521_);
lean_ctor_set_uint64(v_reuseFailAlloc_1531_, sizeof(void*)*1, v_tid_1507_);
v___x_1523_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1525_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 9, v___x_1523_);
v___x_1525_ = v___x_1505_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_env_1492_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_messages_1493_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_scopes_1494_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_usedQuotCtxts_1495_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_nextMacroScope_1496_);
lean_ctor_set(v_reuseFailAlloc_1530_, 5, v_maxRecDepth_1497_);
lean_ctor_set(v_reuseFailAlloc_1530_, 6, v_ngen_1498_);
lean_ctor_set(v_reuseFailAlloc_1530_, 7, v_auxDeclNGen_1499_);
lean_ctor_set(v_reuseFailAlloc_1530_, 8, v_infoState_1500_);
lean_ctor_set(v_reuseFailAlloc_1530_, 9, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1530_, 10, v_snapshotTasks_1501_);
lean_ctor_set(v_reuseFailAlloc_1530_, 11, v_prevLinterStates_1502_);
lean_ctor_set(v_reuseFailAlloc_1530_, 12, v_codeQualityEntryTasks_1503_);
v___x_1525_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1526_ = lean_st_ref_put(v___y_1481_, v___x_1525_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1512_);
v___x_1528_ = v___x_1488_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1512_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec_ref(v_msg_1479_);
lean_dec(v_cls_1478_);
v_a_1535_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1483_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1483_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1478_ = stack[0].m_obj;
lean_object* v_msg_1479_ = stack[1].m_obj;
lean_object* v___y_1480_ = stack[2].m_obj;
lean_object* v___y_1481_ = stack[3].m_obj;
lean_object* v_res_1543_;
v_res_1543_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_1478_, v_msg_1479_, v___y_1480_, v___y_1481_);
stack->m_obj
 = v_res_1543_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___boxed(lean_object* v_cls_1544_, lean_object* v_msg_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_1544_, v_msg_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1549_;
}
}
lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(lean_object* v_as_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
if (lean_obj_tag(v_as_1550_) == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
return v___x_1555_;
}
else
{
lean_object* v_head_1556_; lean_object* v_tail_1557_; lean_object* v_fst_1558_; lean_object* v_snd_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_scopes_1564_; lean_object* v___x_1565_; lean_object* v_opts_1566_; uint8_t v_hasTrace_1567_; 
v_head_1556_ = lean_ctor_get(v_as_1550_, 0);
lean_inc(v_head_1556_);
v_tail_1557_ = lean_ctor_get(v_as_1550_, 1);
lean_inc(v_tail_1557_);
lean_dec_ref_known(v_as_1550_, 2);
v_fst_1558_ = lean_ctor_get(v_head_1556_, 0);
lean_inc(v_fst_1558_);
v_snd_1559_ = lean_ctor_get(v_head_1556_, 1);
lean_inc(v_snd_1559_);
lean_dec(v_head_1556_);
v___x_1560_ = l_Lean_inheritedTraceOptions;
v___x_1561_ = lean_st_ref_get(v___x_1560_);
v___x_1562_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1563_ = lean_st_ref_get(v___y_1552_);
v_scopes_1564_ = lean_ctor_get(v___x_1563_, 2);
lean_inc(v_scopes_1564_);
lean_dec(v___x_1563_);
v___x_1565_ = l_List_head_x21___redArg(v___x_1562_, v_scopes_1564_);
lean_dec(v_scopes_1564_);
v_opts_1566_ = lean_ctor_get(v___x_1565_, 1);
lean_inc_ref(v_opts_1566_);
lean_dec(v___x_1565_);
v_hasTrace_1567_ = lean_ctor_get_uint8(v_opts_1566_, sizeof(void*)*1);
if (v_hasTrace_1567_ == 0)
{
lean_dec_ref(v_opts_1566_);
lean_dec(v___x_1561_);
lean_dec(v_snd_1559_);
lean_dec(v_fst_1558_);
v_as_1550_ = v_tail_1557_;
goto _start;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1569_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
lean_inc(v_fst_1558_);
v___x_1570_ = l_Lean_Name_append(v___x_1569_, v_fst_1558_);
v___x_1571_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1561_, v_opts_1566_, v___x_1570_);
lean_dec(v___x_1570_);
lean_dec_ref(v_opts_1566_);
lean_dec(v___x_1561_);
if (v___x_1571_ == 0)
{
lean_dec(v_snd_1559_);
lean_dec(v_fst_1558_);
v_as_1550_ = v_tail_1557_;
goto _start;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1573_, 0, v_snd_1559_);
v___x_1574_ = l_Lean_MessageData_ofFormat(v___x_1573_);
v___x_1575_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_fst_1558_, v___x_1574_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_dec_ref_known(v___x_1575_, 1);
v_as_1550_ = v_tail_1557_;
goto _start;
}
else
{
lean_dec(v_tail_1557_);
return v___x_1575_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1550_ = stack[0].m_obj;
lean_object* v___y_1551_ = stack[1].m_obj;
lean_object* v___y_1552_ = stack[2].m_obj;
lean_object* v_res_1577_;
v_res_1577_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v_as_1550_, v___y_1551_, v___y_1552_);
stack->m_obj
 = v_res_1577_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___boxed(lean_object* v_as_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v_as_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(lean_object* v_currNamespace_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_currNamespace_1583_);
lean_ctor_set(v___x_1586_, 1, v___y_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(v_currNamespace_1587_, v___y_1588_, v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(lean_object* v_env_1591_, lean_object* v_opts_1592_, lean_object* v_currNamespace_1593_, lean_object* v_openDecls_1594_, lean_object* v_n_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = l_Lean_ResolveName_resolveGlobalName(v_env_1591_, v_opts_1592_, v_currNamespace_1593_, v_openDecls_1594_, v_n_1595_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v___y_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed(lean_object* v_env_1600_, lean_object* v_opts_1601_, lean_object* v_currNamespace_1602_, lean_object* v_openDecls_1603_, lean_object* v_n_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(v_env_1600_, v_opts_1601_, v_currNamespace_1602_, v_openDecls_1603_, v_n_1604_, v___y_1605_, v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec_ref(v_opts_1601_);
return v_res_1607_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = lean_box(1);
v___x_1609_ = l_Lean_MessageData_ofFormat(v___x_1608_);
return v___x_1609_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__2));
v___x_1614_ = l_Lean_MessageData_ofFormat(v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(lean_object* v_x_1615_, lean_object* v_x_1616_){
_start:
{
if (lean_obj_tag(v_x_1616_) == 0)
{
return v_x_1615_;
}
else
{
lean_object* v_head_1617_; lean_object* v_tail_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1640_; 
v_head_1617_ = lean_ctor_get(v_x_1616_, 0);
v_tail_1618_ = lean_ctor_get(v_x_1616_, 1);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_x_1616_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1620_ = v_x_1616_;
v_isShared_1621_ = v_isSharedCheck_1640_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_tail_1618_);
lean_inc(v_head_1617_);
lean_dec(v_x_1616_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1640_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_before_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1638_; 
v_before_1622_ = lean_ctor_get(v_head_1617_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_head_1617_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; 
v_unused_1639_ = lean_ctor_get(v_head_1617_, 1);
lean_dec(v_unused_1639_);
v___x_1624_ = v_head_1617_;
v_isShared_1625_ = v_isSharedCheck_1638_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_before_1622_);
lean_dec(v_head_1617_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1638_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1626_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0);
if (v_isShared_1625_ == 0)
{
lean_ctor_set_tag(v___x_1624_, 7);
lean_ctor_set(v___x_1624_, 1, v___x_1626_);
lean_ctor_set(v___x_1624_, 0, v_x_1615_);
v___x_1628_ = v___x_1624_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_x_1615_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3);
if (v_isShared_1621_ == 0)
{
lean_ctor_set_tag(v___x_1620_, 7);
lean_ctor_set(v___x_1620_, 1, v___x_1629_);
lean_ctor_set(v___x_1620_, 0, v___x_1628_);
v___x_1631_ = v___x_1620_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = l_Lean_MessageData_ofSyntax(v_before_1622_);
v___x_1633_ = l_Lean_indentD(v___x_1632_);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1631_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v_x_1615_ = v___x_1634_;
v_x_1616_ = v_tail_1618_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(lean_object* v_opts_1641_, lean_object* v_opt_1642_){
_start:
{
lean_object* v_name_1643_; lean_object* v_defValue_1644_; lean_object* v_map_1645_; lean_object* v___x_1646_; 
v_name_1643_ = lean_ctor_get(v_opt_1642_, 0);
v_defValue_1644_ = lean_ctor_get(v_opt_1642_, 1);
v_map_1645_ = lean_ctor_get(v_opts_1641_, 0);
v___x_1646_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1645_, v_name_1643_);
if (lean_obj_tag(v___x_1646_) == 0)
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_unbox(v_defValue_1644_);
return v___x_1647_;
}
else
{
lean_object* v_val_1648_; 
v_val_1648_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_val_1648_);
lean_dec_ref_known(v___x_1646_, 1);
if (lean_obj_tag(v_val_1648_) == 1)
{
uint8_t v_v_1649_; 
v_v_1649_ = lean_ctor_get_uint8(v_val_1648_, 0);
lean_dec_ref_known(v_val_1648_, 0);
return v_v_1649_;
}
else
{
uint8_t v___x_1650_; 
lean_dec(v_val_1648_);
v___x_1650_ = lean_unbox(v_defValue_1644_);
return v___x_1650_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1641_ = stack[0].m_obj;
lean_object* v_opt_1642_ = stack[1].m_obj;
uint8_t v_res_1651_;
v_res_1651_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(v_opts_1641_, v_opt_1642_);
stack->m_num = v_res_1651_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25___boxed(lean_object* v_opts_1652_, lean_object* v_opt_1653_){
_start:
{
uint8_t v_res_1654_; lean_object* v_r_1655_; 
v_res_1654_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(v_opts_1652_, v_opt_1653_);
lean_dec_ref(v_opt_1653_);
lean_dec_ref(v_opts_1652_);
v_r_1655_ = lean_box(v_res_1654_);
return v_r_1655_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__1));
v___x_1660_ = l_Lean_MessageData_ofFormat(v___x_1659_);
return v___x_1660_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(lean_object* v_msgData_1661_, lean_object* v_macroStack_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v_scopes_1667_; lean_object* v___x_1668_; lean_object* v_opts_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1665_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1666_ = lean_st_ref_get(v___y_1663_);
v_scopes_1667_ = lean_ctor_get(v___x_1666_, 2);
lean_inc(v_scopes_1667_);
lean_dec(v___x_1666_);
v___x_1668_ = l_List_head_x21___redArg(v___x_1665_, v_scopes_1667_);
lean_dec(v_scopes_1667_);
v_opts_1669_ = lean_ctor_get(v___x_1668_, 1);
lean_inc_ref(v_opts_1669_);
lean_dec(v___x_1668_);
v___x_1670_ = l_Lean_Elab_pp_macroStack;
v___x_1671_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(v_opts_1669_, v___x_1670_);
lean_dec_ref(v_opts_1669_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; 
lean_dec(v_macroStack_1662_);
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v_msgData_1661_);
return v___x_1672_;
}
else
{
if (lean_obj_tag(v_macroStack_1662_) == 0)
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_msgData_1661_);
return v___x_1673_;
}
else
{
lean_object* v_head_1674_; lean_object* v_after_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1690_; 
v_head_1674_ = lean_ctor_get(v_macroStack_1662_, 0);
lean_inc(v_head_1674_);
v_after_1675_ = lean_ctor_get(v_head_1674_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_head_1674_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; 
v_unused_1691_ = lean_ctor_get(v_head_1674_, 0);
lean_dec(v_unused_1691_);
v___x_1677_ = v_head_1674_;
v_isShared_1678_ = v_isSharedCheck_1690_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_after_1675_);
lean_dec(v_head_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1690_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0);
if (v_isShared_1678_ == 0)
{
lean_ctor_set_tag(v___x_1677_, 7);
lean_ctor_set(v___x_1677_, 1, v___x_1679_);
lean_ctor_set(v___x_1677_, 0, v_msgData_1661_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_msgData_1661_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v_msgData_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1682_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2);
v___x_1683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = l_Lean_MessageData_ofSyntax(v_after_1675_);
v___x_1685_ = l_Lean_indentD(v___x_1684_);
v_msgData_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1686_, 0, v___x_1683_);
lean_ctor_set(v_msgData_1686_, 1, v___x_1685_);
v___x_1687_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(v_msgData_1686_, v_macroStack_1662_);
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
return v___x_1688_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1661_ = stack[0].m_obj;
lean_object* v_macroStack_1662_ = stack[1].m_obj;
lean_object* v___y_1663_ = stack[2].m_obj;
lean_object* v_res_1692_;
v_res_1692_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_msgData_1661_, v_macroStack_1662_, v___y_1663_);
stack->m_obj
 = v_res_1692_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___boxed(lean_object* v_msgData_1693_, lean_object* v_macroStack_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_msgData_1693_, v_macroStack_1694_, v___y_1695_);
lean_dec(v___y_1695_);
return v_res_1697_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(lean_object* v_msg_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Elab_Command_getRef___redArg(v___y_1699_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v_macroStack_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v_a_1707_; lean_object* v___x_1708_; lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1717_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
v_macroStack_1704_ = lean_ctor_get(v___y_1699_, 4);
v___x_1705_ = l_Lean_Elab_getBetterRef(v_a_1703_, v_macroStack_1704_);
lean_dec(v_a_1703_);
v___x_1706_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msg_1698_, v___y_1700_);
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref(v___x_1706_);
lean_inc(v_macroStack_1704_);
v___x_1708_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_a_1707_, v_macroStack_1704_, v___y_1700_);
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1717_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1717_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1705_);
lean_ctor_set(v___x_1713_, 1, v_a_1709_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set_tag(v___x_1711_, 1);
lean_ctor_set(v___x_1711_, 0, v___x_1713_);
v___x_1715_ = v___x_1711_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec_ref(v_msg_1698_);
v_a_1718_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1702_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1702_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1698_ = stack[0].m_obj;
lean_object* v___y_1699_ = stack[1].m_obj;
lean_object* v___y_1700_ = stack[2].m_obj;
lean_object* v_res_1726_;
v_res_1726_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_1698_, v___y_1699_, v___y_1700_);
stack->m_obj
 = v_res_1726_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg___boxed(lean_object* v_msg_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
return v_res_1731_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(lean_object* v_ref_1732_, lean_object* v_msg_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_Elab_Command_getRef___redArg(v___y_1734_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v_fileName_1739_; lean_object* v_fileMap_1740_; lean_object* v_currRecDepth_1741_; lean_object* v_cmdPos_1742_; lean_object* v_macroStack_1743_; lean_object* v_quotContext_x3f_1744_; lean_object* v_currMacroScope_1745_; lean_object* v_snap_x3f_1746_; lean_object* v_cancelTk_x3f_1747_; uint8_t v_suppressElabErrors_1748_; lean_object* v_ref_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1737_, 1);
v_fileName_1739_ = lean_ctor_get(v___y_1734_, 0);
v_fileMap_1740_ = lean_ctor_get(v___y_1734_, 1);
v_currRecDepth_1741_ = lean_ctor_get(v___y_1734_, 2);
v_cmdPos_1742_ = lean_ctor_get(v___y_1734_, 3);
v_macroStack_1743_ = lean_ctor_get(v___y_1734_, 4);
v_quotContext_x3f_1744_ = lean_ctor_get(v___y_1734_, 5);
v_currMacroScope_1745_ = lean_ctor_get(v___y_1734_, 6);
v_snap_x3f_1746_ = lean_ctor_get(v___y_1734_, 8);
v_cancelTk_x3f_1747_ = lean_ctor_get(v___y_1734_, 9);
v_suppressElabErrors_1748_ = lean_ctor_get_uint8(v___y_1734_, sizeof(void*)*10);
v_ref_1749_ = l_Lean_replaceRef(v_ref_1732_, v_a_1738_);
lean_dec(v_a_1738_);
lean_inc(v_cancelTk_x3f_1747_);
lean_inc(v_snap_x3f_1746_);
lean_inc(v_currMacroScope_1745_);
lean_inc(v_quotContext_x3f_1744_);
lean_inc(v_macroStack_1743_);
lean_inc(v_cmdPos_1742_);
lean_inc(v_currRecDepth_1741_);
lean_inc_ref(v_fileMap_1740_);
lean_inc_ref(v_fileName_1739_);
v___x_1750_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1750_, 0, v_fileName_1739_);
lean_ctor_set(v___x_1750_, 1, v_fileMap_1740_);
lean_ctor_set(v___x_1750_, 2, v_currRecDepth_1741_);
lean_ctor_set(v___x_1750_, 3, v_cmdPos_1742_);
lean_ctor_set(v___x_1750_, 4, v_macroStack_1743_);
lean_ctor_set(v___x_1750_, 5, v_quotContext_x3f_1744_);
lean_ctor_set(v___x_1750_, 6, v_currMacroScope_1745_);
lean_ctor_set(v___x_1750_, 7, v_ref_1749_);
lean_ctor_set(v___x_1750_, 8, v_snap_x3f_1746_);
lean_ctor_set(v___x_1750_, 9, v_cancelTk_x3f_1747_);
lean_ctor_set_uint8(v___x_1750_, sizeof(void*)*10, v_suppressElabErrors_1748_);
v___x_1751_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_1733_, v___x_1750_, v___y_1735_);
lean_dec_ref_known(v___x_1750_, 10);
return v___x_1751_;
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec_ref(v_msg_1733_);
v_a_1752_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1737_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1737_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1732_ = stack[0].m_obj;
lean_object* v_msg_1733_ = stack[1].m_obj;
lean_object* v___y_1734_ = stack[2].m_obj;
lean_object* v___y_1735_ = stack[3].m_obj;
lean_object* v_res_1760_;
v_res_1760_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_ref_1732_, v_msg_1733_, v___y_1734_, v___y_1735_);
stack->m_obj
 = v_res_1760_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg___boxed(lean_object* v_ref_1761_, lean_object* v_msg_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_ref_1761_, v_msg_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v_ref_1761_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(lean_object* v_env_1767_, lean_object* v_declName_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
uint8_t v___x_1771_; lean_object* v_env_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; uint8_t v___x_1775_; 
v___x_1771_ = 0;
v_env_1772_ = l_Lean_Environment_setExporting(v_env_1767_, v___x_1771_);
lean_inc(v_declName_1768_);
v___x_1773_ = l_Lean_mkPrivateName(v_env_1772_, v_declName_1768_);
v___x_1774_ = 1;
lean_inc_ref(v_env_1772_);
v___x_1775_ = l_Lean_Environment_contains(v_env_1772_, v___x_1773_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1776_ = l_Lean_privateToUserName(v_declName_1768_);
v___x_1777_ = l_Lean_Environment_contains(v_env_1772_, v___x_1776_, v___x_1774_);
v___x_1778_ = lean_box(v___x_1777_);
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v___y_1770_);
return v___x_1779_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_dec_ref(v_env_1772_);
lean_dec(v_declName_1768_);
v___x_1780_ = lean_box(v___x_1775_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v___y_1770_);
return v___x_1781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed(lean_object* v_env_1782_, lean_object* v_declName_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(v_env_1782_, v_declName_1783_, v___y_1784_, v___y_1785_);
lean_dec_ref(v___y_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(lean_object* v_x_1787_, lean_object* v___y_1788_){
_start:
{
if (lean_obj_tag(v_x_1787_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; 
v_a_1789_ = lean_ctor_get(v_x_1787_, 0);
lean_inc(v_a_1789_);
v___x_1790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1790_, 0, v_a_1789_);
lean_ctor_set(v___x_1790_, 1, v___y_1788_);
return v___x_1790_;
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1792_; 
v_a_1791_ = lean_ctor_get(v_x_1787_, 0);
lean_inc(v_a_1791_);
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v_a_1791_);
lean_ctor_set(v___x_1792_, 1, v___y_1788_);
return v___x_1792_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg___boxed(lean_object* v_x_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v_x_1793_, v___y_1794_);
lean_dec_ref(v_x_1793_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(lean_object* v_env_1796_, lean_object* v_stx_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1796_, v_stx_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
if (lean_obj_tag(v_a_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1810_; 
v_a_1802_ = lean_ctor_get(v___x_1800_, 1);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1810_ == 0)
{
lean_object* v_unused_1811_; 
v_unused_1811_ = lean_ctor_get(v___x_1800_, 0);
lean_dec(v_unused_1811_);
v___x_1804_ = v___x_1800_;
v_isShared_1805_ = v_isSharedCheck_1810_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1800_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1810_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1806_ = lean_box(0);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1806_);
v___x_1808_ = v___x_1804_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_a_1802_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
else
{
lean_object* v_val_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1840_; 
v_val_1812_ = lean_ctor_get(v_a_1801_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_a_1801_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1814_ = v_a_1801_;
v_isShared_1815_ = v_isSharedCheck_1840_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_val_1812_);
lean_dec(v_a_1801_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1840_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v_snd_1816_; 
v_snd_1816_ = lean_ctor_get(v_val_1812_, 1);
lean_inc(v_snd_1816_);
lean_dec(v_val_1812_);
if (lean_obj_tag(v_snd_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1826_; 
lean_del_object(v___x_1814_);
v_a_1817_ = lean_ctor_get(v___x_1800_, 1);
lean_inc(v_a_1817_);
lean_dec_ref_known(v___x_1800_, 2);
v_a_1818_ = lean_ctor_get(v_snd_1816_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_snd_1816_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1820_ = v_snd_1816_;
v_isShared_1821_ = v_isSharedCheck_1826_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v_snd_1816_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1826_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v___x_1823_, v_a_1817_);
lean_dec_ref(v___x_1823_);
return v___x_1824_;
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1839_; 
v_a_1827_ = lean_ctor_get(v___x_1800_, 1);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1800_, 2);
v_a_1828_ = lean_ctor_get(v_snd_1816_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_snd_1816_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1830_ = v_snd_1816_;
v_isShared_1831_ = v_isSharedCheck_1839_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v_snd_1816_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1839_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v_a_1828_);
v___x_1833_ = v___x_1814_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1835_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1833_);
v___x_1835_ = v___x_1830_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v___x_1835_, v_a_1827_);
lean_dec_ref(v___x_1835_);
return v___x_1836_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_a_1841_ = lean_ctor_get(v___x_1800_, 0);
v_a_1842_ = lean_ctor_get(v___x_1800_, 1);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1800_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_inc(v_a_1841_);
lean_dec(v___x_1800_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1841_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed(lean_object* v_env_1850_, lean_object* v_stx_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(v_env_1850_, v_stx_1851_, v___y_1852_, v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1854_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = l_Lean_maxRecDepthErrorMessage;
v___x_1861_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
return v___x_1861_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3);
v___x_1863_ = l_Lean_MessageData_ofFormat(v___x_1862_);
return v___x_1863_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4);
v___x_1865_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2));
v___x_1866_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
lean_ctor_set(v___x_1866_, 1, v___x_1864_);
return v___x_1866_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(lean_object* v_ref_1867_){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_ref_1867_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1867_ = stack[0].m_obj;
lean_object* v_res_1872_;
v_res_1872_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_1867_);
stack->m_obj
 = v_res_1872_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___boxed(lean_object* v_ref_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_1873_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___lam__0(lean_object* v___x_1876_, lean_object* v_entry_1877_, lean_object* v_s_1878_){
_start:
{
lean_object* v_addEntryFn_1879_; lean_object* v_importedEntries_1880_; lean_object* v_state_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1889_; 
v_addEntryFn_1879_ = lean_ctor_get(v___x_1876_, 3);
lean_inc(v_addEntryFn_1879_);
lean_dec_ref(v___x_1876_);
v_importedEntries_1880_ = lean_ctor_get(v_s_1878_, 0);
v_state_1881_ = lean_ctor_get(v_s_1878_, 1);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_s_1878_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1883_ = v_s_1878_;
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_state_1881_);
lean_inc(v_importedEntries_1880_);
lean_dec(v_s_1878_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v_state_1885_; lean_object* v___x_1887_; 
v_state_1885_ = lean_apply_2(v_addEntryFn_1879_, v_state_1881_, v_entry_1877_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 1, v_state_1885_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_importedEntries_1880_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_state_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(lean_object* v_keys_1890_, lean_object* v_i_1891_, lean_object* v_k_1892_){
_start:
{
lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = lean_array_get_size(v_keys_1890_);
v___x_1894_ = lean_nat_dec_lt(v_i_1891_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_dec(v_i_1891_);
return v___x_1894_;
}
else
{
lean_object* v_k_x27_1895_; uint8_t v___x_1896_; 
v_k_x27_1895_ = lean_array_fget_borrowed(v_keys_1890_, v_i_1891_);
v___x_1896_ = l_Lean_instBEqExtraModUse_beq(v_k_1892_, v_k_x27_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_unsigned_to_nat(1u);
v___x_1898_ = lean_nat_add(v_i_1891_, v___x_1897_);
lean_dec(v_i_1891_);
v_i_1891_ = v___x_1898_;
goto _start;
}
else
{
lean_dec(v_i_1891_);
return v___x_1894_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1890_ = stack[0].m_obj;
lean_object* v_i_1891_ = stack[1].m_obj;
lean_object* v_k_1892_ = stack[2].m_obj;
uint8_t v_res_1900_;
v_res_1900_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_1890_, v_i_1891_, v_k_1892_);
stack->m_num = v_res_1900_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg___boxed(lean_object* v_keys_1901_, lean_object* v_i_1902_, lean_object* v_k_1903_){
_start:
{
uint8_t v_res_1904_; lean_object* v_r_1905_; 
v_res_1904_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_1901_, v_i_1902_, v_k_1903_);
lean_dec_ref(v_k_1903_);
lean_dec_ref(v_keys_1901_);
v_r_1905_ = lean_box(v_res_1904_);
return v_r_1905_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(lean_object* v_x_1906_, size_t v_x_1907_, lean_object* v_x_1908_){
_start:
{
if (lean_obj_tag(v_x_1906_) == 0)
{
lean_object* v_es_1909_; lean_object* v___x_1910_; size_t v___x_1911_; size_t v___x_1912_; lean_object* v_j_1913_; lean_object* v___x_1914_; 
v_es_1909_ = lean_ctor_get(v_x_1906_, 0);
v___x_1910_ = lean_box(2);
v___x_1911_ = ((size_t)31ULL);
v___x_1912_ = lean_usize_land(v_x_1907_, v___x_1911_);
v_j_1913_ = lean_usize_to_nat(v___x_1912_);
v___x_1914_ = lean_array_get_borrowed(v___x_1910_, v_es_1909_, v_j_1913_);
lean_dec(v_j_1913_);
switch(lean_obj_tag(v___x_1914_))
{
case 0:
{
lean_object* v_key_1915_; uint8_t v___x_1916_; 
v_key_1915_ = lean_ctor_get(v___x_1914_, 0);
v___x_1916_ = l_Lean_instBEqExtraModUse_beq(v_x_1908_, v_key_1915_);
return v___x_1916_;
}
case 1:
{
lean_object* v_node_1917_; size_t v___x_1918_; size_t v___x_1919_; 
v_node_1917_ = lean_ctor_get(v___x_1914_, 0);
v___x_1918_ = ((size_t)5ULL);
v___x_1919_ = lean_usize_shift_right(v_x_1907_, v___x_1918_);
v_x_1906_ = v_node_1917_;
v_x_1907_ = v___x_1919_;
goto _start;
}
default: 
{
uint8_t v___x_1921_; 
v___x_1921_ = 0;
return v___x_1921_;
}
}
}
else
{
lean_object* v_ks_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v_ks_1922_ = lean_ctor_get(v_x_1906_, 0);
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_ks_1922_, v___x_1923_, v_x_1908_);
return v___x_1924_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1906_ = stack[0].m_obj;
size_t v_x_1907_ = stack[1].m_num;
lean_object* v_x_1908_ = stack[2].m_obj;
uint8_t v_res_1925_;
v_res_1925_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_1906_, v_x_1907_, v_x_1908_);
stack->m_num = v_res_1925_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___boxed(lean_object* v_x_1926_, lean_object* v_x_1927_, lean_object* v_x_1928_){
_start:
{
size_t v_x_21636__boxed_1929_; uint8_t v_res_1930_; lean_object* v_r_1931_; 
v_x_21636__boxed_1929_ = lean_unbox_usize(v_x_1927_);
lean_dec(v_x_1927_);
v_res_1930_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_1926_, v_x_21636__boxed_1929_, v_x_1928_);
lean_dec_ref(v_x_1928_);
lean_dec_ref(v_x_1926_);
v_r_1931_ = lean_box(v_res_1930_);
return v_r_1931_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(lean_object* v_x_1932_, lean_object* v_x_1933_){
_start:
{
uint64_t v___x_1934_; size_t v___x_1935_; uint8_t v___x_1936_; 
v___x_1934_ = l_Lean_instHashableExtraModUse_hash(v_x_1933_);
v___x_1935_ = lean_uint64_to_usize(v___x_1934_);
v___x_1936_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_1932_, v___x_1935_, v_x_1933_);
return v___x_1936_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1932_ = stack[0].m_obj;
lean_object* v_x_1933_ = stack[1].m_obj;
uint8_t v_res_1937_;
v_res_1937_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_1932_, v_x_1933_);
stack->m_num = v_res_1937_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg___boxed(lean_object* v_x_1938_, lean_object* v_x_1939_){
_start:
{
uint8_t v_res_1940_; lean_object* v_r_1941_; 
v_res_1940_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_1938_, v_x_1939_);
lean_dec_ref(v_x_1939_);
lean_dec_ref(v_x_1938_);
v_r_1941_ = lean_box(v_res_1940_);
return v_r_1941_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1942_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4(void){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__3));
v___x_1948_ = l_Lean_stringToMessageData(v___x_1947_);
return v___x_1948_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5));
v___x_1951_ = l_Lean_stringToMessageData(v___x_1950_);
return v___x_1951_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7(void){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__54));
v___x_1953_ = l_Lean_stringToMessageData(v___x_1952_);
return v___x_1953_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8(void){
_start:
{
lean_object* v_cls_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v_cls_1954_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2));
v___x_1955_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1));
v___x_1956_ = l_Lean_Name_append(v___x_1955_, v_cls_1954_);
return v___x_1956_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9));
v___x_1959_ = l_Lean_stringToMessageData(v___x_1958_);
return v___x_1959_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11));
v___x_1962_ = l_Lean_stringToMessageData(v___x_1961_);
return v___x_1962_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(lean_object* v_mod_1967_, uint8_t v_isMeta_1968_, lean_object* v_hint_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v_env_1994_; uint8_t v_isExporting_1995_; lean_object* v_entry_1996_; lean_object* v___x_1997_; lean_object* v_env_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_1992_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0);
v___x_1993_ = lean_st_ref_get(v___y_1971_);
v_env_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc_ref(v_env_1994_);
lean_dec(v___x_1993_);
v_isExporting_1995_ = lean_ctor_get_uint8(v_env_1994_, sizeof(void*)*13);
lean_dec_ref(v_env_1994_);
lean_inc(v_mod_1967_);
v_entry_1996_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1996_, 0, v_mod_1967_);
lean_ctor_set_uint8(v_entry_1996_, sizeof(void*)*1, v_isExporting_1995_);
lean_ctor_set_uint8(v_entry_1996_, sizeof(void*)*1 + 1, v_isMeta_1968_);
v___x_1997_ = lean_st_ref_get(v___y_1971_);
v_env_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc_ref(v_env_1998_);
lean_dec(v___x_1997_);
v___x_1999_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2000_ = lean_box(1);
v___x_2001_ = lean_box(0);
v___x_2002_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1992_, v___x_1999_, v_env_1998_, v___x_2000_, v___x_2001_);
v___x_2003_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v___x_2002_, v_entry_1996_);
lean_dec(v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___f_2004_; uint8_t v___x_2005_; lean_object* v___y_2007_; lean_object* v_cls_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v_scopes_2053_; lean_object* v___x_2054_; lean_object* v_opts_2055_; uint8_t v_hasTrace_2056_; 
v___f_2004_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___lam__0), 3, 2);
lean_closure_set(v___f_2004_, 0, v___x_1999_);
lean_closure_set(v___f_2004_, 1, v_entry_1996_);
v___x_2005_ = 1;
v_cls_2029_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2));
v___x_2030_ = l_Lean_inheritedTraceOptions;
v___x_2031_ = lean_st_ref_get(v___x_2030_);
v___x_2032_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2033_ = lean_st_ref_get(v___y_1971_);
v_scopes_2053_ = lean_ctor_get(v___x_2033_, 2);
lean_inc(v_scopes_2053_);
lean_dec(v___x_2033_);
v___x_2054_ = l_List_head_x21___redArg(v___x_2032_, v_scopes_2053_);
lean_dec(v_scopes_2053_);
v_opts_2055_ = lean_ctor_get(v___x_2054_, 1);
lean_inc_ref(v_opts_2055_);
lean_dec(v___x_2054_);
v_hasTrace_2056_ = lean_ctor_get_uint8(v_opts_2055_, sizeof(void*)*1);
if (v_hasTrace_2056_ == 0)
{
lean_dec_ref(v_opts_2055_);
lean_dec(v___x_2031_);
lean_dec(v_hint_1969_);
lean_dec(v_mod_1967_);
v___y_2007_ = v___y_1971_;
goto v___jp_2006_;
}
else
{
lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2057_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8);
v___x_2058_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2031_, v_opts_2055_, v___x_2057_);
lean_dec_ref(v_opts_2055_);
lean_dec(v___x_2031_);
if (v___x_2058_ == 0)
{
lean_dec(v_hint_1969_);
lean_dec(v_mod_1967_);
v___y_2007_ = v___y_1971_;
goto v___jp_2006_;
}
else
{
lean_object* v___x_2059_; lean_object* v___y_2061_; 
v___x_2059_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10);
if (v_isExporting_1995_ == 0)
{
lean_object* v___x_2068_; 
v___x_2068_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15));
v___y_2061_ = v___x_2068_;
goto v___jp_2060_;
}
else
{
lean_object* v___x_2069_; 
v___x_2069_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16));
v___y_2061_ = v___x_2069_;
goto v___jp_2060_;
}
v___jp_2060_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_inc_ref(v___y_2061_);
v___x_2062_ = l_Lean_stringToMessageData(v___y_2061_);
v___x_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2059_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
v___x_2064_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12);
v___x_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
if (v_isMeta_1968_ == 0)
{
lean_object* v___x_2066_; 
v___x_2066_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13));
v___y_2040_ = v___x_2065_;
v___y_2041_ = v___x_2066_;
goto v___jp_2039_;
}
else
{
lean_object* v___x_2067_; 
v___x_2067_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14));
v___y_2040_ = v___x_2065_;
v___y_2041_ = v___x_2067_;
goto v___jp_2039_;
}
}
}
}
v___jp_2006_:
{
lean_object* v___x_2008_; lean_object* v_toEnvExtension_2009_; lean_object* v_env_2010_; lean_object* v_messages_2011_; lean_object* v_scopes_2012_; lean_object* v_usedQuotCtxts_2013_; lean_object* v_nextMacroScope_2014_; lean_object* v_maxRecDepth_2015_; lean_object* v_ngen_2016_; lean_object* v_auxDeclNGen_2017_; lean_object* v_infoState_2018_; lean_object* v_traceState_2019_; lean_object* v_snapshotTasks_2020_; lean_object* v_prevLinterStates_2021_; lean_object* v_codeQualityEntryTasks_2022_; lean_object* v_asyncMode_2023_; uint8_t v_logWrites_2024_; lean_object* v___x_2025_; 
v___x_2008_ = lean_st_ref_take(v___y_2007_);
v_toEnvExtension_2009_ = lean_ctor_get(v___x_1999_, 0);
v_env_2010_ = lean_ctor_get(v___x_2008_, 0);
lean_inc_ref(v_env_2010_);
v_messages_2011_ = lean_ctor_get(v___x_2008_, 1);
lean_inc_ref(v_messages_2011_);
v_scopes_2012_ = lean_ctor_get(v___x_2008_, 2);
lean_inc(v_scopes_2012_);
v_usedQuotCtxts_2013_ = lean_ctor_get(v___x_2008_, 3);
lean_inc(v_usedQuotCtxts_2013_);
v_nextMacroScope_2014_ = lean_ctor_get(v___x_2008_, 4);
lean_inc(v_nextMacroScope_2014_);
v_maxRecDepth_2015_ = lean_ctor_get(v___x_2008_, 5);
lean_inc(v_maxRecDepth_2015_);
v_ngen_2016_ = lean_ctor_get(v___x_2008_, 6);
lean_inc_ref(v_ngen_2016_);
v_auxDeclNGen_2017_ = lean_ctor_get(v___x_2008_, 7);
lean_inc_ref(v_auxDeclNGen_2017_);
v_infoState_2018_ = lean_ctor_get(v___x_2008_, 8);
lean_inc_ref(v_infoState_2018_);
v_traceState_2019_ = lean_ctor_get(v___x_2008_, 9);
lean_inc_ref(v_traceState_2019_);
v_snapshotTasks_2020_ = lean_ctor_get(v___x_2008_, 10);
lean_inc_ref(v_snapshotTasks_2020_);
v_prevLinterStates_2021_ = lean_ctor_get(v___x_2008_, 11);
lean_inc(v_prevLinterStates_2021_);
v_codeQualityEntryTasks_2022_ = lean_ctor_get(v___x_2008_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2022_);
lean_dec(v___x_2008_);
v_asyncMode_2023_ = lean_ctor_get(v_toEnvExtension_2009_, 2);
v_logWrites_2024_ = lean_ctor_get_uint8(v_toEnvExtension_2009_, sizeof(void*)*6);
v___x_2025_ = lean_box(0);
if (v_logWrites_2024_ == 0)
{
lean_object* v___x_2026_; 
lean_inc_ref(v_toEnvExtension_2009_);
v___x_2026_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2009_, v_env_2010_, v___f_2004_, v_asyncMode_2023_, v___x_2001_, v___x_2005_);
v___y_1974_ = v_snapshotTasks_2020_;
v___y_1975_ = v_prevLinterStates_2021_;
v___y_1976_ = v_ngen_2016_;
v___y_1977_ = v_scopes_2012_;
v___y_1978_ = v___y_2007_;
v___y_1979_ = v___x_2025_;
v___y_1980_ = v_messages_2011_;
v___y_1981_ = v_usedQuotCtxts_2013_;
v___y_1982_ = v_maxRecDepth_2015_;
v___y_1983_ = v_nextMacroScope_2014_;
v___y_1984_ = v_auxDeclNGen_2017_;
v___y_1985_ = v_traceState_2019_;
v___y_1986_ = v_infoState_2018_;
v___y_1987_ = v_codeQualityEntryTasks_2022_;
v___y_1988_ = v___x_2026_;
goto v___jp_1973_;
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_inc_ref_n(v_toEnvExtension_2009_, 2);
v___x_2027_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2009_, v_env_2010_);
lean_dec_ref(v_env_2010_);
v___x_2028_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2009_, v___x_2027_, v___f_2004_, v_asyncMode_2023_, v___x_2001_, v___x_2005_);
v___y_1974_ = v_snapshotTasks_2020_;
v___y_1975_ = v_prevLinterStates_2021_;
v___y_1976_ = v_ngen_2016_;
v___y_1977_ = v_scopes_2012_;
v___y_1978_ = v___y_2007_;
v___y_1979_ = v___x_2025_;
v___y_1980_ = v_messages_2011_;
v___y_1981_ = v_usedQuotCtxts_2013_;
v___y_1982_ = v_maxRecDepth_2015_;
v___y_1983_ = v_nextMacroScope_2014_;
v___y_1984_ = v_auxDeclNGen_2017_;
v___y_1985_ = v_traceState_2019_;
v___y_1986_ = v_infoState_2018_;
v___y_1987_ = v_codeQualityEntryTasks_2022_;
v___y_1988_ = v___x_2028_;
goto v___jp_1973_;
}
}
v___jp_2034_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___y_2035_);
lean_ctor_set(v___x_2037_, 1, v___y_2036_);
v___x_2038_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_2029_, v___x_2037_, v___y_1970_, v___y_1971_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_dec_ref_known(v___x_2038_, 1);
v___y_2007_ = v___y_1971_;
goto v___jp_2006_;
}
else
{
lean_dec_ref(v___f_2004_);
return v___x_2038_;
}
}
v___jp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
lean_inc_ref(v___y_2041_);
v___x_2042_ = l_Lean_stringToMessageData(v___y_2041_);
v___x_2043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___y_2040_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4);
v___x_2045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2043_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v___x_2046_ = l_Lean_MessageData_ofName(v_mod_1967_);
v___x_2047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2045_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
v___x_2048_ = l_Lean_Name_isAnonymous(v_hint_1969_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6);
v___x_2050_ = l_Lean_MessageData_ofName(v_hint_1969_);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2049_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___y_2035_ = v___x_2047_;
v___y_2036_ = v___x_2051_;
goto v___jp_2034_;
}
else
{
lean_object* v___x_2052_; 
lean_dec(v_hint_1969_);
v___x_2052_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7);
v___y_2035_ = v___x_2047_;
v___y_2036_ = v___x_2052_;
goto v___jp_2034_;
}
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
lean_dec_ref_known(v_entry_1996_, 1);
lean_dec(v_hint_1969_);
lean_dec(v_mod_1967_);
v___x_2070_ = lean_box(0);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
return v___x_2071_;
}
v___jp_1973_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1989_, 0, v___y_1988_);
lean_ctor_set(v___x_1989_, 1, v___y_1980_);
lean_ctor_set(v___x_1989_, 2, v___y_1977_);
lean_ctor_set(v___x_1989_, 3, v___y_1981_);
lean_ctor_set(v___x_1989_, 4, v___y_1983_);
lean_ctor_set(v___x_1989_, 5, v___y_1982_);
lean_ctor_set(v___x_1989_, 6, v___y_1976_);
lean_ctor_set(v___x_1989_, 7, v___y_1984_);
lean_ctor_set(v___x_1989_, 8, v___y_1986_);
lean_ctor_set(v___x_1989_, 9, v___y_1985_);
lean_ctor_set(v___x_1989_, 10, v___y_1974_);
lean_ctor_set(v___x_1989_, 11, v___y_1975_);
lean_ctor_set(v___x_1989_, 12, v___y_1987_);
v___x_1990_ = lean_st_ref_put(v___y_1978_, v___x_1989_);
v___x_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___y_1979_);
return v___x_1991_;
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1967_ = stack[0].m_obj;
uint8_t v_isMeta_1968_ = stack[1].m_num;
lean_object* v_hint_1969_ = stack[2].m_obj;
lean_object* v___y_1970_ = stack[3].m_obj;
lean_object* v___y_1971_ = stack[4].m_obj;
lean_object* v_res_2072_;
v_res_2072_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_mod_1967_, v_isMeta_1968_, v_hint_1969_, v___y_1970_, v___y_1971_);
stack->m_obj
 = v_res_2072_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___boxed(lean_object* v_mod_2073_, lean_object* v_isMeta_2074_, lean_object* v_hint_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
uint8_t v_isMeta_boxed_2079_; lean_object* v_res_2080_; 
v_isMeta_boxed_2079_ = lean_unbox(v_isMeta_2074_);
v_res_2080_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_mod_2073_, v_isMeta_boxed_2079_, v_hint_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
return v_res_2080_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(lean_object* v___x_2081_, lean_object* v_declName_2082_, lean_object* v_as_2083_, size_t v_sz_2084_, size_t v_i_2085_, lean_object* v_b_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
uint8_t v___x_2090_; 
v___x_2090_ = lean_usize_dec_lt(v_i_2085_, v_sz_2084_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_dec(v_declName_2082_);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v_b_2086_);
return v___x_2091_;
}
else
{
lean_object* v___x_2092_; lean_object* v_modules_2093_; lean_object* v___x_2094_; lean_object* v_a_2095_; lean_object* v___x_2096_; lean_object* v_toImport_2097_; lean_object* v_module_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; lean_object* v___x_2101_; 
v___x_2092_ = l_Lean_Environment_header(v___x_2081_);
v_modules_2093_ = lean_ctor_get(v___x_2092_, 3);
lean_inc_ref(v_modules_2093_);
lean_dec_ref(v___x_2092_);
v___x_2094_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2095_ = lean_array_uget_borrowed(v_as_2083_, v_i_2085_);
v___x_2096_ = lean_array_get(v___x_2094_, v_modules_2093_, v_a_2095_);
lean_dec_ref(v_modules_2093_);
v_toImport_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc_ref(v_toImport_2097_);
lean_dec(v___x_2096_);
v_module_2098_ = lean_ctor_get(v_toImport_2097_, 0);
lean_inc(v_module_2098_);
lean_dec_ref(v_toImport_2097_);
v___x_2099_ = lean_box(0);
v___x_2100_ = 0;
lean_inc(v_declName_2082_);
v___x_2101_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_module_2098_, v___x_2100_, v_declName_2082_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2101_) == 0)
{
size_t v___x_2102_; size_t v___x_2103_; 
lean_dec_ref_known(v___x_2101_, 1);
v___x_2102_ = ((size_t)1ULL);
v___x_2103_ = lean_usize_add(v_i_2085_, v___x_2102_);
v_i_2085_ = v___x_2103_;
v_b_2086_ = v___x_2099_;
goto _start;
}
else
{
lean_dec(v_declName_2082_);
return v___x_2101_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2081_ = stack[0].m_obj;
lean_object* v_declName_2082_ = stack[1].m_obj;
lean_object* v_as_2083_ = stack[2].m_obj;
size_t v_sz_2084_ = stack[3].m_num;
size_t v_i_2085_ = stack[4].m_num;
lean_object* v_b_2086_ = stack[5].m_obj;
lean_object* v___y_2087_ = stack[6].m_obj;
lean_object* v___y_2088_ = stack[7].m_obj;
lean_object* v_res_2105_;
v_res_2105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v___x_2081_, v_declName_2082_, v_as_2083_, v_sz_2084_, v_i_2085_, v_b_2086_, v___y_2087_, v___y_2088_);
stack->m_obj
 = v_res_2105_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7___boxed(lean_object* v___x_2106_, lean_object* v_declName_2107_, lean_object* v_as_2108_, lean_object* v_sz_2109_, lean_object* v_i_2110_, lean_object* v_b_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
size_t v_sz_boxed_2115_; size_t v_i_boxed_2116_; lean_object* v_res_2117_; 
v_sz_boxed_2115_ = lean_unbox_usize(v_sz_2109_);
lean_dec(v_sz_2109_);
v_i_boxed_2116_ = lean_unbox_usize(v_i_2110_);
lean_dec(v_i_2110_);
v_res_2117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v___x_2106_, v_declName_2107_, v_as_2108_, v_sz_boxed_2115_, v_i_boxed_2116_, v_b_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec_ref(v_as_2108_);
lean_dec_ref(v___x_2106_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(lean_object* v_a_2118_, lean_object* v_x_2119_){
_start:
{
if (lean_obj_tag(v_x_2119_) == 0)
{
lean_object* v___x_2120_; 
v___x_2120_ = lean_box(0);
return v___x_2120_;
}
else
{
lean_object* v_key_2121_; lean_object* v_value_2122_; lean_object* v_tail_2123_; uint8_t v___x_2124_; 
v_key_2121_ = lean_ctor_get(v_x_2119_, 0);
v_value_2122_ = lean_ctor_get(v_x_2119_, 1);
v_tail_2123_ = lean_ctor_get(v_x_2119_, 2);
v___x_2124_ = lean_name_eq(v_key_2121_, v_a_2118_);
if (v___x_2124_ == 0)
{
v_x_2119_ = v_tail_2123_;
goto _start;
}
else
{
lean_object* v___x_2126_; 
lean_inc(v_value_2122_);
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_value_2122_);
return v___x_2126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg___boxed(lean_object* v_a_2127_, lean_object* v_x_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_2127_, v_x_2128_);
lean_dec(v_x_2128_);
lean_dec(v_a_2127_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(lean_object* v_m_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v_buckets_2132_; lean_object* v___x_2133_; uint64_t v___y_2135_; 
v_buckets_2132_ = lean_ctor_get(v_m_2130_, 1);
v___x_2133_ = lean_array_get_size(v_buckets_2132_);
if (lean_obj_tag(v_a_2131_) == 0)
{
uint64_t v___x_2149_; 
v___x_2149_ = 1723ULL;
v___y_2135_ = v___x_2149_;
goto v___jp_2134_;
}
else
{
uint64_t v_hash_2150_; 
v_hash_2150_ = lean_ctor_get_uint64(v_a_2131_, sizeof(void*)*2);
v___y_2135_ = v_hash_2150_;
goto v___jp_2134_;
}
v___jp_2134_:
{
uint64_t v___x_2136_; uint64_t v___x_2137_; uint64_t v_fold_2138_; uint64_t v___x_2139_; uint64_t v___x_2140_; uint64_t v___x_2141_; size_t v___x_2142_; size_t v___x_2143_; size_t v___x_2144_; size_t v___x_2145_; size_t v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2136_ = 32ULL;
v___x_2137_ = lean_uint64_shift_right(v___y_2135_, v___x_2136_);
v_fold_2138_ = lean_uint64_xor(v___y_2135_, v___x_2137_);
v___x_2139_ = 16ULL;
v___x_2140_ = lean_uint64_shift_right(v_fold_2138_, v___x_2139_);
v___x_2141_ = lean_uint64_xor(v_fold_2138_, v___x_2140_);
v___x_2142_ = lean_uint64_to_usize(v___x_2141_);
v___x_2143_ = lean_usize_of_nat(v___x_2133_);
v___x_2144_ = ((size_t)1ULL);
v___x_2145_ = lean_usize_sub(v___x_2143_, v___x_2144_);
v___x_2146_ = lean_usize_land(v___x_2142_, v___x_2145_);
v___x_2147_ = lean_array_uget_borrowed(v_buckets_2132_, v___x_2146_);
v___x_2148_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_2131_, v___x_2147_);
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_m_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v_m_2151_, v_a_2152_);
lean_dec(v_a_2152_);
lean_dec_ref(v_m_2151_);
return v_res_2153_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2154_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(lean_object* v_declName_2157_, uint8_t v_isMeta_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v_env_2167_; lean_object* v___y_2169_; lean_object* v___x_2182_; 
v___x_2162_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0);
v___x_2163_ = lean_st_ref_get(v___y_2160_);
v_env_2167_ = lean_ctor_get(v___x_2163_, 0);
lean_inc_ref(v_env_2167_);
lean_dec(v___x_2163_);
v___x_2182_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2167_, v_declName_2157_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_dec_ref(v_env_2167_);
lean_dec(v_declName_2157_);
goto v___jp_2164_;
}
else
{
lean_object* v_val_2183_; lean_object* v___x_2184_; lean_object* v_modules_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v_val_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_val_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v___x_2184_ = l_Lean_Environment_header(v_env_2167_);
v_modules_2185_ = lean_ctor_get(v___x_2184_, 3);
lean_inc_ref(v_modules_2185_);
lean_dec_ref(v___x_2184_);
v___x_2186_ = lean_array_get_size(v_modules_2185_);
v___x_2187_ = lean_nat_dec_lt(v_val_2183_, v___x_2186_);
if (v___x_2187_ == 0)
{
lean_dec_ref(v_modules_2185_);
lean_dec(v_val_2183_);
lean_dec_ref(v_env_2167_);
lean_dec(v_declName_2157_);
goto v___jp_2164_;
}
else
{
lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___y_2191_; 
v___x_2188_ = lean_array_fget(v_modules_2185_, v_val_2183_);
lean_dec(v_val_2183_);
lean_dec_ref(v_modules_2185_);
v___x_2189_ = lean_st_ref_get(v___y_2160_);
if (v_isMeta_2158_ == 0)
{
lean_dec(v___x_2189_);
v___y_2191_ = v_isMeta_2158_;
goto v___jp_2190_;
}
else
{
lean_object* v_env_2202_; uint8_t v___x_2203_; 
v_env_2202_ = lean_ctor_get(v___x_2189_, 0);
lean_inc_ref(v_env_2202_);
lean_dec(v___x_2189_);
lean_inc(v_declName_2157_);
v___x_2203_ = l_Lean_isMarkedMeta(v_env_2202_, v_declName_2157_);
if (v___x_2203_ == 0)
{
v___y_2191_ = v_isMeta_2158_;
goto v___jp_2190_;
}
else
{
uint8_t v___x_2204_; 
v___x_2204_ = 0;
v___y_2191_ = v___x_2204_;
goto v___jp_2190_;
}
}
v___jp_2190_:
{
lean_object* v_toImport_2192_; lean_object* v_module_2193_; lean_object* v___x_2194_; 
v_toImport_2192_ = lean_ctor_get(v___x_2188_, 0);
lean_inc_ref(v_toImport_2192_);
lean_dec(v___x_2188_);
v_module_2193_ = lean_ctor_get(v_toImport_2192_, 0);
lean_inc(v_module_2193_);
lean_dec_ref(v_toImport_2192_);
lean_inc(v_declName_2157_);
v___x_2194_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_module_2193_, v___y_2191_, v_declName_2157_, v___y_2159_, v___y_2160_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_dec_ref_known(v___x_2194_, 1);
v___x_2195_ = l_Lean_indirectModUseExt;
v___x_2196_ = lean_box(1);
v___x_2197_ = lean_box(0);
lean_inc_ref(v_env_2167_);
v___x_2198_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2162_, v___x_2195_, v_env_2167_, v___x_2196_, v___x_2197_);
v___x_2199_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v___x_2198_, v_declName_2157_);
lean_dec(v___x_2198_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v___x_2200_; 
v___x_2200_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1));
v___y_2169_ = v___x_2200_;
goto v___jp_2168_;
}
else
{
lean_object* v_val_2201_; 
v_val_2201_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_val_2201_);
lean_dec_ref_known(v___x_2199_, 1);
v___y_2169_ = v_val_2201_;
goto v___jp_2168_;
}
}
else
{
lean_dec_ref(v_env_2167_);
lean_dec(v_declName_2157_);
return v___x_2194_;
}
}
}
}
v___jp_2164_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
return v___x_2166_;
}
v___jp_2168_:
{
lean_object* v___x_2170_; size_t v_sz_2171_; size_t v___x_2172_; lean_object* v___x_2173_; 
v___x_2170_ = lean_box(0);
v_sz_2171_ = lean_array_size(v___y_2169_);
v___x_2172_ = ((size_t)0ULL);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v_env_2167_, v_declName_2157_, v___y_2169_, v_sz_2171_, v___x_2172_, v___x_2170_, v___y_2159_, v___y_2160_);
lean_dec_ref(v___y_2169_);
lean_dec_ref(v_env_2167_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; 
v_unused_2181_ = lean_ctor_get(v___x_2173_, 0);
lean_dec(v_unused_2181_);
v___x_2175_ = v___x_2173_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_dec(v___x_2173_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2170_);
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2170_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
else
{
return v___x_2173_;
}
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2157_ = stack[0].m_obj;
uint8_t v_isMeta_2158_ = stack[1].m_num;
lean_object* v___y_2159_ = stack[2].m_obj;
lean_object* v___y_2160_ = stack[3].m_obj;
lean_object* v_res_2205_;
v_res_2205_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_declName_2157_, v_isMeta_2158_, v___y_2159_, v___y_2160_);
stack->m_obj
 = v_res_2205_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___boxed(lean_object* v_declName_2206_, lean_object* v_isMeta_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
uint8_t v_isMeta_boxed_2211_; lean_object* v_res_2212_; 
v_isMeta_boxed_2211_ = lean_unbox(v_isMeta_2207_);
v_res_2212_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_declName_2206_, v_isMeta_boxed_2211_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
return v_res_2212_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(lean_object* v_as_x27_2213_, lean_object* v_b_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
if (lean_obj_tag(v_as_x27_2213_) == 0)
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2218_, 0, v_b_2214_);
return v___x_2218_;
}
else
{
lean_object* v_head_2219_; lean_object* v_tail_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; lean_object* v___x_2223_; 
v_head_2219_ = lean_ctor_get(v_as_x27_2213_, 0);
v_tail_2220_ = lean_ctor_get(v_as_x27_2213_, 1);
v___x_2221_ = lean_box(0);
v___x_2222_ = 1;
lean_inc(v_head_2219_);
v___x_2223_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_head_2219_, v___x_2222_, v___y_2215_, v___y_2216_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_dec_ref_known(v___x_2223_, 1);
v_as_x27_2213_ = v_tail_2220_;
v_b_2214_ = v___x_2221_;
goto _start;
}
else
{
return v___x_2223_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_2213_ = stack[0].m_obj;
lean_object* v_b_2214_ = stack[1].m_obj;
lean_object* v___y_2215_ = stack[2].m_obj;
lean_object* v___y_2216_ = stack[3].m_obj;
lean_object* v_res_2225_;
v_res_2225_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_2213_, v_b_2214_, v___y_2215_, v___y_2216_);
stack->m_obj
 = v_res_2225_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2226_, lean_object* v_b_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_2226_, v_b_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v_as_x27_2226_);
return v_res_2231_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(lean_object* v_x_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2237_; lean_object* v_env_2238_; lean_object* v___f_2239_; lean_object* v___f_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v_scopes_2243_; lean_object* v___x_2244_; lean_object* v_opts_2245_; lean_object* v___x_2246_; 
v___x_2237_ = lean_st_ref_get(v___y_2235_);
v_env_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc_ref_n(v_env_2238_, 3);
lean_dec(v___x_2237_);
v___f_2239_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2239_, 0, v_env_2238_);
v___f_2240_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2240_, 0, v_env_2238_);
v___x_2241_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2242_ = lean_st_ref_get(v___y_2235_);
v_scopes_2243_ = lean_ctor_get(v___x_2242_, 2);
lean_inc(v_scopes_2243_);
lean_dec(v___x_2242_);
v___x_2244_ = l_List_head_x21___redArg(v___x_2241_, v_scopes_2243_);
lean_dec(v_scopes_2243_);
v_opts_2245_ = lean_ctor_get(v___x_2244_, 1);
lean_inc_ref(v_opts_2245_);
lean_dec(v___x_2244_);
v___x_2246_ = l_Lean_Elab_Command_getScope___redArg(v___y_2235_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v_currNamespace_2248_; lean_object* v___f_2249_; lean_object* v___x_2250_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
v_currNamespace_2248_ = lean_ctor_get(v_a_2247_, 2);
lean_inc_n(v_currNamespace_2248_, 2);
lean_dec(v_a_2247_);
v___f_2249_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2249_, 0, v_currNamespace_2248_);
v___x_2250_ = l_Lean_Elab_Command_getScope___redArg(v___y_2235_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v_openDecls_2252_; lean_object* v___f_2253_; lean_object* v___f_2254_; lean_object* v_methods_2255_; lean_object* v___x_2256_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2251_);
lean_dec_ref_known(v___x_2250_, 1);
v_openDecls_2252_ = lean_ctor_get(v_a_2251_, 3);
lean_inc_n(v_openDecls_2252_, 2);
lean_dec(v_a_2251_);
lean_inc(v_currNamespace_2248_);
lean_inc_ref(v_env_2238_);
v___f_2253_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2253_, 0, v_env_2238_);
lean_closure_set(v___f_2253_, 1, v_currNamespace_2248_);
lean_closure_set(v___f_2253_, 2, v_openDecls_2252_);
v___f_2254_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2254_, 0, v_env_2238_);
lean_closure_set(v___f_2254_, 1, v_opts_2245_);
lean_closure_set(v___f_2254_, 2, v_currNamespace_2248_);
lean_closure_set(v___f_2254_, 3, v_openDecls_2252_);
v_methods_2255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2255_, 0, v___f_2240_);
lean_ctor_set(v_methods_2255_, 1, v___f_2249_);
lean_ctor_set(v_methods_2255_, 2, v___f_2239_);
lean_ctor_set(v_methods_2255_, 3, v___f_2253_);
lean_ctor_set(v_methods_2255_, 4, v___f_2254_);
v___x_2256_ = l_Lean_Elab_Command_getRef___redArg(v___y_2234_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2258_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2256_, 1);
v___x_2258_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2234_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v_currRecDepth_2260_; lean_object* v_quotContext_x3f_2261_; lean_object* v_a_2263_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref_known(v___x_2258_, 1);
v_currRecDepth_2260_ = lean_ctor_get(v___y_2234_, 2);
v_quotContext_x3f_2261_ = lean_ctor_get(v___y_2234_, 5);
if (lean_obj_tag(v_quotContext_x3f_2261_) == 0)
{
lean_object* v___x_2337_; lean_object* v_a_2338_; 
v___x_2337_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2235_);
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref(v___x_2337_);
v_a_2263_ = v_a_2338_;
goto v___jp_2262_;
}
else
{
lean_object* v_val_2339_; 
v_val_2339_ = lean_ctor_get(v_quotContext_x3f_2261_, 0);
lean_inc(v_val_2339_);
v_a_2263_ = v_val_2339_;
goto v___jp_2262_;
}
v___jp_2262_:
{
lean_object* v___x_2264_; lean_object* v_maxRecDepth_2265_; lean_object* v___x_2266_; lean_object* v_nextMacroScope_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2264_ = lean_st_ref_get(v___y_2235_);
v_maxRecDepth_2265_ = lean_ctor_get(v___x_2264_, 5);
lean_inc(v_maxRecDepth_2265_);
lean_dec(v___x_2264_);
v___x_2266_ = lean_st_ref_get(v___y_2235_);
v_nextMacroScope_2267_ = lean_ctor_get(v___x_2266_, 4);
lean_inc(v_nextMacroScope_2267_);
lean_dec(v___x_2266_);
lean_inc(v_currRecDepth_2260_);
v___x_2268_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2268_, 0, v_methods_2255_);
lean_ctor_set(v___x_2268_, 1, v_a_2263_);
lean_ctor_set(v___x_2268_, 2, v_a_2259_);
lean_ctor_set(v___x_2268_, 3, v_currRecDepth_2260_);
lean_ctor_set(v___x_2268_, 4, v_maxRecDepth_2265_);
lean_ctor_set(v___x_2268_, 5, v_a_2257_);
v___x_2269_ = lean_box(0);
v___x_2270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2270_, 0, v_nextMacroScope_2267_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
lean_ctor_set(v___x_2270_, 2, v___x_2269_);
v___x_2271_ = lean_apply_2(v_x_2233_, v___x_2268_, v___x_2270_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v_a_2273_; lean_object* v_macroScope_2274_; lean_object* v_traceMsgs_2275_; lean_object* v_expandedMacroDecls_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 1);
lean_inc(v_a_2272_);
v_a_2273_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2271_, 2);
v_macroScope_2274_ = lean_ctor_get(v_a_2272_, 0);
lean_inc(v_macroScope_2274_);
v_traceMsgs_2275_ = lean_ctor_get(v_a_2272_, 1);
lean_inc(v_traceMsgs_2275_);
v_expandedMacroDecls_2276_ = lean_ctor_get(v_a_2272_, 2);
lean_inc(v_expandedMacroDecls_2276_);
lean_dec(v_a_2272_);
v___x_2277_ = lean_box(0);
v___x_2278_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_expandedMacroDecls_2276_, v___x_2277_, v___y_2234_, v___y_2235_);
lean_dec(v_expandedMacroDecls_2276_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v___x_2279_; lean_object* v_env_2280_; lean_object* v_messages_2281_; lean_object* v_scopes_2282_; lean_object* v_usedQuotCtxts_2283_; lean_object* v_maxRecDepth_2284_; lean_object* v_ngen_2285_; lean_object* v_auxDeclNGen_2286_; lean_object* v_infoState_2287_; lean_object* v_traceState_2288_; lean_object* v_snapshotTasks_2289_; lean_object* v_prevLinterStates_2290_; lean_object* v_codeQualityEntryTasks_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref_known(v___x_2278_, 1);
v___x_2279_ = lean_st_ref_take(v___y_2235_);
v_env_2280_ = lean_ctor_get(v___x_2279_, 0);
v_messages_2281_ = lean_ctor_get(v___x_2279_, 1);
v_scopes_2282_ = lean_ctor_get(v___x_2279_, 2);
v_usedQuotCtxts_2283_ = lean_ctor_get(v___x_2279_, 3);
v_maxRecDepth_2284_ = lean_ctor_get(v___x_2279_, 5);
v_ngen_2285_ = lean_ctor_get(v___x_2279_, 6);
v_auxDeclNGen_2286_ = lean_ctor_get(v___x_2279_, 7);
v_infoState_2287_ = lean_ctor_get(v___x_2279_, 8);
v_traceState_2288_ = lean_ctor_get(v___x_2279_, 9);
v_snapshotTasks_2289_ = lean_ctor_get(v___x_2279_, 10);
v_prevLinterStates_2290_ = lean_ctor_get(v___x_2279_, 11);
v_codeQualityEntryTasks_2291_ = lean_ctor_get(v___x_2279_, 12);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; 
v_unused_2318_ = lean_ctor_get(v___x_2279_, 4);
lean_dec(v_unused_2318_);
v___x_2293_ = v___x_2279_;
v_isShared_2294_ = v_isSharedCheck_2317_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2291_);
lean_inc(v_prevLinterStates_2290_);
lean_inc(v_snapshotTasks_2289_);
lean_inc(v_traceState_2288_);
lean_inc(v_infoState_2287_);
lean_inc(v_auxDeclNGen_2286_);
lean_inc(v_ngen_2285_);
lean_inc(v_maxRecDepth_2284_);
lean_inc(v_usedQuotCtxts_2283_);
lean_inc(v_scopes_2282_);
lean_inc(v_messages_2281_);
lean_inc(v_env_2280_);
lean_dec(v___x_2279_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2317_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 4, v_macroScope_2274_);
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_env_2280_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_messages_2281_);
lean_ctor_set(v_reuseFailAlloc_2316_, 2, v_scopes_2282_);
lean_ctor_set(v_reuseFailAlloc_2316_, 3, v_usedQuotCtxts_2283_);
lean_ctor_set(v_reuseFailAlloc_2316_, 4, v_macroScope_2274_);
lean_ctor_set(v_reuseFailAlloc_2316_, 5, v_maxRecDepth_2284_);
lean_ctor_set(v_reuseFailAlloc_2316_, 6, v_ngen_2285_);
lean_ctor_set(v_reuseFailAlloc_2316_, 7, v_auxDeclNGen_2286_);
lean_ctor_set(v_reuseFailAlloc_2316_, 8, v_infoState_2287_);
lean_ctor_set(v_reuseFailAlloc_2316_, 9, v_traceState_2288_);
lean_ctor_set(v_reuseFailAlloc_2316_, 10, v_snapshotTasks_2289_);
lean_ctor_set(v_reuseFailAlloc_2316_, 11, v_prevLinterStates_2290_);
lean_ctor_set(v_reuseFailAlloc_2316_, 12, v_codeQualityEntryTasks_2291_);
v___x_2296_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2297_ = lean_st_ref_put(v___y_2235_, v___x_2296_);
v___x_2298_ = l_List_reverse___redArg(v_traceMsgs_2275_);
v___x_2299_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v___x_2298_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2306_ == 0)
{
lean_object* v_unused_2307_; 
v_unused_2307_ = lean_ctor_get(v___x_2299_, 0);
lean_dec(v_unused_2307_);
v___x_2301_ = v___x_2299_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_dec(v___x_2299_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v_a_2273_);
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2273_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec(v_a_2273_);
v_a_2308_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2299_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2299_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v_traceMsgs_2275_);
lean_dec(v_macroScope_2274_);
lean_dec(v_a_2273_);
v_a_2319_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2278_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2278_);
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
else
{
lean_object* v_a_2327_; 
v_a_2327_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2271_, 2);
if (lean_obj_tag(v_a_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v_a_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v_a_2328_ = lean_ctor_get(v_a_2327_, 0);
lean_inc(v_a_2328_);
v_a_2329_ = lean_ctor_get(v_a_2327_, 1);
lean_inc_ref(v_a_2329_);
lean_dec_ref_known(v_a_2327_, 2);
v___x_2330_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0));
v___x_2331_ = lean_string_dec_eq(v_a_2329_, v___x_2330_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2332_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2332_, 0, v_a_2329_);
v___x_2333_ = l_Lean_MessageData_ofFormat(v___x_2332_);
v___x_2334_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_a_2328_, v___x_2333_, v___y_2234_, v___y_2235_);
lean_dec(v_a_2328_);
return v___x_2334_;
}
else
{
lean_object* v___x_2335_; 
lean_dec_ref(v_a_2329_);
v___x_2335_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_a_2328_);
return v___x_2335_;
}
}
else
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2336_;
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v_a_2257_);
lean_dec_ref_known(v_methods_2255_, 5);
lean_dec_ref(v_x_2233_);
v_a_2340_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2258_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2258_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec_ref_known(v_methods_2255_, 5);
lean_dec_ref(v_x_2233_);
v_a_2348_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2256_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2256_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref(v___f_2249_);
lean_dec(v_currNamespace_2248_);
lean_dec_ref(v_opts_2245_);
lean_dec_ref(v___f_2240_);
lean_dec_ref(v___f_2239_);
lean_dec_ref(v_env_2238_);
lean_dec_ref(v_x_2233_);
v_a_2356_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2250_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2250_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec_ref(v_opts_2245_);
lean_dec_ref(v___f_2240_);
lean_dec_ref(v___f_2239_);
lean_dec_ref(v_env_2238_);
lean_dec_ref(v_x_2233_);
v_a_2364_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2246_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2246_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2233_ = stack[0].m_obj;
lean_object* v___y_2234_ = stack[1].m_obj;
lean_object* v___y_2235_ = stack[2].m_obj;
lean_object* v_res_2372_;
v_res_2372_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2233_, v___y_2234_, v___y_2235_);
stack->m_obj
 = v_res_2372_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___boxed(lean_object* v_x_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
return v_res_2377_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(lean_object* v_as_2378_, size_t v_i_2379_, size_t v_stop_2380_, lean_object* v_b_2381_){
_start:
{
lean_object* v___y_2383_; uint8_t v___x_2387_; 
v___x_2387_ = lean_usize_dec_eq(v_i_2379_, v_stop_2380_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; 
v___x_2388_ = lean_array_uget_borrowed(v_as_2378_, v_i_2379_);
lean_inc(v___x_2388_);
v___x_2389_ = l_Lean_Syntax_getKind(v___x_2388_);
v___x_2390_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10));
v___x_2391_ = lean_name_eq(v___x_2389_, v___x_2390_);
lean_dec(v___x_2389_);
if (v___x_2391_ == 0)
{
v___y_2383_ = v_b_2381_;
goto v___jp_2382_;
}
else
{
lean_object* v___x_2392_; 
lean_inc(v___x_2388_);
v___x_2392_ = lean_array_push(v_b_2381_, v___x_2388_);
v___y_2383_ = v___x_2392_;
goto v___jp_2382_;
}
}
else
{
return v_b_2381_;
}
v___jp_2382_:
{
size_t v___x_2384_; size_t v___x_2385_; 
v___x_2384_ = ((size_t)1ULL);
v___x_2385_ = lean_usize_add(v_i_2379_, v___x_2384_);
v_i_2379_ = v___x_2385_;
v_b_2381_ = v___y_2383_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2378_ = stack[0].m_obj;
size_t v_i_2379_ = stack[1].m_num;
size_t v_stop_2380_ = stack[2].m_num;
lean_object* v_b_2381_ = stack[3].m_obj;
lean_object* v_res_2393_;
v_res_2393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v_as_2378_, v_i_2379_, v_stop_2380_, v_b_2381_);
stack->m_obj
 = v_res_2393_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8___boxed(lean_object* v_as_2394_, lean_object* v_i_2395_, lean_object* v_stop_2396_, lean_object* v_b_2397_){
_start:
{
size_t v_i_boxed_2398_; size_t v_stop_boxed_2399_; lean_object* v_res_2400_; 
v_i_boxed_2398_ = lean_unbox_usize(v_i_2395_);
lean_dec(v_i_2395_);
v_stop_boxed_2399_ = lean_unbox_usize(v_stop_2396_);
lean_dec(v_stop_2396_);
v_res_2400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v_as_2394_, v_i_boxed_2398_, v_stop_boxed_2399_, v_b_2397_);
lean_dec_ref(v_as_2394_);
return v_res_2400_;
}
}
lean_object* l_Lean_Elab_Command_elabNotation(lean_object* v_x_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; size_t v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; uint8_t v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; 
v___x_2474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0));
v___x_2475_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1));
v___x_2476_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
lean_inc(v_x_2443_);
v___x_2477_ = l_Lean_Syntax_isOfKind(v_x_2443_, v___x_2476_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2586_; 
lean_dec(v_x_2443_);
v___x_2586_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2586_;
}
else
{
lean_object* v___x_2587_; size_t v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; uint8_t v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; size_t v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; uint8_t v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; size_t v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; uint8_t v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; size_t v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; uint8_t v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; size_t v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; uint8_t v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v_prio_x3f_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v_name_x3f_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v_prec_x3f_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v_attrs_x3f_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v_doc_x3f_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2587_ = lean_unsigned_to_nat(0u);
v___x_2942_ = l_Lean_Syntax_getArg(v_x_2443_, v___x_2587_);
v___x_2943_ = l_Lean_Syntax_isNone(v___x_2942_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2944_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2942_);
v___x_2945_ = l_Lean_Syntax_matchesNull(v___x_2942_, v___x_2944_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; 
lean_dec(v___x_2942_);
lean_dec(v_x_2443_);
v___x_2946_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2946_;
}
else
{
lean_object* v_doc_x3f_2947_; 
v_doc_x3f_2947_ = l_Lean_Syntax_getArg(v___x_2942_, v___x_2587_);
lean_dec(v___x_2942_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2950_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__15));
lean_inc(v_doc_x3f_2947_);
v___x_2951_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2947_, v___x_2950_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; 
lean_dec(v_doc_x3f_2947_);
lean_dec(v_x_2443_);
v___x_2952_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2952_;
}
else
{
goto v___jp_2948_;
}
}
else
{
goto v___jp_2948_;
}
v___jp_2948_:
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_doc_x3f_2947_);
v_doc_x3f_2926_ = v___x_2949_;
v___y_2927_ = v_a_2444_;
v___y_2928_ = v_a_2445_;
goto v___jp_2925_;
}
}
}
else
{
lean_object* v___x_2953_; 
lean_dec(v___x_2942_);
v___x_2953_ = lean_box(0);
v_doc_x3f_2926_ = v___x_2953_;
v___y_2927_ = v_a_2444_;
v___y_2928_ = v_a_2445_;
goto v___jp_2925_;
}
v___jp_2588_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; size_t v_sz_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
lean_inc_ref_n(v___y_2605_, 2);
v___x_2609_ = l_Array_append___redArg(v___y_2605_, v___y_2608_);
lean_dec_ref(v___y_2608_);
lean_inc_n(v___y_2596_, 3);
lean_inc_n(v___y_2591_, 9);
v___x_2610_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2610_, 0, v___y_2591_);
lean_ctor_set(v___x_2610_, 1, v___y_2596_);
lean_ctor_set(v___x_2610_, 2, v___x_2609_);
v___x_2611_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
v___x_2612_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
v___x_2613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___y_2591_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__8));
v___x_2615_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___y_2591_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_2617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___y_2591_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = l_Nat_reprFast(v___y_2593_);
v___x_2619_ = lean_box(2);
v___x_2620_ = l_Lean_Syntax_mkNumLit(v___x_2618_, v___x_2619_);
v___x_2621_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_2622_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___y_2591_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = l_Lean_Syntax_node5(v___y_2591_, v___x_2611_, v___x_2613_, v___x_2615_, v___x_2617_, v___x_2620_, v___x_2622_);
v___x_2624_ = l_Lean_Syntax_node1(v___y_2591_, v___y_2596_, v___x_2623_);
v_sz_2625_ = lean_array_size(v___y_2597_);
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_2625_, v___y_2589_, v___y_2597_);
v___x_2627_ = l_Array_append___redArg(v___y_2605_, v___x_2626_);
lean_dec_ref(v___x_2626_);
v___x_2628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2628_, 0, v___y_2591_);
lean_ctor_set(v___x_2628_, 1, v___y_2596_);
lean_ctor_set(v___x_2628_, 2, v___x_2627_);
v___x_2629_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
v___x_2630_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___y_2591_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = lean_unsigned_to_nat(10u);
v___x_2632_ = lean_mk_empty_array_with_capacity(v___x_2631_);
v___x_2633_ = lean_array_push(v___x_2632_, v___y_2594_);
v___x_2634_ = lean_array_push(v___x_2633_, v___y_2598_);
lean_inc(v___y_2595_);
v___x_2635_ = lean_array_push(v___x_2634_, v___y_2595_);
v___x_2636_ = lean_array_push(v___x_2635_, v___y_2599_);
v___x_2637_ = lean_array_push(v___x_2636_, v___y_2607_);
v___x_2638_ = lean_array_push(v___x_2637_, v___x_2610_);
v___x_2639_ = lean_array_push(v___x_2638_, v___x_2624_);
v___x_2640_ = lean_array_push(v___x_2639_, v___x_2628_);
v___x_2641_ = lean_array_push(v___x_2640_, v___x_2630_);
v___x_2642_ = lean_array_push(v___x_2641_, v___y_2601_);
lean_inc(v___y_2602_);
v___x_2643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2643_, 0, v___y_2591_);
lean_ctor_set(v___x_2643_, 1, v___y_2602_);
lean_ctor_set(v___x_2643_, 2, v___x_2642_);
v___x_2644_ = l_Lean_Elab_Command_elabSyntax(v___x_2643_, v___y_2592_, v___y_2606_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2644_, 1);
v___x_2646_ = lean_array_get_size(v___y_2590_);
v___x_2647_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__68));
v___x_2648_ = lean_nat_dec_lt(v___x_2587_, v___x_2646_);
if (v___x_2648_ == 0)
{
v___y_2532_ = v___y_2589_;
v___y_2533_ = v___y_2590_;
v___y_2534_ = v___y_2592_;
v___y_2535_ = v___y_2595_;
v___y_2536_ = v___y_2596_;
v___y_2537_ = v___x_2621_;
v___y_2538_ = v___y_2600_;
v___y_2539_ = v___x_2619_;
v___y_2540_ = v___y_2604_;
v___y_2541_ = v___y_2603_;
v___y_2542_ = v_a_2645_;
v___y_2543_ = v___y_2605_;
v___y_2544_ = v___y_2606_;
v___y_2545_ = v___x_2647_;
goto v___jp_2531_;
}
else
{
uint8_t v___x_2649_; 
v___x_2649_ = lean_nat_dec_le(v___x_2646_, v___x_2646_);
if (v___x_2649_ == 0)
{
if (v___x_2648_ == 0)
{
v___y_2532_ = v___y_2589_;
v___y_2533_ = v___y_2590_;
v___y_2534_ = v___y_2592_;
v___y_2535_ = v___y_2595_;
v___y_2536_ = v___y_2596_;
v___y_2537_ = v___x_2621_;
v___y_2538_ = v___y_2600_;
v___y_2539_ = v___x_2619_;
v___y_2540_ = v___y_2604_;
v___y_2541_ = v___y_2603_;
v___y_2542_ = v_a_2645_;
v___y_2543_ = v___y_2605_;
v___y_2544_ = v___y_2606_;
v___y_2545_ = v___x_2647_;
goto v___jp_2531_;
}
else
{
size_t v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_usize_of_nat(v___x_2646_);
v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2590_, v___y_2589_, v___x_2650_, v___x_2647_);
v___y_2532_ = v___y_2589_;
v___y_2533_ = v___y_2590_;
v___y_2534_ = v___y_2592_;
v___y_2535_ = v___y_2595_;
v___y_2536_ = v___y_2596_;
v___y_2537_ = v___x_2621_;
v___y_2538_ = v___y_2600_;
v___y_2539_ = v___x_2619_;
v___y_2540_ = v___y_2604_;
v___y_2541_ = v___y_2603_;
v___y_2542_ = v_a_2645_;
v___y_2543_ = v___y_2605_;
v___y_2544_ = v___y_2606_;
v___y_2545_ = v___x_2651_;
goto v___jp_2531_;
}
}
else
{
size_t v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_usize_of_nat(v___x_2646_);
v___x_2653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_2590_, v___y_2589_, v___x_2652_, v___x_2647_);
v___y_2532_ = v___y_2589_;
v___y_2533_ = v___y_2590_;
v___y_2534_ = v___y_2592_;
v___y_2535_ = v___y_2595_;
v___y_2536_ = v___y_2596_;
v___y_2537_ = v___x_2621_;
v___y_2538_ = v___y_2600_;
v___y_2539_ = v___x_2619_;
v___y_2540_ = v___y_2604_;
v___y_2541_ = v___y_2603_;
v___y_2542_ = v_a_2645_;
v___y_2543_ = v___y_2605_;
v___y_2544_ = v___y_2606_;
v___y_2545_ = v___x_2653_;
goto v___jp_2531_;
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec(v___y_2600_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2590_);
v_a_2654_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2644_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2644_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
v___jp_2662_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
lean_inc_ref(v___y_2680_);
v___x_2683_ = l_Array_append___redArg(v___y_2680_, v___y_2682_);
lean_dec_ref(v___y_2682_);
lean_inc(v___y_2671_);
lean_inc(v___y_2664_);
v___x_2684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2684_, 0, v___y_2664_);
lean_ctor_set(v___x_2684_, 1, v___y_2671_);
lean_ctor_set(v___x_2684_, 2, v___x_2683_);
if (lean_obj_tag(v___y_2670_) == 1)
{
lean_object* v_val_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v_val_2685_ = lean_ctor_get(v___y_2670_, 0);
lean_inc(v_val_2685_);
lean_dec_ref_known(v___y_2670_, 1);
v___x_2686_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
v___x_2687_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__53));
lean_inc_n(v___y_2664_, 5);
v___x_2688_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___y_2664_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
v___x_2689_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__11));
v___x_2690_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___y_2664_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v___x_2691_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__26));
v___x_2692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___y_2664_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__37));
v___x_2694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___y_2664_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = l_Lean_Syntax_node5(v___y_2664_, v___x_2686_, v___x_2688_, v___x_2690_, v___x_2692_, v_val_2685_, v___x_2694_);
v___x_2696_ = l_Array_mkArray1___redArg(v___x_2695_);
v___y_2589_ = v___y_2663_;
v___y_2590_ = v___y_2665_;
v___y_2591_ = v___y_2664_;
v___y_2592_ = v___y_2666_;
v___y_2593_ = v___y_2667_;
v___y_2594_ = v___y_2668_;
v___y_2595_ = v___y_2669_;
v___y_2596_ = v___y_2671_;
v___y_2597_ = v___y_2672_;
v___y_2598_ = v___y_2673_;
v___y_2599_ = v___y_2674_;
v___y_2600_ = v___y_2675_;
v___y_2601_ = v___y_2676_;
v___y_2602_ = v___y_2677_;
v___y_2603_ = v___y_2679_;
v___y_2604_ = v___y_2678_;
v___y_2605_ = v___y_2680_;
v___y_2606_ = v___y_2681_;
v___y_2607_ = v___x_2684_;
v___y_2608_ = v___x_2696_;
goto v___jp_2588_;
}
else
{
lean_object* v___x_2697_; 
lean_dec(v___y_2670_);
v___x_2697_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2589_ = v___y_2663_;
v___y_2590_ = v___y_2665_;
v___y_2591_ = v___y_2664_;
v___y_2592_ = v___y_2666_;
v___y_2593_ = v___y_2667_;
v___y_2594_ = v___y_2668_;
v___y_2595_ = v___y_2669_;
v___y_2596_ = v___y_2671_;
v___y_2597_ = v___y_2672_;
v___y_2598_ = v___y_2673_;
v___y_2599_ = v___y_2674_;
v___y_2600_ = v___y_2675_;
v___y_2601_ = v___y_2676_;
v___y_2602_ = v___y_2677_;
v___y_2603_ = v___y_2679_;
v___y_2604_ = v___y_2678_;
v___y_2605_ = v___y_2680_;
v___y_2606_ = v___y_2681_;
v___y_2607_ = v___x_2684_;
v___y_2608_ = v___x_2697_;
goto v___jp_2588_;
}
}
v___jp_2698_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
lean_inc_ref(v___y_2716_);
v___x_2719_ = l_Array_append___redArg(v___y_2716_, v___y_2718_);
lean_dec_ref(v___y_2718_);
lean_inc(v___y_2709_);
lean_inc_n(v___y_2700_, 2);
v___x_2720_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2720_, 0, v___y_2700_);
lean_ctor_set(v___x_2720_, 1, v___y_2709_);
lean_ctor_set(v___x_2720_, 2, v___x_2719_);
lean_inc_ref(v___y_2706_);
v___x_2721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___y_2700_);
lean_ctor_set(v___x_2721_, 1, v___y_2706_);
if (lean_obj_tag(v___y_2708_) == 1)
{
lean_object* v_val_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v_val_2722_ = lean_ctor_get(v___y_2708_, 0);
lean_inc(v_val_2722_);
lean_dec_ref_known(v___y_2708_, 1);
v___x_2723_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
v___x_2724_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6));
lean_inc_n(v___y_2700_, 2);
v___x_2725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___y_2700_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = l_Lean_Syntax_node2(v___y_2700_, v___x_2723_, v___x_2725_, v_val_2722_);
v___x_2727_ = l_Array_mkArray1___redArg(v___x_2726_);
v___y_2663_ = v___y_2699_;
v___y_2664_ = v___y_2700_;
v___y_2665_ = v___y_2701_;
v___y_2666_ = v___y_2702_;
v___y_2667_ = v___y_2703_;
v___y_2668_ = v___y_2704_;
v___y_2669_ = v___y_2705_;
v___y_2670_ = v___y_2707_;
v___y_2671_ = v___y_2709_;
v___y_2672_ = v___y_2710_;
v___y_2673_ = v___x_2720_;
v___y_2674_ = v___x_2721_;
v___y_2675_ = v___y_2711_;
v___y_2676_ = v___y_2712_;
v___y_2677_ = v___y_2713_;
v___y_2678_ = v___y_2715_;
v___y_2679_ = v___y_2714_;
v___y_2680_ = v___y_2716_;
v___y_2681_ = v___y_2717_;
v___y_2682_ = v___x_2727_;
goto v___jp_2662_;
}
else
{
lean_object* v___x_2728_; 
lean_dec(v___y_2708_);
v___x_2728_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2663_ = v___y_2699_;
v___y_2664_ = v___y_2700_;
v___y_2665_ = v___y_2701_;
v___y_2666_ = v___y_2702_;
v___y_2667_ = v___y_2703_;
v___y_2668_ = v___y_2704_;
v___y_2669_ = v___y_2705_;
v___y_2670_ = v___y_2707_;
v___y_2671_ = v___y_2709_;
v___y_2672_ = v___y_2710_;
v___y_2673_ = v___x_2720_;
v___y_2674_ = v___x_2721_;
v___y_2675_ = v___y_2711_;
v___y_2676_ = v___y_2712_;
v___y_2677_ = v___y_2713_;
v___y_2678_ = v___y_2715_;
v___y_2679_ = v___y_2714_;
v___y_2680_ = v___y_2716_;
v___y_2681_ = v___y_2717_;
v___y_2682_ = v___x_2728_;
goto v___jp_2662_;
}
}
v___jp_2729_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
lean_inc_ref(v___y_2747_);
v___x_2750_ = l_Array_append___redArg(v___y_2747_, v___y_2749_);
lean_dec_ref(v___y_2749_);
lean_inc(v___y_2739_);
lean_inc(v___y_2731_);
v___x_2751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2751_, 0, v___y_2731_);
lean_ctor_set(v___x_2751_, 1, v___y_2739_);
lean_ctor_set(v___x_2751_, 2, v___x_2750_);
if (lean_obj_tag(v___y_2733_) == 1)
{
lean_object* v_val_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v_val_2752_ = lean_ctor_get(v___y_2733_, 0);
lean_inc(v_val_2752_);
lean_dec_ref_known(v___y_2733_, 1);
v___x_2753_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__11));
lean_inc_ref(v___y_2746_);
v___x_2754_ = l_Lean_Name_mkStr4(v___x_2474_, v___x_2475_, v___y_2746_, v___x_2753_);
v___x_2755_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__13));
lean_inc_n(v___y_2731_, 4);
v___x_2756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___y_2731_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
lean_inc_ref(v___y_2747_);
v___x_2757_ = l_Array_append___redArg(v___y_2747_, v_val_2752_);
lean_dec(v_val_2752_);
lean_inc(v___y_2739_);
v___x_2758_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2758_, 0, v___y_2731_);
lean_ctor_set(v___x_2758_, 1, v___y_2739_);
lean_ctor_set(v___x_2758_, 2, v___x_2757_);
v___x_2759_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__17));
v___x_2760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___y_2731_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = l_Lean_Syntax_node3(v___y_2731_, v___x_2754_, v___x_2756_, v___x_2758_, v___x_2760_);
v___x_2762_ = l_Array_mkArray1___redArg(v___x_2761_);
v___y_2699_ = v___y_2730_;
v___y_2700_ = v___y_2731_;
v___y_2701_ = v___y_2732_;
v___y_2702_ = v___y_2734_;
v___y_2703_ = v___y_2735_;
v___y_2704_ = v___x_2751_;
v___y_2705_ = v___y_2736_;
v___y_2706_ = v___y_2737_;
v___y_2707_ = v___y_2738_;
v___y_2708_ = v___y_2740_;
v___y_2709_ = v___y_2739_;
v___y_2710_ = v___y_2741_;
v___y_2711_ = v___y_2742_;
v___y_2712_ = v___y_2743_;
v___y_2713_ = v___y_2744_;
v___y_2714_ = v___y_2746_;
v___y_2715_ = v___y_2745_;
v___y_2716_ = v___y_2747_;
v___y_2717_ = v___y_2748_;
v___y_2718_ = v___x_2762_;
goto v___jp_2698_;
}
else
{
lean_object* v___x_2763_; 
lean_dec(v___y_2733_);
v___x_2763_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2699_ = v___y_2730_;
v___y_2700_ = v___y_2731_;
v___y_2701_ = v___y_2732_;
v___y_2702_ = v___y_2734_;
v___y_2703_ = v___y_2735_;
v___y_2704_ = v___x_2751_;
v___y_2705_ = v___y_2736_;
v___y_2706_ = v___y_2737_;
v___y_2707_ = v___y_2738_;
v___y_2708_ = v___y_2740_;
v___y_2709_ = v___y_2739_;
v___y_2710_ = v___y_2741_;
v___y_2711_ = v___y_2742_;
v___y_2712_ = v___y_2743_;
v___y_2713_ = v___y_2744_;
v___y_2714_ = v___y_2746_;
v___y_2715_ = v___y_2745_;
v___y_2716_ = v___y_2747_;
v___y_2717_ = v___y_2748_;
v___y_2718_ = v___x_2763_;
goto v___jp_2698_;
}
}
v___jp_2764_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2781_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__12));
v___x_2782_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__13));
v___x_2783_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13));
v___x_2784_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
if (lean_obj_tag(v___y_2777_) == 1)
{
lean_object* v_val_2785_; lean_object* v___x_2786_; 
v_val_2785_ = lean_ctor_get(v___y_2777_, 0);
lean_inc(v_val_2785_);
lean_dec_ref_known(v___y_2777_, 1);
v___x_2786_ = l_Array_mkArray1___redArg(v_val_2785_);
v___y_2730_ = v___y_2765_;
v___y_2731_ = v___y_2766_;
v___y_2732_ = v___y_2767_;
v___y_2733_ = v___y_2768_;
v___y_2734_ = v___y_2769_;
v___y_2735_ = v___y_2770_;
v___y_2736_ = v___y_2771_;
v___y_2737_ = v___x_2781_;
v___y_2738_ = v___y_2772_;
v___y_2739_ = v___x_2783_;
v___y_2740_ = v___y_2773_;
v___y_2741_ = v___y_2774_;
v___y_2742_ = v___y_2775_;
v___y_2743_ = v___y_2776_;
v___y_2744_ = v___x_2782_;
v___y_2745_ = v___y_2779_;
v___y_2746_ = v___y_2778_;
v___y_2747_ = v___x_2784_;
v___y_2748_ = v___y_2780_;
v___y_2749_ = v___x_2786_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2787_; 
lean_dec(v___y_2777_);
v___x_2787_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7));
v___y_2730_ = v___y_2765_;
v___y_2731_ = v___y_2766_;
v___y_2732_ = v___y_2767_;
v___y_2733_ = v___y_2768_;
v___y_2734_ = v___y_2769_;
v___y_2735_ = v___y_2770_;
v___y_2736_ = v___y_2771_;
v___y_2737_ = v___x_2781_;
v___y_2738_ = v___y_2772_;
v___y_2739_ = v___x_2783_;
v___y_2740_ = v___y_2773_;
v___y_2741_ = v___y_2774_;
v___y_2742_ = v___y_2775_;
v___y_2743_ = v___y_2776_;
v___y_2744_ = v___x_2782_;
v___y_2745_ = v___y_2779_;
v___y_2746_ = v___y_2778_;
v___y_2747_ = v___x_2784_;
v___y_2748_ = v___y_2780_;
v___y_2749_ = v___x_2787_;
goto v___jp_2729_;
}
}
v___jp_2788_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v_rhs_2801_; lean_object* v___x_2802_; lean_object* v_items_2803_; lean_object* v_attrs_x3f_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2798_ = lean_unsigned_to_nat(7u);
v___x_2799_ = l_Lean_Syntax_getArg(v_x_2443_, v___x_2798_);
v___x_2800_ = lean_unsigned_to_nat(9u);
v_rhs_2801_ = l_Lean_Syntax_getArg(v_x_2443_, v___x_2800_);
v___x_2802_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3));
v_items_2803_ = l_Lean_Syntax_getArgs(v___x_2799_);
lean_dec(v___x_2799_);
lean_inc(v_rhs_2801_);
v_attrs_x3f_2804_ = l_Lean_Elab_Command_addInheritDocDefault(v_rhs_2801_, v___y_2790_);
v___x_2805_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_2805_, 0, v_prio_x3f_2795_);
v___x_2806_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2805_, v___y_2796_, v___y_2797_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; size_t v_sz_2808_; size_t v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v_sz_2808_ = lean_array_size(v_items_2803_);
v___x_2809_ = ((size_t)0ULL);
v___x_2810_ = lean_box_usize(v_sz_2808_);
v___x_2811_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___boxed__const__1));
lean_inc_ref(v_items_2803_);
v___x_2812_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed), 5, 3);
lean_closure_set(v___x_2812_, 0, v___x_2810_);
lean_closure_set(v___x_2812_, 1, v___x_2811_);
lean_closure_set(v___x_2812_, 2, v_items_2803_);
v___x_2813_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2812_, v___y_2796_, v___y_2797_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
v___x_2815_ = 0;
v___x_2816_ = l_Lean_mkIdentFrom(v_x_2443_, v___x_2802_, v___x_2815_);
lean_dec(v_x_2443_);
v___x_2817_ = l_Lean_Elab_Command_getRef___redArg(v___y_2796_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref_known(v___x_2817_, 1);
v___x_2819_ = l_Lean_SourceInfo_fromRef(v_a_2818_, v___x_2815_);
lean_dec(v_a_2818_);
v___x_2820_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2796_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_quotContext_x3f_2821_; 
lean_dec_ref_known(v___x_2820_, 1);
v_quotContext_x3f_2821_ = lean_ctor_get(v___y_2796_, 5);
if (lean_obj_tag(v_quotContext_x3f_2821_) == 0)
{
lean_object* v___x_2822_; 
v___x_2822_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2797_);
lean_dec_ref(v___x_2822_);
v___y_2765_ = v___x_2809_;
v___y_2766_ = v___x_2819_;
v___y_2767_ = v_items_2803_;
v___y_2768_ = v_attrs_x3f_2804_;
v___y_2769_ = v___y_2796_;
v___y_2770_ = v_a_2807_;
v___y_2771_ = v___y_2792_;
v___y_2772_ = v___y_2793_;
v___y_2773_ = v___y_2794_;
v___y_2774_ = v_a_2814_;
v___y_2775_ = v_rhs_2801_;
v___y_2776_ = v___x_2816_;
v___y_2777_ = v___y_2789_;
v___y_2778_ = v___y_2791_;
v___y_2779_ = v___x_2815_;
v___y_2780_ = v___y_2797_;
goto v___jp_2764_;
}
else
{
v___y_2765_ = v___x_2809_;
v___y_2766_ = v___x_2819_;
v___y_2767_ = v_items_2803_;
v___y_2768_ = v_attrs_x3f_2804_;
v___y_2769_ = v___y_2796_;
v___y_2770_ = v_a_2807_;
v___y_2771_ = v___y_2792_;
v___y_2772_ = v___y_2793_;
v___y_2773_ = v___y_2794_;
v___y_2774_ = v_a_2814_;
v___y_2775_ = v_rhs_2801_;
v___y_2776_ = v___x_2816_;
v___y_2777_ = v___y_2789_;
v___y_2778_ = v___y_2791_;
v___y_2779_ = v___x_2815_;
v___y_2780_ = v___y_2797_;
goto v___jp_2764_;
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec(v___x_2819_);
lean_dec(v___x_2816_);
lean_dec(v_a_2814_);
lean_dec(v_a_2807_);
lean_dec(v_attrs_x3f_2804_);
lean_dec_ref(v_items_2803_);
lean_dec(v_rhs_2801_);
lean_dec(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec(v___y_2789_);
v_a_2823_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2820_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2820_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec(v___x_2816_);
lean_dec(v_a_2814_);
lean_dec(v_a_2807_);
lean_dec(v_attrs_x3f_2804_);
lean_dec_ref(v_items_2803_);
lean_dec(v_rhs_2801_);
lean_dec(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec(v___y_2789_);
v_a_2831_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2817_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2817_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec(v_a_2807_);
lean_dec(v_attrs_x3f_2804_);
lean_dec_ref(v_items_2803_);
lean_dec(v_rhs_2801_);
lean_dec(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec(v___y_2789_);
lean_dec(v_x_2443_);
v_a_2839_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2813_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2813_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_attrs_x3f_2804_);
lean_dec_ref(v_items_2803_);
lean_dec(v_rhs_2801_);
lean_dec(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec(v___y_2789_);
lean_dec(v_x_2443_);
v_a_2847_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2806_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2806_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
v___jp_2855_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; 
v___x_2866_ = lean_unsigned_to_nat(6u);
v___x_2867_ = l_Lean_Syntax_getArg(v_x_2443_, v___x_2866_);
v___x_2868_ = l_Lean_Syntax_isNone(v___x_2867_);
if (v___x_2868_ == 0)
{
uint8_t v___x_2869_; 
lean_inc(v___x_2867_);
v___x_2869_ = l_Lean_Syntax_matchesNull(v___x_2867_, v___y_2861_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; 
lean_dec(v___x_2867_);
lean_dec(v_name_x3f_2863_);
lean_dec(v___y_2862_);
lean_dec(v___y_2860_);
lean_dec(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec(v_x_2443_);
v___x_2870_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2870_;
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; 
v___x_2871_ = l_Lean_Syntax_getArg(v___x_2867_, v___x_2587_);
lean_dec(v___x_2867_);
v___x_2872_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__7));
lean_inc(v___x_2871_);
v___x_2873_ = l_Lean_Syntax_isOfKind(v___x_2871_, v___x_2872_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; 
lean_dec(v___x_2871_);
lean_dec(v_name_x3f_2863_);
lean_dec(v___y_2862_);
lean_dec(v___y_2860_);
lean_dec(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec(v_x_2443_);
v___x_2874_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2874_;
}
else
{
lean_object* v_prio_x3f_2875_; lean_object* v___x_2876_; 
v_prio_x3f_2875_ = l_Lean_Syntax_getArg(v___x_2871_, v___y_2859_);
lean_dec(v___x_2871_);
v___x_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2876_, 0, v_prio_x3f_2875_);
v___y_2789_ = v___y_2856_;
v___y_2790_ = v___y_2857_;
v___y_2791_ = v___y_2858_;
v___y_2792_ = v___y_2860_;
v___y_2793_ = v_name_x3f_2863_;
v___y_2794_ = v___y_2862_;
v_prio_x3f_2795_ = v___x_2876_;
v___y_2796_ = v___y_2864_;
v___y_2797_ = v___y_2865_;
goto v___jp_2788_;
}
}
}
else
{
lean_object* v___x_2877_; 
lean_dec(v___x_2867_);
v___x_2877_ = lean_box(0);
v___y_2789_ = v___y_2856_;
v___y_2790_ = v___y_2857_;
v___y_2791_ = v___y_2858_;
v___y_2792_ = v___y_2860_;
v___y_2793_ = v_name_x3f_2863_;
v___y_2794_ = v___y_2862_;
v_prio_x3f_2795_ = v___x_2877_;
v___y_2796_ = v___y_2864_;
v___y_2797_ = v___y_2865_;
goto v___jp_2788_;
}
}
v___jp_2878_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v___x_2888_ = lean_unsigned_to_nat(5u);
v___x_2889_ = l_Lean_Syntax_getArg(v_x_2443_, v___x_2888_);
v___x_2890_ = l_Lean_Syntax_isNone(v___x_2889_);
if (v___x_2890_ == 0)
{
uint8_t v___x_2891_; 
lean_inc(v___x_2889_);
v___x_2891_ = l_Lean_Syntax_matchesNull(v___x_2889_, v___y_2884_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; 
lean_dec(v___x_2889_);
lean_dec(v_prec_x3f_2885_);
lean_dec(v___y_2883_);
lean_dec(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec(v_x_2443_);
v___x_2892_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2892_;
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; 
v___x_2893_ = l_Lean_Syntax_getArg(v___x_2889_, v___x_2587_);
lean_dec(v___x_2889_);
v___x_2894_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__10));
lean_inc(v___x_2893_);
v___x_2895_ = l_Lean_Syntax_isOfKind(v___x_2893_, v___x_2894_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; 
lean_dec(v___x_2893_);
lean_dec(v_prec_x3f_2885_);
lean_dec(v___y_2883_);
lean_dec(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec(v_x_2443_);
v___x_2896_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2896_;
}
else
{
lean_object* v_name_x3f_2897_; lean_object* v___x_2898_; 
v_name_x3f_2897_ = l_Lean_Syntax_getArg(v___x_2893_, v___y_2882_);
lean_dec(v___x_2893_);
v___x_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2898_, 0, v_name_x3f_2897_);
v___y_2856_ = v___y_2879_;
v___y_2857_ = v___y_2880_;
v___y_2858_ = v___y_2881_;
v___y_2859_ = v___y_2882_;
v___y_2860_ = v___y_2883_;
v___y_2861_ = v___y_2884_;
v___y_2862_ = v_prec_x3f_2885_;
v_name_x3f_2863_ = v___x_2898_;
v___y_2864_ = v___y_2886_;
v___y_2865_ = v___y_2887_;
goto v___jp_2855_;
}
}
}
else
{
lean_object* v___x_2899_; 
lean_dec(v___x_2889_);
v___x_2899_ = lean_box(0);
v___y_2856_ = v___y_2879_;
v___y_2857_ = v___y_2880_;
v___y_2858_ = v___y_2881_;
v___y_2859_ = v___y_2882_;
v___y_2860_ = v___y_2883_;
v___y_2861_ = v___y_2884_;
v___y_2862_ = v_prec_x3f_2885_;
v_name_x3f_2863_ = v___x_2899_;
v___y_2864_ = v___y_2886_;
v___y_2865_ = v___y_2887_;
goto v___jp_2855_;
}
}
v___jp_2900_:
{
lean_object* v___x_2906_; lean_object* v_attrKind_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
v___x_2906_ = lean_unsigned_to_nat(2u);
v_attrKind_2907_ = l_Lean_Syntax_getArg(v_x_2443_, v___x_2906_);
v___x_2908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2));
v___x_2909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6));
lean_inc(v_attrKind_2907_);
v___x_2910_ = l_Lean_Syntax_isOfKind(v_attrKind_2907_, v___x_2909_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; 
lean_dec(v_attrKind_2907_);
lean_dec(v_attrs_x3f_2903_);
lean_dec(v___y_2901_);
lean_dec(v_x_2443_);
v___x_2911_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2911_;
}
else
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; 
v___x_2912_ = lean_unsigned_to_nat(3u);
v___x_2913_ = lean_unsigned_to_nat(4u);
v___x_2914_ = l_Lean_Syntax_getArg(v_x_2443_, v___x_2913_);
v___x_2915_ = l_Lean_Syntax_isNone(v___x_2914_);
if (v___x_2915_ == 0)
{
uint8_t v___x_2916_; 
lean_inc(v___x_2914_);
v___x_2916_ = l_Lean_Syntax_matchesNull(v___x_2914_, v___y_2902_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; 
lean_dec(v___x_2914_);
lean_dec(v_attrKind_2907_);
lean_dec(v_attrs_x3f_2903_);
lean_dec(v___y_2901_);
lean_dec(v_x_2443_);
v___x_2917_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2917_;
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2918_ = l_Lean_Syntax_getArg(v___x_2914_, v___x_2587_);
lean_dec(v___x_2914_);
v___x_2919_ = ((lean_object*)(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5));
lean_inc(v___x_2918_);
v___x_2920_ = l_Lean_Syntax_isOfKind(v___x_2918_, v___x_2919_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; 
lean_dec(v___x_2918_);
lean_dec(v_attrKind_2907_);
lean_dec(v_attrs_x3f_2903_);
lean_dec(v___y_2901_);
lean_dec(v_x_2443_);
v___x_2921_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2921_;
}
else
{
lean_object* v_prec_x3f_2922_; lean_object* v___x_2923_; 
v_prec_x3f_2922_ = l_Lean_Syntax_getArg(v___x_2918_, v___y_2902_);
lean_dec(v___x_2918_);
v___x_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_prec_x3f_2922_);
v___y_2879_ = v___y_2901_;
v___y_2880_ = v_attrs_x3f_2903_;
v___y_2881_ = v___x_2908_;
v___y_2882_ = v___x_2912_;
v___y_2883_ = v_attrKind_2907_;
v___y_2884_ = v___y_2902_;
v_prec_x3f_2885_ = v___x_2923_;
v___y_2886_ = v___y_2904_;
v___y_2887_ = v___y_2905_;
goto v___jp_2878_;
}
}
}
else
{
lean_object* v___x_2924_; 
lean_dec(v___x_2914_);
v___x_2924_ = lean_box(0);
v___y_2879_ = v___y_2901_;
v___y_2880_ = v_attrs_x3f_2903_;
v___y_2881_ = v___x_2908_;
v___y_2882_ = v___x_2912_;
v___y_2883_ = v_attrKind_2907_;
v___y_2884_ = v___y_2902_;
v_prec_x3f_2885_ = v___x_2924_;
v___y_2886_ = v___y_2904_;
v___y_2887_ = v___y_2905_;
goto v___jp_2878_;
}
}
}
v___jp_2925_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2929_ = lean_unsigned_to_nat(1u);
v___x_2930_ = l_Lean_Syntax_getArg(v_x_2443_, v___x_2929_);
v___x_2931_ = l_Lean_Syntax_isNone(v___x_2930_);
if (v___x_2931_ == 0)
{
uint8_t v___x_2932_; 
lean_inc(v___x_2930_);
v___x_2932_ = l_Lean_Syntax_matchesNull(v___x_2930_, v___x_2929_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; 
lean_dec(v___x_2930_);
lean_dec(v_doc_x3f_2926_);
lean_dec(v_x_2443_);
v___x_2933_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2933_;
}
else
{
lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2934_ = l_Lean_Syntax_getArg(v___x_2930_, v___x_2587_);
lean_dec(v___x_2930_);
v___x_2935_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__12));
lean_inc(v___x_2934_);
v___x_2936_ = l_Lean_Syntax_isOfKind(v___x_2934_, v___x_2935_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; 
lean_dec(v___x_2934_);
lean_dec(v_doc_x3f_2926_);
lean_dec(v_x_2443_);
v___x_2937_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
return v___x_2937_;
}
else
{
lean_object* v___x_2938_; lean_object* v_attrs_x3f_2939_; lean_object* v___x_2940_; 
v___x_2938_ = l_Lean_Syntax_getArg(v___x_2934_, v___x_2929_);
lean_dec(v___x_2934_);
v_attrs_x3f_2939_ = l_Lean_Syntax_getArgs(v___x_2938_);
lean_dec(v___x_2938_);
v___x_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2940_, 0, v_attrs_x3f_2939_);
v___y_2901_ = v_doc_x3f_2926_;
v___y_2902_ = v___x_2929_;
v_attrs_x3f_2903_ = v___x_2940_;
v___y_2904_ = v___y_2927_;
v___y_2905_ = v___y_2928_;
goto v___jp_2900_;
}
}
}
else
{
lean_object* v___x_2941_; 
lean_dec(v___x_2930_);
v___x_2941_ = lean_box(0);
v___y_2901_ = v_doc_x3f_2926_;
v___y_2902_ = v___x_2929_;
v_attrs_x3f_2903_ = v___x_2941_;
v___y_2904_ = v___y_2927_;
v___y_2905_ = v___y_2928_;
goto v___jp_2900_;
}
}
}
v___jp_2447_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkUnexpander___boxed), 5, 3);
lean_closure_set(v___x_2453_, 0, v___y_2449_);
lean_closure_set(v___x_2453_, 1, v___y_2448_);
lean_closure_set(v___x_2453_, 2, v___y_2450_);
v___x_2454_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2453_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2465_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2465_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2465_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
if (lean_obj_tag(v_a_2455_) == 1)
{
lean_object* v_val_2459_; lean_object* v___x_2460_; 
lean_del_object(v___x_2457_);
v_val_2459_ = lean_ctor_get(v_a_2455_, 0);
lean_inc(v_val_2459_);
lean_dec_ref_known(v_a_2455_, 1);
v___x_2460_ = l_Lean_Elab_Command_elabCommand(v_val_2459_, v___y_2451_, v___y_2452_);
return v___x_2460_;
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2463_; 
lean_dec(v_a_2455_);
v___x_2461_ = lean_box(0);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2461_);
v___x_2463_ = v___x_2457_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
v_a_2466_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2454_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2454_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
v___jp_2478_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2489_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__2));
v___x_2490_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__3));
lean_inc_ref(v___y_2485_);
lean_inc_n(v___y_2484_, 4);
lean_inc_n(v___y_2479_, 15);
v___x_2491_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2491_, 0, v___y_2479_);
lean_ctor_set(v___x_2491_, 1, v___y_2484_);
lean_ctor_set(v___x_2491_, 2, v___y_2485_);
v___x_2492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___y_2479_);
lean_ctor_set(v___x_2492_, 1, v___x_2489_);
v___x_2493_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__29));
lean_inc_ref_n(v___y_2480_, 4);
v___x_2494_ = l_Lean_Name_mkStr4(v___x_2474_, v___x_2475_, v___y_2480_, v___x_2493_);
v___x_2495_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__31));
v___x_2496_ = l_Lean_Name_mkStr4(v___x_2474_, v___x_2475_, v___y_2480_, v___x_2495_);
v___x_2497_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__33));
v___x_2498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___y_2479_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__34));
v___x_2500_ = l_Lean_Name_mkStr4(v___x_2474_, v___x_2475_, v___y_2480_, v___x_2499_);
v___x_2501_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__36));
v___x_2502_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___y_2479_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
lean_inc_ref(v___y_2486_);
v___x_2503_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___y_2479_);
lean_ctor_set(v___x_2503_, 1, v___y_2486_);
lean_inc_ref(v___x_2503_);
lean_inc(v___y_2481_);
lean_inc_ref(v___x_2502_);
lean_inc(v___x_2500_);
v___x_2504_ = l_Lean_Syntax_node3(v___y_2479_, v___x_2500_, v___x_2502_, v___y_2481_, v___x_2503_);
v___x_2505_ = l_Lean_Syntax_node1(v___y_2479_, v___y_2484_, v___x_2504_);
v___x_2506_ = l_Lean_Syntax_node1(v___y_2479_, v___y_2484_, v___x_2505_);
v___x_2507_ = ((lean_object*)(l_Lean_Elab_Command_mkUnexpander___closed__38));
v___x_2508_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___y_2479_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__4));
v___x_2510_ = l_Lean_Name_mkStr4(v___x_2474_, v___x_2475_, v___y_2480_, v___x_2509_);
v___x_2511_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__5));
v___x_2512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___y_2479_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
lean_inc(v___y_2488_);
v___x_2513_ = l_Lean_Syntax_node3(v___y_2479_, v___x_2500_, v___x_2502_, v___y_2488_, v___x_2503_);
v___x_2514_ = l_Lean_Syntax_node2(v___y_2479_, v___x_2510_, v___x_2512_, v___x_2513_);
v___x_2515_ = l_Lean_Syntax_node4(v___y_2479_, v___x_2496_, v___x_2498_, v___x_2506_, v___x_2508_, v___x_2514_);
v___x_2516_ = l_Lean_Syntax_node1(v___y_2479_, v___y_2484_, v___x_2515_);
v___x_2517_ = l_Lean_Syntax_node1(v___y_2479_, v___x_2494_, v___x_2516_);
lean_inc_n(v___y_2483_, 2);
lean_inc_ref_n(v___x_2491_, 2);
v___x_2518_ = l_Lean_Syntax_node6(v___y_2479_, v___x_2490_, v___x_2491_, v___x_2491_, v___y_2483_, v___x_2492_, v___x_2491_, v___x_2517_);
v___x_2519_ = l_Lean_Elab_Command_isLocalAttrKind(v___y_2483_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Lean_Elab_Command_elabCommand(v___x_2518_, v___y_2482_, v___y_2487_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_dec_ref_known(v___x_2520_, 1);
v___y_2448_ = v___y_2481_;
v___y_2449_ = v___y_2483_;
v___y_2450_ = v___y_2488_;
v___y_2451_ = v___y_2482_;
v___y_2452_ = v___y_2487_;
goto v___jp_2447_;
}
else
{
lean_dec(v___y_2488_);
lean_dec(v___y_2483_);
lean_dec(v___y_2481_);
return v___x_2520_;
}
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v_scopes_2523_; lean_object* v___x_2524_; lean_object* v_opts_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___f_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2521_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2522_ = lean_st_ref_get(v___y_2487_);
v_scopes_2523_ = lean_ctor_get(v___x_2522_, 2);
lean_inc(v_scopes_2523_);
lean_dec(v___x_2522_);
v___x_2524_ = l_List_head_x21___redArg(v___x_2521_, v_scopes_2523_);
lean_dec(v_scopes_2523_);
v_opts_2525_ = lean_ctor_get(v___x_2524_, 1);
lean_inc_ref(v_opts_2525_);
lean_dec(v___x_2524_);
v___x_2526_ = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
v___x_2527_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(v_opts_2525_, v___x_2526_, v___x_2477_);
v___f_2528_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___lam__0), 2, 1);
lean_closure_set(v___f_2528_, 0, v___x_2527_);
v___x_2529_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_2529_, 0, v___x_2518_);
v___x_2530_ = l_Lean_Elab_Command_withScope___redArg(v___f_2528_, v___x_2529_, v___y_2482_, v___y_2487_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_dec_ref_known(v___x_2530_, 1);
v___y_2448_ = v___y_2481_;
v___y_2449_ = v___y_2483_;
v___y_2450_ = v___y_2488_;
v___y_2451_ = v___y_2482_;
v___y_2452_ = v___y_2487_;
goto v___jp_2447_;
}
else
{
lean_dec(v___y_2488_);
lean_dec(v___y_2483_);
lean_dec(v___y_2481_);
return v___x_2530_;
}
}
}
v___jp_2531_:
{
size_t v_sz_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; size_t v_sz_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v_sz_2546_ = lean_array_size(v___y_2545_);
v___x_2547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(v_sz_2546_, v___y_2532_, v___y_2545_);
v___x_2548_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(v___x_2547_, v___y_2538_);
lean_dec_ref(v___x_2547_);
v_sz_2549_ = lean_array_size(v___y_2533_);
v___x_2550_ = lean_box_usize(v_sz_2549_);
v___x_2551_ = lean_box_usize(v___y_2532_);
v___x_2552_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed), 5, 3);
lean_closure_set(v___x_2552_, 0, v___x_2550_);
lean_closure_set(v___x_2552_, 1, v___x_2551_);
lean_closure_set(v___x_2552_, 2, v___y_2533_);
v___x_2553_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_2552_, v___y_2534_, v___y_2544_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
v___x_2555_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2555_, 0, v___y_2539_);
lean_ctor_set(v___x_2555_, 1, v___y_2542_);
lean_ctor_set(v___x_2555_, 2, v_a_2554_);
v___x_2556_ = l_Lean_Elab_Command_getRef___redArg(v___y_2534_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2556_, 1);
v___x_2558_ = l_Lean_SourceInfo_fromRef(v_a_2557_, v___y_2540_);
lean_dec(v_a_2557_);
v___x_2559_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2534_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_quotContext_x3f_2560_; 
lean_dec_ref_known(v___x_2559_, 1);
v_quotContext_x3f_2560_ = lean_ctor_get(v___y_2534_, 5);
if (lean_obj_tag(v_quotContext_x3f_2560_) == 0)
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_2544_);
lean_dec_ref(v___x_2561_);
v___y_2479_ = v___x_2558_;
v___y_2480_ = v___y_2541_;
v___y_2481_ = v___x_2555_;
v___y_2482_ = v___y_2534_;
v___y_2483_ = v___y_2535_;
v___y_2484_ = v___y_2536_;
v___y_2485_ = v___y_2543_;
v___y_2486_ = v___y_2537_;
v___y_2487_ = v___y_2544_;
v___y_2488_ = v___x_2548_;
goto v___jp_2478_;
}
else
{
v___y_2479_ = v___x_2558_;
v___y_2480_ = v___y_2541_;
v___y_2481_ = v___x_2555_;
v___y_2482_ = v___y_2534_;
v___y_2483_ = v___y_2535_;
v___y_2484_ = v___y_2536_;
v___y_2485_ = v___y_2543_;
v___y_2486_ = v___y_2537_;
v___y_2487_ = v___y_2544_;
v___y_2488_ = v___x_2548_;
goto v___jp_2478_;
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_dec(v___x_2558_);
lean_dec_ref_known(v___x_2555_, 3);
lean_dec(v___x_2548_);
lean_dec(v___y_2535_);
v_a_2562_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2559_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2559_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec_ref_known(v___x_2555_, 3);
lean_dec(v___x_2548_);
lean_dec(v___y_2535_);
v_a_2570_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2556_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2556_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec(v___x_2548_);
lean_dec(v___y_2542_);
lean_dec(v___y_2539_);
lean_dec(v___y_2535_);
v_a_2578_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2553_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2553_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabNotation_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2443_ = stack[0].m_obj;
lean_object* v_a_2444_ = stack[1].m_obj;
lean_object* v_a_2445_ = stack[2].m_obj;
lean_object* v_res_2954_;
v_res_2954_ = l_Lean_Elab_Command_elabNotation(v_x_2443_, v_a_2444_, v_a_2445_);
stack->m_obj
 = v_res_2954_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNotation___boxed(lean_object* v_x_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_Elab_Command_elabNotation(v_x_2955_, v_a_2956_, v_a_2957_);
lean_dec(v_a_2957_);
lean_dec_ref(v_a_2956_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(lean_object* v_00_u03b1_2960_, lean_object* v_x_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2964_; 
v___x_2964_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v_x_2961_, v___y_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2965_, lean_object* v_x_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(v_00_u03b1_2965_, v_x_2966_, v___y_2967_, v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v_x_2966_);
return v_res_2969_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(lean_object* v_00_u03b1_2970_, lean_object* v_ref_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_2971_);
return v___x_2975_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2971_ = stack[1].m_obj;
lean_object* v___y_2972_ = stack[2].m_obj;
lean_object* v___y_2973_ = stack[3].m_obj;
lean_object* v_res_2976_;
v_res_2976_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(lean_box(0), v_ref_2971_, v___y_2972_, v___y_2973_);
stack->m_obj
 = v_res_2976_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___boxed(lean_object* v_00_u03b1_2977_, lean_object* v_ref_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(v_00_u03b1_2977_, v_ref_2978_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
return v_res_2982_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(lean_object* v_00_u03b1_2983_, lean_object* v_x_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v_x_2984_, v___y_2985_, v___y_2986_);
return v___x_2988_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2984_ = stack[1].m_obj;
lean_object* v___y_2985_ = stack[2].m_obj;
lean_object* v___y_2986_ = stack[3].m_obj;
lean_object* v_res_2989_;
v_res_2989_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(lean_box(0), v_x_2984_, v___y_2985_, v___y_2986_);
stack->m_obj
 = v_res_2989_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___boxed(lean_object* v_00_u03b1_2990_, lean_object* v_x_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(v_00_u03b1_2990_, v_x_2991_, v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
return v_res_2995_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(lean_object* v_msgData_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msgData_2996_, v___y_2998_);
return v___x_3000_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2996_ = stack[0].m_obj;
lean_object* v___y_2997_ = stack[1].m_obj;
lean_object* v___y_2998_ = stack[2].m_obj;
lean_object* v_res_3001_;
v_res_3001_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(v_msgData_2996_, v___y_2997_, v___y_2998_);
stack->m_obj
 = v_res_3001_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(v_msgData_3002_, v___y_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
return v_res_3006_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(lean_object* v_as_3007_, lean_object* v_as_x27_3008_, lean_object* v_b_3009_, lean_object* v_a_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_3008_, v_b_3009_, v___y_3011_, v___y_3012_);
return v___x_3014_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3007_ = stack[0].m_obj;
lean_object* v_as_x27_3008_ = stack[1].m_obj;
lean_object* v_b_3009_ = stack[2].m_obj;
lean_object* v___y_3011_ = stack[4].m_obj;
lean_object* v___y_3012_ = stack[5].m_obj;
lean_object* v_res_3015_;
v_res_3015_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(v_as_3007_, v_as_x27_3008_, v_b_3009_, lean_box(0), v___y_3011_, v___y_3012_);
stack->m_obj
 = v_res_3015_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___boxed(lean_object* v_as_3016_, lean_object* v_as_x27_3017_, lean_object* v_b_3018_, lean_object* v_a_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(v_as_3016_, v_as_x27_3017_, v_b_3018_, v_a_3019_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v_as_x27_3017_);
lean_dec(v_as_3016_);
return v_res_3023_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(lean_object* v_00_u03b1_3024_, lean_object* v_ref_3025_, lean_object* v_msg_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_ref_3025_, v_msg_3026_, v___y_3027_, v___y_3028_);
return v___x_3030_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3025_ = stack[1].m_obj;
lean_object* v_msg_3026_ = stack[2].m_obj;
lean_object* v___y_3027_ = stack[3].m_obj;
lean_object* v___y_3028_ = stack[4].m_obj;
lean_object* v_res_3031_;
v_res_3031_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(lean_box(0), v_ref_3025_, v_msg_3026_, v___y_3027_, v___y_3028_);
stack->m_obj
 = v_res_3031_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3032_, lean_object* v_ref_3033_, lean_object* v_msg_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(v_00_u03b1_3032_, v_ref_3033_, v_msg_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v_ref_3033_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_3039_, lean_object* v_m_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v_m_3040_, v_a_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_3043_, lean_object* v_m_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(v_00_u03b2_3043_, v_m_3044_, v_a_3045_);
lean_dec(v_a_3045_);
lean_dec_ref(v_m_3044_);
return v_res_3046_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(lean_object* v_00_u03b1_3047_, lean_object* v_msg_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_3048_, v___y_3049_, v___y_3050_);
return v___x_3052_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3048_ = stack[1].m_obj;
lean_object* v___y_3049_ = stack[2].m_obj;
lean_object* v___y_3050_ = stack[3].m_obj;
lean_object* v_res_3053_;
v_res_3053_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(lean_box(0), v_msg_3048_, v___y_3049_, v___y_3050_);
stack->m_obj
 = v_res_3053_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___boxed(lean_object* v_00_u03b1_3054_, lean_object* v_msg_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(v_00_u03b1_3054_, v_msg_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
return v_res_3059_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(lean_object* v_00_u03b2_3060_, lean_object* v_x_3061_, lean_object* v_x_3062_){
_start:
{
uint8_t v___x_3063_; 
v___x_3063_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_3061_, v_x_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3061_ = stack[1].m_obj;
lean_object* v_x_3062_ = stack[2].m_obj;
uint8_t v_res_3064_;
v_res_3064_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(lean_box(0), v_x_3061_, v_x_3062_);
stack->m_num = v_res_3064_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3065_, lean_object* v_x_3066_, lean_object* v_x_3067_){
_start:
{
uint8_t v_res_3068_; lean_object* v_r_3069_; 
v_res_3068_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(v_00_u03b2_3065_, v_x_3066_, v_x_3067_);
lean_dec_ref(v_x_3067_);
lean_dec_ref(v_x_3066_);
v_r_3069_ = lean_box(v_res_3068_);
return v_r_3069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(lean_object* v_00_u03b2_3070_, lean_object* v_a_3071_, lean_object* v_x_3072_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_3071_, v_x_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___boxed(lean_object* v_00_u03b2_3074_, lean_object* v_a_3075_, lean_object* v_x_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(v_00_u03b2_3074_, v_a_3075_, v_x_3076_);
lean_dec(v_x_3076_);
lean_dec(v_a_3075_);
return v_res_3077_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(lean_object* v_msgData_3078_, lean_object* v_macroStack_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_msgData_3078_, v_macroStack_3079_, v___y_3081_);
return v___x_3083_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3078_ = stack[0].m_obj;
lean_object* v_macroStack_3079_ = stack[1].m_obj;
lean_object* v___y_3080_ = stack[2].m_obj;
lean_object* v___y_3081_ = stack[3].m_obj;
lean_object* v_res_3084_;
v_res_3084_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(v_msgData_3078_, v_macroStack_3079_, v___y_3080_, v___y_3081_);
stack->m_obj
 = v_res_3084_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___boxed(lean_object* v_msgData_3085_, lean_object* v_macroStack_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(v_msgData_3085_, v_macroStack_3086_, v___y_3087_, v___y_3088_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
return v_res_3090_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(lean_object* v_00_u03b2_3091_, lean_object* v_x_3092_, size_t v_x_3093_, lean_object* v_x_3094_){
_start:
{
uint8_t v___x_3095_; 
v___x_3095_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_3092_, v_x_3093_, v_x_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3092_ = stack[1].m_obj;
size_t v_x_3093_ = stack[2].m_num;
lean_object* v_x_3094_ = stack[3].m_obj;
uint8_t v_res_3096_;
v_res_3096_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(lean_box(0), v_x_3092_, v_x_3093_, v_x_3094_);
stack->m_num = v_res_3096_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___boxed(lean_object* v_00_u03b2_3097_, lean_object* v_x_3098_, lean_object* v_x_3099_, lean_object* v_x_3100_){
_start:
{
size_t v_x_24664__boxed_3101_; uint8_t v_res_3102_; lean_object* v_r_3103_; 
v_x_24664__boxed_3101_ = lean_unbox_usize(v_x_3099_);
lean_dec(v_x_3099_);
v_res_3102_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(v_00_u03b2_3097_, v_x_3098_, v_x_24664__boxed_3101_, v_x_3100_);
lean_dec_ref(v_x_3100_);
lean_dec_ref(v_x_3098_);
v_r_3103_ = lean_box(v_res_3102_);
return v_r_3103_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(lean_object* v_00_u03b2_3104_, lean_object* v_keys_3105_, lean_object* v_vals_3106_, lean_object* v_heq_3107_, lean_object* v_i_3108_, lean_object* v_k_3109_){
_start:
{
uint8_t v___x_3110_; 
v___x_3110_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_3105_, v_i_3108_, v_k_3109_);
return v___x_3110_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_3105_ = stack[1].m_obj;
lean_object* v_vals_3106_ = stack[2].m_obj;
lean_object* v_i_3108_ = stack[4].m_obj;
lean_object* v_k_3109_ = stack[5].m_obj;
uint8_t v_res_3111_;
v_res_3111_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(lean_box(0), v_keys_3105_, v_vals_3106_, lean_box(0), v_i_3108_, v_k_3109_);
stack->m_num = v_res_3111_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___boxed(lean_object* v_00_u03b2_3112_, lean_object* v_keys_3113_, lean_object* v_vals_3114_, lean_object* v_heq_3115_, lean_object* v_i_3116_, lean_object* v_k_3117_){
_start:
{
uint8_t v_res_3118_; lean_object* v_r_3119_; 
v_res_3118_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(v_00_u03b2_3112_, v_keys_3113_, v_vals_3114_, v_heq_3115_, v_i_3116_, v_k_3117_);
lean_dec_ref(v_k_3117_);
lean_dec_ref(v_vals_3114_);
lean_dec_ref(v_keys_3113_);
v_r_3119_ = lean_box(v_res_3118_);
return v_r_3119_;
}
}
lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1(){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3127_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3128_ = ((lean_object*)(l_Lean_Elab_Command_elabNotation___closed__1));
v___x_3129_ = ((lean_object*)(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1));
v___x_3130_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___boxed), 4, 0);
v___x_3131_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3127_, v___x_3128_, v___x_3129_, v___x_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3132_;
v_res_3132_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
stack->m_obj
 = v_res_3132_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___boxed(lean_object* v_a_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
return v_res_3134_;
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
