// Lean compiler output
// Module: Lean.Elab.ElabRules
// Imports: public import Lean.Elab.MacroArgUtil public import Lean.Elab.AuxDef public import Lean.Elab.Do.Basic
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
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
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSyntax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_evalOptPrio___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Array_mkArray5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkRuleAltKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Parser_Command_visibility_ofAttrKind(lean_object*);
lean_object* l_Lean_Elab_Command_adaptRulesExpander(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elab_rules"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabRules"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__5;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__4_value),LEAN_SCALAR_PTR_LITERAL(187, 124, 47, 85, 21, 141, 50, 117)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Elab.Do.DoElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__9;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DoElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__14_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "stx"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__16;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__15_value),LEAN_SCALAR_PTR_LITERAL(89, 124, 230, 186, 154, 11, 21, 78)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__17 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__17_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__18 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__18_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__19 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__19_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__20 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__21 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__21_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__22 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__22_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__23 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__23_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__24 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__24_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__25 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__25_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__26 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__26_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noErrorIfUnused"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__27 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__27_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "no_error_if_unused%"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__28 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "throwUnsupportedSyntax"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__29 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__30;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(225, 251, 194, 35, 13, 152, 147, 184)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__31 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__32 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__33 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__34 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__35_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__35_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__35_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__35 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__35_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__36;
static const lean_array_object l_Lean_Elab_Command_elabElabRulesAux___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__37 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__37_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Term.TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__38 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__38_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__39;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__40 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__40_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expectedType\?"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__41 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__41_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__42;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__41_value),LEAN_SCALAR_PTR_LITERAL(47, 72, 75, 114, 68, 52, 233, 214)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__43 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__43_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__44 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__44_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Elab.Term.withExpectedType"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__45 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__45_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__46;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withExpectedType"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__47 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__47_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Tactic.Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__48 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__48_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__49;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__50 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__50_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cont"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__51 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__51_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__52;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__51_value),LEAN_SCALAR_PTR_LITERAL(53, 231, 177, 147, 174, 255, 200, 174)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__53 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__53_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Elab.Command.CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__54 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__54_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__55;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__56 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__56_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__57 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__57_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__57_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__58 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__58_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doElem"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__59 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__59_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__59_value),LEAN_SCALAR_PTR_LITERAL(224, 169, 39, 82, 97, 101, 60, 174)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__60 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__60_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "syntax category `"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__61 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__61_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__62;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "` does not support expected type specification"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__63 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__63_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__64;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doElem_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__65 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__65_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__65_value),LEAN_SCALAR_PTR_LITERAL(211, 179, 163, 70, 253, 44, 85, 125)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__66 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__66_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__67 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__67_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__67_value),LEAN_SCALAR_PTR_LITERAL(226, 9, 43, 122, 104, 86, 206, 223)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__68 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__68_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__69 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__69_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__69_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__70 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__70_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__71 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__71_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__71_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__72 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__72_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "conv"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__73 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__73_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__73_value),LEAN_SCALAR_PTR_LITERAL(232, 67, 39, 189, 45, 247, 54, 81)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__74 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__74_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "unsupported syntax category `"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__75 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__75_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__76;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__77 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__77_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__78;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "command_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__79 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__79_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__79_value),LEAN_SCALAR_PTR_LITERAL(7, 200, 102, 28, 219, 237, 42, 33)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__80 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__80_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "invalid elab_rules command, specify category using `elab_rules : <cat> ...`"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__81 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__81_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__82;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "<="};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object**);
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 70, 226, 250, 127, 121, 118, 247)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__22_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Command_elabElabRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_elabElabRules___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_elabElabRules___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___closed__0_value;
static const lean_closure_object l_Lean_Elab_Command_elabElabRules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_elabElabRules___lam__2___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___closed__0_value)} };
static const lean_object* l_Lean_Elab_Command_elabElabRules___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabElabRules"};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 97, 52, 186, 206, 196, 221, 235)}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(81) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value),((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value),((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`("};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elab"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 177, 45, 203, 60, 20, 245, 118)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__7_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__9_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "precedence"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__10_value),LEAN_SCALAR_PTR_LITERAL(69, 243, 176, 51, 48, 112, 202, 160)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__12_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabTail"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__14_value),LEAN_SCALAR_PTR_LITERAL(131, 240, 225, 71, 37, 75, 83, 37)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabElab"};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 235, 135, 254, 44, 234, 233, 9)}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(lean_object* v_val_1_, uint8_t v_canonical_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Lean_Elab_Command_getRef___redArg(v___y_3_);
if (lean_obj_tag(v___x_5_) == 0)
{
lean_object* v_a_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_14_; 
v_a_6_ = lean_ctor_get(v___x_5_, 0);
v_isSharedCheck_14_ = !lean_is_exclusive(v___x_5_);
if (v_isSharedCheck_14_ == 0)
{
v___x_8_ = v___x_5_;
v_isShared_9_ = v_isSharedCheck_14_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_a_6_);
lean_dec(v___x_5_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_14_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v___x_12_; 
v___x_10_ = l_Lean_mkIdentFrom(v_a_6_, v_val_1_, v_canonical_2_);
lean_dec(v_a_6_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 0, v___x_10_);
v___x_12_ = v___x_8_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v___x_10_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
}
else
{
lean_object* v_a_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_22_; 
lean_dec(v_val_1_);
v_a_15_ = lean_ctor_get(v___x_5_, 0);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_5_);
if (v_isSharedCheck_22_ == 0)
{
v___x_17_ = v___x_5_;
v_isShared_18_ = v_isSharedCheck_22_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_a_15_);
lean_dec(v___x_5_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_22_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_a_15_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg___boxed(lean_object* v_val_23_, lean_object* v_canonical_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
uint8_t v_canonical_boxed_27_; lean_object* v_res_28_; 
v_canonical_boxed_27_ = lean_unbox(v_canonical_24_);
v_res_28_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(v_val_23_, v_canonical_boxed_27_, v___y_25_);
lean_dec_ref(v___y_25_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(lean_object* v_val_29_, uint8_t v_canonical_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(v_val_29_, v_canonical_30_, v___y_31_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___boxed(lean_object* v_val_35_, lean_object* v_canonical_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
uint8_t v_canonical_boxed_40_; lean_object* v_res_41_; 
v_canonical_boxed_40_ = lean_unbox(v_canonical_36_);
v_res_41_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(v_val_35_, v_canonical_boxed_40_, v___y_37_, v___y_38_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(lean_object* v___y_42_){
_start:
{
lean_object* v___x_44_; lean_object* v_env_45_; lean_object* v___x_46_; lean_object* v_mainModule_47_; lean_object* v___x_48_; 
v___x_44_ = lean_st_ref_get(v___y_42_);
v_env_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc_ref(v_env_45_);
lean_dec(v___x_44_);
v___x_46_ = l_Lean_Environment_header(v_env_45_);
lean_dec_ref(v_env_45_);
v_mainModule_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_mainModule_47_);
lean_dec_ref(v___x_46_);
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v_mainModule_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg___boxed(lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_49_);
lean_dec(v___y_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_53_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___boxed(lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0(lean_object* v_k_79_, lean_object* v_attrKind_80_, lean_object* v_attrs_x3f_81_, lean_object* v_kind_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
uint8_t v___x_86_; lean_object* v___x_87_; 
v___x_86_ = 0;
v___x_87_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(v_k_79_, v___x_86_, v___y_83_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_89_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_a_88_);
lean_dec_ref_known(v___x_87_, 1);
v___x_89_ = l_Lean_Elab_Command_getRef___redArg(v___y_83_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_126_; 
v_a_90_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_126_ == 0)
{
v___x_92_ = v___x_89_;
v_isShared_93_ = v_isSharedCheck_126_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_126_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; lean_object* v___x_115_; 
v___x_94_ = l_Lean_SourceInfo_fromRef(v_a_90_, v___x_86_);
lean_dec(v_a_90_);
v___x_115_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_83_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_quotContext_x3f_116_; 
lean_dec_ref_known(v___x_115_, 1);
v_quotContext_x3f_116_ = lean_ctor_get(v___y_83_, 5);
if (lean_obj_tag(v_quotContext_x3f_116_) == 0)
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_84_);
lean_dec_ref(v___x_117_);
goto v___jp_95_;
}
else
{
goto v___jp_95_;
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec(v___x_94_);
lean_del_object(v___x_92_);
lean_dec(v_a_88_);
lean_dec(v_kind_82_);
lean_dec(v_attrKind_80_);
v_a_118_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_115_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_115_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
v___jp_95_:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_96_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4));
v___x_97_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7));
v___x_98_ = l_Lean_mkIdent(v_kind_82_);
v___x_99_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
lean_inc_n(v___x_94_, 2);
v___x_100_ = l_Lean_Syntax_node1(v___x_94_, v___x_99_, v_a_88_);
v___x_101_ = l_Lean_Syntax_node2(v___x_94_, v___x_97_, v___x_98_, v___x_100_);
v___x_102_ = l_Lean_Syntax_node2(v___x_94_, v___x_96_, v_attrKind_80_, v___x_101_);
if (lean_obj_tag(v_attrs_x3f_81_) == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_mk_empty_array_with_capacity(v___x_103_);
v___x_105_ = lean_array_push(v___x_104_, v___x_102_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v___x_105_);
v___x_107_ = v___x_92_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
else
{
lean_object* v_val_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v_val_109_ = lean_ctor_get(v_attrs_x3f_81_, 0);
v___x_110_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_109_);
v___x_111_ = lean_array_push(v___x_110_, v___x_102_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v___x_111_);
v___x_113_ = v___x_92_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
else
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
lean_dec(v_a_88_);
lean_dec(v_kind_82_);
lean_dec(v_attrKind_80_);
v_a_127_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_89_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_89_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
else
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
lean_dec(v_kind_82_);
lean_dec(v_attrKind_80_);
v_a_135_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_87_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_87_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object* v_k_143_, lean_object* v_attrKind_144_, lean_object* v_attrs_x3f_145_, lean_object* v_kind_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_143_, v_attrKind_144_, v_attrs_x3f_145_, v_kind_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v_attrs_x3f_145_);
return v_res_150_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_151_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__0);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_154_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_155_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
lean_ctor_set(v___x_157_, 2, v___x_156_);
lean_ctor_set(v___x_157_, 3, v___x_156_);
lean_ctor_set(v___x_157_, 4, v___x_155_);
lean_ctor_set(v___x_157_, 5, v___x_155_);
lean_ctor_set(v___x_157_, 6, v___x_155_);
lean_ctor_set(v___x_157_, 7, v___x_155_);
lean_ctor_set(v___x_157_, 8, v___x_155_);
lean_ctor_set(v___x_157_, 9, v___x_155_);
lean_ctor_set(v___x_157_, 10, v___x_155_);
lean_ctor_set(v___x_157_, 11, v___x_154_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(32u);
v___x_159_ = lean_mk_empty_array_with_capacity(v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_161_ = ((size_t)5ULL);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_unsigned_to_nat(32u);
v___x_164_ = lean_mk_empty_array_with_capacity(v___x_163_);
v___x_165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3);
v___x_166_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_162_);
lean_ctor_set(v___x_166_, 3, v___x_162_);
lean_ctor_set_usize(v___x_166_, 4, v___x_161_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_box(1);
v___x_168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4);
v___x_169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1);
v___x_170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(lean_object* v_msgData_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; lean_object* v_env_175_; uint8_t v___x_176_; lean_object* v_env_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_scopes_180_; lean_object* v___x_181_; lean_object* v_opts_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_174_ = lean_st_ref_get(v___y_172_);
v_env_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc_ref(v_env_175_);
lean_dec(v___x_174_);
v___x_176_ = 0;
v_env_177_ = l_Lean_Environment_setRecordingDeps(v_env_175_, v___x_176_);
v___x_178_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_179_ = lean_st_ref_get(v___y_172_);
v_scopes_180_ = lean_ctor_get(v___x_179_, 2);
lean_inc(v_scopes_180_);
lean_dec(v___x_179_);
v___x_181_ = l_List_head_x21___redArg(v___x_178_, v_scopes_180_);
lean_dec(v_scopes_180_);
v_opts_182_ = lean_ctor_get(v___x_181_, 1);
lean_inc_ref(v_opts_182_);
lean_dec(v___x_181_);
v___x_183_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2);
v___x_184_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5);
v___x_185_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_185_, 0, v_env_177_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 2, v___x_184_);
lean_ctor_set(v___x_185_, 3, v_opts_182_);
v___x_186_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_msgData_171_);
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___boxed(lean_object* v_msgData_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(v_msgData_188_, v___y_189_);
lean_dec(v___y_189_);
return v_res_191_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_box(1);
v___x_193_ = l_Lean_MessageData_ofFormat(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__2));
v___x_198_ = l_Lean_MessageData_ofFormat(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7(lean_object* v_x_199_, lean_object* v_x_200_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
return v_x_199_;
}
else
{
lean_object* v_head_201_; lean_object* v_tail_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_224_; 
v_head_201_ = lean_ctor_get(v_x_200_, 0);
v_tail_202_ = lean_ctor_get(v_x_200_, 1);
v_isSharedCheck_224_ = !lean_is_exclusive(v_x_200_);
if (v_isSharedCheck_224_ == 0)
{
v___x_204_ = v_x_200_;
v_isShared_205_ = v_isSharedCheck_224_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_tail_202_);
lean_inc(v_head_201_);
lean_dec(v_x_200_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_224_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v_before_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_222_; 
v_before_206_ = lean_ctor_get(v_head_201_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v_head_201_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; 
v_unused_223_ = lean_ctor_get(v_head_201_, 1);
lean_dec(v_unused_223_);
v___x_208_ = v_head_201_;
v_isShared_209_ = v_isSharedCheck_222_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_before_206_);
lean_dec(v_head_201_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_222_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0);
if (v_isShared_209_ == 0)
{
lean_ctor_set_tag(v___x_208_, 7);
lean_ctor_set(v___x_208_, 1, v___x_210_);
lean_ctor_set(v___x_208_, 0, v_x_199_);
v___x_212_ = v___x_208_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_x_199_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_221_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3);
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 7);
lean_ctor_set(v___x_204_, 1, v___x_213_);
lean_ctor_set(v___x_204_, 0, v___x_212_);
v___x_215_ = v___x_204_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_213_);
v___x_215_ = v_reuseFailAlloc_220_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = l_Lean_MessageData_ofSyntax(v_before_206_);
v___x_217_ = l_Lean_indentD(v___x_216_);
v___x_218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_215_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v_x_199_ = v___x_218_;
v_x_200_ = v_tail_202_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6(lean_object* v_opts_225_, lean_object* v_opt_226_){
_start:
{
lean_object* v_name_227_; lean_object* v_defValue_228_; lean_object* v_map_229_; lean_object* v___x_230_; 
v_name_227_ = lean_ctor_get(v_opt_226_, 0);
v_defValue_228_ = lean_ctor_get(v_opt_226_, 1);
v_map_229_ = lean_ctor_get(v_opts_225_, 0);
v___x_230_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_229_, v_name_227_);
if (lean_obj_tag(v___x_230_) == 0)
{
uint8_t v___x_231_; 
v___x_231_ = lean_unbox(v_defValue_228_);
return v___x_231_;
}
else
{
lean_object* v_val_232_; 
v_val_232_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_val_232_);
lean_dec_ref_known(v___x_230_, 1);
if (lean_obj_tag(v_val_232_) == 1)
{
uint8_t v_v_233_; 
v_v_233_ = lean_ctor_get_uint8(v_val_232_, 0);
lean_dec_ref_known(v_val_232_, 0);
return v_v_233_;
}
else
{
uint8_t v___x_234_; 
lean_dec(v_val_232_);
v___x_234_ = lean_unbox(v_defValue_228_);
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6___boxed(lean_object* v_opts_235_, lean_object* v_opt_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6(v_opts_235_, v_opt_236_);
lean_dec_ref(v_opt_236_);
lean_dec_ref(v_opts_235_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__1));
v___x_243_ = l_Lean_MessageData_ofFormat(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg(lean_object* v_msgData_244_, lean_object* v_macroStack_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v_scopes_250_; lean_object* v___x_251_; lean_object* v_opts_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_248_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_249_ = lean_st_ref_get(v___y_246_);
v_scopes_250_ = lean_ctor_get(v___x_249_, 2);
lean_inc(v_scopes_250_);
lean_dec(v___x_249_);
v___x_251_ = l_List_head_x21___redArg(v___x_248_, v_scopes_250_);
lean_dec(v_scopes_250_);
v_opts_252_ = lean_ctor_get(v___x_251_, 1);
lean_inc_ref(v_opts_252_);
lean_dec(v___x_251_);
v___x_253_ = l_Lean_Elab_pp_macroStack;
v___x_254_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6(v_opts_252_, v___x_253_);
lean_dec_ref(v_opts_252_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec(v_macroStack_245_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v_msgData_244_);
return v___x_255_;
}
else
{
if (lean_obj_tag(v_macroStack_245_) == 0)
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v_msgData_244_);
return v___x_256_;
}
else
{
lean_object* v_head_257_; lean_object* v_after_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_273_; 
v_head_257_ = lean_ctor_get(v_macroStack_245_, 0);
lean_inc(v_head_257_);
v_after_258_ = lean_ctor_get(v_head_257_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_head_257_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v_head_257_, 0);
lean_dec(v_unused_274_);
v___x_260_ = v_head_257_;
v_isShared_261_ = v_isSharedCheck_273_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_after_258_);
lean_dec(v_head_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_273_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0);
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 7);
lean_ctor_set(v___x_260_, 1, v___x_262_);
lean_ctor_set(v___x_260_, 0, v_msgData_244_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_msgData_244_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v___x_262_);
v___x_264_ = v_reuseFailAlloc_272_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_msgData_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_265_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2);
v___x_266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = l_Lean_MessageData_ofSyntax(v_after_258_);
v___x_268_ = l_Lean_indentD(v___x_267_);
v_msgData_269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_269_, 0, v___x_266_);
lean_ctor_set(v_msgData_269_, 1, v___x_268_);
v___x_270_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7(v_msgData_269_, v_macroStack_245_);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___boxed(lean_object* v_msgData_275_, lean_object* v_macroStack_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg(v_msgData_275_, v_macroStack_276_, v___y_277_);
lean_dec(v___y_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(lean_object* v_msg_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Elab_Command_getRef___redArg(v___y_281_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v_macroStack_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_a_289_; lean_object* v___x_290_; lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_299_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
lean_dec_ref_known(v___x_284_, 1);
v_macroStack_286_ = lean_ctor_get(v___y_281_, 4);
v___x_287_ = l_Lean_Elab_getBetterRef(v_a_285_, v_macroStack_286_);
lean_dec(v_a_285_);
v___x_288_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(v_msg_280_, v___y_282_);
v_a_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_289_);
lean_dec_ref(v___x_288_);
lean_inc(v_macroStack_286_);
v___x_290_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg(v_a_289_, v_macroStack_286_, v___y_282_);
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_299_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_287_);
lean_ctor_set(v___x_295_, 1, v_a_291_);
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 1);
lean_ctor_set(v___x_293_, 0, v___x_295_);
v___x_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec_ref(v_msg_280_);
v_a_300_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_284_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_284_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg___boxed(lean_object* v_msg_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v_msg_308_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object* v_ref_313_, lean_object* v_msg_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Elab_Command_getRef___redArg(v___y_315_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v_fileName_320_; lean_object* v_fileMap_321_; lean_object* v_currRecDepth_322_; lean_object* v_cmdPos_323_; lean_object* v_macroStack_324_; lean_object* v_quotContext_x3f_325_; lean_object* v_currMacroScope_326_; lean_object* v_snap_x3f_327_; lean_object* v_cancelTk_x3f_328_; uint8_t v_suppressElabErrors_329_; uint8_t v_checkDeprecated_330_; lean_object* v_ref_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_318_, 1);
v_fileName_320_ = lean_ctor_get(v___y_315_, 0);
v_fileMap_321_ = lean_ctor_get(v___y_315_, 1);
v_currRecDepth_322_ = lean_ctor_get(v___y_315_, 2);
v_cmdPos_323_ = lean_ctor_get(v___y_315_, 3);
v_macroStack_324_ = lean_ctor_get(v___y_315_, 4);
v_quotContext_x3f_325_ = lean_ctor_get(v___y_315_, 5);
v_currMacroScope_326_ = lean_ctor_get(v___y_315_, 6);
v_snap_x3f_327_ = lean_ctor_get(v___y_315_, 8);
v_cancelTk_x3f_328_ = lean_ctor_get(v___y_315_, 9);
v_suppressElabErrors_329_ = lean_ctor_get_uint8(v___y_315_, sizeof(void*)*10);
v_checkDeprecated_330_ = lean_ctor_get_uint8(v___y_315_, sizeof(void*)*10 + 1);
v_ref_331_ = l_Lean_replaceRef(v_ref_313_, v_a_319_);
lean_dec(v_a_319_);
lean_inc(v_cancelTk_x3f_328_);
lean_inc(v_snap_x3f_327_);
lean_inc(v_currMacroScope_326_);
lean_inc(v_quotContext_x3f_325_);
lean_inc(v_macroStack_324_);
lean_inc(v_cmdPos_323_);
lean_inc(v_currRecDepth_322_);
lean_inc_ref(v_fileMap_321_);
lean_inc_ref(v_fileName_320_);
v___x_332_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_332_, 0, v_fileName_320_);
lean_ctor_set(v___x_332_, 1, v_fileMap_321_);
lean_ctor_set(v___x_332_, 2, v_currRecDepth_322_);
lean_ctor_set(v___x_332_, 3, v_cmdPos_323_);
lean_ctor_set(v___x_332_, 4, v_macroStack_324_);
lean_ctor_set(v___x_332_, 5, v_quotContext_x3f_325_);
lean_ctor_set(v___x_332_, 6, v_currMacroScope_326_);
lean_ctor_set(v___x_332_, 7, v_ref_331_);
lean_ctor_set(v___x_332_, 8, v_snap_x3f_327_);
lean_ctor_set(v___x_332_, 9, v_cancelTk_x3f_328_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*10, v_suppressElabErrors_329_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*10 + 1, v_checkDeprecated_330_);
v___x_333_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v_msg_314_, v___x_332_, v___y_316_);
lean_dec_ref_known(v___x_332_, 10);
return v___x_333_;
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec_ref(v_msg_314_);
v_a_334_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_318_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_318_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object* v_ref_342_, lean_object* v_msg_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_342_, v_msg_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v_ref_342_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object* v_k_349_, size_t v_sz_350_, size_t v_i_351_, lean_object* v_bs_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = lean_usize_dec_lt(v_i_351_, v_sz_350_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
lean_dec(v_k_349_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v_bs_352_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; lean_object* v_v_359_; lean_object* v___x_360_; lean_object* v_bs_x27_361_; lean_object* v___x_362_; 
v___x_358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0));
v_v_359_ = lean_array_uget(v_bs_352_, v_i_351_);
v___x_360_ = lean_unsigned_to_nat(0u);
v_bs_x27_361_ = lean_array_uset(v_bs_352_, v_i_351_, v___x_360_);
lean_inc(v_k_349_);
v___x_362_ = l_Lean_Elab_Command_checkRuleAltKind(v___x_358_, v_k_349_, v_v_359_, v___y_353_, v___y_354_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; size_t v___x_364_; size_t v___x_365_; lean_object* v___x_366_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
v___x_364_ = ((size_t)1ULL);
v___x_365_ = lean_usize_add(v_i_351_, v___x_364_);
v___x_366_ = lean_array_uset(v_bs_x27_361_, v_i_351_, v_a_363_);
v_i_351_ = v___x_365_;
v_bs_352_ = v___x_366_;
goto _start;
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref(v_bs_x27_361_);
lean_dec(v_k_349_);
v_a_368_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_362_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_362_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object* v_k_376_, lean_object* v_sz_377_, lean_object* v_i_378_, lean_object* v_bs_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
size_t v_sz_boxed_383_; size_t v_i_boxed_384_; lean_object* v_res_385_; 
v_sz_boxed_383_ = lean_unbox_usize(v_sz_377_);
lean_dec(v_sz_377_);
v_i_boxed_384_ = lean_unbox_usize(v_i_378_);
lean_dec(v_i_378_);
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(v_k_376_, v_sz_boxed_383_, v_i_boxed_384_, v_bs_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_385_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__4));
v___x_392_ = l_String_toRawSubstring_x27(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__8));
v___x_398_ = l_String_toRawSubstring_x27(v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__15));
v___x_406_ = l_String_toRawSubstring_x27(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_422_ = l_String_toRawSubstring_x27(v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36(void){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Array_mkArray0___redArg();
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__39(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__38));
v___x_438_ = l_String_toRawSubstring_x27(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__41));
v___x_442_ = l_String_toRawSubstring_x27(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__46(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__45));
v___x_448_ = l_String_toRawSubstring_x27(v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__49(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__48));
v___x_452_ = l_String_toRawSubstring_x27(v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__52(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__51));
v___x_456_ = l_String_toRawSubstring_x27(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__55(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_461_ = l_String_toRawSubstring_x27(v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__62(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__61));
v___x_471_ = l_Lean_stringToMessageData(v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__64(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__63));
v___x_474_ = l_Lean_stringToMessageData(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__75));
v___x_492_ = l_Lean_stringToMessageData(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__78(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__77));
v___x_495_ = l_Lean_stringToMessageData(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__82(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__81));
v___x_501_ = l_Lean_stringToMessageData(v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object* v_doc_x3f_502_, lean_object* v_attrs_x3f_503_, lean_object* v_attrKind_504_, lean_object* v_k_505_, lean_object* v_cat_x3f_506_, lean_object* v_expty_x3f_507_, lean_object* v_alts_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
size_t v_sz_512_; size_t v___x_513_; lean_object* v___x_514_; 
v_sz_512_ = lean_array_size(v_alts_508_);
v___x_513_ = ((size_t)0ULL);
lean_inc(v_k_505_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(v_k_505_, v_sz_512_, v___x_513_, v_alts_508_, v_a_509_, v_a_510_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_1531_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_1531_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_1531_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v_a_646_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v_a_798_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v_a_911_; uint8_t v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v_a_1082_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v_a_1196_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v_a_1329_; lean_object* v_catName_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; 
if (lean_obj_tag(v_cat_x3f_506_) == 1)
{
lean_object* v_val_1518_; lean_object* v___x_1519_; 
v_val_1518_ = lean_ctor_get(v_cat_x3f_506_, 0);
v___x_1519_ = l_Lean_TSyntax_getId(v_val_1518_);
v_catName_1340_ = v___x_1519_;
v___y_1341_ = v_a_509_;
v___y_1342_ = v_a_510_;
goto v___jp_1339_;
}
else
{
if (lean_obj_tag(v_expty_x3f_507_) == 1)
{
lean_object* v___x_1520_; 
v___x_1520_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__58));
v_catName_1340_ = v___x_1520_;
v___y_1341_ = v_a_509_;
v___y_1342_ = v_a_510_;
goto v___jp_1339_;
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_del_object(v___x_517_);
lean_dec(v_a_515_);
lean_dec(v_expty_x3f_507_);
lean_dec(v_k_505_);
lean_dec(v_attrKind_504_);
lean_dec(v_doc_x3f_502_);
v___x_1521_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__82, &l_Lean_Elab_Command_elabElabRulesAux___closed__82_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__82);
v___x_1522_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v___x_1521_, v_a_509_, v_a_510_);
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1522_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
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
v___jp_519_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
lean_inc_ref_n(v___y_523_, 4);
v___x_533_ = l_Array_append___redArg(v___y_523_, v___y_532_);
lean_dec_ref(v___y_532_);
lean_inc_n(v___y_531_, 10);
lean_inc_n(v___y_520_, 35);
v___x_534_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_534_, 0, v___y_520_);
lean_ctor_set(v___x_534_, 1, v___y_531_);
lean_ctor_set(v___x_534_, 2, v___x_533_);
v___x_535_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_536_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_537_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_525_, 11);
v___x_538_ = l_Lean_Name_mkStr4(v___y_525_, v___x_535_, v___x_536_, v___x_537_);
v___x_539_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_540_, 0, v___y_520_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_542_ = l_Lean_Syntax_SepArray_ofElems(v___x_541_, v___y_524_);
lean_dec_ref(v___y_524_);
v___x_543_ = l_Array_append___redArg(v___y_523_, v___x_542_);
lean_dec_ref(v___x_542_);
v___x_544_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_544_, 0, v___y_520_);
lean_ctor_set(v___x_544_, 1, v___y_531_);
lean_ctor_set(v___x_544_, 2, v___x_543_);
v___x_545_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_546_, 0, v___y_520_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = l_Lean_Syntax_node3(v___y_520_, v___x_538_, v___x_540_, v___x_544_, v___x_546_);
v___x_548_ = l_Lean_Syntax_node1(v___y_520_, v___y_531_, v___x_547_);
lean_inc_ref(v___y_521_);
v___x_549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_549_, 0, v___y_520_);
lean_ctor_set(v___x_549_, 1, v___y_521_);
v___x_550_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_551_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_526_, 3);
lean_inc_n(v___y_527_, 3);
v___x_552_ = l_Lean_addMacroScope(v___y_527_, v___x_551_, v___y_526_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_554_, 0, v___y_520_);
lean_ctor_set(v___x_554_, 1, v___x_550_);
lean_ctor_set(v___x_554_, 2, v___x_552_);
lean_ctor_set(v___x_554_, 3, v___x_553_);
v___x_555_ = l_Lean_mkIdent(v_k_505_);
v___x_556_ = l_Lean_Syntax_node2(v___y_520_, v___y_531_, v___x_554_, v___x_555_);
v___x_557_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_558_, 0, v___y_520_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_560_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
v___x_561_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc_ref_n(v___y_522_, 2);
v___x_562_ = l_Lean_Name_mkStr4(v___y_525_, v___y_522_, v___x_560_, v___x_561_);
lean_inc(v___x_562_);
v___x_563_ = l_Lean_addMacroScope(v___y_527_, v___x_562_, v___y_526_);
v___x_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_553_);
v___x_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v___x_553_);
v___x_566_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_566_, 0, v___y_520_);
lean_ctor_set(v___x_566_, 1, v___x_559_);
lean_ctor_set(v___x_566_, 2, v___x_563_);
lean_ctor_set(v___x_566_, 3, v___x_565_);
v___x_567_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_568_, 0, v___y_520_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_570_ = l_Lean_Name_mkStr4(v___y_525_, v___x_535_, v___x_536_, v___x_569_);
v___x_571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_571_, 0, v___y_520_);
lean_ctor_set(v___x_571_, 1, v___x_569_);
v___x_572_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_573_ = l_Lean_Name_mkStr4(v___y_525_, v___x_535_, v___x_536_, v___x_572_);
v___x_574_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_575_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_576_ = l_Lean_addMacroScope(v___y_527_, v___x_575_, v___y_526_);
v___x_577_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_577_, 0, v___y_520_);
lean_ctor_set(v___x_577_, 1, v___x_574_);
lean_ctor_set(v___x_577_, 2, v___x_576_);
lean_ctor_set(v___x_577_, 3, v___x_553_);
lean_inc_ref(v___x_577_);
v___x_578_ = l_Lean_Syntax_node2(v___y_520_, v___y_531_, v___x_577_, v___y_528_);
v___x_579_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_579_, 0, v___y_520_);
lean_ctor_set(v___x_579_, 1, v___y_531_);
lean_ctor_set(v___x_579_, 2, v___y_523_);
v___x_580_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_581_, 0, v___y_520_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_583_ = l_Lean_Name_mkStr4(v___y_525_, v___x_535_, v___x_536_, v___x_582_);
v___x_584_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_584_, 0, v___y_520_);
lean_ctor_set(v___x_584_, 1, v___x_582_);
v___x_585_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_586_ = l_Lean_Name_mkStr4(v___y_525_, v___x_535_, v___x_536_, v___x_585_);
lean_inc_ref_n(v___x_579_, 3);
v___x_587_ = l_Lean_Syntax_node2(v___y_520_, v___x_586_, v___x_579_, v___x_577_);
v___x_588_ = l_Lean_Syntax_node1(v___y_520_, v___y_531_, v___x_587_);
v___x_589_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_590_, 0, v___y_520_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_592_ = l_Lean_Name_mkStr4(v___y_525_, v___x_535_, v___x_536_, v___x_591_);
v___x_593_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_594_ = l_Lean_Name_mkStr4(v___y_525_, v___x_535_, v___x_536_, v___x_593_);
v___x_595_ = l_Array_append___redArg(v___y_523_, v_a_515_);
lean_dec(v_a_515_);
v___x_596_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_597_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_597_, 0, v___y_520_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_599_ = l_Lean_Name_mkStr4(v___y_525_, v___x_535_, v___x_536_, v___x_598_);
v___x_600_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_601_, 0, v___y_520_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Lean_Syntax_node1(v___y_520_, v___x_599_, v___x_601_);
v___x_603_ = l_Lean_Syntax_node1(v___y_520_, v___y_531_, v___x_602_);
v___x_604_ = l_Lean_Syntax_node1(v___y_520_, v___y_531_, v___x_603_);
v___x_605_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_606_ = l_Lean_Name_mkStr4(v___y_525_, v___x_535_, v___x_536_, v___x_605_);
v___x_607_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_608_, 0, v___y_520_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_610_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_611_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_612_ = l_Lean_addMacroScope(v___y_527_, v___x_611_, v___y_526_);
v___x_613_ = l_Lean_Name_mkStr3(v___y_525_, v___y_522_, v___x_609_);
v___x_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_553_);
v___x_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___x_553_);
v___x_616_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_616_, 0, v___y_520_);
lean_ctor_set(v___x_616_, 1, v___x_610_);
lean_ctor_set(v___x_616_, 2, v___x_612_);
lean_ctor_set(v___x_616_, 3, v___x_615_);
v___x_617_ = l_Lean_Syntax_node2(v___y_520_, v___x_606_, v___x_608_, v___x_616_);
lean_inc_ref(v___x_581_);
v___x_618_ = l_Lean_Syntax_node4(v___y_520_, v___x_594_, v___x_597_, v___x_604_, v___x_581_, v___x_617_);
v___x_619_ = lean_array_push(v___x_595_, v___x_618_);
v___x_620_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_620_, 0, v___y_520_);
lean_ctor_set(v___x_620_, 1, v___y_531_);
lean_ctor_set(v___x_620_, 2, v___x_619_);
v___x_621_ = l_Lean_Syntax_node1(v___y_520_, v___x_592_, v___x_620_);
v___x_622_ = l_Lean_Syntax_node6(v___y_520_, v___x_583_, v___x_584_, v___x_579_, v___x_579_, v___x_588_, v___x_590_, v___x_621_);
v___x_623_ = l_Lean_Syntax_node4(v___y_520_, v___x_573_, v___x_578_, v___x_579_, v___x_581_, v___x_622_);
v___x_624_ = l_Lean_Syntax_node2(v___y_520_, v___x_570_, v___x_571_, v___x_623_);
v___x_625_ = lean_unsigned_to_nat(9u);
v___x_626_ = lean_mk_empty_array_with_capacity(v___x_625_);
v___x_627_ = lean_array_push(v___x_626_, v___x_534_);
v___x_628_ = lean_array_push(v___x_627_, v___x_548_);
v___x_629_ = lean_array_push(v___x_628_, v___y_530_);
v___x_630_ = lean_array_push(v___x_629_, v___x_549_);
v___x_631_ = lean_array_push(v___x_630_, v___x_556_);
v___x_632_ = lean_array_push(v___x_631_, v___x_558_);
v___x_633_ = lean_array_push(v___x_632_, v___x_566_);
v___x_634_ = lean_array_push(v___x_633_, v___x_568_);
v___x_635_ = lean_array_push(v___x_634_, v___x_624_);
lean_inc(v___y_529_);
v___x_636_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_636_, 0, v___y_520_);
lean_ctor_set(v___x_636_, 1, v___y_529_);
lean_ctor_set(v___x_636_, 2, v___x_635_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_636_);
v___x_638_ = v___x_517_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
v___jp_640_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_647_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_648_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_649_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_650_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_651_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_652_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_502_) == 1)
{
lean_object* v_val_653_; lean_object* v___x_654_; 
v_val_653_ = lean_ctor_get(v_doc_x3f_502_, 0);
lean_inc(v_val_653_);
lean_dec_ref_known(v_doc_x3f_502_, 1);
v___x_654_ = l_Array_mkArray1___redArg(v_val_653_);
v___y_520_ = v___y_642_;
v___y_521_ = v___x_649_;
v___y_522_ = v___x_648_;
v___y_523_ = v___x_652_;
v___y_524_ = v___y_644_;
v___y_525_ = v___x_647_;
v___y_526_ = v___y_641_;
v___y_527_ = v_a_646_;
v___y_528_ = v___y_643_;
v___y_529_ = v___x_650_;
v___y_530_ = v___y_645_;
v___y_531_ = v___x_651_;
v___y_532_ = v___x_654_;
goto v___jp_519_;
}
else
{
lean_object* v___x_655_; 
lean_dec(v_doc_x3f_502_);
v___x_655_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_520_ = v___y_642_;
v___y_521_ = v___x_649_;
v___y_522_ = v___x_648_;
v___y_523_ = v___x_652_;
v___y_524_ = v___y_644_;
v___y_525_ = v___x_647_;
v___y_526_ = v___y_641_;
v___y_527_ = v_a_646_;
v___y_528_ = v___y_643_;
v___y_529_ = v___x_650_;
v___y_530_ = v___y_645_;
v___y_531_ = v___x_651_;
v___y_532_ = v___x_655_;
goto v___jp_519_;
}
}
v___jp_656_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
lean_inc_ref_n(v___y_657_, 4);
v___x_670_ = l_Array_append___redArg(v___y_657_, v___y_669_);
lean_dec_ref(v___y_669_);
lean_inc_n(v___y_662_, 12);
lean_inc_n(v___y_665_, 42);
v___x_671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_671_, 0, v___y_665_);
lean_ctor_set(v___x_671_, 1, v___y_662_);
lean_ctor_set(v___x_671_, 2, v___x_670_);
v___x_672_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_673_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_674_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_660_, 13);
v___x_675_ = l_Lean_Name_mkStr4(v___y_660_, v___x_672_, v___x_673_, v___x_674_);
v___x_676_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_677_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_677_, 0, v___y_665_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_679_ = l_Lean_Syntax_SepArray_ofElems(v___x_678_, v___y_666_);
lean_dec_ref(v___y_666_);
v___x_680_ = l_Array_append___redArg(v___y_657_, v___x_679_);
lean_dec_ref(v___x_679_);
v___x_681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_681_, 0, v___y_665_);
lean_ctor_set(v___x_681_, 1, v___y_662_);
lean_ctor_set(v___x_681_, 2, v___x_680_);
v___x_682_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_683_, 0, v___y_665_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = l_Lean_Syntax_node3(v___y_665_, v___x_675_, v___x_677_, v___x_681_, v___x_683_);
v___x_685_ = l_Lean_Syntax_node1(v___y_665_, v___y_662_, v___x_684_);
lean_inc_ref(v___y_658_);
v___x_686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_686_, 0, v___y_665_);
lean_ctor_set(v___x_686_, 1, v___y_658_);
v___x_687_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_688_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_661_, 5);
lean_inc_n(v___y_668_, 5);
v___x_689_ = l_Lean_addMacroScope(v___y_668_, v___x_688_, v___y_661_);
v___x_690_ = lean_box(0);
v___x_691_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_691_, 0, v___y_665_);
lean_ctor_set(v___x_691_, 1, v___x_687_);
lean_ctor_set(v___x_691_, 2, v___x_689_);
lean_ctor_set(v___x_691_, 3, v___x_690_);
v___x_692_ = l_Lean_mkIdent(v_k_505_);
v___x_693_ = l_Lean_Syntax_node2(v___y_665_, v___y_662_, v___x_691_, v___x_692_);
v___x_694_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_695_, 0, v___y_665_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__39, &l_Lean_Elab_Command_elabElabRulesAux___closed__39_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__39);
v___x_697_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
lean_inc_ref_n(v___y_659_, 3);
v___x_698_ = l_Lean_Name_mkStr4(v___y_660_, v___y_659_, v___x_673_, v___x_697_);
lean_inc(v___x_698_);
v___x_699_ = l_Lean_addMacroScope(v___y_668_, v___x_698_, v___y_661_);
v___x_700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_690_);
v___x_701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v___x_690_);
v___x_702_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_702_, 0, v___y_665_);
lean_ctor_set(v___x_702_, 1, v___x_696_);
lean_ctor_set(v___x_702_, 2, v___x_699_);
lean_ctor_set(v___x_702_, 3, v___x_701_);
v___x_703_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_704_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_704_, 0, v___y_665_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_706_ = l_Lean_Name_mkStr4(v___y_660_, v___x_672_, v___x_673_, v___x_705_);
v___x_707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_707_, 0, v___y_665_);
lean_ctor_set(v___x_707_, 1, v___x_705_);
v___x_708_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_709_ = l_Lean_Name_mkStr4(v___y_660_, v___x_672_, v___x_673_, v___x_708_);
v___x_710_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_711_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_712_ = l_Lean_addMacroScope(v___y_668_, v___x_711_, v___y_661_);
v___x_713_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_713_, 0, v___y_665_);
lean_ctor_set(v___x_713_, 1, v___x_710_);
lean_ctor_set(v___x_713_, 2, v___x_712_);
lean_ctor_set(v___x_713_, 3, v___x_690_);
v___x_714_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__42, &l_Lean_Elab_Command_elabElabRulesAux___closed__42_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42);
v___x_715_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__43));
v___x_716_ = l_Lean_addMacroScope(v___y_668_, v___x_715_, v___y_661_);
v___x_717_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_717_, 0, v___y_665_);
lean_ctor_set(v___x_717_, 1, v___x_714_);
lean_ctor_set(v___x_717_, 2, v___x_716_);
lean_ctor_set(v___x_717_, 3, v___x_690_);
lean_inc_ref(v___x_717_);
lean_inc_ref(v___x_713_);
v___x_718_ = l_Lean_Syntax_node2(v___y_665_, v___y_662_, v___x_713_, v___x_717_);
v___x_719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_719_, 0, v___y_665_);
lean_ctor_set(v___x_719_, 1, v___y_662_);
lean_ctor_set(v___x_719_, 2, v___y_657_);
v___x_720_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_721_, 0, v___y_665_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__44));
v___x_723_ = l_Lean_Name_mkStr4(v___y_660_, v___x_672_, v___x_673_, v___x_722_);
v___x_724_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__46, &l_Lean_Elab_Command_elabElabRulesAux___closed__46_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__46);
v___x_725_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__47));
v___x_726_ = l_Lean_Name_mkStr4(v___y_660_, v___y_659_, v___x_673_, v___x_725_);
lean_inc(v___x_726_);
v___x_727_ = l_Lean_addMacroScope(v___y_668_, v___x_726_, v___y_661_);
v___x_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_726_);
lean_ctor_set(v___x_728_, 1, v___x_690_);
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v___x_690_);
v___x_730_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_730_, 0, v___y_665_);
lean_ctor_set(v___x_730_, 1, v___x_724_);
lean_ctor_set(v___x_730_, 2, v___x_727_);
lean_ctor_set(v___x_730_, 3, v___x_729_);
v___x_731_ = l_Lean_Syntax_node1(v___y_665_, v___y_662_, v___y_663_);
v___x_732_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_733_ = l_Lean_Name_mkStr4(v___y_660_, v___x_672_, v___x_673_, v___x_732_);
v___x_734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_734_, 0, v___y_665_);
lean_ctor_set(v___x_734_, 1, v___x_732_);
v___x_735_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_736_ = l_Lean_Name_mkStr4(v___y_660_, v___x_672_, v___x_673_, v___x_735_);
lean_inc_ref_n(v___x_719_, 4);
v___x_737_ = l_Lean_Syntax_node2(v___y_665_, v___x_736_, v___x_719_, v___x_713_);
v___x_738_ = l_Lean_Syntax_node1(v___y_665_, v___y_662_, v___x_737_);
v___x_739_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_740_, 0, v___y_665_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_742_ = l_Lean_Name_mkStr4(v___y_660_, v___x_672_, v___x_673_, v___x_741_);
v___x_743_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_744_ = l_Lean_Name_mkStr4(v___y_660_, v___x_672_, v___x_673_, v___x_743_);
v___x_745_ = l_Array_append___redArg(v___y_657_, v_a_515_);
lean_dec(v_a_515_);
v___x_746_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_747_, 0, v___y_665_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_749_ = l_Lean_Name_mkStr4(v___y_660_, v___x_672_, v___x_673_, v___x_748_);
v___x_750_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_751_, 0, v___y_665_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = l_Lean_Syntax_node1(v___y_665_, v___x_749_, v___x_751_);
v___x_753_ = l_Lean_Syntax_node1(v___y_665_, v___y_662_, v___x_752_);
v___x_754_ = l_Lean_Syntax_node1(v___y_665_, v___y_662_, v___x_753_);
v___x_755_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_756_ = l_Lean_Name_mkStr4(v___y_660_, v___x_672_, v___x_673_, v___x_755_);
v___x_757_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_758_, 0, v___y_665_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_760_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_761_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_762_ = l_Lean_addMacroScope(v___y_668_, v___x_761_, v___y_661_);
v___x_763_ = l_Lean_Name_mkStr3(v___y_660_, v___y_659_, v___x_759_);
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v___x_690_);
v___x_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_690_);
v___x_766_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_766_, 0, v___y_665_);
lean_ctor_set(v___x_766_, 1, v___x_760_);
lean_ctor_set(v___x_766_, 2, v___x_762_);
lean_ctor_set(v___x_766_, 3, v___x_765_);
v___x_767_ = l_Lean_Syntax_node2(v___y_665_, v___x_756_, v___x_758_, v___x_766_);
lean_inc_ref_n(v___x_721_, 2);
v___x_768_ = l_Lean_Syntax_node4(v___y_665_, v___x_744_, v___x_747_, v___x_754_, v___x_721_, v___x_767_);
v___x_769_ = lean_array_push(v___x_745_, v___x_768_);
v___x_770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_770_, 0, v___y_665_);
lean_ctor_set(v___x_770_, 1, v___y_662_);
lean_ctor_set(v___x_770_, 2, v___x_769_);
v___x_771_ = l_Lean_Syntax_node1(v___y_665_, v___x_742_, v___x_770_);
v___x_772_ = l_Lean_Syntax_node6(v___y_665_, v___x_733_, v___x_734_, v___x_719_, v___x_719_, v___x_738_, v___x_740_, v___x_771_);
lean_inc(v___x_709_);
v___x_773_ = l_Lean_Syntax_node4(v___y_665_, v___x_709_, v___x_731_, v___x_719_, v___x_721_, v___x_772_);
lean_inc_ref(v___x_707_);
lean_inc(v___x_706_);
v___x_774_ = l_Lean_Syntax_node2(v___y_665_, v___x_706_, v___x_707_, v___x_773_);
v___x_775_ = l_Lean_Syntax_node2(v___y_665_, v___y_662_, v___x_717_, v___x_774_);
v___x_776_ = l_Lean_Syntax_node2(v___y_665_, v___x_723_, v___x_730_, v___x_775_);
v___x_777_ = l_Lean_Syntax_node4(v___y_665_, v___x_709_, v___x_718_, v___x_719_, v___x_721_, v___x_776_);
v___x_778_ = l_Lean_Syntax_node2(v___y_665_, v___x_706_, v___x_707_, v___x_777_);
v___x_779_ = lean_unsigned_to_nat(9u);
v___x_780_ = lean_mk_empty_array_with_capacity(v___x_779_);
v___x_781_ = lean_array_push(v___x_780_, v___x_671_);
v___x_782_ = lean_array_push(v___x_781_, v___x_685_);
v___x_783_ = lean_array_push(v___x_782_, v___y_667_);
v___x_784_ = lean_array_push(v___x_783_, v___x_686_);
v___x_785_ = lean_array_push(v___x_784_, v___x_693_);
v___x_786_ = lean_array_push(v___x_785_, v___x_695_);
v___x_787_ = lean_array_push(v___x_786_, v___x_702_);
v___x_788_ = lean_array_push(v___x_787_, v___x_704_);
v___x_789_ = lean_array_push(v___x_788_, v___x_778_);
lean_inc(v___y_664_);
v___x_790_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_790_, 0, v___y_665_);
lean_ctor_set(v___x_790_, 1, v___y_664_);
lean_ctor_set(v___x_790_, 2, v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
v___jp_792_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_799_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_800_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_801_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_802_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_803_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_804_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_502_) == 1)
{
lean_object* v_val_805_; lean_object* v___x_806_; 
v_val_805_ = lean_ctor_get(v_doc_x3f_502_, 0);
lean_inc(v_val_805_);
lean_dec_ref_known(v_doc_x3f_502_, 1);
v___x_806_ = l_Array_mkArray1___redArg(v_val_805_);
v___y_657_ = v___x_804_;
v___y_658_ = v___x_801_;
v___y_659_ = v___x_800_;
v___y_660_ = v___x_799_;
v___y_661_ = v___y_796_;
v___y_662_ = v___x_803_;
v___y_663_ = v___y_793_;
v___y_664_ = v___x_802_;
v___y_665_ = v___y_795_;
v___y_666_ = v___y_794_;
v___y_667_ = v___y_797_;
v___y_668_ = v_a_798_;
v___y_669_ = v___x_806_;
goto v___jp_656_;
}
else
{
lean_object* v___x_807_; 
lean_dec(v_doc_x3f_502_);
v___x_807_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_657_ = v___x_804_;
v___y_658_ = v___x_801_;
v___y_659_ = v___x_800_;
v___y_660_ = v___x_799_;
v___y_661_ = v___y_796_;
v___y_662_ = v___x_803_;
v___y_663_ = v___y_793_;
v___y_664_ = v___x_802_;
v___y_665_ = v___y_795_;
v___y_666_ = v___y_794_;
v___y_667_ = v___y_797_;
v___y_668_ = v_a_798_;
v___y_669_ = v___x_807_;
goto v___jp_656_;
}
}
v___jp_808_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
lean_inc_ref_n(v___y_814_, 3);
v___x_821_ = l_Array_append___redArg(v___y_814_, v___y_820_);
lean_dec_ref(v___y_820_);
lean_inc_n(v___y_819_, 7);
lean_inc_n(v___y_816_, 26);
v___x_822_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_822_, 0, v___y_816_);
lean_ctor_set(v___x_822_, 1, v___y_819_);
lean_ctor_set(v___x_822_, 2, v___x_821_);
v___x_823_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_824_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_825_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_811_, 8);
v___x_826_ = l_Lean_Name_mkStr4(v___y_811_, v___x_823_, v___x_824_, v___x_825_);
v___x_827_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_828_, 0, v___y_816_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_830_ = l_Lean_Syntax_SepArray_ofElems(v___x_829_, v___y_813_);
lean_dec_ref(v___y_813_);
v___x_831_ = l_Array_append___redArg(v___y_814_, v___x_830_);
lean_dec_ref(v___x_830_);
v___x_832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_832_, 0, v___y_816_);
lean_ctor_set(v___x_832_, 1, v___y_819_);
lean_ctor_set(v___x_832_, 2, v___x_831_);
v___x_833_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_834_, 0, v___y_816_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = l_Lean_Syntax_node3(v___y_816_, v___x_826_, v___x_828_, v___x_832_, v___x_834_);
v___x_836_ = l_Lean_Syntax_node1(v___y_816_, v___y_819_, v___x_835_);
lean_inc_ref(v___y_818_);
v___x_837_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_837_, 0, v___y_816_);
lean_ctor_set(v___x_837_, 1, v___y_818_);
v___x_838_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_839_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_810_, 2);
lean_inc_n(v___y_817_, 2);
v___x_840_ = l_Lean_addMacroScope(v___y_817_, v___x_839_, v___y_810_);
v___x_841_ = lean_box(0);
v___x_842_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_842_, 0, v___y_816_);
lean_ctor_set(v___x_842_, 1, v___x_838_);
lean_ctor_set(v___x_842_, 2, v___x_840_);
lean_ctor_set(v___x_842_, 3, v___x_841_);
v___x_843_ = l_Lean_mkIdent(v_k_505_);
v___x_844_ = l_Lean_Syntax_node2(v___y_816_, v___y_819_, v___x_842_, v___x_843_);
v___x_845_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_846_, 0, v___y_816_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__49, &l_Lean_Elab_Command_elabElabRulesAux___closed__49_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__49);
v___x_848_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__50));
lean_inc_ref_n(v___y_809_, 2);
v___x_849_ = l_Lean_Name_mkStr4(v___y_811_, v___y_809_, v___x_848_, v___x_848_);
lean_inc(v___x_849_);
v___x_850_ = l_Lean_addMacroScope(v___y_817_, v___x_849_, v___y_810_);
v___x_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_841_);
v___x_852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
lean_ctor_set(v___x_852_, 1, v___x_841_);
v___x_853_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_853_, 0, v___y_816_);
lean_ctor_set(v___x_853_, 1, v___x_847_);
lean_ctor_set(v___x_853_, 2, v___x_850_);
lean_ctor_set(v___x_853_, 3, v___x_852_);
v___x_854_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_855_, 0, v___y_816_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_857_ = l_Lean_Name_mkStr4(v___y_811_, v___x_823_, v___x_824_, v___x_856_);
v___x_858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_858_, 0, v___y_816_);
lean_ctor_set(v___x_858_, 1, v___x_856_);
v___x_859_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_860_ = l_Lean_Name_mkStr4(v___y_811_, v___x_823_, v___x_824_, v___x_859_);
v___x_861_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_862_ = l_Lean_Name_mkStr4(v___y_811_, v___x_823_, v___x_824_, v___x_861_);
v___x_863_ = l_Array_append___redArg(v___y_814_, v_a_515_);
lean_dec(v_a_515_);
v___x_864_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_865_, 0, v___y_816_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_867_ = l_Lean_Name_mkStr4(v___y_811_, v___x_823_, v___x_824_, v___x_866_);
v___x_868_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_869_, 0, v___y_816_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = l_Lean_Syntax_node1(v___y_816_, v___x_867_, v___x_869_);
v___x_871_ = l_Lean_Syntax_node1(v___y_816_, v___y_819_, v___x_870_);
v___x_872_ = l_Lean_Syntax_node1(v___y_816_, v___y_819_, v___x_871_);
v___x_873_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_874_, 0, v___y_816_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_876_ = l_Lean_Name_mkStr4(v___y_811_, v___x_823_, v___x_824_, v___x_875_);
v___x_877_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_878_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_878_, 0, v___y_816_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_880_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_881_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_882_ = l_Lean_addMacroScope(v___y_817_, v___x_881_, v___y_810_);
v___x_883_ = l_Lean_Name_mkStr3(v___y_811_, v___y_809_, v___x_879_);
v___x_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_841_);
v___x_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_841_);
v___x_886_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_886_, 0, v___y_816_);
lean_ctor_set(v___x_886_, 1, v___x_880_);
lean_ctor_set(v___x_886_, 2, v___x_882_);
lean_ctor_set(v___x_886_, 3, v___x_885_);
v___x_887_ = l_Lean_Syntax_node2(v___y_816_, v___x_876_, v___x_878_, v___x_886_);
v___x_888_ = l_Lean_Syntax_node4(v___y_816_, v___x_862_, v___x_865_, v___x_872_, v___x_874_, v___x_887_);
v___x_889_ = lean_array_push(v___x_863_, v___x_888_);
v___x_890_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_890_, 0, v___y_816_);
lean_ctor_set(v___x_890_, 1, v___y_819_);
lean_ctor_set(v___x_890_, 2, v___x_889_);
v___x_891_ = l_Lean_Syntax_node1(v___y_816_, v___x_860_, v___x_890_);
v___x_892_ = l_Lean_Syntax_node2(v___y_816_, v___x_857_, v___x_858_, v___x_891_);
v___x_893_ = lean_unsigned_to_nat(9u);
v___x_894_ = lean_mk_empty_array_with_capacity(v___x_893_);
v___x_895_ = lean_array_push(v___x_894_, v___x_822_);
v___x_896_ = lean_array_push(v___x_895_, v___x_836_);
v___x_897_ = lean_array_push(v___x_896_, v___y_815_);
v___x_898_ = lean_array_push(v___x_897_, v___x_837_);
v___x_899_ = lean_array_push(v___x_898_, v___x_844_);
v___x_900_ = lean_array_push(v___x_899_, v___x_846_);
v___x_901_ = lean_array_push(v___x_900_, v___x_853_);
v___x_902_ = lean_array_push(v___x_901_, v___x_855_);
v___x_903_ = lean_array_push(v___x_902_, v___x_892_);
lean_inc(v___y_812_);
v___x_904_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_904_, 0, v___y_816_);
lean_ctor_set(v___x_904_, 1, v___y_812_);
lean_ctor_set(v___x_904_, 2, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
v___jp_906_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_912_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_913_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_914_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_915_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_916_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_917_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_502_) == 1)
{
lean_object* v_val_918_; lean_object* v___x_919_; 
v_val_918_ = lean_ctor_get(v_doc_x3f_502_, 0);
lean_inc(v_val_918_);
lean_dec_ref_known(v_doc_x3f_502_, 1);
v___x_919_ = l_Array_mkArray1___redArg(v_val_918_);
v___y_809_ = v___x_913_;
v___y_810_ = v___y_907_;
v___y_811_ = v___x_912_;
v___y_812_ = v___x_915_;
v___y_813_ = v___y_908_;
v___y_814_ = v___x_917_;
v___y_815_ = v___y_910_;
v___y_816_ = v___y_909_;
v___y_817_ = v_a_911_;
v___y_818_ = v___x_914_;
v___y_819_ = v___x_916_;
v___y_820_ = v___x_919_;
goto v___jp_808_;
}
else
{
lean_object* v___x_920_; 
lean_dec(v_doc_x3f_502_);
v___x_920_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_809_ = v___x_913_;
v___y_810_ = v___y_907_;
v___y_811_ = v___x_912_;
v___y_812_ = v___x_915_;
v___y_813_ = v___y_908_;
v___y_814_ = v___x_917_;
v___y_815_ = v___y_910_;
v___y_816_ = v___y_909_;
v___y_817_ = v_a_911_;
v___y_818_ = v___x_914_;
v___y_819_ = v___x_916_;
v___y_820_ = v___x_920_;
goto v___jp_808_;
}
}
v___jp_921_:
{
lean_object* v___x_927_; 
lean_inc(v___y_923_);
lean_inc(v_k_505_);
v___x_927_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_505_, v_attrKind_504_, v_attrs_x3f_503_, v___y_923_, v___y_925_, v___y_924_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_929_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_927_, 1);
v___x_929_ = l_Lean_Elab_Command_getRef___redArg(v___y_925_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_929_, 1);
v___x_931_ = l_Lean_SourceInfo_fromRef(v_a_930_, v___y_922_);
lean_dec(v_a_930_);
v___x_932_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_925_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_quotContext_x3f_933_; 
v_quotContext_x3f_933_ = lean_ctor_get(v___y_925_, 5);
if (lean_obj_tag(v_quotContext_x3f_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_935_; lean_object* v_a_936_; 
v_a_934_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_932_, 1);
v___x_935_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_924_);
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref(v___x_935_);
v___y_907_ = v_a_934_;
v___y_908_ = v_a_928_;
v___y_909_ = v___x_931_;
v___y_910_ = v___y_926_;
v_a_911_ = v_a_936_;
goto v___jp_906_;
}
else
{
lean_object* v_a_937_; lean_object* v_val_938_; 
v_a_937_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_932_, 1);
v_val_938_ = lean_ctor_get(v_quotContext_x3f_933_, 0);
lean_inc(v_val_938_);
v___y_907_ = v_a_937_;
v___y_908_ = v_a_928_;
v___y_909_ = v___x_931_;
v___y_910_ = v___y_926_;
v_a_911_ = v_val_938_;
goto v___jp_906_;
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec(v___x_931_);
lean_dec(v_a_928_);
lean_dec(v___y_926_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
v_a_939_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_932_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_932_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
else
{
lean_dec(v_a_928_);
lean_dec(v___y_926_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
return v___x_929_;
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec(v___y_926_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
v_a_947_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_927_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_927_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
v___jp_955_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_inc_ref_n(v___y_960_, 4);
v___x_968_ = l_Array_append___redArg(v___y_960_, v___y_967_);
lean_dec_ref(v___y_967_);
lean_inc_n(v___y_959_, 10);
lean_inc_n(v___y_965_, 36);
v___x_969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_969_, 0, v___y_965_);
lean_ctor_set(v___x_969_, 1, v___y_959_);
lean_ctor_set(v___x_969_, 2, v___x_968_);
v___x_970_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_971_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_972_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_963_, 11);
v___x_973_ = l_Lean_Name_mkStr4(v___y_963_, v___x_970_, v___x_971_, v___x_972_);
v___x_974_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_975_, 0, v___y_965_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_977_ = l_Lean_Syntax_SepArray_ofElems(v___x_976_, v___y_966_);
lean_dec_ref(v___y_966_);
v___x_978_ = l_Array_append___redArg(v___y_960_, v___x_977_);
lean_dec_ref(v___x_977_);
v___x_979_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_979_, 0, v___y_965_);
lean_ctor_set(v___x_979_, 1, v___y_959_);
lean_ctor_set(v___x_979_, 2, v___x_978_);
v___x_980_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_981_, 0, v___y_965_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = l_Lean_Syntax_node3(v___y_965_, v___x_973_, v___x_975_, v___x_979_, v___x_981_);
v___x_983_ = l_Lean_Syntax_node1(v___y_965_, v___y_959_, v___x_982_);
lean_inc_ref(v___y_962_);
v___x_984_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_984_, 0, v___y_965_);
lean_ctor_set(v___x_984_, 1, v___y_962_);
v___x_985_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_986_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_957_, 4);
lean_inc_n(v___y_958_, 4);
v___x_987_ = l_Lean_addMacroScope(v___y_958_, v___x_986_, v___y_957_);
v___x_988_ = lean_box(0);
v___x_989_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_989_, 0, v___y_965_);
lean_ctor_set(v___x_989_, 1, v___x_985_);
lean_ctor_set(v___x_989_, 2, v___x_987_);
lean_ctor_set(v___x_989_, 3, v___x_988_);
v___x_990_ = l_Lean_mkIdent(v_k_505_);
v___x_991_ = l_Lean_Syntax_node2(v___y_965_, v___y_959_, v___x_989_, v___x_990_);
v___x_992_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_993_, 0, v___y_965_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_995_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
v___x_996_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc_ref_n(v___y_956_, 2);
v___x_997_ = l_Lean_Name_mkStr4(v___y_963_, v___y_956_, v___x_995_, v___x_996_);
lean_inc(v___x_997_);
v___x_998_ = l_Lean_addMacroScope(v___y_958_, v___x_997_, v___y_957_);
v___x_999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_988_);
v___x_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_988_);
v___x_1001_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1001_, 0, v___y_965_);
lean_ctor_set(v___x_1001_, 1, v___x_994_);
lean_ctor_set(v___x_1001_, 2, v___x_998_);
lean_ctor_set(v___x_1001_, 3, v___x_1000_);
v___x_1002_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___y_965_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1005_ = l_Lean_Name_mkStr4(v___y_963_, v___x_970_, v___x_971_, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___y_965_);
lean_ctor_set(v___x_1006_, 1, v___x_1004_);
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_1008_ = l_Lean_Name_mkStr4(v___y_963_, v___x_970_, v___x_971_, v___x_1007_);
v___x_1009_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_1010_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1011_ = l_Lean_addMacroScope(v___y_958_, v___x_1010_, v___y_957_);
v___x_1012_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1012_, 0, v___y_965_);
lean_ctor_set(v___x_1012_, 1, v___x_1009_);
lean_ctor_set(v___x_1012_, 2, v___x_1011_);
lean_ctor_set(v___x_1012_, 3, v___x_988_);
v___x_1013_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__52, &l_Lean_Elab_Command_elabElabRulesAux___closed__52_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__52);
v___x_1014_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__53));
v___x_1015_ = l_Lean_addMacroScope(v___y_958_, v___x_1014_, v___y_957_);
v___x_1016_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1016_, 0, v___y_965_);
lean_ctor_set(v___x_1016_, 1, v___x_1013_);
lean_ctor_set(v___x_1016_, 2, v___x_1015_);
lean_ctor_set(v___x_1016_, 3, v___x_988_);
lean_inc_ref(v___x_1012_);
v___x_1017_ = l_Lean_Syntax_node2(v___y_965_, v___y_959_, v___x_1012_, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1018_, 0, v___y_965_);
lean_ctor_set(v___x_1018_, 1, v___y_959_);
lean_ctor_set(v___x_1018_, 2, v___y_960_);
v___x_1019_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___y_965_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1022_ = l_Lean_Name_mkStr4(v___y_963_, v___x_970_, v___x_971_, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___y_965_);
lean_ctor_set(v___x_1023_, 1, v___x_1021_);
v___x_1024_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1025_ = l_Lean_Name_mkStr4(v___y_963_, v___x_970_, v___x_971_, v___x_1024_);
lean_inc_ref_n(v___x_1018_, 3);
v___x_1026_ = l_Lean_Syntax_node2(v___y_965_, v___x_1025_, v___x_1018_, v___x_1012_);
v___x_1027_ = l_Lean_Syntax_node1(v___y_965_, v___y_959_, v___x_1026_);
v___x_1028_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___y_965_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1031_ = l_Lean_Name_mkStr4(v___y_963_, v___x_970_, v___x_971_, v___x_1030_);
v___x_1032_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1033_ = l_Lean_Name_mkStr4(v___y_963_, v___x_970_, v___x_971_, v___x_1032_);
v___x_1034_ = l_Array_append___redArg(v___y_960_, v_a_515_);
lean_dec(v_a_515_);
v___x_1035_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1036_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___y_965_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1038_ = l_Lean_Name_mkStr4(v___y_963_, v___x_970_, v___x_971_, v___x_1037_);
v___x_1039_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___y_965_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_Syntax_node1(v___y_965_, v___x_1038_, v___x_1040_);
v___x_1042_ = l_Lean_Syntax_node1(v___y_965_, v___y_959_, v___x_1041_);
v___x_1043_ = l_Lean_Syntax_node1(v___y_965_, v___y_959_, v___x_1042_);
v___x_1044_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1045_ = l_Lean_Name_mkStr4(v___y_963_, v___x_970_, v___x_971_, v___x_1044_);
v___x_1046_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___y_965_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1049_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_1050_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1051_ = l_Lean_addMacroScope(v___y_958_, v___x_1050_, v___y_957_);
v___x_1052_ = l_Lean_Name_mkStr3(v___y_963_, v___y_956_, v___x_1048_);
v___x_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v___x_988_);
v___x_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___x_988_);
v___x_1055_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1055_, 0, v___y_965_);
lean_ctor_set(v___x_1055_, 1, v___x_1049_);
lean_ctor_set(v___x_1055_, 2, v___x_1051_);
lean_ctor_set(v___x_1055_, 3, v___x_1054_);
v___x_1056_ = l_Lean_Syntax_node2(v___y_965_, v___x_1045_, v___x_1047_, v___x_1055_);
lean_inc_ref(v___x_1020_);
v___x_1057_ = l_Lean_Syntax_node4(v___y_965_, v___x_1033_, v___x_1036_, v___x_1043_, v___x_1020_, v___x_1056_);
v___x_1058_ = lean_array_push(v___x_1034_, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1059_, 0, v___y_965_);
lean_ctor_set(v___x_1059_, 1, v___y_959_);
lean_ctor_set(v___x_1059_, 2, v___x_1058_);
v___x_1060_ = l_Lean_Syntax_node1(v___y_965_, v___x_1031_, v___x_1059_);
v___x_1061_ = l_Lean_Syntax_node6(v___y_965_, v___x_1022_, v___x_1023_, v___x_1018_, v___x_1018_, v___x_1027_, v___x_1029_, v___x_1060_);
v___x_1062_ = l_Lean_Syntax_node4(v___y_965_, v___x_1008_, v___x_1017_, v___x_1018_, v___x_1020_, v___x_1061_);
v___x_1063_ = l_Lean_Syntax_node2(v___y_965_, v___x_1005_, v___x_1006_, v___x_1062_);
v___x_1064_ = lean_unsigned_to_nat(9u);
v___x_1065_ = lean_mk_empty_array_with_capacity(v___x_1064_);
v___x_1066_ = lean_array_push(v___x_1065_, v___x_969_);
v___x_1067_ = lean_array_push(v___x_1066_, v___x_983_);
v___x_1068_ = lean_array_push(v___x_1067_, v___y_964_);
v___x_1069_ = lean_array_push(v___x_1068_, v___x_984_);
v___x_1070_ = lean_array_push(v___x_1069_, v___x_991_);
v___x_1071_ = lean_array_push(v___x_1070_, v___x_993_);
v___x_1072_ = lean_array_push(v___x_1071_, v___x_1001_);
v___x_1073_ = lean_array_push(v___x_1072_, v___x_1003_);
v___x_1074_ = lean_array_push(v___x_1073_, v___x_1063_);
lean_inc(v___y_961_);
v___x_1075_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1075_, 0, v___y_965_);
lean_ctor_set(v___x_1075_, 1, v___y_961_);
lean_ctor_set(v___x_1075_, 2, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
v___jp_1077_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1083_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1084_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1085_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_1086_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_1087_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1088_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_502_) == 1)
{
lean_object* v_val_1089_; lean_object* v___x_1090_; 
v_val_1089_ = lean_ctor_get(v_doc_x3f_502_, 0);
lean_inc(v_val_1089_);
lean_dec_ref_known(v_doc_x3f_502_, 1);
v___x_1090_ = l_Array_mkArray1___redArg(v_val_1089_);
v___y_956_ = v___x_1084_;
v___y_957_ = v___y_1078_;
v___y_958_ = v_a_1082_;
v___y_959_ = v___x_1087_;
v___y_960_ = v___x_1088_;
v___y_961_ = v___x_1086_;
v___y_962_ = v___x_1085_;
v___y_963_ = v___x_1083_;
v___y_964_ = v___y_1079_;
v___y_965_ = v___y_1080_;
v___y_966_ = v___y_1081_;
v___y_967_ = v___x_1090_;
goto v___jp_955_;
}
else
{
lean_object* v___x_1091_; 
lean_dec(v_doc_x3f_502_);
v___x_1091_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_956_ = v___x_1084_;
v___y_957_ = v___y_1078_;
v___y_958_ = v_a_1082_;
v___y_959_ = v___x_1087_;
v___y_960_ = v___x_1088_;
v___y_961_ = v___x_1086_;
v___y_962_ = v___x_1085_;
v___y_963_ = v___x_1083_;
v___y_964_ = v___y_1079_;
v___y_965_ = v___y_1080_;
v___y_966_ = v___y_1081_;
v___y_967_ = v___x_1091_;
goto v___jp_955_;
}
}
v___jp_1092_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_inc_ref_n(v___y_1104_, 3);
v___x_1106_ = l_Array_append___redArg(v___y_1104_, v___y_1105_);
lean_dec_ref(v___y_1105_);
lean_inc_n(v___y_1096_, 7);
lean_inc_n(v___y_1093_, 26);
v___x_1107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1107_, 0, v___y_1093_);
lean_ctor_set(v___x_1107_, 1, v___y_1096_);
lean_ctor_set(v___x_1107_, 2, v___x_1106_);
v___x_1108_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1109_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1110_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1100_, 8);
v___x_1111_ = l_Lean_Name_mkStr4(v___y_1100_, v___x_1108_, v___x_1109_, v___x_1110_);
v___x_1112_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___y_1093_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1115_ = l_Lean_Syntax_SepArray_ofElems(v___x_1114_, v___y_1095_);
lean_dec_ref(v___y_1095_);
v___x_1116_ = l_Array_append___redArg(v___y_1104_, v___x_1115_);
lean_dec_ref(v___x_1115_);
v___x_1117_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1117_, 0, v___y_1093_);
lean_ctor_set(v___x_1117_, 1, v___y_1096_);
lean_ctor_set(v___x_1117_, 2, v___x_1116_);
v___x_1118_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___y_1093_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = l_Lean_Syntax_node3(v___y_1093_, v___x_1111_, v___x_1113_, v___x_1117_, v___x_1119_);
v___x_1121_ = l_Lean_Syntax_node1(v___y_1093_, v___y_1096_, v___x_1120_);
lean_inc_ref(v___y_1097_);
v___x_1122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___y_1093_);
lean_ctor_set(v___x_1122_, 1, v___y_1097_);
v___x_1123_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1124_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1094_, 2);
lean_inc_n(v___y_1098_, 2);
v___x_1125_ = l_Lean_addMacroScope(v___y_1098_, v___x_1124_, v___y_1094_);
v___x_1126_ = lean_box(0);
v___x_1127_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1127_, 0, v___y_1093_);
lean_ctor_set(v___x_1127_, 1, v___x_1123_);
lean_ctor_set(v___x_1127_, 2, v___x_1125_);
lean_ctor_set(v___x_1127_, 3, v___x_1126_);
v___x_1128_ = l_Lean_mkIdent(v_k_505_);
v___x_1129_ = l_Lean_Syntax_node2(v___y_1093_, v___y_1096_, v___x_1127_, v___x_1128_);
v___x_1130_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___y_1093_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__55, &l_Lean_Elab_Command_elabElabRulesAux___closed__55_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__55);
v___x_1133_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
lean_inc_ref(v___y_1101_);
lean_inc_ref_n(v___y_1099_, 2);
v___x_1134_ = l_Lean_Name_mkStr4(v___y_1100_, v___y_1099_, v___y_1101_, v___x_1133_);
lean_inc(v___x_1134_);
v___x_1135_ = l_Lean_addMacroScope(v___y_1098_, v___x_1134_, v___y_1094_);
v___x_1136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1126_);
v___x_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v___x_1126_);
v___x_1138_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1138_, 0, v___y_1093_);
lean_ctor_set(v___x_1138_, 1, v___x_1132_);
lean_ctor_set(v___x_1138_, 2, v___x_1135_);
lean_ctor_set(v___x_1138_, 3, v___x_1137_);
v___x_1139_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___y_1093_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1142_ = l_Lean_Name_mkStr4(v___y_1100_, v___x_1108_, v___x_1109_, v___x_1141_);
v___x_1143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___y_1093_);
lean_ctor_set(v___x_1143_, 1, v___x_1141_);
v___x_1144_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1145_ = l_Lean_Name_mkStr4(v___y_1100_, v___x_1108_, v___x_1109_, v___x_1144_);
v___x_1146_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1147_ = l_Lean_Name_mkStr4(v___y_1100_, v___x_1108_, v___x_1109_, v___x_1146_);
v___x_1148_ = l_Array_append___redArg(v___y_1104_, v_a_515_);
lean_dec(v_a_515_);
v___x_1149_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___y_1093_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1152_ = l_Lean_Name_mkStr4(v___y_1100_, v___x_1108_, v___x_1109_, v___x_1151_);
v___x_1153_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___y_1093_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = l_Lean_Syntax_node1(v___y_1093_, v___x_1152_, v___x_1154_);
v___x_1156_ = l_Lean_Syntax_node1(v___y_1093_, v___y_1096_, v___x_1155_);
v___x_1157_ = l_Lean_Syntax_node1(v___y_1093_, v___y_1096_, v___x_1156_);
v___x_1158_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___y_1093_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1161_ = l_Lean_Name_mkStr4(v___y_1100_, v___x_1108_, v___x_1109_, v___x_1160_);
v___x_1162_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___y_1093_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1165_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1167_ = l_Lean_addMacroScope(v___y_1098_, v___x_1166_, v___y_1094_);
v___x_1168_ = l_Lean_Name_mkStr3(v___y_1100_, v___y_1099_, v___x_1164_);
v___x_1169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v___x_1126_);
v___x_1170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v___x_1126_);
v___x_1171_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1171_, 0, v___y_1093_);
lean_ctor_set(v___x_1171_, 1, v___x_1165_);
lean_ctor_set(v___x_1171_, 2, v___x_1167_);
lean_ctor_set(v___x_1171_, 3, v___x_1170_);
v___x_1172_ = l_Lean_Syntax_node2(v___y_1093_, v___x_1161_, v___x_1163_, v___x_1171_);
v___x_1173_ = l_Lean_Syntax_node4(v___y_1093_, v___x_1147_, v___x_1150_, v___x_1157_, v___x_1159_, v___x_1172_);
v___x_1174_ = lean_array_push(v___x_1148_, v___x_1173_);
v___x_1175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1175_, 0, v___y_1093_);
lean_ctor_set(v___x_1175_, 1, v___y_1096_);
lean_ctor_set(v___x_1175_, 2, v___x_1174_);
v___x_1176_ = l_Lean_Syntax_node1(v___y_1093_, v___x_1145_, v___x_1175_);
v___x_1177_ = l_Lean_Syntax_node2(v___y_1093_, v___x_1142_, v___x_1143_, v___x_1176_);
v___x_1178_ = lean_unsigned_to_nat(9u);
v___x_1179_ = lean_mk_empty_array_with_capacity(v___x_1178_);
v___x_1180_ = lean_array_push(v___x_1179_, v___x_1107_);
v___x_1181_ = lean_array_push(v___x_1180_, v___x_1121_);
v___x_1182_ = lean_array_push(v___x_1181_, v___y_1102_);
v___x_1183_ = lean_array_push(v___x_1182_, v___x_1122_);
v___x_1184_ = lean_array_push(v___x_1183_, v___x_1129_);
v___x_1185_ = lean_array_push(v___x_1184_, v___x_1131_);
v___x_1186_ = lean_array_push(v___x_1185_, v___x_1138_);
v___x_1187_ = lean_array_push(v___x_1186_, v___x_1140_);
v___x_1188_ = lean_array_push(v___x_1187_, v___x_1177_);
lean_inc(v___y_1103_);
v___x_1189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1189_, 0, v___y_1093_);
lean_ctor_set(v___x_1189_, 1, v___y_1103_);
lean_ctor_set(v___x_1189_, 2, v___x_1188_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
v___jp_1191_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1198_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1199_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___x_1200_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_1202_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1203_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_502_) == 1)
{
lean_object* v_val_1204_; lean_object* v___x_1205_; 
v_val_1204_ = lean_ctor_get(v_doc_x3f_502_, 0);
lean_inc(v_val_1204_);
lean_dec_ref_known(v_doc_x3f_502_, 1);
v___x_1205_ = l_Array_mkArray1___redArg(v_val_1204_);
v___y_1093_ = v___y_1192_;
v___y_1094_ = v___y_1193_;
v___y_1095_ = v___y_1194_;
v___y_1096_ = v___x_1202_;
v___y_1097_ = v___x_1200_;
v___y_1098_ = v_a_1196_;
v___y_1099_ = v___x_1198_;
v___y_1100_ = v___x_1197_;
v___y_1101_ = v___x_1199_;
v___y_1102_ = v___y_1195_;
v___y_1103_ = v___x_1201_;
v___y_1104_ = v___x_1203_;
v___y_1105_ = v___x_1205_;
goto v___jp_1092_;
}
else
{
lean_object* v___x_1206_; 
lean_dec(v_doc_x3f_502_);
v___x_1206_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_1093_ = v___y_1192_;
v___y_1094_ = v___y_1193_;
v___y_1095_ = v___y_1194_;
v___y_1096_ = v___x_1202_;
v___y_1097_ = v___x_1200_;
v___y_1098_ = v_a_1196_;
v___y_1099_ = v___x_1198_;
v___y_1100_ = v___x_1197_;
v___y_1101_ = v___x_1199_;
v___y_1102_ = v___y_1195_;
v___y_1103_ = v___x_1201_;
v___y_1104_ = v___x_1203_;
v___y_1105_ = v___x_1206_;
goto v___jp_1092_;
}
}
v___jp_1207_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_inc_ref_n(v___y_1211_, 4);
v___x_1220_ = l_Array_append___redArg(v___y_1211_, v___y_1219_);
lean_dec_ref(v___y_1219_);
lean_inc_n(v___y_1218_, 10);
lean_inc_n(v___y_1216_, 35);
v___x_1221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1221_, 0, v___y_1216_);
lean_ctor_set(v___x_1221_, 1, v___y_1218_);
lean_ctor_set(v___x_1221_, 2, v___x_1220_);
v___x_1222_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1223_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1224_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1208_, 11);
v___x_1225_ = l_Lean_Name_mkStr4(v___y_1208_, v___x_1222_, v___x_1223_, v___x_1224_);
v___x_1226_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___y_1216_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1229_ = l_Lean_Syntax_SepArray_ofElems(v___x_1228_, v___y_1217_);
lean_dec_ref(v___y_1217_);
v___x_1230_ = l_Array_append___redArg(v___y_1211_, v___x_1229_);
lean_dec_ref(v___x_1229_);
v___x_1231_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1231_, 0, v___y_1216_);
lean_ctor_set(v___x_1231_, 1, v___y_1218_);
lean_ctor_set(v___x_1231_, 2, v___x_1230_);
v___x_1232_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___y_1216_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = l_Lean_Syntax_node3(v___y_1216_, v___x_1225_, v___x_1227_, v___x_1231_, v___x_1233_);
v___x_1235_ = l_Lean_Syntax_node1(v___y_1216_, v___y_1218_, v___x_1234_);
lean_inc_ref(v___y_1210_);
v___x_1236_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___y_1216_);
lean_ctor_set(v___x_1236_, 1, v___y_1210_);
v___x_1237_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1238_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1213_, 3);
lean_inc_n(v___y_1214_, 3);
v___x_1239_ = l_Lean_addMacroScope(v___y_1214_, v___x_1238_, v___y_1213_);
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1241_, 0, v___y_1216_);
lean_ctor_set(v___x_1241_, 1, v___x_1237_);
lean_ctor_set(v___x_1241_, 2, v___x_1239_);
lean_ctor_set(v___x_1241_, 3, v___x_1240_);
v___x_1242_ = l_Lean_mkIdent(v_k_505_);
v___x_1243_ = l_Lean_Syntax_node2(v___y_1216_, v___y_1218_, v___x_1241_, v___x_1242_);
v___x_1244_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___y_1216_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__39, &l_Lean_Elab_Command_elabElabRulesAux___closed__39_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__39);
v___x_1247_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
lean_inc_ref_n(v___y_1209_, 2);
v___x_1248_ = l_Lean_Name_mkStr4(v___y_1208_, v___y_1209_, v___x_1223_, v___x_1247_);
lean_inc(v___x_1248_);
v___x_1249_ = l_Lean_addMacroScope(v___y_1214_, v___x_1248_, v___y_1213_);
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1240_);
v___x_1251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v___x_1240_);
v___x_1252_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1252_, 0, v___y_1216_);
lean_ctor_set(v___x_1252_, 1, v___x_1246_);
lean_ctor_set(v___x_1252_, 2, v___x_1249_);
lean_ctor_set(v___x_1252_, 3, v___x_1251_);
v___x_1253_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___y_1216_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1256_ = l_Lean_Name_mkStr4(v___y_1208_, v___x_1222_, v___x_1223_, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___y_1216_);
lean_ctor_set(v___x_1257_, 1, v___x_1255_);
v___x_1258_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_1259_ = l_Lean_Name_mkStr4(v___y_1208_, v___x_1222_, v___x_1223_, v___x_1258_);
v___x_1260_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_1261_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1262_ = l_Lean_addMacroScope(v___y_1214_, v___x_1261_, v___y_1213_);
v___x_1263_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1263_, 0, v___y_1216_);
lean_ctor_set(v___x_1263_, 1, v___x_1260_);
lean_ctor_set(v___x_1263_, 2, v___x_1262_);
lean_ctor_set(v___x_1263_, 3, v___x_1240_);
v___x_1264_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1265_ = l_Lean_Name_mkStr4(v___y_1208_, v___x_1222_, v___x_1223_, v___x_1264_);
v___x_1266_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___y_1216_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = l_Lean_Syntax_node1(v___y_1216_, v___x_1265_, v___x_1267_);
lean_inc(v___x_1268_);
lean_inc_ref(v___x_1263_);
v___x_1269_ = l_Lean_Syntax_node2(v___y_1216_, v___y_1218_, v___x_1263_, v___x_1268_);
v___x_1270_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1270_, 0, v___y_1216_);
lean_ctor_set(v___x_1270_, 1, v___y_1218_);
lean_ctor_set(v___x_1270_, 2, v___y_1211_);
v___x_1271_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___y_1216_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1274_ = l_Lean_Name_mkStr4(v___y_1208_, v___x_1222_, v___x_1223_, v___x_1273_);
v___x_1275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___y_1216_);
lean_ctor_set(v___x_1275_, 1, v___x_1273_);
v___x_1276_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1277_ = l_Lean_Name_mkStr4(v___y_1208_, v___x_1222_, v___x_1223_, v___x_1276_);
lean_inc_ref_n(v___x_1270_, 3);
v___x_1278_ = l_Lean_Syntax_node2(v___y_1216_, v___x_1277_, v___x_1270_, v___x_1263_);
v___x_1279_ = l_Lean_Syntax_node1(v___y_1216_, v___y_1218_, v___x_1278_);
v___x_1280_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___y_1216_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1283_ = l_Lean_Name_mkStr4(v___y_1208_, v___x_1222_, v___x_1223_, v___x_1282_);
v___x_1284_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1285_ = l_Lean_Name_mkStr4(v___y_1208_, v___x_1222_, v___x_1223_, v___x_1284_);
v___x_1286_ = l_Array_append___redArg(v___y_1211_, v_a_515_);
lean_dec(v_a_515_);
v___x_1287_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1288_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___y_1216_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = l_Lean_Syntax_node1(v___y_1216_, v___y_1218_, v___x_1268_);
v___x_1290_ = l_Lean_Syntax_node1(v___y_1216_, v___y_1218_, v___x_1289_);
v___x_1291_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1292_ = l_Lean_Name_mkStr4(v___y_1208_, v___x_1222_, v___x_1223_, v___x_1291_);
v___x_1293_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___y_1216_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1296_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_1297_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1298_ = l_Lean_addMacroScope(v___y_1214_, v___x_1297_, v___y_1213_);
v___x_1299_ = l_Lean_Name_mkStr3(v___y_1208_, v___y_1209_, v___x_1295_);
v___x_1300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1240_);
v___x_1301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v___x_1240_);
v___x_1302_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1302_, 0, v___y_1216_);
lean_ctor_set(v___x_1302_, 1, v___x_1296_);
lean_ctor_set(v___x_1302_, 2, v___x_1298_);
lean_ctor_set(v___x_1302_, 3, v___x_1301_);
v___x_1303_ = l_Lean_Syntax_node2(v___y_1216_, v___x_1292_, v___x_1294_, v___x_1302_);
lean_inc_ref(v___x_1272_);
v___x_1304_ = l_Lean_Syntax_node4(v___y_1216_, v___x_1285_, v___x_1288_, v___x_1290_, v___x_1272_, v___x_1303_);
v___x_1305_ = lean_array_push(v___x_1286_, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1306_, 0, v___y_1216_);
lean_ctor_set(v___x_1306_, 1, v___y_1218_);
lean_ctor_set(v___x_1306_, 2, v___x_1305_);
v___x_1307_ = l_Lean_Syntax_node1(v___y_1216_, v___x_1283_, v___x_1306_);
v___x_1308_ = l_Lean_Syntax_node6(v___y_1216_, v___x_1274_, v___x_1275_, v___x_1270_, v___x_1270_, v___x_1279_, v___x_1281_, v___x_1307_);
v___x_1309_ = l_Lean_Syntax_node4(v___y_1216_, v___x_1259_, v___x_1269_, v___x_1270_, v___x_1272_, v___x_1308_);
v___x_1310_ = l_Lean_Syntax_node2(v___y_1216_, v___x_1256_, v___x_1257_, v___x_1309_);
v___x_1311_ = lean_unsigned_to_nat(9u);
v___x_1312_ = lean_mk_empty_array_with_capacity(v___x_1311_);
v___x_1313_ = lean_array_push(v___x_1312_, v___x_1221_);
v___x_1314_ = lean_array_push(v___x_1313_, v___x_1235_);
v___x_1315_ = lean_array_push(v___x_1314_, v___y_1212_);
v___x_1316_ = lean_array_push(v___x_1315_, v___x_1236_);
v___x_1317_ = lean_array_push(v___x_1316_, v___x_1243_);
v___x_1318_ = lean_array_push(v___x_1317_, v___x_1245_);
v___x_1319_ = lean_array_push(v___x_1318_, v___x_1252_);
v___x_1320_ = lean_array_push(v___x_1319_, v___x_1254_);
v___x_1321_ = lean_array_push(v___x_1320_, v___x_1310_);
lean_inc(v___y_1215_);
v___x_1322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1322_, 0, v___y_1216_);
lean_ctor_set(v___x_1322_, 1, v___y_1215_);
lean_ctor_set(v___x_1322_, 2, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
v___jp_1324_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1330_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1331_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1332_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_1333_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_1334_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1335_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_502_) == 1)
{
lean_object* v_val_1336_; lean_object* v___x_1337_; 
v_val_1336_ = lean_ctor_get(v_doc_x3f_502_, 0);
lean_inc(v_val_1336_);
lean_dec_ref_known(v_doc_x3f_502_, 1);
v___x_1337_ = l_Array_mkArray1___redArg(v_val_1336_);
v___y_1208_ = v___x_1330_;
v___y_1209_ = v___x_1331_;
v___y_1210_ = v___x_1332_;
v___y_1211_ = v___x_1335_;
v___y_1212_ = v___y_1326_;
v___y_1213_ = v___y_1325_;
v___y_1214_ = v_a_1329_;
v___y_1215_ = v___x_1333_;
v___y_1216_ = v___y_1327_;
v___y_1217_ = v___y_1328_;
v___y_1218_ = v___x_1334_;
v___y_1219_ = v___x_1337_;
goto v___jp_1207_;
}
else
{
lean_object* v___x_1338_; 
lean_dec(v_doc_x3f_502_);
v___x_1338_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_1208_ = v___x_1330_;
v___y_1209_ = v___x_1331_;
v___y_1210_ = v___x_1332_;
v___y_1211_ = v___x_1335_;
v___y_1212_ = v___y_1326_;
v___y_1213_ = v___y_1325_;
v___y_1214_ = v_a_1329_;
v___y_1215_ = v___x_1333_;
v___y_1216_ = v___y_1327_;
v___y_1217_ = v___y_1328_;
v___y_1218_ = v___x_1334_;
v___y_1219_ = v___x_1338_;
goto v___jp_1207_;
}
}
v___jp_1339_:
{
lean_object* v___x_1343_; 
lean_inc(v_attrKind_504_);
v___x_1343_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_504_);
if (lean_obj_tag(v_expty_x3f_507_) == 1)
{
lean_object* v_val_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_val_1344_ = lean_ctor_get(v_expty_x3f_507_, 0);
lean_inc(v_val_1344_);
lean_dec_ref_known(v_expty_x3f_507_, 1);
v___x_1345_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__58));
v___x_1346_ = lean_name_eq(v_catName_1340_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1347_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__60));
v___x_1348_ = lean_name_eq(v_catName_1340_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec(v___x_1343_);
lean_del_object(v___x_517_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_attrKind_504_);
lean_dec(v_doc_x3f_502_);
v___x_1349_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__62, &l_Lean_Elab_Command_elabElabRulesAux___closed__62_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__62);
v___x_1350_ = l_Lean_MessageData_ofName(v_catName_1340_);
v___x_1351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1349_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__64, &l_Lean_Elab_Command_elabElabRulesAux___closed__64_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__64);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_val_1344_, v___x_1353_, v___y_1341_, v___y_1342_);
lean_dec(v_val_1344_);
return v___x_1354_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v_catName_1340_);
v___x_1355_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__66));
lean_inc(v_k_505_);
v___x_1356_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_505_, v_attrKind_504_, v_attrs_x3f_503_, v___x_1355_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1358_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1356_, 1);
v___x_1358_ = l_Lean_Elab_Command_getRef___redArg(v___y_1341_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1358_, 1);
v___x_1360_ = l_Lean_SourceInfo_fromRef(v_a_1359_, v___x_1346_);
lean_dec(v_a_1359_);
v___x_1361_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1341_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_quotContext_x3f_1362_; 
v_quotContext_x3f_1362_ = lean_ctor_get(v___y_1341_, 5);
if (lean_obj_tag(v_quotContext_x3f_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; lean_object* v_a_1365_; 
v_a_1363_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1361_, 1);
v___x_1364_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1342_);
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref(v___x_1364_);
v___y_641_ = v_a_1363_;
v___y_642_ = v___x_1360_;
v___y_643_ = v_val_1344_;
v___y_644_ = v_a_1357_;
v___y_645_ = v___x_1343_;
v_a_646_ = v_a_1365_;
goto v___jp_640_;
}
else
{
lean_object* v_a_1366_; lean_object* v_val_1367_; 
v_a_1366_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1361_, 1);
v_val_1367_ = lean_ctor_get(v_quotContext_x3f_1362_, 0);
lean_inc(v_val_1367_);
v___y_641_ = v_a_1366_;
v___y_642_ = v___x_1360_;
v___y_643_ = v_val_1344_;
v___y_644_ = v_a_1357_;
v___y_645_ = v___x_1343_;
v_a_646_ = v_val_1367_;
goto v___jp_640_;
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v___x_1360_);
lean_dec(v_a_1357_);
lean_dec(v_val_1344_);
lean_dec(v___x_1343_);
lean_del_object(v___x_517_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
v_a_1368_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1361_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1361_);
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
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
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
else
{
lean_dec(v_a_1357_);
lean_dec(v_val_1344_);
lean_dec(v___x_1343_);
lean_del_object(v___x_517_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
return v___x_1358_;
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v_val_1344_);
lean_dec(v___x_1343_);
lean_del_object(v___x_517_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
v_a_1376_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1356_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1356_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec(v_catName_1340_);
lean_del_object(v___x_517_);
v___x_1384_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__68));
lean_inc(v_k_505_);
v___x_1385_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_505_, v_attrKind_504_, v_attrs_x3f_503_, v___x_1384_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1387_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1385_, 1);
v___x_1387_ = l_Lean_Elab_Command_getRef___redArg(v___y_1341_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; uint8_t v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref_known(v___x_1387_, 1);
v___x_1389_ = 0;
v___x_1390_ = l_Lean_SourceInfo_fromRef(v_a_1388_, v___x_1389_);
lean_dec(v_a_1388_);
v___x_1391_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1341_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_quotContext_x3f_1392_; 
v_quotContext_x3f_1392_ = lean_ctor_get(v___y_1341_, 5);
if (lean_obj_tag(v_quotContext_x3f_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1394_; lean_object* v_a_1395_; 
v_a_1393_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1394_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1342_);
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref(v___x_1394_);
v___y_793_ = v_val_1344_;
v___y_794_ = v_a_1386_;
v___y_795_ = v___x_1390_;
v___y_796_ = v_a_1393_;
v___y_797_ = v___x_1343_;
v_a_798_ = v_a_1395_;
goto v___jp_792_;
}
else
{
lean_object* v_a_1396_; lean_object* v_val_1397_; 
v_a_1396_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1391_, 1);
v_val_1397_ = lean_ctor_get(v_quotContext_x3f_1392_, 0);
lean_inc(v_val_1397_);
v___y_793_ = v_val_1344_;
v___y_794_ = v_a_1386_;
v___y_795_ = v___x_1390_;
v___y_796_ = v_a_1396_;
v___y_797_ = v___x_1343_;
v_a_798_ = v_val_1397_;
goto v___jp_792_;
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec(v___x_1390_);
lean_dec(v_a_1386_);
lean_dec(v_val_1344_);
lean_dec(v___x_1343_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
v_a_1398_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1391_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1391_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
else
{
lean_dec(v_a_1386_);
lean_dec(v_val_1344_);
lean_dec(v___x_1343_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
return v___x_1387_;
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_dec(v_val_1344_);
lean_dec(v___x_1343_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
v_a_1406_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1385_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1385_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
else
{
lean_object* v___x_1414_; uint8_t v___x_1415_; 
lean_del_object(v___x_517_);
lean_dec(v_expty_x3f_507_);
v___x_1414_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__58));
v___x_1415_ = lean_name_eq(v_catName_1340_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1416_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__70));
v___x_1417_ = lean_name_eq(v_catName_1340_, v___x_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1418_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__72));
v___x_1419_ = lean_name_eq(v_catName_1340_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1420_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__74));
v___x_1421_ = lean_name_eq(v_catName_1340_, v___x_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__60));
v___x_1423_ = lean_name_eq(v_catName_1340_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec(v___x_1343_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_attrKind_504_);
lean_dec(v_doc_x3f_502_);
v___x_1424_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__76, &l_Lean_Elab_Command_elabElabRulesAux___closed__76_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76);
v___x_1425_ = l_Lean_MessageData_ofName(v_catName_1340_);
v___x_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1424_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v___x_1427_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__78, &l_Lean_Elab_Command_elabElabRulesAux___closed__78_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__78);
v___x_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1426_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v___x_1428_, v___y_1341_, v___y_1342_);
return v___x_1429_;
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec(v_catName_1340_);
v___x_1430_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__66));
lean_inc(v_k_505_);
v___x_1431_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_505_, v_attrKind_504_, v_attrs_x3f_503_, v___x_1430_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1433_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = l_Lean_Elab_Command_getRef___redArg(v___y_1341_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = l_Lean_SourceInfo_fromRef(v_a_1434_, v___x_1421_);
lean_dec(v_a_1434_);
v___x_1436_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1341_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_quotContext_x3f_1437_; 
v_quotContext_x3f_1437_ = lean_ctor_get(v___y_1341_, 5);
if (lean_obj_tag(v_quotContext_x3f_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1439_; lean_object* v_a_1440_; 
v_a_1438_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1436_, 1);
v___x_1439_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1342_);
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref(v___x_1439_);
v___y_1078_ = v_a_1438_;
v___y_1079_ = v___x_1343_;
v___y_1080_ = v___x_1435_;
v___y_1081_ = v_a_1432_;
v_a_1082_ = v_a_1440_;
goto v___jp_1077_;
}
else
{
lean_object* v_a_1441_; lean_object* v_val_1442_; 
v_a_1441_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1436_, 1);
v_val_1442_ = lean_ctor_get(v_quotContext_x3f_1437_, 0);
lean_inc(v_val_1442_);
v___y_1078_ = v_a_1441_;
v___y_1079_ = v___x_1343_;
v___y_1080_ = v___x_1435_;
v___y_1081_ = v_a_1432_;
v_a_1082_ = v_val_1442_;
goto v___jp_1077_;
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v___x_1435_);
lean_dec(v_a_1432_);
lean_dec(v___x_1343_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
v_a_1443_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1436_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1436_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_dec(v_a_1432_);
lean_dec(v___x_1343_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
return v___x_1433_;
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v___x_1343_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
v_a_1451_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1431_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1431_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
else
{
lean_dec(v_catName_1340_);
v___y_922_ = v___x_1417_;
v___y_923_ = v___x_1418_;
v___y_924_ = v___y_1342_;
v___y_925_ = v___y_1341_;
v___y_926_ = v___x_1343_;
goto v___jp_921_;
}
}
else
{
lean_dec(v_catName_1340_);
v___y_922_ = v___x_1417_;
v___y_923_ = v___x_1418_;
v___y_924_ = v___y_1342_;
v___y_925_ = v___y_1341_;
v___y_926_ = v___x_1343_;
goto v___jp_921_;
}
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_dec(v_catName_1340_);
v___x_1459_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__80));
lean_inc(v_k_505_);
v___x_1460_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_505_, v_attrKind_504_, v_attrs_x3f_503_, v___x_1459_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = l_Lean_Elab_Command_getRef___redArg(v___y_1341_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v___x_1464_ = l_Lean_SourceInfo_fromRef(v_a_1463_, v___x_1415_);
lean_dec(v_a_1463_);
v___x_1465_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1341_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_quotContext_x3f_1466_; 
v_quotContext_x3f_1466_ = lean_ctor_get(v___y_1341_, 5);
if (lean_obj_tag(v_quotContext_x3f_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1468_; lean_object* v_a_1469_; 
v_a_1467_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1465_, 1);
v___x_1468_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1342_);
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref(v___x_1468_);
v___y_1192_ = v___x_1464_;
v___y_1193_ = v_a_1467_;
v___y_1194_ = v_a_1461_;
v___y_1195_ = v___x_1343_;
v_a_1196_ = v_a_1469_;
goto v___jp_1191_;
}
else
{
lean_object* v_a_1470_; lean_object* v_val_1471_; 
v_a_1470_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1465_, 1);
v_val_1471_ = lean_ctor_get(v_quotContext_x3f_1466_, 0);
lean_inc(v_val_1471_);
v___y_1192_ = v___x_1464_;
v___y_1193_ = v_a_1470_;
v___y_1194_ = v_a_1461_;
v___y_1195_ = v___x_1343_;
v_a_1196_ = v_val_1471_;
goto v___jp_1191_;
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v___x_1464_);
lean_dec(v_a_1461_);
lean_dec(v___x_1343_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
v_a_1472_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1465_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1465_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_dec(v_a_1461_);
lean_dec(v___x_1343_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
return v___x_1462_;
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec(v___x_1343_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
v_a_1480_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1460_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1460_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec(v_catName_1340_);
v___x_1488_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__68));
lean_inc(v_k_505_);
v___x_1489_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_505_, v_attrKind_504_, v_attrs_x3f_503_, v___x_1488_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1491_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1489_, 1);
v___x_1491_ = l_Lean_Elab_Command_getRef___redArg(v___y_1341_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v___x_1493_ = 0;
v___x_1494_ = l_Lean_SourceInfo_fromRef(v_a_1492_, v___x_1493_);
lean_dec(v_a_1492_);
v___x_1495_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1341_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_quotContext_x3f_1496_; 
v_quotContext_x3f_1496_ = lean_ctor_get(v___y_1341_, 5);
if (lean_obj_tag(v_quotContext_x3f_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v_a_1499_; 
v_a_1497_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1495_, 1);
v___x_1498_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1342_);
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref(v___x_1498_);
v___y_1325_ = v_a_1497_;
v___y_1326_ = v___x_1343_;
v___y_1327_ = v___x_1494_;
v___y_1328_ = v_a_1490_;
v_a_1329_ = v_a_1499_;
goto v___jp_1324_;
}
else
{
lean_object* v_a_1500_; lean_object* v_val_1501_; 
v_a_1500_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1495_, 1);
v_val_1501_ = lean_ctor_get(v_quotContext_x3f_1496_, 0);
lean_inc(v_val_1501_);
v___y_1325_ = v_a_1500_;
v___y_1326_ = v___x_1343_;
v___y_1327_ = v___x_1494_;
v___y_1328_ = v_a_1490_;
v_a_1329_ = v_val_1501_;
goto v___jp_1324_;
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v___x_1494_);
lean_dec(v_a_1490_);
lean_dec(v___x_1343_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
v_a_1502_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1495_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1495_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
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
else
{
lean_dec(v_a_1490_);
lean_dec(v___x_1343_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
return v___x_1491_;
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v___x_1343_);
lean_dec(v_a_515_);
lean_dec(v_k_505_);
lean_dec(v_doc_x3f_502_);
v_a_1510_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1489_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1489_);
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
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_expty_x3f_507_);
lean_dec(v_k_505_);
lean_dec(v_attrKind_504_);
lean_dec(v_doc_x3f_502_);
v_a_1532_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_514_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_514_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object* v_doc_x3f_1540_, lean_object* v_attrs_x3f_1541_, lean_object* v_attrKind_1542_, lean_object* v_k_1543_, lean_object* v_cat_x3f_1544_, lean_object* v_expty_x3f_1545_, lean_object* v_alts_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_Elab_Command_elabElabRulesAux(v_doc_x3f_1540_, v_attrs_x3f_1541_, v_attrKind_1542_, v_k_1543_, v_cat_x3f_1544_, v_expty_x3f_1545_, v_alts_1546_, v_a_1547_, v_a_1548_);
lean_dec(v_a_1548_);
lean_dec_ref(v_a_1547_);
lean_dec(v_cat_x3f_1544_);
lean_dec(v_attrs_x3f_1541_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object* v_00_u03b1_1551_, lean_object* v_ref_1552_, lean_object* v_msg_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_1552_, v_msg_1553_, v___y_1554_, v___y_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object* v_00_u03b1_1558_, lean_object* v_ref_1559_, lean_object* v_msg_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(v_00_u03b1_1558_, v_ref_1559_, v_msg_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v_ref_1559_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4(lean_object* v_msgData_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(v_msgData_1565_, v___y_1567_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___boxed(lean_object* v_msgData_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4(v_msgData_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object* v_00_u03b1_1575_, lean_object* v_msg_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v_msg_1576_, v___y_1577_, v___y_1578_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object* v_00_u03b1_1581_, lean_object* v_msg_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_00_u03b1_1581_, v_msg_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5(lean_object* v_msgData_1587_, lean_object* v_macroStack_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg(v_msgData_1587_, v_macroStack_1588_, v___y_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___boxed(lean_object* v_msgData_1593_, lean_object* v_macroStack_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5(v_msgData_1593_, v_macroStack_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
return v_res_1598_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = lean_box(0);
v___x_1600_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
lean_ctor_set(v___x_1601_, 1, v___x_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg(){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0);
v___x_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___boxed(lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0(lean_object* v_00_u03b1_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___boxed(lean_object* v_00_u03b1_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0(v_00_u03b1_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object* v_x_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object* v_x_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Elab_Command_elabElabRules___lam__0(v_x_1619_);
lean_dec(v_x_1619_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object* v___x_1625_, lean_object* v___x_1626_, lean_object* v_attrKind_1627_, lean_object* v_expty_x3f_1628_, lean_object* v___f_1629_, lean_object* v_cat_x3f_1630_, lean_object* v___x_1631_, lean_object* v___x_1632_, lean_object* v_attrs_x3f_1633_, lean_object* v___x_1634_, lean_object* v___x_1635_, lean_object* v___x_1636_, lean_object* v_doc_x3f_1637_, lean_object* v_kind_x3f_1638_, lean_object* v_alts_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Elab_Command_getRef___redArg(v___y_1640_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1752_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1752_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1752_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___x_1741_; 
v___x_1648_ = 0;
v___x_1649_ = l_Lean_SourceInfo_fromRef(v_a_1644_, v___x_1648_);
lean_dec(v_a_1644_);
v___x_1741_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1640_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_quotContext_x3f_1742_; 
lean_dec_ref_known(v___x_1741_, 1);
v_quotContext_x3f_1742_ = lean_ctor_get(v___y_1640_, 5);
if (lean_obj_tag(v_quotContext_x3f_1742_) == 0)
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1641_);
lean_dec_ref(v___x_1743_);
goto v___jp_1735_;
}
else
{
goto v___jp_1735_;
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec(v___x_1649_);
lean_del_object(v___x_1646_);
lean_dec(v_kind_x3f_1638_);
lean_dec(v_doc_x3f_1637_);
lean_dec_ref(v___x_1636_);
lean_dec_ref(v___x_1635_);
lean_dec_ref(v___x_1634_);
lean_dec_ref(v___x_1631_);
lean_dec(v_cat_x3f_1630_);
lean_dec_ref(v___f_1629_);
lean_dec(v_expty_x3f_1628_);
lean_dec(v_attrKind_1627_);
lean_dec(v___x_1626_);
lean_dec(v___x_1625_);
v_a_1744_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1741_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1741_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
v___jp_1650_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1666_; 
lean_inc_ref_n(v___y_1657_, 2);
v___x_1659_ = l_Array_append___redArg(v___y_1657_, v___y_1658_);
lean_dec_ref(v___y_1658_);
lean_inc_n(v___y_1655_, 2);
lean_inc_n(v___x_1649_, 3);
v___x_1660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1649_);
lean_ctor_set(v___x_1660_, 1, v___y_1655_);
lean_ctor_set(v___x_1660_, 2, v___x_1659_);
v___x_1661_ = l_Array_append___redArg(v___y_1657_, v_alts_1639_);
v___x_1662_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1649_);
lean_ctor_set(v___x_1662_, 1, v___y_1655_);
lean_ctor_set(v___x_1662_, 2, v___x_1661_);
v___x_1663_ = l_Lean_Syntax_node1(v___x_1649_, v___x_1625_, v___x_1662_);
v___x_1664_ = l_Lean_Syntax_node8(v___x_1649_, v___x_1626_, v___y_1653_, v___y_1656_, v_attrKind_1627_, v___y_1651_, v___y_1654_, v___y_1652_, v___x_1660_, v___x_1663_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1664_);
v___x_1666_ = v___x_1646_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
v___jp_1668_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_inc_ref(v___y_1674_);
v___x_1676_ = l_Array_append___redArg(v___y_1674_, v___y_1675_);
lean_dec_ref(v___y_1675_);
lean_inc(v___y_1672_);
lean_inc(v___x_1649_);
v___x_1677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1649_);
lean_ctor_set(v___x_1677_, 1, v___y_1672_);
lean_ctor_set(v___x_1677_, 2, v___x_1676_);
if (lean_obj_tag(v_expty_x3f_1628_) == 1)
{
lean_object* v_val_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec_ref(v___f_1629_);
v_val_1678_ = lean_ctor_get(v_expty_x3f_1628_, 0);
lean_inc(v_val_1678_);
lean_dec_ref_known(v_expty_x3f_1628_, 1);
v___x_1679_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___x_1649_);
v___x_1680_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1649_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = l_Array_mkArray2___redArg(v___x_1680_, v_val_1678_);
v___y_1651_ = v___y_1669_;
v___y_1652_ = v___x_1677_;
v___y_1653_ = v___y_1670_;
v___y_1654_ = v___y_1671_;
v___y_1655_ = v___y_1672_;
v___y_1656_ = v___y_1673_;
v___y_1657_ = v___y_1674_;
v___y_1658_ = v___x_1681_;
goto v___jp_1650_;
}
else
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_apply_1(v___f_1629_, v_expty_x3f_1628_);
v___y_1651_ = v___y_1669_;
v___y_1652_ = v___x_1677_;
v___y_1653_ = v___y_1670_;
v___y_1654_ = v___y_1671_;
v___y_1655_ = v___y_1672_;
v___y_1656_ = v___y_1673_;
v___y_1657_ = v___y_1674_;
v___y_1658_ = v___x_1682_;
goto v___jp_1650_;
}
}
v___jp_1683_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_inc_ref(v___y_1688_);
v___x_1690_ = l_Array_append___redArg(v___y_1688_, v___y_1689_);
lean_dec_ref(v___y_1689_);
lean_inc(v___y_1686_);
lean_inc(v___x_1649_);
v___x_1691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1649_);
lean_ctor_set(v___x_1691_, 1, v___y_1686_);
lean_ctor_set(v___x_1691_, 2, v___x_1690_);
if (lean_obj_tag(v_cat_x3f_1630_) == 1)
{
lean_object* v_val_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v_val_1692_ = lean_ctor_get(v_cat_x3f_1630_, 0);
lean_inc(v_val_1692_);
lean_dec_ref_known(v_cat_x3f_1630_, 1);
v___x_1693_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___x_1649_);
v___x_1694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1649_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = l_Array_mkArray2___redArg(v___x_1694_, v_val_1692_);
v___y_1669_ = v___y_1684_;
v___y_1670_ = v___y_1685_;
v___y_1671_ = v___x_1691_;
v___y_1672_ = v___y_1686_;
v___y_1673_ = v___y_1687_;
v___y_1674_ = v___y_1688_;
v___y_1675_ = v___x_1695_;
goto v___jp_1668_;
}
else
{
lean_object* v___x_1696_; 
lean_inc_ref(v___f_1629_);
v___x_1696_ = lean_apply_1(v___f_1629_, v_cat_x3f_1630_);
v___y_1669_ = v___y_1684_;
v___y_1670_ = v___y_1685_;
v___y_1671_ = v___x_1691_;
v___y_1672_ = v___y_1686_;
v___y_1673_ = v___y_1687_;
v___y_1674_ = v___y_1688_;
v___y_1675_ = v___x_1696_;
goto v___jp_1668_;
}
}
v___jp_1697_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_inc_ref(v___y_1700_);
v___x_1702_ = l_Array_append___redArg(v___y_1700_, v___y_1701_);
lean_dec_ref(v___y_1701_);
lean_inc(v___y_1699_);
lean_inc_n(v___x_1649_, 2);
v___x_1703_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1649_);
lean_ctor_set(v___x_1703_, 1, v___y_1699_);
lean_ctor_set(v___x_1703_, 2, v___x_1702_);
v___x_1704_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1649_);
lean_ctor_set(v___x_1704_, 1, v___x_1631_);
if (lean_obj_tag(v_kind_x3f_1638_) == 0)
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_mk_empty_array_with_capacity(v___x_1632_);
v___y_1684_ = v___x_1704_;
v___y_1685_ = v___y_1698_;
v___y_1686_ = v___y_1699_;
v___y_1687_ = v___x_1703_;
v___y_1688_ = v___y_1700_;
v___y_1689_ = v___x_1705_;
goto v___jp_1683_;
}
else
{
lean_object* v_val_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_val_1706_ = lean_ctor_get(v_kind_x3f_1638_, 0);
lean_inc(v_val_1706_);
lean_dec_ref_known(v_kind_x3f_1638_, 1);
v___x_1707_ = l_Lean_mkIdent(v_val_1706_);
v___x_1708_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___x_1649_, 4);
v___x_1709_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1649_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__2));
v___x_1711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1649_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1649_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_1715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1649_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = l_Array_mkArray5___redArg(v___x_1709_, v___x_1711_, v___x_1713_, v___x_1707_, v___x_1715_);
v___y_1684_ = v___x_1704_;
v___y_1685_ = v___y_1698_;
v___y_1686_ = v___y_1699_;
v___y_1687_ = v___x_1703_;
v___y_1688_ = v___y_1700_;
v___y_1689_ = v___x_1716_;
goto v___jp_1683_;
}
}
v___jp_1717_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_inc_ref(v___y_1719_);
v___x_1721_ = l_Array_append___redArg(v___y_1719_, v___y_1720_);
lean_dec_ref(v___y_1720_);
lean_inc(v___y_1718_);
lean_inc(v___x_1649_);
v___x_1722_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1649_);
lean_ctor_set(v___x_1722_, 1, v___y_1718_);
lean_ctor_set(v___x_1722_, 2, v___x_1721_);
if (lean_obj_tag(v_attrs_x3f_1633_) == 1)
{
lean_object* v_val_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_val_1723_ = lean_ctor_get(v_attrs_x3f_1633_, 0);
v___x_1724_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
v___x_1725_ = l_Lean_Name_mkStr4(v___x_1634_, v___x_1635_, v___x_1636_, v___x_1724_);
v___x_1726_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___x_1649_, 4);
v___x_1727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1649_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
lean_inc_ref(v___y_1719_);
v___x_1728_ = l_Array_append___redArg(v___y_1719_, v_val_1723_);
lean_inc(v___y_1718_);
v___x_1729_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1649_);
lean_ctor_set(v___x_1729_, 1, v___y_1718_);
lean_ctor_set(v___x_1729_, 2, v___x_1728_);
v___x_1730_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1649_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = l_Lean_Syntax_node3(v___x_1649_, v___x_1725_, v___x_1727_, v___x_1729_, v___x_1731_);
v___x_1733_ = l_Array_mkArray1___redArg(v___x_1732_);
v___y_1698_ = v___x_1722_;
v___y_1699_ = v___y_1718_;
v___y_1700_ = v___y_1719_;
v___y_1701_ = v___x_1733_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1734_; 
lean_dec_ref(v___x_1636_);
lean_dec_ref(v___x_1635_);
lean_dec_ref(v___x_1634_);
v___x_1734_ = lean_mk_empty_array_with_capacity(v___x_1632_);
v___y_1698_ = v___x_1722_;
v___y_1699_ = v___y_1718_;
v___y_1700_ = v___y_1719_;
v___y_1701_ = v___x_1734_;
goto v___jp_1697_;
}
}
v___jp_1735_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1737_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_1637_) == 1)
{
lean_object* v_val_1738_; lean_object* v___x_1739_; 
v_val_1738_ = lean_ctor_get(v_doc_x3f_1637_, 0);
lean_inc(v_val_1738_);
lean_dec_ref_known(v_doc_x3f_1637_, 1);
v___x_1739_ = l_Array_mkArray1___redArg(v_val_1738_);
v___y_1718_ = v___x_1736_;
v___y_1719_ = v___x_1737_;
v___y_1720_ = v___x_1739_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_1740_; 
lean_dec(v_doc_x3f_1637_);
v___x_1740_ = lean_mk_empty_array_with_capacity(v___x_1632_);
v___y_1718_ = v___x_1736_;
v___y_1719_ = v___x_1737_;
v___y_1720_ = v___x_1740_;
goto v___jp_1717_;
}
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec(v_kind_x3f_1638_);
lean_dec(v_doc_x3f_1637_);
lean_dec_ref(v___x_1636_);
lean_dec_ref(v___x_1635_);
lean_dec_ref(v___x_1634_);
lean_dec_ref(v___x_1631_);
lean_dec(v_cat_x3f_1630_);
lean_dec_ref(v___f_1629_);
lean_dec(v_expty_x3f_1628_);
lean_dec(v_attrKind_1627_);
lean_dec(v___x_1626_);
lean_dec(v___x_1625_);
v_a_1753_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1643_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1643_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object** _args){
lean_object* v___x_1761_ = _args[0];
lean_object* v___x_1762_ = _args[1];
lean_object* v_attrKind_1763_ = _args[2];
lean_object* v_expty_x3f_1764_ = _args[3];
lean_object* v___f_1765_ = _args[4];
lean_object* v_cat_x3f_1766_ = _args[5];
lean_object* v___x_1767_ = _args[6];
lean_object* v___x_1768_ = _args[7];
lean_object* v_attrs_x3f_1769_ = _args[8];
lean_object* v___x_1770_ = _args[9];
lean_object* v___x_1771_ = _args[10];
lean_object* v___x_1772_ = _args[11];
lean_object* v_doc_x3f_1773_ = _args[12];
lean_object* v_kind_x3f_1774_ = _args[13];
lean_object* v_alts_1775_ = _args[14];
lean_object* v___y_1776_ = _args[15];
lean_object* v___y_1777_ = _args[16];
lean_object* v___y_1778_ = _args[17];
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_Elab_Command_elabElabRules___lam__1(v___x_1761_, v___x_1762_, v_attrKind_1763_, v_expty_x3f_1764_, v___f_1765_, v_cat_x3f_1766_, v___x_1767_, v___x_1768_, v_attrs_x3f_1769_, v___x_1770_, v___x_1771_, v___x_1772_, v_doc_x3f_1773_, v_kind_x3f_1774_, v_alts_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v_alts_1775_);
lean_dec(v_attrs_x3f_1769_);
lean_dec(v___x_1768_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object* v___f_1807_, lean_object* v_stx_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1812_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1813_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0));
v___x_1815_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
lean_inc(v_stx_1808_);
v___x_1816_ = l_Lean_Syntax_isOfKind(v_stx_1808_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; 
lean_dec(v_stx_1808_);
lean_dec_ref(v___f_1807_);
v___x_1817_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1817_;
}
else
{
lean_object* v___x_1818_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v_expty_x3f_1826_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v_cat_x3f_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v_expty_x3f_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v_cat_x3f_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v_attrs_x3f_1944_; lean_object* v_doc_x3f_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
v___x_1818_ = lean_unsigned_to_nat(0u);
v___x_1991_ = l_Lean_Syntax_getArg(v_stx_1808_, v___x_1818_);
v___x_1992_ = l_Lean_Syntax_isNone(v___x_1991_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1993_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1991_);
v___x_1994_ = l_Lean_Syntax_matchesNull(v___x_1991_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; 
lean_dec(v___x_1991_);
lean_dec(v_stx_1808_);
lean_dec_ref(v___f_1807_);
v___x_1995_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1995_;
}
else
{
lean_object* v_doc_x3f_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v_doc_x3f_1996_ = l_Lean_Syntax_getArg(v___x_1991_, v___x_1818_);
lean_dec(v___x_1991_);
v___x_1997_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__6));
lean_inc(v_doc_x3f_1996_);
v___x_1998_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1996_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; 
lean_dec(v_doc_x3f_1996_);
lean_dec(v_stx_1808_);
lean_dec_ref(v___f_1807_);
v___x_1999_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1999_;
}
else
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_doc_x3f_1996_);
v_doc_x3f_1975_ = v___x_2000_;
v___y_1976_ = v___y_1809_;
v___y_1977_ = v___y_1810_;
goto v___jp_1974_;
}
}
}
else
{
lean_object* v___x_2001_; 
lean_dec(v___x_1991_);
v___x_2001_ = lean_box(0);
v_doc_x3f_1975_ = v___x_2001_;
v___y_1976_ = v___y_1809_;
v___y_1977_ = v___y_1810_;
goto v___jp_1974_;
}
v___jp_1819_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1827_ = lean_unsigned_to_nat(7u);
v___x_1828_ = l_Lean_Syntax_getArg(v_stx_1808_, v___x_1827_);
lean_dec(v_stx_1808_);
v___x_1829_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1830_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
lean_inc(v___x_1828_);
v___x_1831_ = l_Lean_Syntax_isOfKind(v___x_1828_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
lean_dec(v___x_1828_);
lean_dec(v_expty_x3f_1826_);
lean_dec(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___f_1807_);
v___x_1832_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1832_;
}
else
{
lean_object* v___f_1833_; lean_object* v___x_1834_; lean_object* v_alts_1835_; lean_object* v___x_1836_; 
v___f_1833_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lam__1___boxed), 18, 13);
lean_closure_set(v___f_1833_, 0, v___x_1830_);
lean_closure_set(v___f_1833_, 1, v___x_1815_);
lean_closure_set(v___f_1833_, 2, v___y_1820_);
lean_closure_set(v___f_1833_, 3, v_expty_x3f_1826_);
lean_closure_set(v___f_1833_, 4, v___f_1807_);
lean_closure_set(v___f_1833_, 5, v___y_1821_);
lean_closure_set(v___f_1833_, 6, v___x_1814_);
lean_closure_set(v___f_1833_, 7, v___x_1818_);
lean_closure_set(v___f_1833_, 8, v___y_1824_);
lean_closure_set(v___f_1833_, 9, v___x_1812_);
lean_closure_set(v___f_1833_, 10, v___x_1813_);
lean_closure_set(v___f_1833_, 11, v___x_1829_);
lean_closure_set(v___f_1833_, 12, v___y_1823_);
v___x_1834_ = l_Lean_Syntax_getArg(v___x_1828_, v___x_1818_);
lean_dec(v___x_1828_);
v_alts_1835_ = l_Lean_Syntax_getArgs(v___x_1834_);
lean_dec(v___x_1834_);
v___x_1836_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_1835_, v___x_1814_, v___f_1833_, v___y_1822_, v___y_1825_);
lean_dec_ref(v_alts_1835_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1846_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1846_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1846_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1841_ = lean_box(0);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v_a_1837_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1842_);
v___x_1844_ = v___x_1839_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
v_a_1847_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1836_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1836_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
v___jp_1855_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1864_ = lean_unsigned_to_nat(6u);
v___x_1865_ = l_Lean_Syntax_getArg(v_stx_1808_, v___x_1864_);
v___x_1866_ = l_Lean_Syntax_isNone(v___x_1865_);
if (v___x_1866_ == 0)
{
uint8_t v___x_1867_; 
lean_inc(v___x_1865_);
v___x_1867_ = l_Lean_Syntax_matchesNull(v___x_1865_, v___y_1860_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; 
lean_dec(v___x_1865_);
lean_dec(v_cat_x3f_1861_);
lean_dec(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v_stx_1808_);
lean_dec_ref(v___f_1807_);
v___x_1868_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1868_;
}
else
{
lean_object* v_expty_x3f_1869_; lean_object* v___x_1870_; 
v_expty_x3f_1869_ = l_Lean_Syntax_getArg(v___x_1865_, v___y_1859_);
lean_dec(v___x_1865_);
v___x_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1870_, 0, v_expty_x3f_1869_);
v___y_1820_ = v___y_1856_;
v___y_1821_ = v_cat_x3f_1861_;
v___y_1822_ = v___y_1862_;
v___y_1823_ = v___y_1857_;
v___y_1824_ = v___y_1858_;
v___y_1825_ = v___y_1863_;
v_expty_x3f_1826_ = v___x_1870_;
goto v___jp_1819_;
}
}
else
{
lean_object* v___x_1871_; 
lean_dec(v___x_1865_);
v___x_1871_ = lean_box(0);
v___y_1820_ = v___y_1856_;
v___y_1821_ = v_cat_x3f_1861_;
v___y_1822_ = v___y_1862_;
v___y_1823_ = v___y_1857_;
v___y_1824_ = v___y_1858_;
v___y_1825_ = v___y_1863_;
v_expty_x3f_1826_ = v___x_1871_;
goto v___jp_1819_;
}
}
v___jp_1872_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1882_ = lean_unsigned_to_nat(7u);
v___x_1883_ = l_Lean_Syntax_getArg(v_stx_1808_, v___x_1882_);
lean_dec(v_stx_1808_);
v___x_1884_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(v___y_1873_);
v___x_1885_ = l_Lean_Name_mkStr4(v___x_1812_, v___x_1813_, v___y_1873_, v___x_1884_);
lean_inc(v___x_1883_);
v___x_1886_ = l_Lean_Syntax_isOfKind(v___x_1883_, v___x_1885_);
lean_dec(v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; 
lean_dec(v___x_1883_);
lean_dec(v_expty_x3f_1879_);
lean_dec(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec(v___y_1874_);
v___x_1887_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1887_;
}
else
{
lean_object* v___x_1888_; lean_object* v_alts_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1888_ = l_Lean_Syntax_getArg(v___x_1883_, v___x_1818_);
lean_dec(v___x_1883_);
v_alts_1889_ = l_Lean_Syntax_getArgs(v___x_1888_);
lean_dec(v___x_1888_);
v___x_1890_ = l_Lean_TSyntax_getId(v___y_1877_);
lean_dec(v___y_1877_);
v___x_1891_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_1890_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1893_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc_n(v_a_1892_, 2);
lean_dec_ref_known(v___x_1891_, 1);
v___x_1893_ = l_Lean_Elab_Command_elabElabRulesAux(v___y_1875_, v___y_1876_, v___y_1878_, v_a_1892_, v___y_1874_, v_expty_x3f_1879_, v_alts_1889_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1874_);
lean_dec(v___y_1876_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1903_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1903_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1903_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v_a_1892_);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v_a_1894_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1899_);
v___x_1901_ = v___x_1896_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_a_1892_);
v_a_1904_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1893_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1893_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec_ref(v_alts_1889_);
lean_dec(v_expty_x3f_1879_);
lean_dec(v___y_1878_);
lean_dec(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec(v___y_1874_);
v_a_1912_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1891_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1891_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
v___jp_1920_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
v___x_1931_ = lean_unsigned_to_nat(6u);
v___x_1932_ = l_Lean_Syntax_getArg(v_stx_1808_, v___x_1931_);
v___x_1933_ = l_Lean_Syntax_isNone(v___x_1932_);
if (v___x_1933_ == 0)
{
uint8_t v___x_1934_; 
lean_inc(v___x_1932_);
v___x_1934_ = l_Lean_Syntax_matchesNull(v___x_1932_, v___y_1925_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; 
lean_dec(v___x_1932_);
lean_dec(v_cat_x3f_1928_);
lean_dec(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec(v_stx_1808_);
v___x_1935_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1935_;
}
else
{
lean_object* v_expty_x3f_1936_; lean_object* v___x_1937_; 
v_expty_x3f_1936_ = l_Lean_Syntax_getArg(v___x_1932_, v___y_1924_);
lean_dec(v___x_1932_);
v___x_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1937_, 0, v_expty_x3f_1936_);
v___y_1873_ = v___y_1921_;
v___y_1874_ = v_cat_x3f_1928_;
v___y_1875_ = v___y_1922_;
v___y_1876_ = v___y_1923_;
v___y_1877_ = v___y_1926_;
v___y_1878_ = v___y_1927_;
v_expty_x3f_1879_ = v___x_1937_;
v___y_1880_ = v___y_1929_;
v___y_1881_ = v___y_1930_;
goto v___jp_1872_;
}
}
else
{
lean_object* v___x_1938_; 
lean_dec(v___x_1932_);
v___x_1938_ = lean_box(0);
v___y_1873_ = v___y_1921_;
v___y_1874_ = v_cat_x3f_1928_;
v___y_1875_ = v___y_1922_;
v___y_1876_ = v___y_1923_;
v___y_1877_ = v___y_1926_;
v___y_1878_ = v___y_1927_;
v_expty_x3f_1879_ = v___x_1938_;
v___y_1880_ = v___y_1929_;
v___y_1881_ = v___y_1930_;
goto v___jp_1872_;
}
}
v___jp_1939_:
{
lean_object* v___x_1945_; lean_object* v_attrKind_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1945_ = lean_unsigned_to_nat(2u);
v_attrKind_1946_ = l_Lean_Syntax_getArg(v_stx_1808_, v___x_1945_);
v___x_1947_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1948_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__3));
lean_inc(v_attrKind_1946_);
v___x_1949_ = l_Lean_Syntax_isOfKind(v_attrKind_1946_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; 
lean_dec(v_attrKind_1946_);
lean_dec(v_attrs_x3f_1944_);
lean_dec(v___y_1941_);
lean_dec(v_stx_1808_);
lean_dec_ref(v___f_1807_);
v___x_1950_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1950_;
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
v___x_1951_ = lean_unsigned_to_nat(4u);
v___x_1952_ = l_Lean_Syntax_getArg(v_stx_1808_, v___x_1951_);
lean_inc(v___x_1952_);
v___x_1953_ = l_Lean_Syntax_matchesNull(v___x_1952_, v___x_1818_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; uint8_t v___x_1955_; 
lean_dec_ref(v___f_1807_);
v___x_1954_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1952_);
v___x_1955_ = l_Lean_Syntax_matchesNull(v___x_1952_, v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; 
lean_dec(v___x_1952_);
lean_dec(v_attrKind_1946_);
lean_dec(v_attrs_x3f_1944_);
lean_dec(v___y_1941_);
lean_dec(v_stx_1808_);
v___x_1956_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1956_;
}
else
{
lean_object* v___x_1957_; lean_object* v_kind_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1957_ = lean_unsigned_to_nat(3u);
v_kind_1958_ = l_Lean_Syntax_getArg(v___x_1952_, v___x_1957_);
lean_dec(v___x_1952_);
v___x_1959_ = l_Lean_Syntax_getArg(v_stx_1808_, v___x_1954_);
v___x_1960_ = l_Lean_Syntax_isNone(v___x_1959_);
if (v___x_1960_ == 0)
{
uint8_t v___x_1961_; 
lean_inc(v___x_1959_);
v___x_1961_ = l_Lean_Syntax_matchesNull(v___x_1959_, v___x_1945_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
lean_dec(v___x_1959_);
lean_dec(v_kind_1958_);
lean_dec(v_attrKind_1946_);
lean_dec(v_attrs_x3f_1944_);
lean_dec(v___y_1941_);
lean_dec(v_stx_1808_);
v___x_1962_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1962_;
}
else
{
lean_object* v_cat_x3f_1963_; lean_object* v___x_1964_; 
v_cat_x3f_1963_ = l_Lean_Syntax_getArg(v___x_1959_, v___y_1943_);
lean_dec(v___x_1959_);
v___x_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1964_, 0, v_cat_x3f_1963_);
v___y_1921_ = v___x_1947_;
v___y_1922_ = v___y_1941_;
v___y_1923_ = v_attrs_x3f_1944_;
v___y_1924_ = v___y_1943_;
v___y_1925_ = v___x_1945_;
v___y_1926_ = v_kind_1958_;
v___y_1927_ = v_attrKind_1946_;
v_cat_x3f_1928_ = v___x_1964_;
v___y_1929_ = v___y_1942_;
v___y_1930_ = v___y_1940_;
goto v___jp_1920_;
}
}
else
{
lean_object* v___x_1965_; 
lean_dec(v___x_1959_);
v___x_1965_ = lean_box(0);
v___y_1921_ = v___x_1947_;
v___y_1922_ = v___y_1941_;
v___y_1923_ = v_attrs_x3f_1944_;
v___y_1924_ = v___y_1943_;
v___y_1925_ = v___x_1945_;
v___y_1926_ = v_kind_1958_;
v___y_1927_ = v_attrKind_1946_;
v_cat_x3f_1928_ = v___x_1965_;
v___y_1929_ = v___y_1942_;
v___y_1930_ = v___y_1940_;
goto v___jp_1920_;
}
}
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
lean_dec(v___x_1952_);
v___x_1966_ = lean_unsigned_to_nat(5u);
v___x_1967_ = l_Lean_Syntax_getArg(v_stx_1808_, v___x_1966_);
v___x_1968_ = l_Lean_Syntax_isNone(v___x_1967_);
if (v___x_1968_ == 0)
{
uint8_t v___x_1969_; 
lean_inc(v___x_1967_);
v___x_1969_ = l_Lean_Syntax_matchesNull(v___x_1967_, v___x_1945_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
lean_dec(v___x_1967_);
lean_dec(v_attrKind_1946_);
lean_dec(v_attrs_x3f_1944_);
lean_dec(v___y_1941_);
lean_dec(v_stx_1808_);
lean_dec_ref(v___f_1807_);
v___x_1970_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1970_;
}
else
{
lean_object* v_cat_x3f_1971_; lean_object* v___x_1972_; 
v_cat_x3f_1971_ = l_Lean_Syntax_getArg(v___x_1967_, v___y_1943_);
lean_dec(v___x_1967_);
v___x_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1972_, 0, v_cat_x3f_1971_);
v___y_1856_ = v_attrKind_1946_;
v___y_1857_ = v___y_1941_;
v___y_1858_ = v_attrs_x3f_1944_;
v___y_1859_ = v___y_1943_;
v___y_1860_ = v___x_1945_;
v_cat_x3f_1861_ = v___x_1972_;
v___y_1862_ = v___y_1942_;
v___y_1863_ = v___y_1940_;
goto v___jp_1855_;
}
}
else
{
lean_object* v___x_1973_; 
lean_dec(v___x_1967_);
v___x_1973_ = lean_box(0);
v___y_1856_ = v_attrKind_1946_;
v___y_1857_ = v___y_1941_;
v___y_1858_ = v_attrs_x3f_1944_;
v___y_1859_ = v___y_1943_;
v___y_1860_ = v___x_1945_;
v_cat_x3f_1861_ = v___x_1973_;
v___y_1862_ = v___y_1942_;
v___y_1863_ = v___y_1940_;
goto v___jp_1855_;
}
}
}
}
v___jp_1974_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1978_ = lean_unsigned_to_nat(1u);
v___x_1979_ = l_Lean_Syntax_getArg(v_stx_1808_, v___x_1978_);
v___x_1980_ = l_Lean_Syntax_isNone(v___x_1979_);
if (v___x_1980_ == 0)
{
uint8_t v___x_1981_; 
lean_inc(v___x_1979_);
v___x_1981_ = l_Lean_Syntax_matchesNull(v___x_1979_, v___x_1978_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; 
lean_dec(v___x_1979_);
lean_dec(v_doc_x3f_1975_);
lean_dec(v_stx_1808_);
lean_dec_ref(v___f_1807_);
v___x_1982_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1982_;
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1983_ = l_Lean_Syntax_getArg(v___x_1979_, v___x_1818_);
lean_dec(v___x_1979_);
v___x_1984_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v___x_1983_);
v___x_1985_ = l_Lean_Syntax_isOfKind(v___x_1983_, v___x_1984_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; 
lean_dec(v___x_1983_);
lean_dec(v_doc_x3f_1975_);
lean_dec(v_stx_1808_);
lean_dec_ref(v___f_1807_);
v___x_1986_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1986_;
}
else
{
lean_object* v___x_1987_; lean_object* v_attrs_x3f_1988_; lean_object* v___x_1989_; 
v___x_1987_ = l_Lean_Syntax_getArg(v___x_1983_, v___x_1978_);
lean_dec(v___x_1983_);
v_attrs_x3f_1988_ = l_Lean_Syntax_getArgs(v___x_1987_);
lean_dec(v___x_1987_);
v___x_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1989_, 0, v_attrs_x3f_1988_);
v___y_1940_ = v___y_1977_;
v___y_1941_ = v_doc_x3f_1975_;
v___y_1942_ = v___y_1976_;
v___y_1943_ = v___x_1978_;
v_attrs_x3f_1944_ = v___x_1989_;
goto v___jp_1939_;
}
}
}
else
{
lean_object* v___x_1990_; 
lean_dec(v___x_1979_);
v___x_1990_ = lean_box(0);
v___y_1940_ = v___y_1977_;
v___y_1941_ = v_doc_x3f_1975_;
v___y_1942_ = v___y_1976_;
v___y_1943_ = v___x_1978_;
v_attrs_x3f_1944_ = v___x_1990_;
goto v___jp_1939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object* v___f_2002_, lean_object* v_stx_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Elab_Command_elabElabRules___lam__2(v___f_2002_, v_stx_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v___f_2015_; lean_object* v___x_2016_; 
v___f_2015_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___closed__1));
v___x_2016_ = l_Lean_Elab_Command_adaptRulesExpander(v___f_2015_, v_a_2011_, v_a_2012_, v_a_2013_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_Elab_Command_elabElabRules(v_a_2017_, v_a_2018_, v_a_2019_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1(){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2029_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2030_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_2031_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2032_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___boxed), 4, 0);
v___x_2033_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2029_, v___x_2030_, v___x_2031_, v___x_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object* v_a_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3(){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2063_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6));
v___x_2064_ = l_Lean_addBuiltinDeclarationRanges(v___x_2062_, v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t v_sz_2067_, size_t v_i_2068_, lean_object* v_bs_2069_){
_start:
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_usize_dec_lt(v_i_2068_, v_sz_2067_);
if (v___x_2070_ == 0)
{
return v_bs_2069_;
}
else
{
lean_object* v_v_2071_; lean_object* v___x_2072_; lean_object* v_bs_x27_2073_; size_t v___x_2074_; size_t v___x_2075_; lean_object* v___x_2076_; 
v_v_2071_ = lean_array_uget(v_bs_2069_, v_i_2068_);
v___x_2072_ = lean_unsigned_to_nat(0u);
v_bs_x27_2073_ = lean_array_uset(v_bs_2069_, v_i_2068_, v___x_2072_);
v___x_2074_ = ((size_t)1ULL);
v___x_2075_ = lean_usize_add(v_i_2068_, v___x_2074_);
v___x_2076_ = lean_array_uset(v_bs_x27_2073_, v_i_2068_, v_v_2071_);
v_i_2068_ = v___x_2075_;
v_bs_2069_ = v___x_2076_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object* v_sz_2078_, lean_object* v_i_2079_, lean_object* v_bs_2080_){
_start:
{
size_t v_sz_boxed_2081_; size_t v_i_boxed_2082_; lean_object* v_res_2083_; 
v_sz_boxed_2081_ = lean_unbox_usize(v_sz_2078_);
lean_dec(v_sz_2078_);
v_i_boxed_2082_ = lean_unbox_usize(v_i_2079_);
lean_dec(v_i_2079_);
v_res_2083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_boxed_2081_, v_i_boxed_2082_, v_bs_2080_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t v_sz_2084_, size_t v_i_2085_, lean_object* v_bs_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
uint8_t v___x_2090_; 
v___x_2090_ = lean_usize_dec_lt(v_i_2085_, v_sz_2084_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v_bs_2086_);
return v___x_2091_;
}
else
{
lean_object* v_v_2092_; lean_object* v___x_2093_; lean_object* v_bs_x27_2094_; lean_object* v___x_2095_; 
v_v_2092_ = lean_array_uget(v_bs_2086_, v_i_2085_);
v___x_2093_ = lean_unsigned_to_nat(0u);
v_bs_x27_2094_ = lean_array_uset(v_bs_2086_, v_i_2085_, v___x_2093_);
v___x_2095_ = l_Lean_Elab_Command_expandMacroArg(v_v_2092_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; size_t v___x_2097_; size_t v___x_2098_; lean_object* v___x_2099_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2097_ = ((size_t)1ULL);
v___x_2098_ = lean_usize_add(v_i_2085_, v___x_2097_);
v___x_2099_ = lean_array_uset(v_bs_x27_2094_, v_i_2085_, v_a_2096_);
v_i_2085_ = v___x_2098_;
v_bs_2086_ = v___x_2099_;
goto _start;
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec_ref(v_bs_x27_2094_);
v_a_2101_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2095_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2095_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object* v_sz_2109_, lean_object* v_i_2110_, lean_object* v_bs_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
size_t v_sz_boxed_2115_; size_t v_i_boxed_2116_; lean_object* v_res_2117_; 
v_sz_boxed_2115_ = lean_unbox_usize(v_sz_2109_);
lean_dec(v_sz_2109_);
v_i_boxed_2116_ = lean_unbox_usize(v_i_2110_);
lean_dec(v_i_2110_);
v_res_2117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_boxed_2115_, v_i_boxed_2116_, v_bs_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
return v_res_2117_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(lean_object* v_keys_2118_, lean_object* v_i_2119_, lean_object* v_k_2120_){
_start:
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = lean_array_get_size(v_keys_2118_);
v___x_2122_ = lean_nat_dec_lt(v_i_2119_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_dec(v_i_2119_);
return v___x_2122_;
}
else
{
lean_object* v_k_x27_2123_; uint8_t v___x_2124_; 
v_k_x27_2123_ = lean_array_fget_borrowed(v_keys_2118_, v_i_2119_);
v___x_2124_ = l_Lean_instBEqExtraModUse_beq(v_k_2120_, v_k_x27_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_unsigned_to_nat(1u);
v___x_2126_ = lean_nat_add(v_i_2119_, v___x_2125_);
lean_dec(v_i_2119_);
v_i_2119_ = v___x_2126_;
goto _start;
}
else
{
lean_dec(v_i_2119_);
return v___x_2122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_keys_2128_, lean_object* v_i_2129_, lean_object* v_k_2130_){
_start:
{
uint8_t v_res_2131_; lean_object* v_r_2132_; 
v_res_2131_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_2128_, v_i_2129_, v_k_2130_);
lean_dec_ref(v_k_2130_);
lean_dec_ref(v_keys_2128_);
v_r_2132_ = lean_box(v_res_2131_);
return v_r_2132_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(lean_object* v_x_2133_, size_t v_x_2134_, lean_object* v_x_2135_){
_start:
{
if (lean_obj_tag(v_x_2133_) == 0)
{
lean_object* v_es_2136_; lean_object* v___x_2137_; size_t v___x_2138_; size_t v___x_2139_; lean_object* v_j_2140_; lean_object* v___x_2141_; 
v_es_2136_ = lean_ctor_get(v_x_2133_, 0);
v___x_2137_ = lean_box(2);
v___x_2138_ = ((size_t)31ULL);
v___x_2139_ = lean_usize_land(v_x_2134_, v___x_2138_);
v_j_2140_ = lean_usize_to_nat(v___x_2139_);
v___x_2141_ = lean_array_get_borrowed(v___x_2137_, v_es_2136_, v_j_2140_);
lean_dec(v_j_2140_);
switch(lean_obj_tag(v___x_2141_))
{
case 0:
{
lean_object* v_key_2142_; uint8_t v___x_2143_; 
v_key_2142_ = lean_ctor_get(v___x_2141_, 0);
v___x_2143_ = l_Lean_instBEqExtraModUse_beq(v_x_2135_, v_key_2142_);
return v___x_2143_;
}
case 1:
{
lean_object* v_node_2144_; size_t v___x_2145_; size_t v___x_2146_; 
v_node_2144_ = lean_ctor_get(v___x_2141_, 0);
v___x_2145_ = ((size_t)5ULL);
v___x_2146_ = lean_usize_shift_right(v_x_2134_, v___x_2145_);
v_x_2133_ = v_node_2144_;
v_x_2134_ = v___x_2146_;
goto _start;
}
default: 
{
uint8_t v___x_2148_; 
v___x_2148_ = 0;
return v___x_2148_;
}
}
}
else
{
lean_object* v_ks_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v_ks_2149_ = lean_ctor_get(v_x_2133_, 0);
v___x_2150_ = lean_unsigned_to_nat(0u);
v___x_2151_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_ks_2149_, v___x_2150_, v_x_2135_);
return v___x_2151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_x_2152_, lean_object* v_x_2153_, lean_object* v_x_2154_){
_start:
{
size_t v_x_16585__boxed_2155_; uint8_t v_res_2156_; lean_object* v_r_2157_; 
v_x_16585__boxed_2155_ = lean_unbox_usize(v_x_2153_);
lean_dec(v_x_2153_);
v_res_2156_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2152_, v_x_16585__boxed_2155_, v_x_2154_);
lean_dec_ref(v_x_2154_);
lean_dec_ref(v_x_2152_);
v_r_2157_ = lean_box(v_res_2156_);
return v_r_2157_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(lean_object* v_x_2158_, lean_object* v_x_2159_){
_start:
{
uint64_t v___x_2160_; size_t v___x_2161_; uint8_t v___x_2162_; 
v___x_2160_ = l_Lean_instHashableExtraModUse_hash(v_x_2159_);
v___x_2161_ = lean_uint64_to_usize(v___x_2160_);
v___x_2162_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2158_, v___x_2161_, v_x_2159_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_x_2163_, lean_object* v_x_2164_){
_start:
{
uint8_t v_res_2165_; lean_object* v_r_2166_; 
v_res_2165_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_2163_, v_x_2164_);
lean_dec_ref(v_x_2164_);
lean_dec_ref(v_x_2163_);
v_r_2166_ = lean_box(v_res_2165_);
return v_r_2166_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2167_; double v___x_2168_; 
v___x_2167_ = lean_unsigned_to_nat(0u);
v___x_2168_ = lean_float_of_nat(v___x_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object* v_cls_2172_, lean_object* v_msg_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_Elab_Command_getRef___redArg(v___y_2174_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2228_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(v_msg_2173_, v___y_2175_);
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2228_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2228_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v_traceState_2185_; lean_object* v_env_2186_; lean_object* v_messages_2187_; lean_object* v_scopes_2188_; lean_object* v_usedQuotCtxts_2189_; lean_object* v_nextMacroScope_2190_; lean_object* v_maxRecDepth_2191_; lean_object* v_ngen_2192_; lean_object* v_auxDeclNGen_2193_; lean_object* v_infoState_2194_; lean_object* v_snapshotTasks_2195_; lean_object* v_prevLinterStates_2196_; lean_object* v_codeQualityEntryTasks_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2227_; 
v___x_2184_ = lean_st_ref_take(v___y_2175_);
v_traceState_2185_ = lean_ctor_get(v___x_2184_, 9);
v_env_2186_ = lean_ctor_get(v___x_2184_, 0);
v_messages_2187_ = lean_ctor_get(v___x_2184_, 1);
v_scopes_2188_ = lean_ctor_get(v___x_2184_, 2);
v_usedQuotCtxts_2189_ = lean_ctor_get(v___x_2184_, 3);
v_nextMacroScope_2190_ = lean_ctor_get(v___x_2184_, 4);
v_maxRecDepth_2191_ = lean_ctor_get(v___x_2184_, 5);
v_ngen_2192_ = lean_ctor_get(v___x_2184_, 6);
v_auxDeclNGen_2193_ = lean_ctor_get(v___x_2184_, 7);
v_infoState_2194_ = lean_ctor_get(v___x_2184_, 8);
v_snapshotTasks_2195_ = lean_ctor_get(v___x_2184_, 10);
v_prevLinterStates_2196_ = lean_ctor_get(v___x_2184_, 11);
v_codeQualityEntryTasks_2197_ = lean_ctor_get(v___x_2184_, 12);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2199_ = v___x_2184_;
v_isShared_2200_ = v_isSharedCheck_2227_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2197_);
lean_inc(v_prevLinterStates_2196_);
lean_inc(v_snapshotTasks_2195_);
lean_inc(v_traceState_2185_);
lean_inc(v_infoState_2194_);
lean_inc(v_auxDeclNGen_2193_);
lean_inc(v_ngen_2192_);
lean_inc(v_maxRecDepth_2191_);
lean_inc(v_nextMacroScope_2190_);
lean_inc(v_usedQuotCtxts_2189_);
lean_inc(v_scopes_2188_);
lean_inc(v_messages_2187_);
lean_inc(v_env_2186_);
lean_dec(v___x_2184_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2227_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
uint64_t v_tid_2201_; lean_object* v_traces_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2226_; 
v_tid_2201_ = lean_ctor_get_uint64(v_traceState_2185_, sizeof(void*)*1);
v_traces_2202_ = lean_ctor_get(v_traceState_2185_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_traceState_2185_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2204_ = v_traceState_2185_;
v_isShared_2205_ = v_isSharedCheck_2226_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_traces_2202_);
lean_dec(v_traceState_2185_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2226_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; double v___x_2208_; uint8_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2206_ = lean_box(0);
v___x_2207_ = lean_box(0);
v___x_2208_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0);
v___x_2209_ = 0;
v___x_2210_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2211_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2211_, 0, v_cls_2172_);
lean_ctor_set(v___x_2211_, 1, v___x_2207_);
lean_ctor_set(v___x_2211_, 2, v___x_2210_);
lean_ctor_set_float(v___x_2211_, sizeof(void*)*3, v___x_2208_);
lean_ctor_set_float(v___x_2211_, sizeof(void*)*3 + 8, v___x_2208_);
lean_ctor_set_uint8(v___x_2211_, sizeof(void*)*3 + 16, v___x_2209_);
v___x_2212_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2));
v___x_2213_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2211_);
lean_ctor_set(v___x_2213_, 1, v_a_2180_);
lean_ctor_set(v___x_2213_, 2, v___x_2212_);
v___x_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2214_, 0, v_a_2178_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = l_Lean_PersistentArray_push___redArg(v_traces_2202_, v___x_2214_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2215_);
v___x_2217_ = v___x_2204_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2215_);
lean_ctor_set_uint64(v_reuseFailAlloc_2225_, sizeof(void*)*1, v_tid_2201_);
v___x_2217_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2219_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 9, v___x_2217_);
v___x_2219_ = v___x_2199_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_env_2186_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_messages_2187_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_scopes_2188_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_usedQuotCtxts_2189_);
lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_nextMacroScope_2190_);
lean_ctor_set(v_reuseFailAlloc_2224_, 5, v_maxRecDepth_2191_);
lean_ctor_set(v_reuseFailAlloc_2224_, 6, v_ngen_2192_);
lean_ctor_set(v_reuseFailAlloc_2224_, 7, v_auxDeclNGen_2193_);
lean_ctor_set(v_reuseFailAlloc_2224_, 8, v_infoState_2194_);
lean_ctor_set(v_reuseFailAlloc_2224_, 9, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2224_, 10, v_snapshotTasks_2195_);
lean_ctor_set(v_reuseFailAlloc_2224_, 11, v_prevLinterStates_2196_);
lean_ctor_set(v_reuseFailAlloc_2224_, 12, v_codeQualityEntryTasks_2197_);
v___x_2219_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = lean_st_ref_put(v___y_2175_, v___x_2219_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2206_);
v___x_2222_ = v___x_2182_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2206_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec_ref(v_msg_2173_);
lean_dec(v_cls_2172_);
v_a_2229_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2177_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2177_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object* v_cls_2237_, lean_object* v_msg_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2237_, v_msg_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___lam__0(lean_object* v___x_2243_, lean_object* v_entry_2244_, lean_object* v_s_2245_){
_start:
{
lean_object* v_addEntryFn_2246_; lean_object* v_importedEntries_2247_; lean_object* v_state_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2256_; 
v_addEntryFn_2246_ = lean_ctor_get(v___x_2243_, 3);
lean_inc(v_addEntryFn_2246_);
lean_dec_ref(v___x_2243_);
v_importedEntries_2247_ = lean_ctor_get(v_s_2245_, 0);
v_state_2248_ = lean_ctor_get(v_s_2245_, 1);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_s_2245_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2250_ = v_s_2245_;
v_isShared_2251_ = v_isSharedCheck_2256_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_state_2248_);
lean_inc(v_importedEntries_2247_);
lean_dec(v_s_2245_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2256_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v_state_2252_; lean_object* v___x_2254_; 
v_state_2252_ = lean_apply_2(v_addEntryFn_2246_, v_state_2248_, v_entry_2244_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 1, v_state_2252_);
v___x_2254_ = v___x_2250_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_importedEntries_2247_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_state_2252_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2257_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3));
v___x_2263_ = l_Lean_stringToMessageData(v___x_2262_);
return v___x_2263_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5));
v___x_2266_ = l_Lean_stringToMessageData(v___x_2265_);
return v___x_2266_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2268_ = l_Lean_stringToMessageData(v___x_2267_);
return v___x_2268_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v_cls_2272_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2));
v___x_2273_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9));
v___x_2274_ = l_Lean_Name_append(v___x_2273_, v_cls_2272_);
return v___x_2274_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11));
v___x_2277_ = l_Lean_stringToMessageData(v___x_2276_);
return v___x_2277_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13));
v___x_2280_ = l_Lean_stringToMessageData(v___x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(lean_object* v_mod_2285_, uint8_t v_isMeta_2286_, lean_object* v_hint_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v_env_2312_; uint8_t v_isExporting_2313_; lean_object* v_entry_2314_; lean_object* v___x_2315_; lean_object* v_env_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2310_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0);
v___x_2311_ = lean_st_ref_get(v___y_2289_);
v_env_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc_ref(v_env_2312_);
lean_dec(v___x_2311_);
v_isExporting_2313_ = lean_ctor_get_uint8(v_env_2312_, sizeof(void*)*13);
lean_dec_ref(v_env_2312_);
lean_inc(v_mod_2285_);
v_entry_2314_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2314_, 0, v_mod_2285_);
lean_ctor_set_uint8(v_entry_2314_, sizeof(void*)*1, v_isExporting_2313_);
lean_ctor_set_uint8(v_entry_2314_, sizeof(void*)*1 + 1, v_isMeta_2286_);
v___x_2315_ = lean_st_ref_get(v___y_2289_);
v_env_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc_ref(v_env_2316_);
lean_dec(v___x_2315_);
v___x_2317_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2318_ = lean_box(1);
v___x_2319_ = lean_box(0);
v___x_2320_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2310_, v___x_2317_, v_env_2316_, v___x_2318_, v___x_2319_);
v___x_2321_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v___x_2320_, v_entry_2314_);
lean_dec(v___x_2320_);
if (v___x_2321_ == 0)
{
lean_object* v___f_2322_; uint8_t v___x_2323_; lean_object* v___y_2325_; lean_object* v_cls_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v_scopes_2371_; lean_object* v___x_2372_; lean_object* v_opts_2373_; uint8_t v_hasTrace_2374_; 
v___f_2322_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_2322_, 0, v___x_2317_);
lean_closure_set(v___f_2322_, 1, v_entry_2314_);
v___x_2323_ = 1;
v_cls_2347_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2));
v___x_2348_ = l_Lean_inheritedTraceOptions;
v___x_2349_ = lean_st_ref_get(v___x_2348_);
v___x_2350_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2351_ = lean_st_ref_get(v___y_2289_);
v_scopes_2371_ = lean_ctor_get(v___x_2351_, 2);
lean_inc(v_scopes_2371_);
lean_dec(v___x_2351_);
v___x_2372_ = l_List_head_x21___redArg(v___x_2350_, v_scopes_2371_);
lean_dec(v_scopes_2371_);
v_opts_2373_ = lean_ctor_get(v___x_2372_, 1);
lean_inc_ref(v_opts_2373_);
lean_dec(v___x_2372_);
v_hasTrace_2374_ = lean_ctor_get_uint8(v_opts_2373_, sizeof(void*)*1);
if (v_hasTrace_2374_ == 0)
{
lean_dec_ref(v_opts_2373_);
lean_dec(v___x_2349_);
lean_dec(v_hint_2287_);
lean_dec(v_mod_2285_);
v___y_2325_ = v___y_2289_;
goto v___jp_2324_;
}
else
{
lean_object* v___x_2375_; uint8_t v___x_2376_; 
v___x_2375_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10);
v___x_2376_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2349_, v_opts_2373_, v___x_2375_);
lean_dec_ref(v_opts_2373_);
lean_dec(v___x_2349_);
if (v___x_2376_ == 0)
{
lean_dec(v_hint_2287_);
lean_dec(v_mod_2285_);
v___y_2325_ = v___y_2289_;
goto v___jp_2324_;
}
else
{
lean_object* v___x_2377_; lean_object* v___y_2379_; 
v___x_2377_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12);
if (v_isExporting_2313_ == 0)
{
lean_object* v___x_2386_; 
v___x_2386_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17));
v___y_2379_ = v___x_2386_;
goto v___jp_2378_;
}
else
{
lean_object* v___x_2387_; 
v___x_2387_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18));
v___y_2379_ = v___x_2387_;
goto v___jp_2378_;
}
v___jp_2378_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_inc_ref(v___y_2379_);
v___x_2380_ = l_Lean_stringToMessageData(v___y_2379_);
v___x_2381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2377_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
v___x_2382_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14);
v___x_2383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
if (v_isMeta_2286_ == 0)
{
lean_object* v___x_2384_; 
v___x_2384_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15));
v___y_2358_ = v___x_2383_;
v___y_2359_ = v___x_2384_;
goto v___jp_2357_;
}
else
{
lean_object* v___x_2385_; 
v___x_2385_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16));
v___y_2358_ = v___x_2383_;
v___y_2359_ = v___x_2385_;
goto v___jp_2357_;
}
}
}
}
v___jp_2324_:
{
lean_object* v___x_2326_; lean_object* v_toEnvExtension_2327_; lean_object* v_env_2328_; lean_object* v_messages_2329_; lean_object* v_scopes_2330_; lean_object* v_usedQuotCtxts_2331_; lean_object* v_nextMacroScope_2332_; lean_object* v_maxRecDepth_2333_; lean_object* v_ngen_2334_; lean_object* v_auxDeclNGen_2335_; lean_object* v_infoState_2336_; lean_object* v_traceState_2337_; lean_object* v_snapshotTasks_2338_; lean_object* v_prevLinterStates_2339_; lean_object* v_codeQualityEntryTasks_2340_; lean_object* v_asyncMode_2341_; uint8_t v_logWrites_2342_; lean_object* v___x_2343_; 
v___x_2326_ = lean_st_ref_take(v___y_2325_);
v_toEnvExtension_2327_ = lean_ctor_get(v___x_2317_, 0);
v_env_2328_ = lean_ctor_get(v___x_2326_, 0);
lean_inc_ref(v_env_2328_);
v_messages_2329_ = lean_ctor_get(v___x_2326_, 1);
lean_inc_ref(v_messages_2329_);
v_scopes_2330_ = lean_ctor_get(v___x_2326_, 2);
lean_inc(v_scopes_2330_);
v_usedQuotCtxts_2331_ = lean_ctor_get(v___x_2326_, 3);
lean_inc(v_usedQuotCtxts_2331_);
v_nextMacroScope_2332_ = lean_ctor_get(v___x_2326_, 4);
lean_inc(v_nextMacroScope_2332_);
v_maxRecDepth_2333_ = lean_ctor_get(v___x_2326_, 5);
lean_inc(v_maxRecDepth_2333_);
v_ngen_2334_ = lean_ctor_get(v___x_2326_, 6);
lean_inc_ref(v_ngen_2334_);
v_auxDeclNGen_2335_ = lean_ctor_get(v___x_2326_, 7);
lean_inc_ref(v_auxDeclNGen_2335_);
v_infoState_2336_ = lean_ctor_get(v___x_2326_, 8);
lean_inc_ref(v_infoState_2336_);
v_traceState_2337_ = lean_ctor_get(v___x_2326_, 9);
lean_inc_ref(v_traceState_2337_);
v_snapshotTasks_2338_ = lean_ctor_get(v___x_2326_, 10);
lean_inc_ref(v_snapshotTasks_2338_);
v_prevLinterStates_2339_ = lean_ctor_get(v___x_2326_, 11);
lean_inc(v_prevLinterStates_2339_);
v_codeQualityEntryTasks_2340_ = lean_ctor_get(v___x_2326_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2340_);
lean_dec(v___x_2326_);
v_asyncMode_2341_ = lean_ctor_get(v_toEnvExtension_2327_, 2);
v_logWrites_2342_ = lean_ctor_get_uint8(v_toEnvExtension_2327_, sizeof(void*)*6);
v___x_2343_ = lean_box(0);
if (v_logWrites_2342_ == 0)
{
lean_object* v___x_2344_; 
lean_inc_ref(v_toEnvExtension_2327_);
v___x_2344_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2327_, v_env_2328_, v___f_2322_, v_asyncMode_2341_, v___x_2319_, v___x_2323_);
v___y_2292_ = v_maxRecDepth_2333_;
v___y_2293_ = v_ngen_2334_;
v___y_2294_ = v_auxDeclNGen_2335_;
v___y_2295_ = v_infoState_2336_;
v___y_2296_ = v_snapshotTasks_2338_;
v___y_2297_ = v_usedQuotCtxts_2331_;
v___y_2298_ = v_traceState_2337_;
v___y_2299_ = v_scopes_2330_;
v___y_2300_ = v_codeQualityEntryTasks_2340_;
v___y_2301_ = v_nextMacroScope_2332_;
v___y_2302_ = v___x_2343_;
v___y_2303_ = v_prevLinterStates_2339_;
v___y_2304_ = v_messages_2329_;
v___y_2305_ = v___y_2325_;
v___y_2306_ = v___x_2344_;
goto v___jp_2291_;
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_inc_ref_n(v_toEnvExtension_2327_, 2);
v___x_2345_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2327_, v_env_2328_);
lean_dec_ref(v_env_2328_);
v___x_2346_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2327_, v___x_2345_, v___f_2322_, v_asyncMode_2341_, v___x_2319_, v___x_2323_);
v___y_2292_ = v_maxRecDepth_2333_;
v___y_2293_ = v_ngen_2334_;
v___y_2294_ = v_auxDeclNGen_2335_;
v___y_2295_ = v_infoState_2336_;
v___y_2296_ = v_snapshotTasks_2338_;
v___y_2297_ = v_usedQuotCtxts_2331_;
v___y_2298_ = v_traceState_2337_;
v___y_2299_ = v_scopes_2330_;
v___y_2300_ = v_codeQualityEntryTasks_2340_;
v___y_2301_ = v_nextMacroScope_2332_;
v___y_2302_ = v___x_2343_;
v___y_2303_ = v_prevLinterStates_2339_;
v___y_2304_ = v_messages_2329_;
v___y_2305_ = v___y_2325_;
v___y_2306_ = v___x_2346_;
goto v___jp_2291_;
}
}
v___jp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___y_2353_);
lean_ctor_set(v___x_2355_, 1, v___y_2354_);
v___x_2356_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2347_, v___x_2355_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_dec_ref_known(v___x_2356_, 1);
v___y_2325_ = v___y_2289_;
goto v___jp_2324_;
}
else
{
lean_dec_ref(v___f_2322_);
return v___x_2356_;
}
}
v___jp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; 
lean_inc_ref(v___y_2359_);
v___x_2360_ = l_Lean_stringToMessageData(v___y_2359_);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___y_2358_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4);
v___x_2363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2361_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = l_Lean_MessageData_ofName(v_mod_2285_);
v___x_2365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = l_Lean_Name_isAnonymous(v_hint_2287_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2367_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6);
v___x_2368_ = l_Lean_MessageData_ofName(v_hint_2287_);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___y_2353_ = v___x_2365_;
v___y_2354_ = v___x_2369_;
goto v___jp_2352_;
}
else
{
lean_object* v___x_2370_; 
lean_dec(v_hint_2287_);
v___x_2370_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7);
v___y_2353_ = v___x_2365_;
v___y_2354_ = v___x_2370_;
goto v___jp_2352_;
}
}
}
else
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec_ref_known(v_entry_2314_, 1);
lean_dec(v_hint_2287_);
lean_dec(v_mod_2285_);
v___x_2388_ = lean_box(0);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
v___jp_2291_:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2307_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2307_, 0, v___y_2306_);
lean_ctor_set(v___x_2307_, 1, v___y_2304_);
lean_ctor_set(v___x_2307_, 2, v___y_2299_);
lean_ctor_set(v___x_2307_, 3, v___y_2297_);
lean_ctor_set(v___x_2307_, 4, v___y_2301_);
lean_ctor_set(v___x_2307_, 5, v___y_2292_);
lean_ctor_set(v___x_2307_, 6, v___y_2293_);
lean_ctor_set(v___x_2307_, 7, v___y_2294_);
lean_ctor_set(v___x_2307_, 8, v___y_2295_);
lean_ctor_set(v___x_2307_, 9, v___y_2298_);
lean_ctor_set(v___x_2307_, 10, v___y_2296_);
lean_ctor_set(v___x_2307_, 11, v___y_2303_);
lean_ctor_set(v___x_2307_, 12, v___y_2300_);
v___x_2308_ = lean_st_ref_put(v___y_2305_, v___x_2307_);
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___y_2302_);
return v___x_2309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___boxed(lean_object* v_mod_2390_, lean_object* v_isMeta_2391_, lean_object* v_hint_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
uint8_t v_isMeta_boxed_2396_; lean_object* v_res_2397_; 
v_isMeta_boxed_2396_ = lean_unbox(v_isMeta_2391_);
v_res_2397_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_mod_2390_, v_isMeta_boxed_2396_, v_hint_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(lean_object* v___x_2398_, lean_object* v_declName_2399_, lean_object* v_as_2400_, size_t v_sz_2401_, size_t v_i_2402_, lean_object* v_b_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
uint8_t v___x_2407_; 
v___x_2407_ = lean_usize_dec_lt(v_i_2402_, v_sz_2401_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; 
lean_dec(v_declName_2399_);
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v_b_2403_);
return v___x_2408_;
}
else
{
lean_object* v___x_2409_; lean_object* v_modules_2410_; lean_object* v___x_2411_; lean_object* v_a_2412_; lean_object* v___x_2413_; lean_object* v_toImport_2414_; lean_object* v_module_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2409_ = l_Lean_Environment_header(v___x_2398_);
v_modules_2410_ = lean_ctor_get(v___x_2409_, 3);
lean_inc_ref(v_modules_2410_);
lean_dec_ref(v___x_2409_);
v___x_2411_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2412_ = lean_array_uget_borrowed(v_as_2400_, v_i_2402_);
v___x_2413_ = lean_array_get(v___x_2411_, v_modules_2410_, v_a_2412_);
lean_dec_ref(v_modules_2410_);
v_toImport_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc_ref(v_toImport_2414_);
lean_dec(v___x_2413_);
v_module_2415_ = lean_ctor_get(v_toImport_2414_, 0);
lean_inc(v_module_2415_);
lean_dec_ref(v_toImport_2414_);
v___x_2416_ = lean_box(0);
v___x_2417_ = 0;
lean_inc(v_declName_2399_);
v___x_2418_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2415_, v___x_2417_, v_declName_2399_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2418_) == 0)
{
size_t v___x_2419_; size_t v___x_2420_; 
lean_dec_ref_known(v___x_2418_, 1);
v___x_2419_ = ((size_t)1ULL);
v___x_2420_ = lean_usize_add(v_i_2402_, v___x_2419_);
v_i_2402_ = v___x_2420_;
v_b_2403_ = v___x_2416_;
goto _start;
}
else
{
lean_dec(v_declName_2399_);
return v___x_2418_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4___boxed(lean_object* v___x_2422_, lean_object* v_declName_2423_, lean_object* v_as_2424_, lean_object* v_sz_2425_, lean_object* v_i_2426_, lean_object* v_b_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
size_t v_sz_boxed_2431_; size_t v_i_boxed_2432_; lean_object* v_res_2433_; 
v_sz_boxed_2431_ = lean_unbox_usize(v_sz_2425_);
lean_dec(v_sz_2425_);
v_i_boxed_2432_ = lean_unbox_usize(v_i_2426_);
lean_dec(v_i_2426_);
v_res_2433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v___x_2422_, v_declName_2423_, v_as_2424_, v_sz_boxed_2431_, v_i_boxed_2432_, v_b_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec_ref(v_as_2424_);
lean_dec_ref(v___x_2422_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(lean_object* v_a_2434_, lean_object* v_x_2435_){
_start:
{
if (lean_obj_tag(v_x_2435_) == 0)
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_box(0);
return v___x_2436_;
}
else
{
lean_object* v_key_2437_; lean_object* v_value_2438_; lean_object* v_tail_2439_; uint8_t v___x_2440_; 
v_key_2437_ = lean_ctor_get(v_x_2435_, 0);
v_value_2438_ = lean_ctor_get(v_x_2435_, 1);
v_tail_2439_ = lean_ctor_get(v_x_2435_, 2);
v___x_2440_ = lean_name_eq(v_key_2437_, v_a_2434_);
if (v___x_2440_ == 0)
{
v_x_2435_ = v_tail_2439_;
goto _start;
}
else
{
lean_object* v___x_2442_; 
lean_inc(v_value_2438_);
v___x_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2442_, 0, v_value_2438_);
return v___x_2442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_a_2443_, lean_object* v_x_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2443_, v_x_2444_);
lean_dec(v_x_2444_);
lean_dec(v_a_2443_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(lean_object* v_m_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_buckets_2448_; lean_object* v___x_2449_; uint64_t v___y_2451_; 
v_buckets_2448_ = lean_ctor_get(v_m_2446_, 1);
v___x_2449_ = lean_array_get_size(v_buckets_2448_);
if (lean_obj_tag(v_a_2447_) == 0)
{
uint64_t v___x_2465_; 
v___x_2465_ = 1723ULL;
v___y_2451_ = v___x_2465_;
goto v___jp_2450_;
}
else
{
uint64_t v_hash_2466_; 
v_hash_2466_ = lean_ctor_get_uint64(v_a_2447_, sizeof(void*)*2);
v___y_2451_ = v_hash_2466_;
goto v___jp_2450_;
}
v___jp_2450_:
{
uint64_t v___x_2452_; uint64_t v___x_2453_; uint64_t v_fold_2454_; uint64_t v___x_2455_; uint64_t v___x_2456_; uint64_t v___x_2457_; size_t v___x_2458_; size_t v___x_2459_; size_t v___x_2460_; size_t v___x_2461_; size_t v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2452_ = 32ULL;
v___x_2453_ = lean_uint64_shift_right(v___y_2451_, v___x_2452_);
v_fold_2454_ = lean_uint64_xor(v___y_2451_, v___x_2453_);
v___x_2455_ = 16ULL;
v___x_2456_ = lean_uint64_shift_right(v_fold_2454_, v___x_2455_);
v___x_2457_ = lean_uint64_xor(v_fold_2454_, v___x_2456_);
v___x_2458_ = lean_uint64_to_usize(v___x_2457_);
v___x_2459_ = lean_usize_of_nat(v___x_2449_);
v___x_2460_ = ((size_t)1ULL);
v___x_2461_ = lean_usize_sub(v___x_2459_, v___x_2460_);
v___x_2462_ = lean_usize_land(v___x_2458_, v___x_2461_);
v___x_2463_ = lean_array_uget_borrowed(v_buckets_2448_, v___x_2462_);
v___x_2464_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2447_, v___x_2463_);
return v___x_2464_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_2467_, v_a_2468_);
lean_dec(v_a_2468_);
lean_dec_ref(v_m_2467_);
return v_res_2469_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object* v_declName_2473_, uint8_t v_isMeta_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v_env_2483_; lean_object* v___y_2485_; lean_object* v___x_2498_; 
v___x_2478_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0);
v___x_2479_ = lean_st_ref_get(v___y_2476_);
v_env_2483_ = lean_ctor_get(v___x_2479_, 0);
lean_inc_ref(v_env_2483_);
lean_dec(v___x_2479_);
v___x_2498_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2483_, v_declName_2473_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_dec_ref(v_env_2483_);
lean_dec(v_declName_2473_);
goto v___jp_2480_;
}
else
{
lean_object* v_val_2499_; lean_object* v___x_2500_; lean_object* v_modules_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v_val_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_val_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v___x_2500_ = l_Lean_Environment_header(v_env_2483_);
v_modules_2501_ = lean_ctor_get(v___x_2500_, 3);
lean_inc_ref(v_modules_2501_);
lean_dec_ref(v___x_2500_);
v___x_2502_ = lean_array_get_size(v_modules_2501_);
v___x_2503_ = lean_nat_dec_lt(v_val_2499_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_dec_ref(v_modules_2501_);
lean_dec(v_val_2499_);
lean_dec_ref(v_env_2483_);
lean_dec(v_declName_2473_);
goto v___jp_2480_;
}
else
{
lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___y_2507_; 
v___x_2504_ = lean_array_fget(v_modules_2501_, v_val_2499_);
lean_dec(v_val_2499_);
lean_dec_ref(v_modules_2501_);
v___x_2505_ = lean_st_ref_get(v___y_2476_);
if (v_isMeta_2474_ == 0)
{
lean_dec(v___x_2505_);
v___y_2507_ = v_isMeta_2474_;
goto v___jp_2506_;
}
else
{
lean_object* v_env_2518_; uint8_t v___x_2519_; 
v_env_2518_ = lean_ctor_get(v___x_2505_, 0);
lean_inc_ref(v_env_2518_);
lean_dec(v___x_2505_);
lean_inc(v_declName_2473_);
v___x_2519_ = l_Lean_isMarkedMeta(v_env_2518_, v_declName_2473_);
if (v___x_2519_ == 0)
{
v___y_2507_ = v_isMeta_2474_;
goto v___jp_2506_;
}
else
{
uint8_t v___x_2520_; 
v___x_2520_ = 0;
v___y_2507_ = v___x_2520_;
goto v___jp_2506_;
}
}
v___jp_2506_:
{
lean_object* v_toImport_2508_; lean_object* v_module_2509_; lean_object* v___x_2510_; 
v_toImport_2508_ = lean_ctor_get(v___x_2504_, 0);
lean_inc_ref(v_toImport_2508_);
lean_dec(v___x_2504_);
v_module_2509_ = lean_ctor_get(v_toImport_2508_, 0);
lean_inc(v_module_2509_);
lean_dec_ref(v_toImport_2508_);
lean_inc(v_declName_2473_);
v___x_2510_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2509_, v___y_2507_, v_declName_2473_, v___y_2475_, v___y_2476_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_dec_ref_known(v___x_2510_, 1);
v___x_2511_ = l_Lean_indirectModUseExt;
v___x_2512_ = lean_box(1);
v___x_2513_ = lean_box(0);
lean_inc_ref(v_env_2483_);
v___x_2514_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2478_, v___x_2511_, v_env_2483_, v___x_2512_, v___x_2513_);
v___x_2515_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v___x_2514_, v_declName_2473_);
lean_dec(v___x_2514_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v___x_2516_; 
v___x_2516_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1));
v___y_2485_ = v___x_2516_;
goto v___jp_2484_;
}
else
{
lean_object* v_val_2517_; 
v_val_2517_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_val_2517_);
lean_dec_ref_known(v___x_2515_, 1);
v___y_2485_ = v_val_2517_;
goto v___jp_2484_;
}
}
else
{
lean_dec_ref(v_env_2483_);
lean_dec(v_declName_2473_);
return v___x_2510_;
}
}
}
}
v___jp_2480_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = lean_box(0);
v___x_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
return v___x_2482_;
}
v___jp_2484_:
{
lean_object* v___x_2486_; size_t v_sz_2487_; size_t v___x_2488_; lean_object* v___x_2489_; 
v___x_2486_ = lean_box(0);
v_sz_2487_ = lean_array_size(v___y_2485_);
v___x_2488_ = ((size_t)0ULL);
v___x_2489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v_env_2483_, v_declName_2473_, v___y_2485_, v_sz_2487_, v___x_2488_, v___x_2486_, v___y_2475_, v___y_2476_);
lean_dec_ref(v___y_2485_);
lean_dec_ref(v_env_2483_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2496_ == 0)
{
lean_object* v_unused_2497_; 
v_unused_2497_ = lean_ctor_get(v___x_2489_, 0);
lean_dec(v_unused_2497_);
v___x_2491_ = v___x_2489_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_dec(v___x_2489_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v___x_2486_);
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2486_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
else
{
return v___x_2489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object* v_declName_2521_, lean_object* v_isMeta_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
uint8_t v_isMeta_boxed_2526_; lean_object* v_res_2527_; 
v_isMeta_boxed_2526_ = lean_unbox(v_isMeta_2522_);
v_res_2527_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_declName_2521_, v_isMeta_boxed_2526_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(lean_object* v_as_x27_2528_, lean_object* v_b_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
if (lean_obj_tag(v_as_x27_2528_) == 0)
{
lean_object* v___x_2533_; 
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v_b_2529_);
return v___x_2533_;
}
else
{
lean_object* v_head_2534_; lean_object* v_tail_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; lean_object* v___x_2538_; 
v_head_2534_ = lean_ctor_get(v_as_x27_2528_, 0);
v_tail_2535_ = lean_ctor_get(v_as_x27_2528_, 1);
v___x_2536_ = lean_box(0);
v___x_2537_ = 1;
lean_inc(v_head_2534_);
v___x_2538_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_head_2534_, v___x_2537_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_dec_ref_known(v___x_2538_, 1);
v_as_x27_2528_ = v_tail_2535_;
v_b_2529_ = v___x_2536_;
goto _start;
}
else
{
return v___x_2538_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_2540_, lean_object* v_b_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_2540_, v_b_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v_as_x27_2540_);
return v_res_2545_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = l_Lean_maxRecDepthErrorMessage;
v___x_2552_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
return v___x_2552_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3);
v___x_2554_ = l_Lean_MessageData_ofFormat(v___x_2553_);
return v___x_2554_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4);
v___x_2556_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2));
v___x_2557_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
lean_ctor_set(v___x_2557_, 1, v___x_2555_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(lean_object* v_ref_2558_){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v_ref_2558_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___boxed(lean_object* v_ref_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_2563_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object* v_currNamespace_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2569_, 0, v_currNamespace_2566_);
lean_ctor_set(v___x_2569_, 1, v___y_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(v_currNamespace_2570_, v___y_2571_, v___y_2572_);
lean_dec_ref(v___y_2571_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object* v_env_2574_, lean_object* v_declName_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
uint8_t v___x_2578_; lean_object* v_env_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; uint8_t v___x_2582_; 
v___x_2578_ = 0;
v_env_2579_ = l_Lean_Environment_setExporting(v_env_2574_, v___x_2578_);
lean_inc(v_declName_2575_);
v___x_2580_ = l_Lean_mkPrivateName(v_env_2579_, v_declName_2575_);
v___x_2581_ = 1;
lean_inc_ref(v_env_2579_);
v___x_2582_ = l_Lean_Environment_contains(v_env_2579_, v___x_2580_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2583_ = l_Lean_privateToUserName(v_declName_2575_);
v___x_2584_ = l_Lean_Environment_contains(v_env_2579_, v___x_2583_, v___x_2581_);
v___x_2585_ = lean_box(v___x_2584_);
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
lean_ctor_set(v___x_2586_, 1, v___y_2577_);
return v___x_2586_;
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_dec_ref(v_env_2579_);
lean_dec(v_declName_2575_);
v___x_2587_ = lean_box(v___x_2582_);
v___x_2588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v___y_2577_);
return v___x_2588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object* v_env_2589_, lean_object* v_declName_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(v_env_2589_, v_declName_2590_, v___y_2591_, v___y_2592_);
lean_dec_ref(v___y_2591_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(lean_object* v_x_2594_, lean_object* v___y_2595_){
_start:
{
if (lean_obj_tag(v_x_2594_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; 
v_a_2596_ = lean_ctor_get(v_x_2594_, 0);
lean_inc(v_a_2596_);
v___x_2597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2597_, 0, v_a_2596_);
lean_ctor_set(v___x_2597_, 1, v___y_2595_);
return v___x_2597_;
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2599_; 
v_a_2598_ = lean_ctor_get(v_x_2594_, 0);
lean_inc(v_a_2598_);
v___x_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2599_, 0, v_a_2598_);
lean_ctor_set(v___x_2599_, 1, v___y_2595_);
return v___x_2599_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_2600_, v___y_2601_);
lean_dec_ref(v_x_2600_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object* v_env_2603_, lean_object* v_stx_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2603_, v_stx_2604_, v___y_2605_, v___y_2606_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
if (lean_obj_tag(v_a_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2617_; 
v_a_2609_ = lean_ctor_get(v___x_2607_, 1);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; 
v_unused_2618_ = lean_ctor_get(v___x_2607_, 0);
lean_dec(v_unused_2618_);
v___x_2611_ = v___x_2607_;
v_isShared_2612_ = v_isSharedCheck_2617_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2607_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2617_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; lean_object* v___x_2615_; 
v___x_2613_ = lean_box(0);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___x_2613_);
v___x_2615_ = v___x_2611_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_a_2609_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
else
{
lean_object* v_val_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2647_; 
v_val_2619_ = lean_ctor_get(v_a_2608_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_a_2608_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2621_ = v_a_2608_;
v_isShared_2622_ = v_isSharedCheck_2647_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_val_2619_);
lean_dec(v_a_2608_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2647_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v_snd_2623_; 
v_snd_2623_ = lean_ctor_get(v_val_2619_, 1);
lean_inc(v_snd_2623_);
lean_dec(v_val_2619_);
if (lean_obj_tag(v_snd_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2633_; 
lean_del_object(v___x_2621_);
v_a_2624_ = lean_ctor_get(v___x_2607_, 1);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2607_, 2);
v_a_2625_ = lean_ctor_get(v_snd_2623_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_snd_2623_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2627_ = v_snd_2623_;
v_isShared_2628_ = v_isSharedCheck_2633_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v_snd_2623_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2633_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2630_, v_a_2624_);
lean_dec_ref(v___x_2630_);
return v___x_2631_;
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2646_; 
v_a_2634_ = lean_ctor_get(v___x_2607_, 1);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2607_, 2);
v_a_2635_ = lean_ctor_get(v_snd_2623_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_snd_2623_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2637_ = v_snd_2623_;
v_isShared_2638_ = v_isSharedCheck_2646_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v_snd_2623_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2646_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v_a_2635_);
v___x_2640_ = v___x_2621_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_object* v___x_2642_; 
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v___x_2640_);
v___x_2642_ = v___x_2637_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2640_);
v___x_2642_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2642_, v_a_2634_);
lean_dec_ref(v___x_2642_);
return v___x_2643_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2648_; lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
v_a_2648_ = lean_ctor_get(v___x_2607_, 0);
v_a_2649_ = lean_ctor_get(v___x_2607_, 1);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2607_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_inc(v_a_2648_);
lean_dec(v___x_2607_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2648_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object* v_env_2657_, lean_object* v_stx_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(v_env_2657_, v_stx_2658_, v___y_2659_, v___y_2660_);
lean_dec_ref(v___y_2659_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object* v_env_2662_, lean_object* v_currNamespace_2663_, lean_object* v_openDecls_2664_, lean_object* v_n_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = l_Lean_ResolveName_resolveNamespace(v_env_2662_, v_currNamespace_2663_, v_openDecls_2664_, v_n_2665_);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
lean_ctor_set(v___x_2669_, 1, v___y_2667_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object* v_env_2670_, lean_object* v_currNamespace_2671_, lean_object* v_openDecls_2672_, lean_object* v_n_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(v_env_2670_, v_currNamespace_2671_, v_openDecls_2672_, v_n_2673_, v___y_2674_, v___y_2675_);
lean_dec_ref(v___y_2674_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object* v_as_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
if (lean_obj_tag(v_as_2677_) == 0)
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2681_ = lean_box(0);
v___x_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
return v___x_2682_;
}
else
{
lean_object* v_head_2683_; lean_object* v_tail_2684_; lean_object* v_fst_2685_; lean_object* v_snd_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v_scopes_2691_; lean_object* v___x_2692_; lean_object* v_opts_2693_; uint8_t v_hasTrace_2694_; 
v_head_2683_ = lean_ctor_get(v_as_2677_, 0);
lean_inc(v_head_2683_);
v_tail_2684_ = lean_ctor_get(v_as_2677_, 1);
lean_inc(v_tail_2684_);
lean_dec_ref_known(v_as_2677_, 2);
v_fst_2685_ = lean_ctor_get(v_head_2683_, 0);
lean_inc(v_fst_2685_);
v_snd_2686_ = lean_ctor_get(v_head_2683_, 1);
lean_inc(v_snd_2686_);
lean_dec(v_head_2683_);
v___x_2687_ = l_Lean_inheritedTraceOptions;
v___x_2688_ = lean_st_ref_get(v___x_2687_);
v___x_2689_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2690_ = lean_st_ref_get(v___y_2679_);
v_scopes_2691_ = lean_ctor_get(v___x_2690_, 2);
lean_inc(v_scopes_2691_);
lean_dec(v___x_2690_);
v___x_2692_ = l_List_head_x21___redArg(v___x_2689_, v_scopes_2691_);
lean_dec(v_scopes_2691_);
v_opts_2693_ = lean_ctor_get(v___x_2692_, 1);
lean_inc_ref(v_opts_2693_);
lean_dec(v___x_2692_);
v_hasTrace_2694_ = lean_ctor_get_uint8(v_opts_2693_, sizeof(void*)*1);
if (v_hasTrace_2694_ == 0)
{
lean_dec_ref(v_opts_2693_);
lean_dec(v___x_2688_);
lean_dec(v_snd_2686_);
lean_dec(v_fst_2685_);
v_as_2677_ = v_tail_2684_;
goto _start;
}
else
{
lean_object* v___x_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2696_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9));
lean_inc(v_fst_2685_);
v___x_2697_ = l_Lean_Name_append(v___x_2696_, v_fst_2685_);
v___x_2698_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2688_, v_opts_2693_, v___x_2697_);
lean_dec(v___x_2697_);
lean_dec_ref(v_opts_2693_);
lean_dec(v___x_2688_);
if (v___x_2698_ == 0)
{
lean_dec(v_snd_2686_);
lean_dec(v_fst_2685_);
v_as_2677_ = v_tail_2684_;
goto _start;
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2700_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2700_, 0, v_snd_2686_);
v___x_2701_ = l_Lean_MessageData_ofFormat(v___x_2700_);
v___x_2702_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_fst_2685_, v___x_2701_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_dec_ref_known(v___x_2702_, 1);
v_as_2677_ = v_tail_2684_;
goto _start;
}
else
{
lean_dec(v_tail_2684_);
return v___x_2702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object* v_as_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v_as_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object* v_env_2709_, lean_object* v_opts_2710_, lean_object* v_currNamespace_2711_, lean_object* v_openDecls_2712_, lean_object* v_n_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = l_Lean_ResolveName_resolveGlobalName(v_env_2709_, v_opts_2710_, v_currNamespace_2711_, v_openDecls_2712_, v_n_2713_);
v___x_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v___y_2715_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object* v_env_2718_, lean_object* v_opts_2719_, lean_object* v_currNamespace_2720_, lean_object* v_openDecls_2721_, lean_object* v_n_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(v_env_2718_, v_opts_2719_, v_currNamespace_2720_, v_openDecls_2721_, v_n_2722_, v___y_2723_, v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec_ref(v_opts_2719_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object* v_x_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; lean_object* v_env_2732_; lean_object* v___f_2733_; lean_object* v___f_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v_scopes_2737_; lean_object* v___x_2738_; lean_object* v_opts_2739_; lean_object* v___x_2740_; 
v___x_2731_ = lean_st_ref_get(v___y_2729_);
v_env_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc_ref_n(v_env_2732_, 3);
lean_dec(v___x_2731_);
v___f_2733_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2733_, 0, v_env_2732_);
v___f_2734_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2734_, 0, v_env_2732_);
v___x_2735_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2736_ = lean_st_ref_get(v___y_2729_);
v_scopes_2737_ = lean_ctor_get(v___x_2736_, 2);
lean_inc(v_scopes_2737_);
lean_dec(v___x_2736_);
v___x_2738_ = l_List_head_x21___redArg(v___x_2735_, v_scopes_2737_);
lean_dec(v_scopes_2737_);
v_opts_2739_ = lean_ctor_get(v___x_2738_, 1);
lean_inc_ref(v_opts_2739_);
lean_dec(v___x_2738_);
v___x_2740_ = l_Lean_Elab_Command_getScope___redArg(v___y_2729_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v_currNamespace_2742_; lean_object* v___f_2743_; lean_object* v___x_2744_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
v_currNamespace_2742_ = lean_ctor_get(v_a_2741_, 2);
lean_inc_n(v_currNamespace_2742_, 2);
lean_dec(v_a_2741_);
v___f_2743_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2743_, 0, v_currNamespace_2742_);
v___x_2744_ = l_Lean_Elab_Command_getScope___redArg(v___y_2729_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v_openDecls_2746_; lean_object* v___f_2747_; lean_object* v___f_2748_; lean_object* v_methods_2749_; lean_object* v___x_2750_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2744_, 1);
v_openDecls_2746_ = lean_ctor_get(v_a_2745_, 3);
lean_inc_n(v_openDecls_2746_, 2);
lean_dec(v_a_2745_);
lean_inc(v_currNamespace_2742_);
lean_inc_ref(v_env_2732_);
v___f_2747_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2747_, 0, v_env_2732_);
lean_closure_set(v___f_2747_, 1, v_currNamespace_2742_);
lean_closure_set(v___f_2747_, 2, v_openDecls_2746_);
v___f_2748_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2748_, 0, v_env_2732_);
lean_closure_set(v___f_2748_, 1, v_opts_2739_);
lean_closure_set(v___f_2748_, 2, v_currNamespace_2742_);
lean_closure_set(v___f_2748_, 3, v_openDecls_2746_);
v_methods_2749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2749_, 0, v___f_2734_);
lean_ctor_set(v_methods_2749_, 1, v___f_2743_);
lean_ctor_set(v_methods_2749_, 2, v___f_2733_);
lean_ctor_set(v_methods_2749_, 3, v___f_2747_);
lean_ctor_set(v_methods_2749_, 4, v___f_2748_);
v___x_2750_ = l_Lean_Elab_Command_getRef___redArg(v___y_2728_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2752_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v___x_2752_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2728_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v_currRecDepth_2754_; lean_object* v_quotContext_x3f_2755_; lean_object* v_a_2757_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
v_currRecDepth_2754_ = lean_ctor_get(v___y_2728_, 2);
v_quotContext_x3f_2755_ = lean_ctor_get(v___y_2728_, 5);
if (lean_obj_tag(v_quotContext_x3f_2755_) == 0)
{
lean_object* v___x_2831_; lean_object* v_a_2832_; 
v___x_2831_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_2729_);
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref(v___x_2831_);
v_a_2757_ = v_a_2832_;
goto v___jp_2756_;
}
else
{
lean_object* v_val_2833_; 
v_val_2833_ = lean_ctor_get(v_quotContext_x3f_2755_, 0);
lean_inc(v_val_2833_);
v_a_2757_ = v_val_2833_;
goto v___jp_2756_;
}
v___jp_2756_:
{
lean_object* v___x_2758_; lean_object* v_maxRecDepth_2759_; lean_object* v___x_2760_; lean_object* v_nextMacroScope_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2758_ = lean_st_ref_get(v___y_2729_);
v_maxRecDepth_2759_ = lean_ctor_get(v___x_2758_, 5);
lean_inc(v_maxRecDepth_2759_);
lean_dec(v___x_2758_);
v___x_2760_ = lean_st_ref_get(v___y_2729_);
v_nextMacroScope_2761_ = lean_ctor_get(v___x_2760_, 4);
lean_inc(v_nextMacroScope_2761_);
lean_dec(v___x_2760_);
lean_inc(v_currRecDepth_2754_);
v___x_2762_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2762_, 0, v_methods_2749_);
lean_ctor_set(v___x_2762_, 1, v_a_2757_);
lean_ctor_set(v___x_2762_, 2, v_a_2753_);
lean_ctor_set(v___x_2762_, 3, v_currRecDepth_2754_);
lean_ctor_set(v___x_2762_, 4, v_maxRecDepth_2759_);
lean_ctor_set(v___x_2762_, 5, v_a_2751_);
v___x_2763_ = lean_box(0);
v___x_2764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2764_, 0, v_nextMacroScope_2761_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
lean_ctor_set(v___x_2764_, 2, v___x_2763_);
v___x_2765_ = lean_apply_2(v_x_2727_, v___x_2762_, v___x_2764_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v_a_2767_; lean_object* v_macroScope_2768_; lean_object* v_traceMsgs_2769_; lean_object* v_expandedMacroDecls_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 1);
lean_inc(v_a_2766_);
v_a_2767_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2765_, 2);
v_macroScope_2768_ = lean_ctor_get(v_a_2766_, 0);
lean_inc(v_macroScope_2768_);
v_traceMsgs_2769_ = lean_ctor_get(v_a_2766_, 1);
lean_inc(v_traceMsgs_2769_);
v_expandedMacroDecls_2770_ = lean_ctor_get(v_a_2766_, 2);
lean_inc(v_expandedMacroDecls_2770_);
lean_dec(v_a_2766_);
v___x_2771_ = lean_box(0);
v___x_2772_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_expandedMacroDecls_2770_, v___x_2771_, v___y_2728_, v___y_2729_);
lean_dec(v_expandedMacroDecls_2770_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v___x_2773_; lean_object* v_env_2774_; lean_object* v_messages_2775_; lean_object* v_scopes_2776_; lean_object* v_usedQuotCtxts_2777_; lean_object* v_maxRecDepth_2778_; lean_object* v_ngen_2779_; lean_object* v_auxDeclNGen_2780_; lean_object* v_infoState_2781_; lean_object* v_traceState_2782_; lean_object* v_snapshotTasks_2783_; lean_object* v_prevLinterStates_2784_; lean_object* v_codeQualityEntryTasks_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2811_; 
lean_dec_ref_known(v___x_2772_, 1);
v___x_2773_ = lean_st_ref_take(v___y_2729_);
v_env_2774_ = lean_ctor_get(v___x_2773_, 0);
v_messages_2775_ = lean_ctor_get(v___x_2773_, 1);
v_scopes_2776_ = lean_ctor_get(v___x_2773_, 2);
v_usedQuotCtxts_2777_ = lean_ctor_get(v___x_2773_, 3);
v_maxRecDepth_2778_ = lean_ctor_get(v___x_2773_, 5);
v_ngen_2779_ = lean_ctor_get(v___x_2773_, 6);
v_auxDeclNGen_2780_ = lean_ctor_get(v___x_2773_, 7);
v_infoState_2781_ = lean_ctor_get(v___x_2773_, 8);
v_traceState_2782_ = lean_ctor_get(v___x_2773_, 9);
v_snapshotTasks_2783_ = lean_ctor_get(v___x_2773_, 10);
v_prevLinterStates_2784_ = lean_ctor_get(v___x_2773_, 11);
v_codeQualityEntryTasks_2785_ = lean_ctor_get(v___x_2773_, 12);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2811_ == 0)
{
lean_object* v_unused_2812_; 
v_unused_2812_ = lean_ctor_get(v___x_2773_, 4);
lean_dec(v_unused_2812_);
v___x_2787_ = v___x_2773_;
v_isShared_2788_ = v_isSharedCheck_2811_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2785_);
lean_inc(v_prevLinterStates_2784_);
lean_inc(v_snapshotTasks_2783_);
lean_inc(v_traceState_2782_);
lean_inc(v_infoState_2781_);
lean_inc(v_auxDeclNGen_2780_);
lean_inc(v_ngen_2779_);
lean_inc(v_maxRecDepth_2778_);
lean_inc(v_usedQuotCtxts_2777_);
lean_inc(v_scopes_2776_);
lean_inc(v_messages_2775_);
lean_inc(v_env_2774_);
lean_dec(v___x_2773_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2811_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 4, v_macroScope_2768_);
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_env_2774_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_messages_2775_);
lean_ctor_set(v_reuseFailAlloc_2810_, 2, v_scopes_2776_);
lean_ctor_set(v_reuseFailAlloc_2810_, 3, v_usedQuotCtxts_2777_);
lean_ctor_set(v_reuseFailAlloc_2810_, 4, v_macroScope_2768_);
lean_ctor_set(v_reuseFailAlloc_2810_, 5, v_maxRecDepth_2778_);
lean_ctor_set(v_reuseFailAlloc_2810_, 6, v_ngen_2779_);
lean_ctor_set(v_reuseFailAlloc_2810_, 7, v_auxDeclNGen_2780_);
lean_ctor_set(v_reuseFailAlloc_2810_, 8, v_infoState_2781_);
lean_ctor_set(v_reuseFailAlloc_2810_, 9, v_traceState_2782_);
lean_ctor_set(v_reuseFailAlloc_2810_, 10, v_snapshotTasks_2783_);
lean_ctor_set(v_reuseFailAlloc_2810_, 11, v_prevLinterStates_2784_);
lean_ctor_set(v_reuseFailAlloc_2810_, 12, v_codeQualityEntryTasks_2785_);
v___x_2790_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = lean_st_ref_put(v___y_2729_, v___x_2790_);
v___x_2792_ = l_List_reverse___redArg(v_traceMsgs_2769_);
v___x_2793_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v___x_2792_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2800_ == 0)
{
lean_object* v_unused_2801_; 
v_unused_2801_ = lean_ctor_get(v___x_2793_, 0);
lean_dec(v_unused_2801_);
v___x_2795_ = v___x_2793_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_dec(v___x_2793_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 0, v_a_2767_);
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2767_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v_a_2767_);
v_a_2802_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2793_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2793_);
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
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec(v_traceMsgs_2769_);
lean_dec(v_macroScope_2768_);
lean_dec(v_a_2767_);
v_a_2813_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2772_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2772_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
else
{
lean_object* v_a_2821_; 
v_a_2821_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2765_, 2);
if (lean_obj_tag(v_a_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v_a_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; 
v_a_2822_ = lean_ctor_get(v_a_2821_, 0);
lean_inc(v_a_2822_);
v_a_2823_ = lean_ctor_get(v_a_2821_, 1);
lean_inc_ref(v_a_2823_);
lean_dec_ref_known(v_a_2821_, 2);
v___x_2824_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0));
v___x_2825_ = lean_string_dec_eq(v_a_2823_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2826_, 0, v_a_2823_);
v___x_2827_ = l_Lean_MessageData_ofFormat(v___x_2826_);
v___x_2828_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_a_2822_, v___x_2827_, v___y_2728_, v___y_2729_);
lean_dec(v_a_2822_);
return v___x_2828_;
}
else
{
lean_object* v___x_2829_; 
lean_dec_ref(v_a_2823_);
v___x_2829_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_a_2822_);
return v___x_2829_;
}
}
else
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_2830_;
}
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_a_2751_);
lean_dec_ref_known(v_methods_2749_, 5);
lean_dec_ref(v_x_2727_);
v_a_2834_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2752_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2752_);
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
lean_dec_ref_known(v_methods_2749_, 5);
lean_dec_ref(v_x_2727_);
v_a_2842_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2750_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2750_);
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
lean_dec_ref(v___f_2743_);
lean_dec(v_currNamespace_2742_);
lean_dec_ref(v_opts_2739_);
lean_dec_ref(v___f_2734_);
lean_dec_ref(v___f_2733_);
lean_dec_ref(v_env_2732_);
lean_dec_ref(v_x_2727_);
v_a_2850_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2744_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2744_);
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
lean_dec_ref(v_opts_2739_);
lean_dec_ref(v___f_2734_);
lean_dec_ref(v___f_2733_);
lean_dec_ref(v_env_2732_);
lean_dec_ref(v_x_2727_);
v_a_2858_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2740_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2740_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object* v_x_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object* v_x_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___x_2914_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_2915_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_2956_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
lean_inc(v_x_2910_);
v___x_2957_ = l_Lean_Syntax_isOfKind(v_x_2910_, v___x_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; 
lean_dec(v_x_2910_);
v___x_2958_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_2958_;
}
else
{
lean_object* v___x_2959_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; uint8_t v___y_3019_; lean_object* v___y_3020_; size_t v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; uint8_t v___y_3110_; lean_object* v___y_3111_; size_t v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; uint8_t v___y_3150_; size_t v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; uint8_t v___y_3187_; lean_object* v___y_3188_; size_t v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; uint8_t v___y_3225_; size_t v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v_expectedType_x3f_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v_prio_x3f_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v_name_x3f_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v_prec_x3f_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v_attrs_x3f_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v_doc_x3f_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v___x_2959_ = lean_unsigned_to_nat(0u);
v___x_3436_ = l_Lean_Syntax_getArg(v_x_2910_, v___x_2959_);
v___x_3437_ = l_Lean_Syntax_isNone(v___x_3436_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___x_3438_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3436_);
v___x_3439_ = l_Lean_Syntax_matchesNull(v___x_3436_, v___x_3438_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; 
lean_dec(v___x_3436_);
lean_dec(v_x_2910_);
v___x_3440_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3440_;
}
else
{
lean_object* v_doc_x3f_3441_; lean_object* v___x_3442_; uint8_t v___x_3443_; 
v_doc_x3f_3441_ = l_Lean_Syntax_getArg(v___x_3436_, v___x_2959_);
lean_dec(v___x_3436_);
v___x_3442_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__6));
lean_inc(v_doc_x3f_3441_);
v___x_3443_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3441_, v___x_3442_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; 
lean_dec(v_doc_x3f_3441_);
lean_dec(v_x_2910_);
v___x_3444_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3444_;
}
else
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3445_, 0, v_doc_x3f_3441_);
v_doc_x3f_3420_ = v___x_3445_;
v___y_3421_ = v_a_2911_;
v___y_3422_ = v_a_2912_;
goto v___jp_3419_;
}
}
}
else
{
lean_object* v___x_3446_; 
lean_dec(v___x_3436_);
v___x_3446_ = lean_box(0);
v_doc_x3f_3420_ = v___x_3446_;
v___y_3421_ = v_a_2911_;
v___y_3422_ = v_a_2912_;
goto v___jp_3419_;
}
v___jp_2960_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
lean_inc_ref_n(v___y_2972_, 2);
v___x_2977_ = l_Array_append___redArg(v___y_2972_, v___y_2976_);
lean_dec_ref(v___y_2976_);
lean_inc_n(v___y_2962_, 3);
lean_inc_n(v___y_2964_, 6);
v___x_2978_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2978_, 0, v___y_2964_);
lean_ctor_set(v___x_2978_, 1, v___y_2962_);
lean_ctor_set(v___x_2978_, 2, v___x_2977_);
v___x_2979_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2979_, 0, v___y_2964_);
lean_ctor_set(v___x_2979_, 1, v___y_2962_);
lean_ctor_set(v___x_2979_, 2, v___y_2972_);
lean_inc_ref(v___x_2979_);
lean_inc(v___y_2961_);
v___x_2980_ = l_Lean_Syntax_node1(v___y_2964_, v___y_2961_, v___x_2979_);
lean_inc_ref(v___y_2965_);
v___x_2981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___y_2964_);
lean_ctor_set(v___x_2981_, 1, v___y_2965_);
lean_inc_ref(v___y_2966_);
v___x_2982_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___y_2964_);
lean_ctor_set(v___x_2982_, 1, v___y_2966_);
v___x_2983_ = l_Lean_Syntax_node2(v___y_2964_, v___y_2962_, v___x_2982_, v___y_2967_);
if (lean_obj_tag(v___y_2973_) == 1)
{
lean_object* v_val_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v_val_2984_ = lean_ctor_get(v___y_2973_, 0);
lean_inc(v_val_2984_);
lean_dec_ref_known(v___y_2973_, 1);
v___x_2985_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___y_2964_);
v___x_2986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___y_2964_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = l_Array_mkArray2___redArg(v___x_2986_, v_val_2984_);
v___y_2917_ = v___x_2980_;
v___y_2918_ = v___y_2962_;
v___y_2919_ = v___y_2963_;
v___y_2920_ = v___x_2981_;
v___y_2921_ = v___y_2964_;
v___y_2922_ = v___x_2978_;
v___y_2923_ = v___x_2983_;
v___y_2924_ = v___y_2968_;
v___y_2925_ = v___y_2969_;
v___y_2926_ = v___y_2970_;
v___y_2927_ = v___y_2971_;
v___y_2928_ = v___y_2972_;
v___y_2929_ = v___x_2979_;
v___y_2930_ = v___y_2974_;
v___y_2931_ = v___y_2975_;
v___y_2932_ = v___x_2987_;
goto v___jp_2916_;
}
else
{
lean_object* v___x_2988_; 
lean_dec(v___y_2973_);
v___x_2988_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_2917_ = v___x_2980_;
v___y_2918_ = v___y_2962_;
v___y_2919_ = v___y_2963_;
v___y_2920_ = v___x_2981_;
v___y_2921_ = v___y_2964_;
v___y_2922_ = v___x_2978_;
v___y_2923_ = v___x_2983_;
v___y_2924_ = v___y_2968_;
v___y_2925_ = v___y_2969_;
v___y_2926_ = v___y_2970_;
v___y_2927_ = v___y_2971_;
v___y_2928_ = v___y_2972_;
v___y_2929_ = v___x_2979_;
v___y_2930_ = v___y_2974_;
v___y_2931_ = v___y_2975_;
v___y_2932_ = v___x_2988_;
goto v___jp_2916_;
}
}
v___jp_2989_:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0));
v___x_3005_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
if (lean_obj_tag(v___y_3002_) == 1)
{
lean_object* v_val_3006_; lean_object* v___x_3007_; 
v_val_3006_ = lean_ctor_get(v___y_3002_, 0);
lean_inc(v_val_3006_);
lean_dec_ref_known(v___y_3002_, 1);
v___x_3007_ = l_Array_mkArray1___redArg(v_val_3006_);
v___y_2961_ = v___y_2990_;
v___y_2962_ = v___y_2991_;
v___y_2963_ = v___y_2992_;
v___y_2964_ = v___y_2993_;
v___y_2965_ = v___x_3004_;
v___y_2966_ = v___y_2994_;
v___y_2967_ = v___y_2995_;
v___y_2968_ = v___y_2996_;
v___y_2969_ = v___y_2997_;
v___y_2970_ = v___x_3005_;
v___y_2971_ = v___y_2998_;
v___y_2972_ = v___y_2999_;
v___y_2973_ = v___y_3000_;
v___y_2974_ = v___y_3001_;
v___y_2975_ = v___y_3003_;
v___y_2976_ = v___x_3007_;
goto v___jp_2960_;
}
else
{
lean_object* v___x_3008_; 
lean_dec(v___y_3002_);
v___x_3008_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_2961_ = v___y_2990_;
v___y_2962_ = v___y_2991_;
v___y_2963_ = v___y_2992_;
v___y_2964_ = v___y_2993_;
v___y_2965_ = v___x_3004_;
v___y_2966_ = v___y_2994_;
v___y_2967_ = v___y_2995_;
v___y_2968_ = v___y_2996_;
v___y_2969_ = v___y_2997_;
v___y_2970_ = v___x_3005_;
v___y_2971_ = v___y_2998_;
v___y_2972_ = v___y_2999_;
v___y_2973_ = v___y_3000_;
v___y_2974_ = v___y_3001_;
v___y_2975_ = v___y_3003_;
v___y_2976_ = v___x_3008_;
goto v___jp_2960_;
}
}
v___jp_3009_:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; size_t v_sz_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_inc_ref_n(v___y_3020_, 2);
v___x_3033_ = l_Array_append___redArg(v___y_3020_, v___y_3032_);
lean_dec_ref(v___y_3032_);
lean_inc_n(v___y_3012_, 3);
lean_inc_n(v___y_3030_, 9);
v___x_3034_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3034_, 0, v___y_3030_);
lean_ctor_set(v___x_3034_, 1, v___y_3012_);
lean_ctor_set(v___x_3034_, 2, v___x_3033_);
v___x_3035_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
v___x_3036_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
v___x_3037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___y_3030_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__6));
v___x_3039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___y_3030_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
v___x_3040_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_3041_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___y_3030_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v___x_3042_ = l_Nat_reprFast(v___y_3026_);
v___x_3043_ = lean_box(2);
v___x_3044_ = l_Lean_Syntax_mkNumLit(v___x_3042_, v___x_3043_);
v___x_3045_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___y_3030_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = l_Lean_Syntax_node5(v___y_3030_, v___x_3035_, v___x_3037_, v___x_3039_, v___x_3041_, v___x_3044_, v___x_3046_);
v___x_3048_ = l_Lean_Syntax_node1(v___y_3030_, v___y_3012_, v___x_3047_);
v_sz_3049_ = lean_array_size(v___y_3011_);
v___x_3050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_3049_, v___y_3021_, v___y_3011_);
v___x_3051_ = l_Array_append___redArg(v___y_3020_, v___x_3050_);
lean_dec_ref(v___x_3050_);
v___x_3052_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3052_, 0, v___y_3030_);
lean_ctor_set(v___x_3052_, 1, v___y_3012_);
lean_ctor_set(v___x_3052_, 2, v___x_3051_);
v___x_3053_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_3054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___y_3030_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = lean_unsigned_to_nat(10u);
v___x_3056_ = lean_mk_empty_array_with_capacity(v___x_3055_);
v___x_3057_ = lean_array_push(v___x_3056_, v___y_3023_);
v___x_3058_ = lean_array_push(v___x_3057_, v___y_3028_);
v___x_3059_ = lean_array_push(v___x_3058_, v___y_3022_);
v___x_3060_ = lean_array_push(v___x_3059_, v___y_3014_);
v___x_3061_ = lean_array_push(v___x_3060_, v___y_3015_);
v___x_3062_ = lean_array_push(v___x_3061_, v___x_3034_);
v___x_3063_ = lean_array_push(v___x_3062_, v___x_3048_);
v___x_3064_ = lean_array_push(v___x_3063_, v___x_3052_);
v___x_3065_ = lean_array_push(v___x_3064_, v___x_3054_);
lean_inc(v___y_3016_);
v___x_3066_ = lean_array_push(v___x_3065_, v___y_3016_);
lean_inc(v___y_3031_);
v___x_3067_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3067_, 0, v___y_3030_);
lean_ctor_set(v___x_3067_, 1, v___y_3031_);
lean_ctor_set(v___x_3067_, 2, v___x_3066_);
v___x_3068_ = l_Lean_Elab_Command_elabSyntax(v___x_3067_, v___y_3017_, v___y_3013_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_a_3069_);
lean_dec_ref_known(v___x_3068_, 1);
v___x_3070_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3043_);
lean_ctor_set(v___x_3070_, 1, v_a_3069_);
lean_ctor_set(v___x_3070_, 2, v___y_3018_);
v___x_3071_ = l_Lean_Elab_Command_getRef___redArg(v___y_3017_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3071_, 1);
v___x_3073_ = l_Lean_SourceInfo_fromRef(v_a_3072_, v___y_3019_);
lean_dec(v_a_3072_);
v___x_3074_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3017_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_quotContext_x3f_3075_; 
lean_dec_ref_known(v___x_3074_, 1);
v_quotContext_x3f_3075_ = lean_ctor_get(v___y_3017_, 5);
if (lean_obj_tag(v_quotContext_x3f_3075_) == 0)
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3013_);
lean_dec_ref(v___x_3076_);
v___y_2990_ = v___y_3010_;
v___y_2991_ = v___y_3012_;
v___y_2992_ = v___y_3013_;
v___y_2993_ = v___x_3073_;
v___y_2994_ = v___x_3053_;
v___y_2995_ = v___y_3016_;
v___y_2996_ = v___y_3017_;
v___y_2997_ = v___x_3070_;
v___y_2998_ = v___x_3045_;
v___y_2999_ = v___y_3020_;
v___y_3000_ = v___y_3025_;
v___y_3001_ = v___y_3024_;
v___y_3002_ = v___y_3027_;
v___y_3003_ = v___y_3029_;
goto v___jp_2989_;
}
else
{
v___y_2990_ = v___y_3010_;
v___y_2991_ = v___y_3012_;
v___y_2992_ = v___y_3013_;
v___y_2993_ = v___x_3073_;
v___y_2994_ = v___x_3053_;
v___y_2995_ = v___y_3016_;
v___y_2996_ = v___y_3017_;
v___y_2997_ = v___x_3070_;
v___y_2998_ = v___x_3045_;
v___y_2999_ = v___y_3020_;
v___y_3000_ = v___y_3025_;
v___y_3001_ = v___y_3024_;
v___y_3002_ = v___y_3027_;
v___y_3003_ = v___y_3029_;
goto v___jp_2989_;
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec(v___x_3073_);
lean_dec_ref_known(v___x_3070_, 3);
lean_dec(v___y_3029_);
lean_dec(v___y_3027_);
lean_dec(v___y_3025_);
lean_dec(v___y_3016_);
v_a_3077_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3074_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3074_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec_ref_known(v___x_3070_, 3);
lean_dec(v___y_3029_);
lean_dec(v___y_3027_);
lean_dec(v___y_3025_);
lean_dec(v___y_3016_);
v_a_3085_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3071_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3071_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec(v___y_3029_);
lean_dec(v___y_3027_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3016_);
v_a_3093_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3068_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3068_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
v___jp_3101_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_inc_ref(v___y_3111_);
v___x_3125_ = l_Array_append___redArg(v___y_3111_, v___y_3124_);
lean_dec_ref(v___y_3124_);
lean_inc(v___y_3104_);
lean_inc(v___y_3123_);
v___x_3126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3126_, 0, v___y_3123_);
lean_ctor_set(v___x_3126_, 1, v___y_3104_);
lean_ctor_set(v___x_3126_, 2, v___x_3125_);
if (lean_obj_tag(v___y_3113_) == 1)
{
lean_object* v_val_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v_val_3127_ = lean_ctor_get(v___y_3113_, 0);
lean_inc(v_val_3127_);
lean_dec_ref_known(v___y_3113_, 1);
v___x_3128_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
v___x_3129_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___y_3123_, 5);
v___x_3130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___y_3123_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__9));
v___x_3132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___y_3123_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_3134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___y_3123_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___y_3123_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = l_Lean_Syntax_node5(v___y_3123_, v___x_3128_, v___x_3130_, v___x_3132_, v___x_3134_, v_val_3127_, v___x_3136_);
v___x_3138_ = l_Array_mkArray1___redArg(v___x_3137_);
v___y_3010_ = v___y_3102_;
v___y_3011_ = v___y_3103_;
v___y_3012_ = v___y_3104_;
v___y_3013_ = v___y_3105_;
v___y_3014_ = v___y_3106_;
v___y_3015_ = v___x_3126_;
v___y_3016_ = v___y_3107_;
v___y_3017_ = v___y_3108_;
v___y_3018_ = v___y_3109_;
v___y_3019_ = v___y_3110_;
v___y_3020_ = v___y_3111_;
v___y_3021_ = v___y_3112_;
v___y_3022_ = v___y_3114_;
v___y_3023_ = v___y_3115_;
v___y_3024_ = v___y_3118_;
v___y_3025_ = v___y_3117_;
v___y_3026_ = v___y_3116_;
v___y_3027_ = v___y_3120_;
v___y_3028_ = v___y_3119_;
v___y_3029_ = v___y_3121_;
v___y_3030_ = v___y_3123_;
v___y_3031_ = v___y_3122_;
v___y_3032_ = v___x_3138_;
goto v___jp_3009_;
}
else
{
lean_object* v___x_3139_; 
lean_dec(v___y_3113_);
v___x_3139_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_3010_ = v___y_3102_;
v___y_3011_ = v___y_3103_;
v___y_3012_ = v___y_3104_;
v___y_3013_ = v___y_3105_;
v___y_3014_ = v___y_3106_;
v___y_3015_ = v___x_3126_;
v___y_3016_ = v___y_3107_;
v___y_3017_ = v___y_3108_;
v___y_3018_ = v___y_3109_;
v___y_3019_ = v___y_3110_;
v___y_3020_ = v___y_3111_;
v___y_3021_ = v___y_3112_;
v___y_3022_ = v___y_3114_;
v___y_3023_ = v___y_3115_;
v___y_3024_ = v___y_3118_;
v___y_3025_ = v___y_3117_;
v___y_3026_ = v___y_3116_;
v___y_3027_ = v___y_3120_;
v___y_3028_ = v___y_3119_;
v___y_3029_ = v___y_3121_;
v___y_3030_ = v___y_3123_;
v___y_3031_ = v___y_3122_;
v___y_3032_ = v___x_3139_;
goto v___jp_3009_;
}
}
v___jp_3140_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
lean_inc_ref(v___y_3152_);
v___x_3165_ = l_Array_append___redArg(v___y_3152_, v___y_3164_);
lean_dec_ref(v___y_3164_);
lean_inc(v___y_3143_);
lean_inc(v___y_3163_);
v___x_3166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3166_, 0, v___y_3163_);
lean_ctor_set(v___x_3166_, 1, v___y_3143_);
lean_ctor_set(v___x_3166_, 2, v___x_3165_);
v___x_3167_ = l_Lean_SourceInfo_fromRef(v___y_3144_, v___x_2957_);
lean_dec(v___y_3144_);
lean_inc_ref(v___y_3153_);
v___x_3168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
lean_ctor_set(v___x_3168_, 1, v___y_3153_);
if (lean_obj_tag(v___y_3146_) == 1)
{
lean_object* v_val_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_val_3169_ = lean_ctor_get(v___y_3146_, 0);
lean_inc(v_val_3169_);
lean_dec_ref_known(v___y_3146_, 1);
v___x_3170_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
v___x_3171_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc_n(v___y_3163_, 2);
v___x_3172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___y_3163_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = l_Lean_Syntax_node2(v___y_3163_, v___x_3170_, v___x_3172_, v_val_3169_);
v___x_3174_ = l_Array_mkArray1___redArg(v___x_3173_);
v___y_3102_ = v___y_3141_;
v___y_3103_ = v___y_3142_;
v___y_3104_ = v___y_3143_;
v___y_3105_ = v___y_3145_;
v___y_3106_ = v___x_3168_;
v___y_3107_ = v___y_3147_;
v___y_3108_ = v___y_3148_;
v___y_3109_ = v___y_3149_;
v___y_3110_ = v___y_3150_;
v___y_3111_ = v___y_3152_;
v___y_3112_ = v___y_3151_;
v___y_3113_ = v___y_3154_;
v___y_3114_ = v___y_3155_;
v___y_3115_ = v___y_3156_;
v___y_3116_ = v___y_3159_;
v___y_3117_ = v___y_3158_;
v___y_3118_ = v___y_3157_;
v___y_3119_ = v___x_3166_;
v___y_3120_ = v___y_3160_;
v___y_3121_ = v___y_3161_;
v___y_3122_ = v___y_3162_;
v___y_3123_ = v___y_3163_;
v___y_3124_ = v___x_3174_;
goto v___jp_3101_;
}
else
{
lean_object* v___x_3175_; 
lean_dec(v___y_3146_);
v___x_3175_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_3102_ = v___y_3141_;
v___y_3103_ = v___y_3142_;
v___y_3104_ = v___y_3143_;
v___y_3105_ = v___y_3145_;
v___y_3106_ = v___x_3168_;
v___y_3107_ = v___y_3147_;
v___y_3108_ = v___y_3148_;
v___y_3109_ = v___y_3149_;
v___y_3110_ = v___y_3150_;
v___y_3111_ = v___y_3152_;
v___y_3112_ = v___y_3151_;
v___y_3113_ = v___y_3154_;
v___y_3114_ = v___y_3155_;
v___y_3115_ = v___y_3156_;
v___y_3116_ = v___y_3159_;
v___y_3117_ = v___y_3158_;
v___y_3118_ = v___y_3157_;
v___y_3119_ = v___x_3166_;
v___y_3120_ = v___y_3160_;
v___y_3121_ = v___y_3161_;
v___y_3122_ = v___y_3162_;
v___y_3123_ = v___y_3163_;
v___y_3124_ = v___x_3175_;
goto v___jp_3101_;
}
}
v___jp_3176_:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
lean_inc_ref(v___y_3190_);
v___x_3201_ = l_Array_append___redArg(v___y_3190_, v___y_3200_);
lean_dec_ref(v___y_3200_);
lean_inc(v___y_3179_);
lean_inc(v___y_3199_);
v___x_3202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3202_, 0, v___y_3199_);
lean_ctor_set(v___x_3202_, 1, v___y_3179_);
lean_ctor_set(v___x_3202_, 2, v___x_3201_);
if (lean_obj_tag(v___y_3182_) == 1)
{
lean_object* v_val_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v_val_3203_ = lean_ctor_get(v___y_3182_, 0);
lean_inc(v_val_3203_);
lean_dec_ref_known(v___y_3182_, 1);
v___x_3204_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_3195_);
v___x_3205_ = l_Lean_Name_mkStr4(v___x_2914_, v___x_2915_, v___y_3195_, v___x_3204_);
v___x_3206_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___y_3199_, 4);
v___x_3207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___y_3199_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
lean_inc_ref(v___y_3190_);
v___x_3208_ = l_Array_append___redArg(v___y_3190_, v_val_3203_);
lean_dec(v_val_3203_);
lean_inc(v___y_3179_);
v___x_3209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3209_, 0, v___y_3199_);
lean_ctor_set(v___x_3209_, 1, v___y_3179_);
lean_ctor_set(v___x_3209_, 2, v___x_3208_);
v___x_3210_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_3211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___y_3199_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = l_Lean_Syntax_node3(v___y_3199_, v___x_3205_, v___x_3207_, v___x_3209_, v___x_3211_);
v___x_3213_ = l_Array_mkArray1___redArg(v___x_3212_);
v___y_3141_ = v___y_3177_;
v___y_3142_ = v___y_3178_;
v___y_3143_ = v___y_3179_;
v___y_3144_ = v___y_3180_;
v___y_3145_ = v___y_3181_;
v___y_3146_ = v___y_3183_;
v___y_3147_ = v___y_3184_;
v___y_3148_ = v___y_3185_;
v___y_3149_ = v___y_3186_;
v___y_3150_ = v___y_3187_;
v___y_3151_ = v___y_3189_;
v___y_3152_ = v___y_3190_;
v___y_3153_ = v___y_3188_;
v___y_3154_ = v___y_3191_;
v___y_3155_ = v___y_3192_;
v___y_3156_ = v___x_3202_;
v___y_3157_ = v___y_3195_;
v___y_3158_ = v___y_3194_;
v___y_3159_ = v___y_3193_;
v___y_3160_ = v___y_3196_;
v___y_3161_ = v___y_3197_;
v___y_3162_ = v___y_3198_;
v___y_3163_ = v___y_3199_;
v___y_3164_ = v___x_3213_;
goto v___jp_3140_;
}
else
{
lean_object* v___x_3214_; 
lean_dec(v___y_3182_);
v___x_3214_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_3141_ = v___y_3177_;
v___y_3142_ = v___y_3178_;
v___y_3143_ = v___y_3179_;
v___y_3144_ = v___y_3180_;
v___y_3145_ = v___y_3181_;
v___y_3146_ = v___y_3183_;
v___y_3147_ = v___y_3184_;
v___y_3148_ = v___y_3185_;
v___y_3149_ = v___y_3186_;
v___y_3150_ = v___y_3187_;
v___y_3151_ = v___y_3189_;
v___y_3152_ = v___y_3190_;
v___y_3153_ = v___y_3188_;
v___y_3154_ = v___y_3191_;
v___y_3155_ = v___y_3192_;
v___y_3156_ = v___x_3202_;
v___y_3157_ = v___y_3195_;
v___y_3158_ = v___y_3194_;
v___y_3159_ = v___y_3193_;
v___y_3160_ = v___y_3196_;
v___y_3161_ = v___y_3197_;
v___y_3162_ = v___y_3198_;
v___y_3163_ = v___y_3199_;
v___y_3164_ = v___x_3214_;
goto v___jp_3140_;
}
}
v___jp_3215_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3235_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__12));
v___x_3236_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__13));
v___x_3237_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_3238_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v___y_3232_) == 1)
{
lean_object* v_val_3239_; lean_object* v___x_3240_; 
v_val_3239_ = lean_ctor_get(v___y_3232_, 0);
lean_inc(v_val_3239_);
v___x_3240_ = l_Array_mkArray1___redArg(v_val_3239_);
v___y_3177_ = v___y_3216_;
v___y_3178_ = v___y_3217_;
v___y_3179_ = v___x_3237_;
v___y_3180_ = v___y_3218_;
v___y_3181_ = v___y_3219_;
v___y_3182_ = v___y_3220_;
v___y_3183_ = v___y_3221_;
v___y_3184_ = v___y_3222_;
v___y_3185_ = v___y_3223_;
v___y_3186_ = v___y_3224_;
v___y_3187_ = v___y_3225_;
v___y_3188_ = v___x_3235_;
v___y_3189_ = v___y_3226_;
v___y_3190_ = v___x_3238_;
v___y_3191_ = v___y_3227_;
v___y_3192_ = v___y_3228_;
v___y_3193_ = v___y_3231_;
v___y_3194_ = v___y_3230_;
v___y_3195_ = v___y_3229_;
v___y_3196_ = v___y_3232_;
v___y_3197_ = v___y_3233_;
v___y_3198_ = v___x_3236_;
v___y_3199_ = v___y_3234_;
v___y_3200_ = v___x_3240_;
goto v___jp_3176_;
}
else
{
lean_object* v___x_3241_; 
v___x_3241_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_3177_ = v___y_3216_;
v___y_3178_ = v___y_3217_;
v___y_3179_ = v___x_3237_;
v___y_3180_ = v___y_3218_;
v___y_3181_ = v___y_3219_;
v___y_3182_ = v___y_3220_;
v___y_3183_ = v___y_3221_;
v___y_3184_ = v___y_3222_;
v___y_3185_ = v___y_3223_;
v___y_3186_ = v___y_3224_;
v___y_3187_ = v___y_3225_;
v___y_3188_ = v___x_3235_;
v___y_3189_ = v___y_3226_;
v___y_3190_ = v___x_3238_;
v___y_3191_ = v___y_3227_;
v___y_3192_ = v___y_3228_;
v___y_3193_ = v___y_3231_;
v___y_3194_ = v___y_3230_;
v___y_3195_ = v___y_3229_;
v___y_3196_ = v___y_3232_;
v___y_3197_ = v___y_3233_;
v___y_3198_ = v___x_3236_;
v___y_3199_ = v___y_3234_;
v___y_3200_ = v___x_3241_;
goto v___jp_3176_;
}
}
v___jp_3242_:
{
lean_object* v___x_3259_; lean_object* v_args_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3259_ = l_Lean_Syntax_getArg(v___y_3252_, v___y_3247_);
lean_dec(v___y_3252_);
v_args_3260_ = l_Lean_Syntax_getArgs(v___y_3245_);
lean_dec(v___y_3245_);
v___x_3261_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_3261_, 0, v___y_3250_);
v___x_3262_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v___x_3261_, v___y_3257_, v___y_3258_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; size_t v_sz_3264_; size_t v___x_3265_; lean_object* v___x_3266_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3262_, 1);
v_sz_3264_ = lean_array_size(v_args_3260_);
v___x_3265_ = ((size_t)0ULL);
v___x_3266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_3264_, v___x_3265_, v_args_3260_, v___y_3257_, v___y_3258_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3268_; lean_object* v_fst_3269_; lean_object* v_snd_3270_; lean_object* v___x_3271_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref_known(v___x_3266_, 1);
v___x_3268_ = l_Array_unzip___redArg(v_a_3267_);
lean_dec(v_a_3267_);
v_fst_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_fst_3269_);
v_snd_3270_ = lean_ctor_get(v___x_3268_, 1);
lean_inc(v_snd_3270_);
lean_dec_ref(v___x_3268_);
v___x_3271_ = l_Lean_Elab_Command_getRef___redArg(v___y_3257_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; uint8_t v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3271_, 1);
v___x_3273_ = 0;
v___x_3274_ = l_Lean_SourceInfo_fromRef(v_a_3272_, v___x_3273_);
lean_dec(v_a_3272_);
v___x_3275_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3257_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_quotContext_x3f_3276_; 
lean_dec_ref_known(v___x_3275_, 1);
v_quotContext_x3f_3276_ = lean_ctor_get(v___y_3257_, 5);
if (lean_obj_tag(v_quotContext_x3f_3276_) == 0)
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3258_);
lean_dec_ref(v___x_3277_);
v___y_3216_ = v___y_3243_;
v___y_3217_ = v_fst_3269_;
v___y_3218_ = v___y_3244_;
v___y_3219_ = v___y_3258_;
v___y_3220_ = v___y_3246_;
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3249_;
v___y_3223_ = v___y_3257_;
v___y_3224_ = v_snd_3270_;
v___y_3225_ = v___x_3273_;
v___y_3226_ = v___x_3265_;
v___y_3227_ = v___y_3251_;
v___y_3228_ = v___y_3253_;
v___y_3229_ = v___y_3254_;
v___y_3230_ = v_expectedType_x3f_3256_;
v___y_3231_ = v_a_3263_;
v___y_3232_ = v___y_3255_;
v___y_3233_ = v___x_3259_;
v___y_3234_ = v___x_3274_;
goto v___jp_3215_;
}
else
{
v___y_3216_ = v___y_3243_;
v___y_3217_ = v_fst_3269_;
v___y_3218_ = v___y_3244_;
v___y_3219_ = v___y_3258_;
v___y_3220_ = v___y_3246_;
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3249_;
v___y_3223_ = v___y_3257_;
v___y_3224_ = v_snd_3270_;
v___y_3225_ = v___x_3273_;
v___y_3226_ = v___x_3265_;
v___y_3227_ = v___y_3251_;
v___y_3228_ = v___y_3253_;
v___y_3229_ = v___y_3254_;
v___y_3230_ = v_expectedType_x3f_3256_;
v___y_3231_ = v_a_3263_;
v___y_3232_ = v___y_3255_;
v___y_3233_ = v___x_3259_;
v___y_3234_ = v___x_3274_;
goto v___jp_3215_;
}
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_dec(v___x_3274_);
lean_dec(v_snd_3270_);
lean_dec(v_fst_3269_);
lean_dec(v_a_3263_);
lean_dec(v___x_3259_);
lean_dec(v_expectedType_x3f_3256_);
lean_dec(v___y_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3251_);
lean_dec(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec(v___y_3246_);
lean_dec(v___y_3244_);
v_a_3278_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3275_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3275_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec(v_snd_3270_);
lean_dec(v_fst_3269_);
lean_dec(v_a_3263_);
lean_dec(v___x_3259_);
lean_dec(v_expectedType_x3f_3256_);
lean_dec(v___y_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3251_);
lean_dec(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec(v___y_3246_);
lean_dec(v___y_3244_);
v_a_3286_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3271_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3271_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec(v_a_3263_);
lean_dec(v___x_3259_);
lean_dec(v_expectedType_x3f_3256_);
lean_dec(v___y_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3251_);
lean_dec(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec(v___y_3246_);
lean_dec(v___y_3244_);
v_a_3294_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3266_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3266_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec_ref(v_args_3260_);
lean_dec(v___x_3259_);
lean_dec(v_expectedType_x3f_3256_);
lean_dec(v___y_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3251_);
lean_dec(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec(v___y_3246_);
lean_dec(v___y_3244_);
v_a_3302_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3262_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3262_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
v___jp_3310_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
v___x_3325_ = lean_unsigned_to_nat(8u);
v___x_3326_ = l_Lean_Syntax_getArg(v_x_2910_, v___x_3325_);
v___x_3327_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__15));
lean_inc(v___x_3326_);
v___x_3328_ = l_Lean_Syntax_isOfKind(v___x_3326_, v___x_3327_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3329_; 
lean_dec(v___x_3326_);
lean_dec(v_prio_x3f_3322_);
lean_dec(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec(v_x_2910_);
v___x_3329_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3329_;
}
else
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___x_3330_ = lean_unsigned_to_nat(7u);
v___x_3331_ = l_Lean_Syntax_getArg(v_x_2910_, v___x_3330_);
lean_dec(v_x_2910_);
v___x_3332_ = l_Lean_Syntax_getArg(v___x_3326_, v___y_3321_);
v___x_3333_ = l_Lean_Syntax_getArg(v___x_3326_, v___y_3312_);
v___x_3334_ = l_Lean_Syntax_isNone(v___x_3333_);
if (v___x_3334_ == 0)
{
uint8_t v___x_3335_; 
lean_inc(v___x_3333_);
v___x_3335_ = l_Lean_Syntax_matchesNull(v___x_3333_, v___y_3312_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; 
lean_dec(v___x_3333_);
lean_dec(v___x_3332_);
lean_dec(v___x_3331_);
lean_dec(v___x_3326_);
lean_dec(v_prio_x3f_3322_);
lean_dec(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec(v___y_3313_);
v___x_3336_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3336_;
}
else
{
lean_object* v_expectedType_x3f_3337_; lean_object* v___x_3338_; 
v_expectedType_x3f_3337_ = l_Lean_Syntax_getArg(v___x_3333_, v___y_3321_);
lean_dec(v___x_3333_);
v___x_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3338_, 0, v_expectedType_x3f_3337_);
v___y_3243_ = v___y_3311_;
v___y_3244_ = v___y_3313_;
v___y_3245_ = v___x_3331_;
v___y_3246_ = v___y_3315_;
v___y_3247_ = v___y_3317_;
v___y_3248_ = v___y_3320_;
v___y_3249_ = v___x_3332_;
v___y_3250_ = v_prio_x3f_3322_;
v___y_3251_ = v___y_3314_;
v___y_3252_ = v___x_3326_;
v___y_3253_ = v___y_3316_;
v___y_3254_ = v___y_3318_;
v___y_3255_ = v___y_3319_;
v_expectedType_x3f_3256_ = v___x_3338_;
v___y_3257_ = v___y_3323_;
v___y_3258_ = v___y_3324_;
goto v___jp_3242_;
}
}
else
{
lean_object* v___x_3339_; 
lean_dec(v___x_3333_);
v___x_3339_ = lean_box(0);
v___y_3243_ = v___y_3311_;
v___y_3244_ = v___y_3313_;
v___y_3245_ = v___x_3331_;
v___y_3246_ = v___y_3315_;
v___y_3247_ = v___y_3317_;
v___y_3248_ = v___y_3320_;
v___y_3249_ = v___x_3332_;
v___y_3250_ = v_prio_x3f_3322_;
v___y_3251_ = v___y_3314_;
v___y_3252_ = v___x_3326_;
v___y_3253_ = v___y_3316_;
v___y_3254_ = v___y_3318_;
v___y_3255_ = v___y_3319_;
v_expectedType_x3f_3256_ = v___x_3339_;
v___y_3257_ = v___y_3323_;
v___y_3258_ = v___y_3324_;
goto v___jp_3242_;
}
}
}
v___jp_3340_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; uint8_t v___x_3357_; 
v___x_3355_ = lean_unsigned_to_nat(6u);
v___x_3356_ = l_Lean_Syntax_getArg(v_x_2910_, v___x_3355_);
v___x_3357_ = l_Lean_Syntax_isNone(v___x_3356_);
if (v___x_3357_ == 0)
{
uint8_t v___x_3358_; 
lean_inc(v___x_3356_);
v___x_3358_ = l_Lean_Syntax_matchesNull(v___x_3356_, v___y_3351_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; 
lean_dec(v___x_3356_);
lean_dec(v_name_x3f_3352_);
lean_dec(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec(v___y_3342_);
lean_dec(v_x_2910_);
v___x_3359_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3359_;
}
else
{
lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v___x_3360_ = l_Lean_Syntax_getArg(v___x_3356_, v___x_2959_);
lean_dec(v___x_3356_);
v___x_3361_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
lean_inc(v___x_3360_);
v___x_3362_ = l_Lean_Syntax_isOfKind(v___x_3360_, v___x_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; 
lean_dec(v___x_3360_);
lean_dec(v_name_x3f_3352_);
lean_dec(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec(v___y_3342_);
lean_dec(v_x_2910_);
v___x_3363_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3363_;
}
else
{
lean_object* v_prio_x3f_3364_; lean_object* v___x_3365_; 
v_prio_x3f_3364_ = l_Lean_Syntax_getArg(v___x_3360_, v___y_3344_);
lean_dec(v___x_3360_);
v___x_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3365_, 0, v_prio_x3f_3364_);
v___y_3311_ = v___y_3341_;
v___y_3312_ = v___y_3343_;
v___y_3313_ = v___y_3342_;
v___y_3314_ = v_name_x3f_3352_;
v___y_3315_ = v___y_3345_;
v___y_3316_ = v___y_3346_;
v___y_3317_ = v___y_3347_;
v___y_3318_ = v___y_3348_;
v___y_3319_ = v___y_3350_;
v___y_3320_ = v___y_3349_;
v___y_3321_ = v___y_3351_;
v_prio_x3f_3322_ = v___x_3365_;
v___y_3323_ = v___y_3353_;
v___y_3324_ = v___y_3354_;
goto v___jp_3310_;
}
}
}
else
{
lean_object* v___x_3366_; 
lean_dec(v___x_3356_);
v___x_3366_ = lean_box(0);
v___y_3311_ = v___y_3341_;
v___y_3312_ = v___y_3343_;
v___y_3313_ = v___y_3342_;
v___y_3314_ = v_name_x3f_3352_;
v___y_3315_ = v___y_3345_;
v___y_3316_ = v___y_3346_;
v___y_3317_ = v___y_3347_;
v___y_3318_ = v___y_3348_;
v___y_3319_ = v___y_3350_;
v___y_3320_ = v___y_3349_;
v___y_3321_ = v___y_3351_;
v_prio_x3f_3322_ = v___x_3366_;
v___y_3323_ = v___y_3353_;
v___y_3324_ = v___y_3354_;
goto v___jp_3310_;
}
}
v___jp_3367_:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3381_ = lean_unsigned_to_nat(5u);
v___x_3382_ = l_Lean_Syntax_getArg(v_x_2910_, v___x_3381_);
v___x_3383_ = l_Lean_Syntax_isNone(v___x_3382_);
if (v___x_3383_ == 0)
{
uint8_t v___x_3384_; 
lean_inc(v___x_3382_);
v___x_3384_ = l_Lean_Syntax_matchesNull(v___x_3382_, v___y_3377_);
if (v___x_3384_ == 0)
{
lean_object* v___x_3385_; 
lean_dec(v___x_3382_);
lean_dec(v_prec_x3f_3378_);
lean_dec(v___y_3376_);
lean_dec(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec(v___y_3370_);
lean_dec(v_x_2910_);
v___x_3385_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3385_;
}
else
{
lean_object* v___x_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3386_ = l_Lean_Syntax_getArg(v___x_3382_, v___x_2959_);
lean_dec(v___x_3382_);
v___x_3387_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
lean_inc(v___x_3386_);
v___x_3388_ = l_Lean_Syntax_isOfKind(v___x_3386_, v___x_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; 
lean_dec(v___x_3386_);
lean_dec(v_prec_x3f_3378_);
lean_dec(v___y_3376_);
lean_dec(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec(v___y_3370_);
lean_dec(v_x_2910_);
v___x_3389_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3389_;
}
else
{
lean_object* v_name_x3f_3390_; lean_object* v___x_3391_; 
v_name_x3f_3390_ = l_Lean_Syntax_getArg(v___x_3386_, v___y_3371_);
lean_dec(v___x_3386_);
v___x_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3391_, 0, v_name_x3f_3390_);
v___y_3341_ = v___y_3368_;
v___y_3342_ = v___y_3370_;
v___y_3343_ = v___y_3369_;
v___y_3344_ = v___y_3371_;
v___y_3345_ = v___y_3372_;
v___y_3346_ = v___y_3373_;
v___y_3347_ = v___y_3374_;
v___y_3348_ = v___y_3375_;
v___y_3349_ = v_prec_x3f_3378_;
v___y_3350_ = v___y_3376_;
v___y_3351_ = v___y_3377_;
v_name_x3f_3352_ = v___x_3391_;
v___y_3353_ = v___y_3379_;
v___y_3354_ = v___y_3380_;
goto v___jp_3340_;
}
}
}
else
{
lean_object* v___x_3392_; 
lean_dec(v___x_3382_);
v___x_3392_ = lean_box(0);
v___y_3341_ = v___y_3368_;
v___y_3342_ = v___y_3370_;
v___y_3343_ = v___y_3369_;
v___y_3344_ = v___y_3371_;
v___y_3345_ = v___y_3372_;
v___y_3346_ = v___y_3373_;
v___y_3347_ = v___y_3374_;
v___y_3348_ = v___y_3375_;
v___y_3349_ = v_prec_x3f_3378_;
v___y_3350_ = v___y_3376_;
v___y_3351_ = v___y_3377_;
v_name_x3f_3352_ = v___x_3392_;
v___y_3353_ = v___y_3379_;
v___y_3354_ = v___y_3380_;
goto v___jp_3340_;
}
}
v___jp_3393_:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; uint8_t v___x_3403_; 
v___x_3399_ = lean_unsigned_to_nat(2u);
v___x_3400_ = l_Lean_Syntax_getArg(v_x_2910_, v___x_3399_);
v___x_3401_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_3402_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__3));
lean_inc(v___x_3400_);
v___x_3403_ = l_Lean_Syntax_isOfKind(v___x_3400_, v___x_3402_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; 
lean_dec(v___x_3400_);
lean_dec(v_attrs_x3f_3396_);
lean_dec(v___y_3394_);
lean_dec(v_x_2910_);
v___x_3404_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3404_;
}
else
{
lean_object* v___x_3405_; lean_object* v_tk_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; 
v___x_3405_ = lean_unsigned_to_nat(3u);
v_tk_3406_ = l_Lean_Syntax_getArg(v_x_2910_, v___x_3405_);
v___x_3407_ = lean_unsigned_to_nat(4u);
v___x_3408_ = l_Lean_Syntax_getArg(v_x_2910_, v___x_3407_);
v___x_3409_ = l_Lean_Syntax_isNone(v___x_3408_);
if (v___x_3409_ == 0)
{
uint8_t v___x_3410_; 
lean_inc(v___x_3408_);
v___x_3410_ = l_Lean_Syntax_matchesNull(v___x_3408_, v___y_3395_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; 
lean_dec(v___x_3408_);
lean_dec(v_tk_3406_);
lean_dec(v___x_3400_);
lean_dec(v_attrs_x3f_3396_);
lean_dec(v___y_3394_);
lean_dec(v_x_2910_);
v___x_3411_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3411_;
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3412_ = l_Lean_Syntax_getArg(v___x_3408_, v___x_2959_);
lean_dec(v___x_3408_);
v___x_3413_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
lean_inc(v___x_3412_);
v___x_3414_ = l_Lean_Syntax_isOfKind(v___x_3412_, v___x_3413_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; 
lean_dec(v___x_3412_);
lean_dec(v_tk_3406_);
lean_dec(v___x_3400_);
lean_dec(v_attrs_x3f_3396_);
lean_dec(v___y_3394_);
lean_dec(v_x_2910_);
v___x_3415_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3415_;
}
else
{
lean_object* v_prec_x3f_3416_; lean_object* v___x_3417_; 
v_prec_x3f_3416_ = l_Lean_Syntax_getArg(v___x_3412_, v___y_3395_);
lean_dec(v___x_3412_);
v___x_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3417_, 0, v_prec_x3f_3416_);
v___y_3368_ = v___x_3402_;
v___y_3369_ = v___x_3399_;
v___y_3370_ = v_tk_3406_;
v___y_3371_ = v___x_3405_;
v___y_3372_ = v_attrs_x3f_3396_;
v___y_3373_ = v___x_3400_;
v___y_3374_ = v___x_3407_;
v___y_3375_ = v___x_3401_;
v___y_3376_ = v___y_3394_;
v___y_3377_ = v___y_3395_;
v_prec_x3f_3378_ = v___x_3417_;
v___y_3379_ = v___y_3397_;
v___y_3380_ = v___y_3398_;
goto v___jp_3367_;
}
}
}
else
{
lean_object* v___x_3418_; 
lean_dec(v___x_3408_);
v___x_3418_ = lean_box(0);
v___y_3368_ = v___x_3402_;
v___y_3369_ = v___x_3399_;
v___y_3370_ = v_tk_3406_;
v___y_3371_ = v___x_3405_;
v___y_3372_ = v_attrs_x3f_3396_;
v___y_3373_ = v___x_3400_;
v___y_3374_ = v___x_3407_;
v___y_3375_ = v___x_3401_;
v___y_3376_ = v___y_3394_;
v___y_3377_ = v___y_3395_;
v_prec_x3f_3378_ = v___x_3418_;
v___y_3379_ = v___y_3397_;
v___y_3380_ = v___y_3398_;
goto v___jp_3367_;
}
}
}
v___jp_3419_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3423_ = lean_unsigned_to_nat(1u);
v___x_3424_ = l_Lean_Syntax_getArg(v_x_2910_, v___x_3423_);
v___x_3425_ = l_Lean_Syntax_isNone(v___x_3424_);
if (v___x_3425_ == 0)
{
uint8_t v___x_3426_; 
lean_inc(v___x_3424_);
v___x_3426_ = l_Lean_Syntax_matchesNull(v___x_3424_, v___x_3423_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
lean_dec(v___x_3424_);
lean_dec(v_doc_x3f_3420_);
lean_dec(v_x_2910_);
v___x_3427_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3427_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; 
v___x_3428_ = l_Lean_Syntax_getArg(v___x_3424_, v___x_2959_);
lean_dec(v___x_3424_);
v___x_3429_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v___x_3428_);
v___x_3430_ = l_Lean_Syntax_isOfKind(v___x_3428_, v___x_3429_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; 
lean_dec(v___x_3428_);
lean_dec(v_doc_x3f_3420_);
lean_dec(v_x_2910_);
v___x_3431_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3431_;
}
else
{
lean_object* v___x_3432_; lean_object* v_attrs_x3f_3433_; lean_object* v___x_3434_; 
v___x_3432_ = l_Lean_Syntax_getArg(v___x_3428_, v___x_3423_);
lean_dec(v___x_3428_);
v_attrs_x3f_3433_ = l_Lean_Syntax_getArgs(v___x_3432_);
lean_dec(v___x_3432_);
v___x_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3434_, 0, v_attrs_x3f_3433_);
v___y_3394_ = v_doc_x3f_3420_;
v___y_3395_ = v___x_3423_;
v_attrs_x3f_3396_ = v___x_3434_;
v___y_3397_ = v___y_3421_;
v___y_3398_ = v___y_3422_;
goto v___jp_3393_;
}
}
}
else
{
lean_object* v___x_3435_; 
lean_dec(v___x_3424_);
v___x_3435_ = lean_box(0);
v___y_3394_ = v_doc_x3f_3420_;
v___y_3395_ = v___x_3423_;
v_attrs_x3f_3396_ = v___x_3435_;
v___y_3397_ = v___y_3421_;
v___y_3398_ = v___y_3422_;
goto v___jp_3393_;
}
}
}
v___jp_2916_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
lean_inc_ref(v___y_2928_);
v___x_2933_ = l_Array_append___redArg(v___y_2928_, v___y_2932_);
lean_dec_ref(v___y_2932_);
lean_inc_n(v___y_2918_, 4);
lean_inc_n(v___y_2921_, 11);
v___x_2934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2934_, 0, v___y_2921_);
lean_ctor_set(v___x_2934_, 1, v___y_2918_);
lean_ctor_set(v___x_2934_, 2, v___x_2933_);
v___x_2935_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref_n(v___y_2930_, 3);
v___x_2936_ = l_Lean_Name_mkStr4(v___x_2914_, v___x_2915_, v___y_2930_, v___x_2935_);
v___x_2937_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_2938_ = l_Lean_Name_mkStr4(v___x_2914_, v___x_2915_, v___y_2930_, v___x_2937_);
v___x_2939_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_2940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___y_2921_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__0));
v___x_2942_ = l_Lean_Name_mkStr4(v___x_2914_, v___x_2915_, v___y_2930_, v___x_2941_);
v___x_2943_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__1));
v___x_2944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___y_2921_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
lean_inc_ref(v___y_2927_);
v___x_2945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___y_2921_);
lean_ctor_set(v___x_2945_, 1, v___y_2927_);
v___x_2946_ = l_Lean_Syntax_node3(v___y_2921_, v___x_2942_, v___x_2944_, v___y_2925_, v___x_2945_);
v___x_2947_ = l_Lean_Syntax_node1(v___y_2921_, v___y_2918_, v___x_2946_);
v___x_2948_ = l_Lean_Syntax_node1(v___y_2921_, v___y_2918_, v___x_2947_);
v___x_2949_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_2950_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___y_2921_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = l_Lean_Syntax_node4(v___y_2921_, v___x_2938_, v___x_2940_, v___x_2948_, v___x_2950_, v___y_2931_);
v___x_2952_ = l_Lean_Syntax_node1(v___y_2921_, v___y_2918_, v___x_2951_);
v___x_2953_ = l_Lean_Syntax_node1(v___y_2921_, v___x_2936_, v___x_2952_);
lean_inc(v___y_2929_);
lean_inc(v___y_2926_);
v___x_2954_ = l_Lean_Syntax_node8(v___y_2921_, v___y_2926_, v___y_2922_, v___y_2929_, v___y_2917_, v___y_2920_, v___y_2929_, v___y_2923_, v___x_2934_, v___x_2953_);
v___x_2955_ = l_Lean_Elab_Command_elabCommand(v___x_2954_, v___y_2924_, v___y_2919_);
return v___x_2955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object* v_x_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Lean_Elab_Command_elabElab(v_x_3447_, v_a_3448_, v_a_3449_);
lean_dec(v_a_3449_);
lean_dec_ref(v_a_3448_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object* v_00_u03b1_3452_, lean_object* v_x_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v___x_3456_; 
v___x_3456_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_3453_, v___y_3455_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3457_, lean_object* v_x_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(v_00_u03b1_3457_, v_x_3458_, v___y_3459_, v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec_ref(v_x_3458_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object* v_00_u03b1_3462_, lean_object* v_ref_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
lean_object* v___x_3467_; 
v___x_3467_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_3463_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object* v_00_u03b1_3468_, lean_object* v_ref_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(v_00_u03b1_3468_, v_ref_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object* v_00_u03b1_3474_, lean_object* v_x_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v___x_3479_; 
v___x_3479_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_3475_, v___y_3476_, v___y_3477_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object* v_00_u03b1_3480_, lean_object* v_x_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(v_00_u03b1_3480_, v_x_3481_, v___y_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object* v_as_3486_, lean_object* v_as_x27_3487_, lean_object* v_b_3488_, lean_object* v_a_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_3487_, v_b_3488_, v___y_3490_, v___y_3491_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object* v_as_3494_, lean_object* v_as_x27_3495_, lean_object* v_b_3496_, lean_object* v_a_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(v_as_3494_, v_as_x27_3495_, v_b_3496_, v_a_3497_, v___y_3498_, v___y_3499_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v_as_x27_3495_);
lean_dec(v_as_3494_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3502_, lean_object* v_m_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_3503_, v_a_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3506_, lean_object* v_m_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(v_00_u03b2_3506_, v_m_3507_, v_a_3508_);
lean_dec(v_a_3508_);
lean_dec_ref(v_m_3507_);
return v_res_3509_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_3510_, lean_object* v_x_3511_, lean_object* v_x_3512_){
_start:
{
uint8_t v___x_3513_; 
v___x_3513_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_3511_, v_x_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3514_, lean_object* v_x_3515_, lean_object* v_x_3516_){
_start:
{
uint8_t v_res_3517_; lean_object* v_r_3518_; 
v_res_3517_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(v_00_u03b2_3514_, v_x_3515_, v_x_3516_);
lean_dec_ref(v_x_3516_);
lean_dec_ref(v_x_3515_);
v_r_3518_ = lean_box(v_res_3517_);
return v_r_3518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_3519_, lean_object* v_a_3520_, lean_object* v_x_3521_){
_start:
{
lean_object* v___x_3522_; 
v___x_3522_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_3520_, v_x_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_3523_, lean_object* v_a_3524_, lean_object* v_x_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(v_00_u03b2_3523_, v_a_3524_, v_x_3525_);
lean_dec(v_x_3525_);
lean_dec(v_a_3524_);
return v_res_3526_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(lean_object* v_00_u03b2_3527_, lean_object* v_x_3528_, size_t v_x_3529_, lean_object* v_x_3530_){
_start:
{
uint8_t v___x_3531_; 
v___x_3531_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_3528_, v_x_3529_, v_x_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3532_, lean_object* v_x_3533_, lean_object* v_x_3534_, lean_object* v_x_3535_){
_start:
{
size_t v_x_19034__boxed_3536_; uint8_t v_res_3537_; lean_object* v_r_3538_; 
v_x_19034__boxed_3536_ = lean_unbox_usize(v_x_3534_);
lean_dec(v_x_3534_);
v_res_3537_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(v_00_u03b2_3532_, v_x_3533_, v_x_19034__boxed_3536_, v_x_3535_);
lean_dec_ref(v_x_3535_);
lean_dec_ref(v_x_3533_);
v_r_3538_ = lean_box(v_res_3537_);
return v_r_3538_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3539_, lean_object* v_keys_3540_, lean_object* v_vals_3541_, lean_object* v_heq_3542_, lean_object* v_i_3543_, lean_object* v_k_3544_){
_start:
{
uint8_t v___x_3545_; 
v___x_3545_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_3540_, v_i_3543_, v_k_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b2_3546_, lean_object* v_keys_3547_, lean_object* v_vals_3548_, lean_object* v_heq_3549_, lean_object* v_i_3550_, lean_object* v_k_3551_){
_start:
{
uint8_t v_res_3552_; lean_object* v_r_3553_; 
v_res_3552_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(v_00_u03b2_3546_, v_keys_3547_, v_vals_3548_, v_heq_3549_, v_i_3550_, v_k_3551_);
lean_dec_ref(v_k_3551_);
lean_dec_ref(v_vals_3548_);
lean_dec_ref(v_keys_3547_);
v_r_3553_ = lean_box(v_res_3552_);
return v_r_3553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1(){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3561_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3562_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
v___x_3563_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3564_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElab___boxed), 4, 0);
v___x_3565_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3561_, v___x_3562_, v___x_3563_, v___x_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object* v_a_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3(){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3594_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3595_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6));
v___x_3596_ = l_Lean_addBuiltinDeclarationRanges(v___x_3594_, v___x_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object* v_a_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
return v_res_3598_;
}
}
lean_object* runtime_initialize_Lean_Elab_MacroArgUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ElabRules(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_MacroArgUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ElabRules(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_MacroArgUtil(uint8_t builtin);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_MacroArgUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ElabRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ElabRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ElabRules(builtin);
}
#ifdef __cplusplus
}
#endif
