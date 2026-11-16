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
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1);
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
lean_ctor_set(v___x_156_, 2, v___x_155_);
lean_ctor_set(v___x_156_, 3, v___x_155_);
lean_ctor_set(v___x_156_, 4, v___x_154_);
lean_ctor_set(v___x_156_, 5, v___x_154_);
lean_ctor_set(v___x_156_, 6, v___x_154_);
lean_ctor_set(v___x_156_, 7, v___x_154_);
lean_ctor_set(v___x_156_, 8, v___x_154_);
lean_ctor_set(v___x_156_, 9, v___x_154_);
lean_ctor_set(v___x_156_, 10, v___x_154_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_unsigned_to_nat(32u);
v___x_158_ = lean_mk_empty_array_with_capacity(v___x_157_);
v___x_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_160_ = ((size_t)5ULL);
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_unsigned_to_nat(32u);
v___x_163_ = lean_mk_empty_array_with_capacity(v___x_162_);
v___x_164_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3);
v___x_165_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_163_);
lean_ctor_set(v___x_165_, 2, v___x_161_);
lean_ctor_set(v___x_165_, 3, v___x_161_);
lean_ctor_set_usize(v___x_165_, 4, v___x_160_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_166_ = lean_box(1);
v___x_167_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4);
v___x_168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1);
v___x_169_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
lean_ctor_set(v___x_169_, 2, v___x_166_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(lean_object* v_msgData_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_173_; lean_object* v_env_174_; uint8_t v___x_175_; lean_object* v_env_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v_scopes_179_; lean_object* v___x_180_; lean_object* v_opts_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_173_ = lean_st_ref_get(v___y_171_);
v_env_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc_ref(v_env_174_);
lean_dec(v___x_173_);
v___x_175_ = 0;
v_env_176_ = l_Lean_Environment_setRecordingDeps(v_env_174_, v___x_175_);
v___x_177_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_178_ = lean_st_ref_get(v___y_171_);
v_scopes_179_ = lean_ctor_get(v___x_178_, 2);
lean_inc(v_scopes_179_);
lean_dec(v___x_178_);
v___x_180_ = l_List_head_x21___redArg(v___x_177_, v_scopes_179_);
lean_dec(v_scopes_179_);
v_opts_181_ = lean_ctor_get(v___x_180_, 1);
lean_inc_ref(v_opts_181_);
lean_dec(v___x_180_);
v___x_182_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2);
v___x_183_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5);
v___x_184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_184_, 0, v_env_176_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___x_183_);
lean_ctor_set(v___x_184_, 3, v_opts_181_);
v___x_185_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_msgData_170_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___boxed(lean_object* v_msgData_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(v_msgData_187_, v___y_188_);
lean_dec(v___y_188_);
return v_res_190_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_box(1);
v___x_192_ = l_Lean_MessageData_ofFormat(v___x_191_);
return v___x_192_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__2));
v___x_197_ = l_Lean_MessageData_ofFormat(v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7(lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
if (lean_obj_tag(v_x_199_) == 0)
{
return v_x_198_;
}
else
{
lean_object* v_head_200_; lean_object* v_tail_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_223_; 
v_head_200_ = lean_ctor_get(v_x_199_, 0);
v_tail_201_ = lean_ctor_get(v_x_199_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_223_ == 0)
{
v___x_203_ = v_x_199_;
v_isShared_204_ = v_isSharedCheck_223_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_tail_201_);
lean_inc(v_head_200_);
lean_dec(v_x_199_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_223_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_before_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_221_; 
v_before_205_ = lean_ctor_get(v_head_200_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v_head_200_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; 
v_unused_222_ = lean_ctor_get(v_head_200_, 1);
lean_dec(v_unused_222_);
v___x_207_ = v_head_200_;
v_isShared_208_ = v_isSharedCheck_221_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_before_205_);
lean_dec(v_head_200_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_221_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0);
if (v_isShared_208_ == 0)
{
lean_ctor_set_tag(v___x_207_, 7);
lean_ctor_set(v___x_207_, 1, v___x_209_);
lean_ctor_set(v___x_207_, 0, v_x_198_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_x_198_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_220_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_212_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3);
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 7);
lean_ctor_set(v___x_203_, 1, v___x_212_);
lean_ctor_set(v___x_203_, 0, v___x_211_);
v___x_214_ = v___x_203_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v___x_212_);
v___x_214_ = v_reuseFailAlloc_219_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = l_Lean_MessageData_ofSyntax(v_before_205_);
v___x_216_ = l_Lean_indentD(v___x_215_);
v___x_217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_214_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v_x_198_ = v___x_217_;
v_x_199_ = v_tail_201_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6(lean_object* v_opts_224_, lean_object* v_opt_225_){
_start:
{
lean_object* v_name_226_; lean_object* v_defValue_227_; lean_object* v_map_228_; lean_object* v___x_229_; 
v_name_226_ = lean_ctor_get(v_opt_225_, 0);
v_defValue_227_ = lean_ctor_get(v_opt_225_, 1);
v_map_228_ = lean_ctor_get(v_opts_224_, 0);
v___x_229_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_228_, v_name_226_);
if (lean_obj_tag(v___x_229_) == 0)
{
uint8_t v___x_230_; 
v___x_230_ = lean_unbox(v_defValue_227_);
return v___x_230_;
}
else
{
lean_object* v_val_231_; 
v_val_231_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_val_231_);
lean_dec_ref_known(v___x_229_, 1);
if (lean_obj_tag(v_val_231_) == 1)
{
uint8_t v_v_232_; 
v_v_232_ = lean_ctor_get_uint8(v_val_231_, 0);
lean_dec_ref_known(v_val_231_, 0);
return v_v_232_;
}
else
{
uint8_t v___x_233_; 
lean_dec(v_val_231_);
v___x_233_ = lean_unbox(v_defValue_227_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6___boxed(lean_object* v_opts_234_, lean_object* v_opt_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6(v_opts_234_, v_opt_235_);
lean_dec_ref(v_opt_235_);
lean_dec_ref(v_opts_234_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__1));
v___x_242_ = l_Lean_MessageData_ofFormat(v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg(lean_object* v_msgData_243_, lean_object* v_macroStack_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v_scopes_249_; lean_object* v___x_250_; lean_object* v_opts_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_247_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_248_ = lean_st_ref_get(v___y_245_);
v_scopes_249_ = lean_ctor_get(v___x_248_, 2);
lean_inc(v_scopes_249_);
lean_dec(v___x_248_);
v___x_250_ = l_List_head_x21___redArg(v___x_247_, v_scopes_249_);
lean_dec(v_scopes_249_);
v_opts_251_ = lean_ctor_get(v___x_250_, 1);
lean_inc_ref(v_opts_251_);
lean_dec(v___x_250_);
v___x_252_ = l_Lean_Elab_pp_macroStack;
v___x_253_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6(v_opts_251_, v___x_252_);
lean_dec_ref(v_opts_251_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_dec(v_macroStack_244_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v_msgData_243_);
return v___x_254_;
}
else
{
if (lean_obj_tag(v_macroStack_244_) == 0)
{
lean_object* v___x_255_; 
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v_msgData_243_);
return v___x_255_;
}
else
{
lean_object* v_head_256_; lean_object* v_after_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_272_; 
v_head_256_ = lean_ctor_get(v_macroStack_244_, 0);
lean_inc(v_head_256_);
v_after_257_ = lean_ctor_get(v_head_256_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v_head_256_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v_head_256_, 0);
lean_dec(v_unused_273_);
v___x_259_ = v_head_256_;
v_isShared_260_ = v_isSharedCheck_272_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_after_257_);
lean_dec(v_head_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_272_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0);
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 7);
lean_ctor_set(v___x_259_, 1, v___x_261_);
lean_ctor_set(v___x_259_, 0, v_msgData_243_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_msgData_243_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_261_);
v___x_263_ = v_reuseFailAlloc_271_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v_msgData_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_264_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = l_Lean_MessageData_ofSyntax(v_after_257_);
v___x_267_ = l_Lean_indentD(v___x_266_);
v_msgData_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_268_, 0, v___x_265_);
lean_ctor_set(v_msgData_268_, 1, v___x_267_);
v___x_269_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7(v_msgData_268_, v_macroStack_244_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___boxed(lean_object* v_msgData_274_, lean_object* v_macroStack_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg(v_msgData_274_, v_macroStack_275_, v___y_276_);
lean_dec(v___y_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(lean_object* v_msg_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Elab_Command_getRef___redArg(v___y_280_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v_macroStack_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v_a_288_; lean_object* v___x_289_; lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_298_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
lean_dec_ref_known(v___x_283_, 1);
v_macroStack_285_ = lean_ctor_get(v___y_280_, 4);
v___x_286_ = l_Lean_Elab_getBetterRef(v_a_284_, v_macroStack_285_);
lean_dec(v_a_284_);
v___x_287_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(v_msg_279_, v___y_281_);
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref(v___x_287_);
lean_inc(v_macroStack_285_);
v___x_289_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg(v_a_288_, v_macroStack_285_, v___y_281_);
v_a_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_298_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_286_);
lean_ctor_set(v___x_294_, 1, v_a_290_);
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 1);
lean_ctor_set(v___x_292_, 0, v___x_294_);
v___x_296_ = v___x_292_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec_ref(v_msg_279_);
v_a_299_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_283_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_283_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg___boxed(lean_object* v_msg_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v_msg_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object* v_ref_312_, lean_object* v_msg_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Elab_Command_getRef___redArg(v___y_314_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v_fileName_319_; lean_object* v_fileMap_320_; lean_object* v_currRecDepth_321_; lean_object* v_cmdPos_322_; lean_object* v_macroStack_323_; lean_object* v_quotContext_x3f_324_; lean_object* v_currMacroScope_325_; lean_object* v_snap_x3f_326_; lean_object* v_cancelTk_x3f_327_; uint8_t v_suppressElabErrors_328_; uint8_t v_checkDeprecated_329_; lean_object* v_ref_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_317_, 1);
v_fileName_319_ = lean_ctor_get(v___y_314_, 0);
v_fileMap_320_ = lean_ctor_get(v___y_314_, 1);
v_currRecDepth_321_ = lean_ctor_get(v___y_314_, 2);
v_cmdPos_322_ = lean_ctor_get(v___y_314_, 3);
v_macroStack_323_ = lean_ctor_get(v___y_314_, 4);
v_quotContext_x3f_324_ = lean_ctor_get(v___y_314_, 5);
v_currMacroScope_325_ = lean_ctor_get(v___y_314_, 6);
v_snap_x3f_326_ = lean_ctor_get(v___y_314_, 8);
v_cancelTk_x3f_327_ = lean_ctor_get(v___y_314_, 9);
v_suppressElabErrors_328_ = lean_ctor_get_uint8(v___y_314_, sizeof(void*)*10);
v_checkDeprecated_329_ = lean_ctor_get_uint8(v___y_314_, sizeof(void*)*10 + 1);
v_ref_330_ = l_Lean_replaceRef(v_ref_312_, v_a_318_);
lean_dec(v_a_318_);
lean_inc(v_cancelTk_x3f_327_);
lean_inc(v_snap_x3f_326_);
lean_inc(v_currMacroScope_325_);
lean_inc(v_quotContext_x3f_324_);
lean_inc(v_macroStack_323_);
lean_inc(v_cmdPos_322_);
lean_inc(v_currRecDepth_321_);
lean_inc_ref(v_fileMap_320_);
lean_inc_ref(v_fileName_319_);
v___x_331_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_331_, 0, v_fileName_319_);
lean_ctor_set(v___x_331_, 1, v_fileMap_320_);
lean_ctor_set(v___x_331_, 2, v_currRecDepth_321_);
lean_ctor_set(v___x_331_, 3, v_cmdPos_322_);
lean_ctor_set(v___x_331_, 4, v_macroStack_323_);
lean_ctor_set(v___x_331_, 5, v_quotContext_x3f_324_);
lean_ctor_set(v___x_331_, 6, v_currMacroScope_325_);
lean_ctor_set(v___x_331_, 7, v_ref_330_);
lean_ctor_set(v___x_331_, 8, v_snap_x3f_326_);
lean_ctor_set(v___x_331_, 9, v_cancelTk_x3f_327_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*10, v_suppressElabErrors_328_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*10 + 1, v_checkDeprecated_329_);
v___x_332_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v_msg_313_, v___x_331_, v___y_315_);
lean_dec_ref_known(v___x_331_, 10);
return v___x_332_;
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec_ref(v_msg_313_);
v_a_333_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_317_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_317_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object* v_ref_341_, lean_object* v_msg_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_341_, v_msg_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v_ref_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object* v_k_348_, size_t v_sz_349_, size_t v_i_350_, lean_object* v_bs_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
uint8_t v___x_355_; 
v___x_355_ = lean_usize_dec_lt(v_i_350_, v_sz_349_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
lean_dec(v_k_348_);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v_bs_351_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v_v_358_; lean_object* v___x_359_; lean_object* v_bs_x27_360_; lean_object* v___x_361_; 
v___x_357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0));
v_v_358_ = lean_array_uget(v_bs_351_, v_i_350_);
v___x_359_ = lean_unsigned_to_nat(0u);
v_bs_x27_360_ = lean_array_uset(v_bs_351_, v_i_350_, v___x_359_);
lean_inc(v_k_348_);
v___x_361_ = l_Lean_Elab_Command_checkRuleAltKind(v___x_357_, v_k_348_, v_v_358_, v___y_352_, v___y_353_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; size_t v___x_363_; size_t v___x_364_; lean_object* v___x_365_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v___x_361_, 1);
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_add(v_i_350_, v___x_363_);
v___x_365_ = lean_array_uset(v_bs_x27_360_, v_i_350_, v_a_362_);
v_i_350_ = v___x_364_;
v_bs_351_ = v___x_365_;
goto _start;
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec_ref(v_bs_x27_360_);
lean_dec(v_k_348_);
v_a_367_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_361_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_361_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object* v_k_375_, lean_object* v_sz_376_, lean_object* v_i_377_, lean_object* v_bs_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
size_t v_sz_boxed_382_; size_t v_i_boxed_383_; lean_object* v_res_384_; 
v_sz_boxed_382_ = lean_unbox_usize(v_sz_376_);
lean_dec(v_sz_376_);
v_i_boxed_383_ = lean_unbox_usize(v_i_377_);
lean_dec(v_i_377_);
v_res_384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(v_k_375_, v_sz_boxed_382_, v_i_boxed_383_, v_bs_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_384_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__4));
v___x_391_ = l_String_toRawSubstring_x27(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__8));
v___x_397_ = l_String_toRawSubstring_x27(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__15));
v___x_405_ = l_String_toRawSubstring_x27(v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_421_ = l_String_toRawSubstring_x27(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36(void){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Array_mkArray0___redArg();
return v___x_432_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__39(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__38));
v___x_437_ = l_String_toRawSubstring_x27(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__41));
v___x_441_ = l_String_toRawSubstring_x27(v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__46(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__45));
v___x_447_ = l_String_toRawSubstring_x27(v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__49(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__48));
v___x_451_ = l_String_toRawSubstring_x27(v___x_450_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__52(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__51));
v___x_455_ = l_String_toRawSubstring_x27(v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__55(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_460_ = l_String_toRawSubstring_x27(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__62(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__61));
v___x_470_ = l_Lean_stringToMessageData(v___x_469_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__64(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__63));
v___x_473_ = l_Lean_stringToMessageData(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__75));
v___x_491_ = l_Lean_stringToMessageData(v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__78(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__77));
v___x_494_ = l_Lean_stringToMessageData(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__82(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__81));
v___x_500_ = l_Lean_stringToMessageData(v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object* v_doc_x3f_501_, lean_object* v_attrs_x3f_502_, lean_object* v_attrKind_503_, lean_object* v_k_504_, lean_object* v_cat_x3f_505_, lean_object* v_expty_x3f_506_, lean_object* v_alts_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
size_t v_sz_511_; size_t v___x_512_; lean_object* v___x_513_; 
v_sz_511_ = lean_array_size(v_alts_507_);
v___x_512_ = ((size_t)0ULL);
lean_inc(v_k_504_);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(v_k_504_, v_sz_511_, v___x_512_, v_alts_507_, v_a_508_, v_a_509_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_1530_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_1530_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_1530_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v_a_645_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v_a_797_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v_a_910_; uint8_t v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v_a_1081_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v_a_1195_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v_a_1328_; lean_object* v_catName_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; 
if (lean_obj_tag(v_cat_x3f_505_) == 1)
{
lean_object* v_val_1517_; lean_object* v___x_1518_; 
v_val_1517_ = lean_ctor_get(v_cat_x3f_505_, 0);
v___x_1518_ = l_Lean_TSyntax_getId(v_val_1517_);
v_catName_1339_ = v___x_1518_;
v___y_1340_ = v_a_508_;
v___y_1341_ = v_a_509_;
goto v___jp_1338_;
}
else
{
if (lean_obj_tag(v_expty_x3f_506_) == 1)
{
lean_object* v___x_1519_; 
v___x_1519_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__58));
v_catName_1339_ = v___x_1519_;
v___y_1340_ = v_a_508_;
v___y_1341_ = v_a_509_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_del_object(v___x_516_);
lean_dec(v_a_514_);
lean_dec(v_expty_x3f_506_);
lean_dec(v_k_504_);
lean_dec(v_attrKind_503_);
lean_dec(v_doc_x3f_501_);
v___x_1520_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__82, &l_Lean_Elab_Command_elabElabRulesAux___closed__82_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__82);
v___x_1521_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v___x_1520_, v_a_508_, v_a_509_);
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
v___jp_518_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
lean_inc_ref_n(v___y_525_, 4);
v___x_532_ = l_Array_append___redArg(v___y_525_, v___y_531_);
lean_dec_ref(v___y_531_);
lean_inc_n(v___y_527_, 10);
lean_inc_n(v___y_522_, 35);
v___x_533_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_533_, 0, v___y_522_);
lean_ctor_set(v___x_533_, 1, v___y_527_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
v___x_534_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_535_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_536_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_520_, 11);
v___x_537_ = l_Lean_Name_mkStr4(v___y_520_, v___x_534_, v___x_535_, v___x_536_);
v___x_538_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_539_, 0, v___y_522_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_541_ = l_Lean_Syntax_SepArray_ofElems(v___x_540_, v___y_529_);
lean_dec_ref(v___y_529_);
v___x_542_ = l_Array_append___redArg(v___y_525_, v___x_541_);
lean_dec_ref(v___x_541_);
v___x_543_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_543_, 0, v___y_522_);
lean_ctor_set(v___x_543_, 1, v___y_527_);
lean_ctor_set(v___x_543_, 2, v___x_542_);
v___x_544_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_545_, 0, v___y_522_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = l_Lean_Syntax_node3(v___y_522_, v___x_537_, v___x_539_, v___x_543_, v___x_545_);
v___x_547_ = l_Lean_Syntax_node1(v___y_522_, v___y_527_, v___x_546_);
lean_inc_ref(v___y_519_);
v___x_548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_548_, 0, v___y_522_);
lean_ctor_set(v___x_548_, 1, v___y_519_);
v___x_549_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_550_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_523_, 3);
lean_inc_n(v___y_530_, 3);
v___x_551_ = l_Lean_addMacroScope(v___y_530_, v___x_550_, v___y_523_);
v___x_552_ = lean_box(0);
v___x_553_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_553_, 0, v___y_522_);
lean_ctor_set(v___x_553_, 1, v___x_549_);
lean_ctor_set(v___x_553_, 2, v___x_551_);
lean_ctor_set(v___x_553_, 3, v___x_552_);
v___x_554_ = l_Lean_mkIdent(v_k_504_);
v___x_555_ = l_Lean_Syntax_node2(v___y_522_, v___y_527_, v___x_553_, v___x_554_);
v___x_556_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_557_, 0, v___y_522_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_559_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
v___x_560_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc_ref_n(v___y_521_, 2);
v___x_561_ = l_Lean_Name_mkStr4(v___y_520_, v___y_521_, v___x_559_, v___x_560_);
lean_inc(v___x_561_);
v___x_562_ = l_Lean_addMacroScope(v___y_530_, v___x_561_, v___y_523_);
v___x_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_552_);
v___x_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_552_);
v___x_565_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_565_, 0, v___y_522_);
lean_ctor_set(v___x_565_, 1, v___x_558_);
lean_ctor_set(v___x_565_, 2, v___x_562_);
lean_ctor_set(v___x_565_, 3, v___x_564_);
v___x_566_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_567_, 0, v___y_522_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_569_ = l_Lean_Name_mkStr4(v___y_520_, v___x_534_, v___x_535_, v___x_568_);
v___x_570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_570_, 0, v___y_522_);
lean_ctor_set(v___x_570_, 1, v___x_568_);
v___x_571_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_572_ = l_Lean_Name_mkStr4(v___y_520_, v___x_534_, v___x_535_, v___x_571_);
v___x_573_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_574_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_575_ = l_Lean_addMacroScope(v___y_530_, v___x_574_, v___y_523_);
v___x_576_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_576_, 0, v___y_522_);
lean_ctor_set(v___x_576_, 1, v___x_573_);
lean_ctor_set(v___x_576_, 2, v___x_575_);
lean_ctor_set(v___x_576_, 3, v___x_552_);
lean_inc_ref(v___x_576_);
v___x_577_ = l_Lean_Syntax_node2(v___y_522_, v___y_527_, v___x_576_, v___y_526_);
v___x_578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_578_, 0, v___y_522_);
lean_ctor_set(v___x_578_, 1, v___y_527_);
lean_ctor_set(v___x_578_, 2, v___y_525_);
v___x_579_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_580_, 0, v___y_522_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_582_ = l_Lean_Name_mkStr4(v___y_520_, v___x_534_, v___x_535_, v___x_581_);
v___x_583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_583_, 0, v___y_522_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
v___x_584_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_585_ = l_Lean_Name_mkStr4(v___y_520_, v___x_534_, v___x_535_, v___x_584_);
lean_inc_ref_n(v___x_578_, 3);
v___x_586_ = l_Lean_Syntax_node2(v___y_522_, v___x_585_, v___x_578_, v___x_576_);
v___x_587_ = l_Lean_Syntax_node1(v___y_522_, v___y_527_, v___x_586_);
v___x_588_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_589_, 0, v___y_522_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_591_ = l_Lean_Name_mkStr4(v___y_520_, v___x_534_, v___x_535_, v___x_590_);
v___x_592_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_593_ = l_Lean_Name_mkStr4(v___y_520_, v___x_534_, v___x_535_, v___x_592_);
v___x_594_ = l_Array_append___redArg(v___y_525_, v_a_514_);
lean_dec(v_a_514_);
v___x_595_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_596_, 0, v___y_522_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_598_ = l_Lean_Name_mkStr4(v___y_520_, v___x_534_, v___x_535_, v___x_597_);
v___x_599_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_600_, 0, v___y_522_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = l_Lean_Syntax_node1(v___y_522_, v___x_598_, v___x_600_);
v___x_602_ = l_Lean_Syntax_node1(v___y_522_, v___y_527_, v___x_601_);
v___x_603_ = l_Lean_Syntax_node1(v___y_522_, v___y_527_, v___x_602_);
v___x_604_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_605_ = l_Lean_Name_mkStr4(v___y_520_, v___x_534_, v___x_535_, v___x_604_);
v___x_606_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_607_, 0, v___y_522_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_609_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_610_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_611_ = l_Lean_addMacroScope(v___y_530_, v___x_610_, v___y_523_);
v___x_612_ = l_Lean_Name_mkStr3(v___y_520_, v___y_521_, v___x_608_);
v___x_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_552_);
v___x_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_552_);
v___x_615_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_615_, 0, v___y_522_);
lean_ctor_set(v___x_615_, 1, v___x_609_);
lean_ctor_set(v___x_615_, 2, v___x_611_);
lean_ctor_set(v___x_615_, 3, v___x_614_);
v___x_616_ = l_Lean_Syntax_node2(v___y_522_, v___x_605_, v___x_607_, v___x_615_);
lean_inc_ref(v___x_580_);
v___x_617_ = l_Lean_Syntax_node4(v___y_522_, v___x_593_, v___x_596_, v___x_603_, v___x_580_, v___x_616_);
v___x_618_ = lean_array_push(v___x_594_, v___x_617_);
v___x_619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_619_, 0, v___y_522_);
lean_ctor_set(v___x_619_, 1, v___y_527_);
lean_ctor_set(v___x_619_, 2, v___x_618_);
v___x_620_ = l_Lean_Syntax_node1(v___y_522_, v___x_591_, v___x_619_);
v___x_621_ = l_Lean_Syntax_node6(v___y_522_, v___x_582_, v___x_583_, v___x_578_, v___x_578_, v___x_587_, v___x_589_, v___x_620_);
v___x_622_ = l_Lean_Syntax_node4(v___y_522_, v___x_572_, v___x_577_, v___x_578_, v___x_580_, v___x_621_);
v___x_623_ = l_Lean_Syntax_node2(v___y_522_, v___x_569_, v___x_570_, v___x_622_);
v___x_624_ = lean_unsigned_to_nat(9u);
v___x_625_ = lean_mk_empty_array_with_capacity(v___x_624_);
v___x_626_ = lean_array_push(v___x_625_, v___x_533_);
v___x_627_ = lean_array_push(v___x_626_, v___x_547_);
v___x_628_ = lean_array_push(v___x_627_, v___y_528_);
v___x_629_ = lean_array_push(v___x_628_, v___x_548_);
v___x_630_ = lean_array_push(v___x_629_, v___x_555_);
v___x_631_ = lean_array_push(v___x_630_, v___x_557_);
v___x_632_ = lean_array_push(v___x_631_, v___x_565_);
v___x_633_ = lean_array_push(v___x_632_, v___x_567_);
v___x_634_ = lean_array_push(v___x_633_, v___x_623_);
lean_inc(v___y_524_);
v___x_635_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_635_, 0, v___y_522_);
lean_ctor_set(v___x_635_, 1, v___y_524_);
lean_ctor_set(v___x_635_, 2, v___x_634_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_635_);
v___x_637_ = v___x_516_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
v___jp_639_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_646_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_647_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_648_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_649_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_650_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_651_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_501_) == 1)
{
lean_object* v_val_652_; lean_object* v___x_653_; 
v_val_652_ = lean_ctor_get(v_doc_x3f_501_, 0);
lean_inc(v_val_652_);
lean_dec_ref_known(v_doc_x3f_501_, 1);
v___x_653_ = l_Array_mkArray1___redArg(v_val_652_);
v___y_519_ = v___x_648_;
v___y_520_ = v___x_646_;
v___y_521_ = v___x_647_;
v___y_522_ = v___y_641_;
v___y_523_ = v___y_643_;
v___y_524_ = v___x_649_;
v___y_525_ = v___x_651_;
v___y_526_ = v___y_640_;
v___y_527_ = v___x_650_;
v___y_528_ = v___y_642_;
v___y_529_ = v___y_644_;
v___y_530_ = v_a_645_;
v___y_531_ = v___x_653_;
goto v___jp_518_;
}
else
{
lean_object* v___x_654_; 
lean_dec(v_doc_x3f_501_);
v___x_654_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_519_ = v___x_648_;
v___y_520_ = v___x_646_;
v___y_521_ = v___x_647_;
v___y_522_ = v___y_641_;
v___y_523_ = v___y_643_;
v___y_524_ = v___x_649_;
v___y_525_ = v___x_651_;
v___y_526_ = v___y_640_;
v___y_527_ = v___x_650_;
v___y_528_ = v___y_642_;
v___y_529_ = v___y_644_;
v___y_530_ = v_a_645_;
v___y_531_ = v___x_654_;
goto v___jp_518_;
}
}
v___jp_655_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_inc_ref_n(v___y_663_, 4);
v___x_669_ = l_Array_append___redArg(v___y_663_, v___y_668_);
lean_dec_ref(v___y_668_);
lean_inc_n(v___y_662_, 12);
lean_inc_n(v___y_660_, 42);
v___x_670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_670_, 0, v___y_660_);
lean_ctor_set(v___x_670_, 1, v___y_662_);
lean_ctor_set(v___x_670_, 2, v___x_669_);
v___x_671_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_672_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_673_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_656_, 13);
v___x_674_ = l_Lean_Name_mkStr4(v___y_656_, v___x_671_, v___x_672_, v___x_673_);
v___x_675_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_676_, 0, v___y_660_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_678_ = l_Lean_Syntax_SepArray_ofElems(v___x_677_, v___y_658_);
lean_dec_ref(v___y_658_);
v___x_679_ = l_Array_append___redArg(v___y_663_, v___x_678_);
lean_dec_ref(v___x_678_);
v___x_680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_680_, 0, v___y_660_);
lean_ctor_set(v___x_680_, 1, v___y_662_);
lean_ctor_set(v___x_680_, 2, v___x_679_);
v___x_681_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_682_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_682_, 0, v___y_660_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = l_Lean_Syntax_node3(v___y_660_, v___x_674_, v___x_676_, v___x_680_, v___x_682_);
v___x_684_ = l_Lean_Syntax_node1(v___y_660_, v___y_662_, v___x_683_);
lean_inc_ref(v___y_659_);
v___x_685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_685_, 0, v___y_660_);
lean_ctor_set(v___x_685_, 1, v___y_659_);
v___x_686_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_687_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_664_, 5);
lean_inc_n(v___y_657_, 5);
v___x_688_ = l_Lean_addMacroScope(v___y_657_, v___x_687_, v___y_664_);
v___x_689_ = lean_box(0);
v___x_690_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_690_, 0, v___y_660_);
lean_ctor_set(v___x_690_, 1, v___x_686_);
lean_ctor_set(v___x_690_, 2, v___x_688_);
lean_ctor_set(v___x_690_, 3, v___x_689_);
v___x_691_ = l_Lean_mkIdent(v_k_504_);
v___x_692_ = l_Lean_Syntax_node2(v___y_660_, v___y_662_, v___x_690_, v___x_691_);
v___x_693_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_694_, 0, v___y_660_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__39, &l_Lean_Elab_Command_elabElabRulesAux___closed__39_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__39);
v___x_696_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
lean_inc_ref_n(v___y_666_, 3);
v___x_697_ = l_Lean_Name_mkStr4(v___y_656_, v___y_666_, v___x_672_, v___x_696_);
lean_inc(v___x_697_);
v___x_698_ = l_Lean_addMacroScope(v___y_657_, v___x_697_, v___y_664_);
v___x_699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_689_);
v___x_700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_689_);
v___x_701_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_701_, 0, v___y_660_);
lean_ctor_set(v___x_701_, 1, v___x_695_);
lean_ctor_set(v___x_701_, 2, v___x_698_);
lean_ctor_set(v___x_701_, 3, v___x_700_);
v___x_702_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_703_, 0, v___y_660_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_705_ = l_Lean_Name_mkStr4(v___y_656_, v___x_671_, v___x_672_, v___x_704_);
v___x_706_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_706_, 0, v___y_660_);
lean_ctor_set(v___x_706_, 1, v___x_704_);
v___x_707_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_708_ = l_Lean_Name_mkStr4(v___y_656_, v___x_671_, v___x_672_, v___x_707_);
v___x_709_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_710_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_711_ = l_Lean_addMacroScope(v___y_657_, v___x_710_, v___y_664_);
v___x_712_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_712_, 0, v___y_660_);
lean_ctor_set(v___x_712_, 1, v___x_709_);
lean_ctor_set(v___x_712_, 2, v___x_711_);
lean_ctor_set(v___x_712_, 3, v___x_689_);
v___x_713_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__42, &l_Lean_Elab_Command_elabElabRulesAux___closed__42_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42);
v___x_714_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__43));
v___x_715_ = l_Lean_addMacroScope(v___y_657_, v___x_714_, v___y_664_);
v___x_716_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_716_, 0, v___y_660_);
lean_ctor_set(v___x_716_, 1, v___x_713_);
lean_ctor_set(v___x_716_, 2, v___x_715_);
lean_ctor_set(v___x_716_, 3, v___x_689_);
lean_inc_ref(v___x_716_);
lean_inc_ref(v___x_712_);
v___x_717_ = l_Lean_Syntax_node2(v___y_660_, v___y_662_, v___x_712_, v___x_716_);
v___x_718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_718_, 0, v___y_660_);
lean_ctor_set(v___x_718_, 1, v___y_662_);
lean_ctor_set(v___x_718_, 2, v___y_663_);
v___x_719_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_720_, 0, v___y_660_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__44));
v___x_722_ = l_Lean_Name_mkStr4(v___y_656_, v___x_671_, v___x_672_, v___x_721_);
v___x_723_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__46, &l_Lean_Elab_Command_elabElabRulesAux___closed__46_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__46);
v___x_724_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__47));
v___x_725_ = l_Lean_Name_mkStr4(v___y_656_, v___y_666_, v___x_672_, v___x_724_);
lean_inc(v___x_725_);
v___x_726_ = l_Lean_addMacroScope(v___y_657_, v___x_725_, v___y_664_);
v___x_727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_689_);
v___x_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_689_);
v___x_729_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_729_, 0, v___y_660_);
lean_ctor_set(v___x_729_, 1, v___x_723_);
lean_ctor_set(v___x_729_, 2, v___x_726_);
lean_ctor_set(v___x_729_, 3, v___x_728_);
v___x_730_ = l_Lean_Syntax_node1(v___y_660_, v___y_662_, v___y_665_);
v___x_731_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_732_ = l_Lean_Name_mkStr4(v___y_656_, v___x_671_, v___x_672_, v___x_731_);
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v___y_660_);
lean_ctor_set(v___x_733_, 1, v___x_731_);
v___x_734_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_735_ = l_Lean_Name_mkStr4(v___y_656_, v___x_671_, v___x_672_, v___x_734_);
lean_inc_ref_n(v___x_718_, 4);
v___x_736_ = l_Lean_Syntax_node2(v___y_660_, v___x_735_, v___x_718_, v___x_712_);
v___x_737_ = l_Lean_Syntax_node1(v___y_660_, v___y_662_, v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_739_, 0, v___y_660_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_741_ = l_Lean_Name_mkStr4(v___y_656_, v___x_671_, v___x_672_, v___x_740_);
v___x_742_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_743_ = l_Lean_Name_mkStr4(v___y_656_, v___x_671_, v___x_672_, v___x_742_);
v___x_744_ = l_Array_append___redArg(v___y_663_, v_a_514_);
lean_dec(v_a_514_);
v___x_745_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_746_, 0, v___y_660_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_748_ = l_Lean_Name_mkStr4(v___y_656_, v___x_671_, v___x_672_, v___x_747_);
v___x_749_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_750_, 0, v___y_660_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_Syntax_node1(v___y_660_, v___x_748_, v___x_750_);
v___x_752_ = l_Lean_Syntax_node1(v___y_660_, v___y_662_, v___x_751_);
v___x_753_ = l_Lean_Syntax_node1(v___y_660_, v___y_662_, v___x_752_);
v___x_754_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_755_ = l_Lean_Name_mkStr4(v___y_656_, v___x_671_, v___x_672_, v___x_754_);
v___x_756_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_757_, 0, v___y_660_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_759_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_760_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_761_ = l_Lean_addMacroScope(v___y_657_, v___x_760_, v___y_664_);
v___x_762_ = l_Lean_Name_mkStr3(v___y_656_, v___y_666_, v___x_758_);
v___x_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v___x_689_);
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v___x_689_);
v___x_765_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_765_, 0, v___y_660_);
lean_ctor_set(v___x_765_, 1, v___x_759_);
lean_ctor_set(v___x_765_, 2, v___x_761_);
lean_ctor_set(v___x_765_, 3, v___x_764_);
v___x_766_ = l_Lean_Syntax_node2(v___y_660_, v___x_755_, v___x_757_, v___x_765_);
lean_inc_ref_n(v___x_720_, 2);
v___x_767_ = l_Lean_Syntax_node4(v___y_660_, v___x_743_, v___x_746_, v___x_753_, v___x_720_, v___x_766_);
v___x_768_ = lean_array_push(v___x_744_, v___x_767_);
v___x_769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_769_, 0, v___y_660_);
lean_ctor_set(v___x_769_, 1, v___y_662_);
lean_ctor_set(v___x_769_, 2, v___x_768_);
v___x_770_ = l_Lean_Syntax_node1(v___y_660_, v___x_741_, v___x_769_);
v___x_771_ = l_Lean_Syntax_node6(v___y_660_, v___x_732_, v___x_733_, v___x_718_, v___x_718_, v___x_737_, v___x_739_, v___x_770_);
lean_inc(v___x_708_);
v___x_772_ = l_Lean_Syntax_node4(v___y_660_, v___x_708_, v___x_730_, v___x_718_, v___x_720_, v___x_771_);
lean_inc_ref(v___x_706_);
lean_inc(v___x_705_);
v___x_773_ = l_Lean_Syntax_node2(v___y_660_, v___x_705_, v___x_706_, v___x_772_);
v___x_774_ = l_Lean_Syntax_node2(v___y_660_, v___y_662_, v___x_716_, v___x_773_);
v___x_775_ = l_Lean_Syntax_node2(v___y_660_, v___x_722_, v___x_729_, v___x_774_);
v___x_776_ = l_Lean_Syntax_node4(v___y_660_, v___x_708_, v___x_717_, v___x_718_, v___x_720_, v___x_775_);
v___x_777_ = l_Lean_Syntax_node2(v___y_660_, v___x_705_, v___x_706_, v___x_776_);
v___x_778_ = lean_unsigned_to_nat(9u);
v___x_779_ = lean_mk_empty_array_with_capacity(v___x_778_);
v___x_780_ = lean_array_push(v___x_779_, v___x_670_);
v___x_781_ = lean_array_push(v___x_780_, v___x_684_);
v___x_782_ = lean_array_push(v___x_781_, v___y_667_);
v___x_783_ = lean_array_push(v___x_782_, v___x_685_);
v___x_784_ = lean_array_push(v___x_783_, v___x_692_);
v___x_785_ = lean_array_push(v___x_784_, v___x_694_);
v___x_786_ = lean_array_push(v___x_785_, v___x_701_);
v___x_787_ = lean_array_push(v___x_786_, v___x_703_);
v___x_788_ = lean_array_push(v___x_787_, v___x_777_);
lean_inc(v___y_661_);
v___x_789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_789_, 0, v___y_660_);
lean_ctor_set(v___x_789_, 1, v___y_661_);
lean_ctor_set(v___x_789_, 2, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
v___jp_791_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_798_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_799_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_800_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_801_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_802_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_803_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_501_) == 1)
{
lean_object* v_val_804_; lean_object* v___x_805_; 
v_val_804_ = lean_ctor_get(v_doc_x3f_501_, 0);
lean_inc(v_val_804_);
lean_dec_ref_known(v_doc_x3f_501_, 1);
v___x_805_ = l_Array_mkArray1___redArg(v_val_804_);
v___y_656_ = v___x_798_;
v___y_657_ = v_a_797_;
v___y_658_ = v___y_795_;
v___y_659_ = v___x_800_;
v___y_660_ = v___y_796_;
v___y_661_ = v___x_801_;
v___y_662_ = v___x_802_;
v___y_663_ = v___x_803_;
v___y_664_ = v___y_793_;
v___y_665_ = v___y_792_;
v___y_666_ = v___x_799_;
v___y_667_ = v___y_794_;
v___y_668_ = v___x_805_;
goto v___jp_655_;
}
else
{
lean_object* v___x_806_; 
lean_dec(v_doc_x3f_501_);
v___x_806_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_656_ = v___x_798_;
v___y_657_ = v_a_797_;
v___y_658_ = v___y_795_;
v___y_659_ = v___x_800_;
v___y_660_ = v___y_796_;
v___y_661_ = v___x_801_;
v___y_662_ = v___x_802_;
v___y_663_ = v___x_803_;
v___y_664_ = v___y_793_;
v___y_665_ = v___y_792_;
v___y_666_ = v___x_799_;
v___y_667_ = v___y_794_;
v___y_668_ = v___x_806_;
goto v___jp_655_;
}
}
v___jp_807_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
lean_inc_ref_n(v___y_811_, 3);
v___x_820_ = l_Array_append___redArg(v___y_811_, v___y_819_);
lean_dec_ref(v___y_819_);
lean_inc_n(v___y_810_, 7);
lean_inc_n(v___y_814_, 26);
v___x_821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_821_, 0, v___y_814_);
lean_ctor_set(v___x_821_, 1, v___y_810_);
lean_ctor_set(v___x_821_, 2, v___x_820_);
v___x_822_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_823_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_824_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_818_, 8);
v___x_825_ = l_Lean_Name_mkStr4(v___y_818_, v___x_822_, v___x_823_, v___x_824_);
v___x_826_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_827_, 0, v___y_814_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_829_ = l_Lean_Syntax_SepArray_ofElems(v___x_828_, v___y_808_);
lean_dec_ref(v___y_808_);
v___x_830_ = l_Array_append___redArg(v___y_811_, v___x_829_);
lean_dec_ref(v___x_829_);
v___x_831_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_831_, 0, v___y_814_);
lean_ctor_set(v___x_831_, 1, v___y_810_);
lean_ctor_set(v___x_831_, 2, v___x_830_);
v___x_832_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_833_, 0, v___y_814_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = l_Lean_Syntax_node3(v___y_814_, v___x_825_, v___x_827_, v___x_831_, v___x_833_);
v___x_835_ = l_Lean_Syntax_node1(v___y_814_, v___y_810_, v___x_834_);
lean_inc_ref(v___y_817_);
v___x_836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_836_, 0, v___y_814_);
lean_ctor_set(v___x_836_, 1, v___y_817_);
v___x_837_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_838_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_812_, 2);
lean_inc_n(v___y_813_, 2);
v___x_839_ = l_Lean_addMacroScope(v___y_813_, v___x_838_, v___y_812_);
v___x_840_ = lean_box(0);
v___x_841_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_841_, 0, v___y_814_);
lean_ctor_set(v___x_841_, 1, v___x_837_);
lean_ctor_set(v___x_841_, 2, v___x_839_);
lean_ctor_set(v___x_841_, 3, v___x_840_);
v___x_842_ = l_Lean_mkIdent(v_k_504_);
v___x_843_ = l_Lean_Syntax_node2(v___y_814_, v___y_810_, v___x_841_, v___x_842_);
v___x_844_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_845_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_845_, 0, v___y_814_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__49, &l_Lean_Elab_Command_elabElabRulesAux___closed__49_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__49);
v___x_847_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__50));
lean_inc_ref_n(v___y_816_, 2);
v___x_848_ = l_Lean_Name_mkStr4(v___y_818_, v___y_816_, v___x_847_, v___x_847_);
lean_inc(v___x_848_);
v___x_849_ = l_Lean_addMacroScope(v___y_813_, v___x_848_, v___y_812_);
v___x_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_840_);
v___x_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v___x_840_);
v___x_852_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_852_, 0, v___y_814_);
lean_ctor_set(v___x_852_, 1, v___x_846_);
lean_ctor_set(v___x_852_, 2, v___x_849_);
lean_ctor_set(v___x_852_, 3, v___x_851_);
v___x_853_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_854_, 0, v___y_814_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_856_ = l_Lean_Name_mkStr4(v___y_818_, v___x_822_, v___x_823_, v___x_855_);
v___x_857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_857_, 0, v___y_814_);
lean_ctor_set(v___x_857_, 1, v___x_855_);
v___x_858_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_859_ = l_Lean_Name_mkStr4(v___y_818_, v___x_822_, v___x_823_, v___x_858_);
v___x_860_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_861_ = l_Lean_Name_mkStr4(v___y_818_, v___x_822_, v___x_823_, v___x_860_);
v___x_862_ = l_Array_append___redArg(v___y_811_, v_a_514_);
lean_dec(v_a_514_);
v___x_863_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_864_, 0, v___y_814_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_866_ = l_Lean_Name_mkStr4(v___y_818_, v___x_822_, v___x_823_, v___x_865_);
v___x_867_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_868_, 0, v___y_814_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_Syntax_node1(v___y_814_, v___x_866_, v___x_868_);
v___x_870_ = l_Lean_Syntax_node1(v___y_814_, v___y_810_, v___x_869_);
v___x_871_ = l_Lean_Syntax_node1(v___y_814_, v___y_810_, v___x_870_);
v___x_872_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_873_, 0, v___y_814_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_875_ = l_Lean_Name_mkStr4(v___y_818_, v___x_822_, v___x_823_, v___x_874_);
v___x_876_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_877_, 0, v___y_814_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_879_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_880_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_881_ = l_Lean_addMacroScope(v___y_813_, v___x_880_, v___y_812_);
v___x_882_ = l_Lean_Name_mkStr3(v___y_818_, v___y_816_, v___x_878_);
v___x_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v___x_840_);
v___x_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_840_);
v___x_885_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_885_, 0, v___y_814_);
lean_ctor_set(v___x_885_, 1, v___x_879_);
lean_ctor_set(v___x_885_, 2, v___x_881_);
lean_ctor_set(v___x_885_, 3, v___x_884_);
v___x_886_ = l_Lean_Syntax_node2(v___y_814_, v___x_875_, v___x_877_, v___x_885_);
v___x_887_ = l_Lean_Syntax_node4(v___y_814_, v___x_861_, v___x_864_, v___x_871_, v___x_873_, v___x_886_);
v___x_888_ = lean_array_push(v___x_862_, v___x_887_);
v___x_889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_889_, 0, v___y_814_);
lean_ctor_set(v___x_889_, 1, v___y_810_);
lean_ctor_set(v___x_889_, 2, v___x_888_);
v___x_890_ = l_Lean_Syntax_node1(v___y_814_, v___x_859_, v___x_889_);
v___x_891_ = l_Lean_Syntax_node2(v___y_814_, v___x_856_, v___x_857_, v___x_890_);
v___x_892_ = lean_unsigned_to_nat(9u);
v___x_893_ = lean_mk_empty_array_with_capacity(v___x_892_);
v___x_894_ = lean_array_push(v___x_893_, v___x_821_);
v___x_895_ = lean_array_push(v___x_894_, v___x_835_);
v___x_896_ = lean_array_push(v___x_895_, v___y_815_);
v___x_897_ = lean_array_push(v___x_896_, v___x_836_);
v___x_898_ = lean_array_push(v___x_897_, v___x_843_);
v___x_899_ = lean_array_push(v___x_898_, v___x_845_);
v___x_900_ = lean_array_push(v___x_899_, v___x_852_);
v___x_901_ = lean_array_push(v___x_900_, v___x_854_);
v___x_902_ = lean_array_push(v___x_901_, v___x_891_);
lean_inc(v___y_809_);
v___x_903_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_903_, 0, v___y_814_);
lean_ctor_set(v___x_903_, 1, v___y_809_);
lean_ctor_set(v___x_903_, 2, v___x_902_);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
v___jp_905_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_911_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_912_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_913_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_914_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_915_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_916_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_501_) == 1)
{
lean_object* v_val_917_; lean_object* v___x_918_; 
v_val_917_ = lean_ctor_get(v_doc_x3f_501_, 0);
lean_inc(v_val_917_);
lean_dec_ref_known(v_doc_x3f_501_, 1);
v___x_918_ = l_Array_mkArray1___redArg(v_val_917_);
v___y_808_ = v___y_906_;
v___y_809_ = v___x_914_;
v___y_810_ = v___x_915_;
v___y_811_ = v___x_916_;
v___y_812_ = v___y_908_;
v___y_813_ = v_a_910_;
v___y_814_ = v___y_907_;
v___y_815_ = v___y_909_;
v___y_816_ = v___x_912_;
v___y_817_ = v___x_913_;
v___y_818_ = v___x_911_;
v___y_819_ = v___x_918_;
goto v___jp_807_;
}
else
{
lean_object* v___x_919_; 
lean_dec(v_doc_x3f_501_);
v___x_919_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_808_ = v___y_906_;
v___y_809_ = v___x_914_;
v___y_810_ = v___x_915_;
v___y_811_ = v___x_916_;
v___y_812_ = v___y_908_;
v___y_813_ = v_a_910_;
v___y_814_ = v___y_907_;
v___y_815_ = v___y_909_;
v___y_816_ = v___x_912_;
v___y_817_ = v___x_913_;
v___y_818_ = v___x_911_;
v___y_819_ = v___x_919_;
goto v___jp_807_;
}
}
v___jp_920_:
{
lean_object* v___x_926_; 
lean_inc(v___y_925_);
lean_inc(v_k_504_);
v___x_926_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_504_, v_attrKind_503_, v_attrs_x3f_502_, v___y_925_, v___y_924_, v___y_923_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_928_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_926_, 1);
v___x_928_ = l_Lean_Elab_Command_getRef___redArg(v___y_924_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = l_Lean_SourceInfo_fromRef(v_a_929_, v___y_921_);
lean_dec(v_a_929_);
v___x_931_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_924_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_quotContext_x3f_932_; 
v_quotContext_x3f_932_ = lean_ctor_get(v___y_924_, 5);
if (lean_obj_tag(v_quotContext_x3f_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_934_; lean_object* v_a_935_; 
v_a_933_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_931_, 1);
v___x_934_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_923_);
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref(v___x_934_);
v___y_906_ = v_a_927_;
v___y_907_ = v___x_930_;
v___y_908_ = v_a_933_;
v___y_909_ = v___y_922_;
v_a_910_ = v_a_935_;
goto v___jp_905_;
}
else
{
lean_object* v_a_936_; lean_object* v_val_937_; 
v_a_936_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_931_, 1);
v_val_937_ = lean_ctor_get(v_quotContext_x3f_932_, 0);
lean_inc(v_val_937_);
v___y_906_ = v_a_927_;
v___y_907_ = v___x_930_;
v___y_908_ = v_a_936_;
v___y_909_ = v___y_922_;
v_a_910_ = v_val_937_;
goto v___jp_905_;
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v___x_930_);
lean_dec(v_a_927_);
lean_dec(v___y_922_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_938_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_931_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_931_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
lean_dec(v_a_927_);
lean_dec(v___y_922_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
return v___x_928_;
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec(v___y_922_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_946_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_926_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_926_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
v___jp_954_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_inc_ref_n(v___y_964_, 4);
v___x_967_ = l_Array_append___redArg(v___y_964_, v___y_966_);
lean_dec_ref(v___y_966_);
lean_inc_n(v___y_965_, 10);
lean_inc_n(v___y_958_, 36);
v___x_968_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_968_, 0, v___y_958_);
lean_ctor_set(v___x_968_, 1, v___y_965_);
lean_ctor_set(v___x_968_, 2, v___x_967_);
v___x_969_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_970_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_971_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_962_, 11);
v___x_972_ = l_Lean_Name_mkStr4(v___y_962_, v___x_969_, v___x_970_, v___x_971_);
v___x_973_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_974_, 0, v___y_958_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_976_ = l_Lean_Syntax_SepArray_ofElems(v___x_975_, v___y_959_);
lean_dec_ref(v___y_959_);
v___x_977_ = l_Array_append___redArg(v___y_964_, v___x_976_);
lean_dec_ref(v___x_976_);
v___x_978_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_978_, 0, v___y_958_);
lean_ctor_set(v___x_978_, 1, v___y_965_);
lean_ctor_set(v___x_978_, 2, v___x_977_);
v___x_979_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_980_, 0, v___y_958_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = l_Lean_Syntax_node3(v___y_958_, v___x_972_, v___x_974_, v___x_978_, v___x_980_);
v___x_982_ = l_Lean_Syntax_node1(v___y_958_, v___y_965_, v___x_981_);
lean_inc_ref(v___y_961_);
v___x_983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_983_, 0, v___y_958_);
lean_ctor_set(v___x_983_, 1, v___y_961_);
v___x_984_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_985_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_963_, 4);
lean_inc_n(v___y_955_, 4);
v___x_986_ = l_Lean_addMacroScope(v___y_955_, v___x_985_, v___y_963_);
v___x_987_ = lean_box(0);
v___x_988_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_988_, 0, v___y_958_);
lean_ctor_set(v___x_988_, 1, v___x_984_);
lean_ctor_set(v___x_988_, 2, v___x_986_);
lean_ctor_set(v___x_988_, 3, v___x_987_);
v___x_989_ = l_Lean_mkIdent(v_k_504_);
v___x_990_ = l_Lean_Syntax_node2(v___y_958_, v___y_965_, v___x_988_, v___x_989_);
v___x_991_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_992_, 0, v___y_958_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_994_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
v___x_995_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc_ref_n(v___y_956_, 2);
v___x_996_ = l_Lean_Name_mkStr4(v___y_962_, v___y_956_, v___x_994_, v___x_995_);
lean_inc(v___x_996_);
v___x_997_ = l_Lean_addMacroScope(v___y_955_, v___x_996_, v___y_963_);
v___x_998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_987_);
v___x_999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_987_);
v___x_1000_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1000_, 0, v___y_958_);
lean_ctor_set(v___x_1000_, 1, v___x_993_);
lean_ctor_set(v___x_1000_, 2, v___x_997_);
lean_ctor_set(v___x_1000_, 3, v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___y_958_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1004_ = l_Lean_Name_mkStr4(v___y_962_, v___x_969_, v___x_970_, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___y_958_);
lean_ctor_set(v___x_1005_, 1, v___x_1003_);
v___x_1006_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_1007_ = l_Lean_Name_mkStr4(v___y_962_, v___x_969_, v___x_970_, v___x_1006_);
v___x_1008_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_1009_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1010_ = l_Lean_addMacroScope(v___y_955_, v___x_1009_, v___y_963_);
v___x_1011_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1011_, 0, v___y_958_);
lean_ctor_set(v___x_1011_, 1, v___x_1008_);
lean_ctor_set(v___x_1011_, 2, v___x_1010_);
lean_ctor_set(v___x_1011_, 3, v___x_987_);
v___x_1012_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__52, &l_Lean_Elab_Command_elabElabRulesAux___closed__52_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__52);
v___x_1013_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__53));
v___x_1014_ = l_Lean_addMacroScope(v___y_955_, v___x_1013_, v___y_963_);
v___x_1015_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1015_, 0, v___y_958_);
lean_ctor_set(v___x_1015_, 1, v___x_1012_);
lean_ctor_set(v___x_1015_, 2, v___x_1014_);
lean_ctor_set(v___x_1015_, 3, v___x_987_);
lean_inc_ref(v___x_1011_);
v___x_1016_ = l_Lean_Syntax_node2(v___y_958_, v___y_965_, v___x_1011_, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1017_, 0, v___y_958_);
lean_ctor_set(v___x_1017_, 1, v___y_965_);
lean_ctor_set(v___x_1017_, 2, v___y_964_);
v___x_1018_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1019_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___y_958_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1021_ = l_Lean_Name_mkStr4(v___y_962_, v___x_969_, v___x_970_, v___x_1020_);
v___x_1022_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___y_958_);
lean_ctor_set(v___x_1022_, 1, v___x_1020_);
v___x_1023_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1024_ = l_Lean_Name_mkStr4(v___y_962_, v___x_969_, v___x_970_, v___x_1023_);
lean_inc_ref_n(v___x_1017_, 3);
v___x_1025_ = l_Lean_Syntax_node2(v___y_958_, v___x_1024_, v___x_1017_, v___x_1011_);
v___x_1026_ = l_Lean_Syntax_node1(v___y_958_, v___y_965_, v___x_1025_);
v___x_1027_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___y_958_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1030_ = l_Lean_Name_mkStr4(v___y_962_, v___x_969_, v___x_970_, v___x_1029_);
v___x_1031_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1032_ = l_Lean_Name_mkStr4(v___y_962_, v___x_969_, v___x_970_, v___x_1031_);
v___x_1033_ = l_Array_append___redArg(v___y_964_, v_a_514_);
lean_dec(v_a_514_);
v___x_1034_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1035_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___y_958_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1037_ = l_Lean_Name_mkStr4(v___y_962_, v___x_969_, v___x_970_, v___x_1036_);
v___x_1038_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___y_958_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = l_Lean_Syntax_node1(v___y_958_, v___x_1037_, v___x_1039_);
v___x_1041_ = l_Lean_Syntax_node1(v___y_958_, v___y_965_, v___x_1040_);
v___x_1042_ = l_Lean_Syntax_node1(v___y_958_, v___y_965_, v___x_1041_);
v___x_1043_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1044_ = l_Lean_Name_mkStr4(v___y_962_, v___x_969_, v___x_970_, v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___y_958_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1048_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_1049_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1050_ = l_Lean_addMacroScope(v___y_955_, v___x_1049_, v___y_963_);
v___x_1051_ = l_Lean_Name_mkStr3(v___y_962_, v___y_956_, v___x_1047_);
v___x_1052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v___x_987_);
v___x_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v___x_987_);
v___x_1054_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1054_, 0, v___y_958_);
lean_ctor_set(v___x_1054_, 1, v___x_1048_);
lean_ctor_set(v___x_1054_, 2, v___x_1050_);
lean_ctor_set(v___x_1054_, 3, v___x_1053_);
v___x_1055_ = l_Lean_Syntax_node2(v___y_958_, v___x_1044_, v___x_1046_, v___x_1054_);
lean_inc_ref(v___x_1019_);
v___x_1056_ = l_Lean_Syntax_node4(v___y_958_, v___x_1032_, v___x_1035_, v___x_1042_, v___x_1019_, v___x_1055_);
v___x_1057_ = lean_array_push(v___x_1033_, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1058_, 0, v___y_958_);
lean_ctor_set(v___x_1058_, 1, v___y_965_);
lean_ctor_set(v___x_1058_, 2, v___x_1057_);
v___x_1059_ = l_Lean_Syntax_node1(v___y_958_, v___x_1030_, v___x_1058_);
v___x_1060_ = l_Lean_Syntax_node6(v___y_958_, v___x_1021_, v___x_1022_, v___x_1017_, v___x_1017_, v___x_1026_, v___x_1028_, v___x_1059_);
v___x_1061_ = l_Lean_Syntax_node4(v___y_958_, v___x_1007_, v___x_1016_, v___x_1017_, v___x_1019_, v___x_1060_);
v___x_1062_ = l_Lean_Syntax_node2(v___y_958_, v___x_1004_, v___x_1005_, v___x_1061_);
v___x_1063_ = lean_unsigned_to_nat(9u);
v___x_1064_ = lean_mk_empty_array_with_capacity(v___x_1063_);
v___x_1065_ = lean_array_push(v___x_1064_, v___x_968_);
v___x_1066_ = lean_array_push(v___x_1065_, v___x_982_);
v___x_1067_ = lean_array_push(v___x_1066_, v___y_960_);
v___x_1068_ = lean_array_push(v___x_1067_, v___x_983_);
v___x_1069_ = lean_array_push(v___x_1068_, v___x_990_);
v___x_1070_ = lean_array_push(v___x_1069_, v___x_992_);
v___x_1071_ = lean_array_push(v___x_1070_, v___x_1000_);
v___x_1072_ = lean_array_push(v___x_1071_, v___x_1002_);
v___x_1073_ = lean_array_push(v___x_1072_, v___x_1062_);
lean_inc(v___y_957_);
v___x_1074_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1074_, 0, v___y_958_);
lean_ctor_set(v___x_1074_, 1, v___y_957_);
lean_ctor_set(v___x_1074_, 2, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
v___jp_1076_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1082_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1083_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1084_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_1085_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_1086_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1087_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_501_) == 1)
{
lean_object* v_val_1088_; lean_object* v___x_1089_; 
v_val_1088_ = lean_ctor_get(v_doc_x3f_501_, 0);
lean_inc(v_val_1088_);
lean_dec_ref_known(v_doc_x3f_501_, 1);
v___x_1089_ = l_Array_mkArray1___redArg(v_val_1088_);
v___y_955_ = v_a_1081_;
v___y_956_ = v___x_1083_;
v___y_957_ = v___x_1085_;
v___y_958_ = v___y_1077_;
v___y_959_ = v___y_1078_;
v___y_960_ = v___y_1079_;
v___y_961_ = v___x_1084_;
v___y_962_ = v___x_1082_;
v___y_963_ = v___y_1080_;
v___y_964_ = v___x_1087_;
v___y_965_ = v___x_1086_;
v___y_966_ = v___x_1089_;
goto v___jp_954_;
}
else
{
lean_object* v___x_1090_; 
lean_dec(v_doc_x3f_501_);
v___x_1090_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_955_ = v_a_1081_;
v___y_956_ = v___x_1083_;
v___y_957_ = v___x_1085_;
v___y_958_ = v___y_1077_;
v___y_959_ = v___y_1078_;
v___y_960_ = v___y_1079_;
v___y_961_ = v___x_1084_;
v___y_962_ = v___x_1082_;
v___y_963_ = v___y_1080_;
v___y_964_ = v___x_1087_;
v___y_965_ = v___x_1086_;
v___y_966_ = v___x_1090_;
goto v___jp_954_;
}
}
v___jp_1091_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_inc_ref_n(v___y_1099_, 3);
v___x_1105_ = l_Array_append___redArg(v___y_1099_, v___y_1104_);
lean_dec_ref(v___y_1104_);
lean_inc_n(v___y_1100_, 7);
lean_inc_n(v___y_1097_, 26);
v___x_1106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1106_, 0, v___y_1097_);
lean_ctor_set(v___x_1106_, 1, v___y_1100_);
lean_ctor_set(v___x_1106_, 2, v___x_1105_);
v___x_1107_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1108_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1109_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1092_, 8);
v___x_1110_ = l_Lean_Name_mkStr4(v___y_1092_, v___x_1107_, v___x_1108_, v___x_1109_);
v___x_1111_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___y_1097_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1114_ = l_Lean_Syntax_SepArray_ofElems(v___x_1113_, v___y_1094_);
lean_dec_ref(v___y_1094_);
v___x_1115_ = l_Array_append___redArg(v___y_1099_, v___x_1114_);
lean_dec_ref(v___x_1114_);
v___x_1116_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1116_, 0, v___y_1097_);
lean_ctor_set(v___x_1116_, 1, v___y_1100_);
lean_ctor_set(v___x_1116_, 2, v___x_1115_);
v___x_1117_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1118_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___y_1097_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_Lean_Syntax_node3(v___y_1097_, v___x_1110_, v___x_1112_, v___x_1116_, v___x_1118_);
v___x_1120_ = l_Lean_Syntax_node1(v___y_1097_, v___y_1100_, v___x_1119_);
lean_inc_ref(v___y_1096_);
v___x_1121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___y_1097_);
lean_ctor_set(v___x_1121_, 1, v___y_1096_);
v___x_1122_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1123_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1103_, 2);
lean_inc_n(v___y_1098_, 2);
v___x_1124_ = l_Lean_addMacroScope(v___y_1098_, v___x_1123_, v___y_1103_);
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1126_, 0, v___y_1097_);
lean_ctor_set(v___x_1126_, 1, v___x_1122_);
lean_ctor_set(v___x_1126_, 2, v___x_1124_);
lean_ctor_set(v___x_1126_, 3, v___x_1125_);
v___x_1127_ = l_Lean_mkIdent(v_k_504_);
v___x_1128_ = l_Lean_Syntax_node2(v___y_1097_, v___y_1100_, v___x_1126_, v___x_1127_);
v___x_1129_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___y_1097_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__55, &l_Lean_Elab_Command_elabElabRulesAux___closed__55_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__55);
v___x_1132_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
lean_inc_ref(v___y_1095_);
lean_inc_ref_n(v___y_1093_, 2);
v___x_1133_ = l_Lean_Name_mkStr4(v___y_1092_, v___y_1093_, v___y_1095_, v___x_1132_);
lean_inc(v___x_1133_);
v___x_1134_ = l_Lean_addMacroScope(v___y_1098_, v___x_1133_, v___y_1103_);
v___x_1135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1125_);
v___x_1136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___x_1125_);
v___x_1137_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1137_, 0, v___y_1097_);
lean_ctor_set(v___x_1137_, 1, v___x_1131_);
lean_ctor_set(v___x_1137_, 2, v___x_1134_);
lean_ctor_set(v___x_1137_, 3, v___x_1136_);
v___x_1138_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___y_1097_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1141_ = l_Lean_Name_mkStr4(v___y_1092_, v___x_1107_, v___x_1108_, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___y_1097_);
lean_ctor_set(v___x_1142_, 1, v___x_1140_);
v___x_1143_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1144_ = l_Lean_Name_mkStr4(v___y_1092_, v___x_1107_, v___x_1108_, v___x_1143_);
v___x_1145_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1146_ = l_Lean_Name_mkStr4(v___y_1092_, v___x_1107_, v___x_1108_, v___x_1145_);
v___x_1147_ = l_Array_append___redArg(v___y_1099_, v_a_514_);
lean_dec(v_a_514_);
v___x_1148_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___y_1097_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1151_ = l_Lean_Name_mkStr4(v___y_1092_, v___x_1107_, v___x_1108_, v___x_1150_);
v___x_1152_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___y_1097_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_Syntax_node1(v___y_1097_, v___x_1151_, v___x_1153_);
v___x_1155_ = l_Lean_Syntax_node1(v___y_1097_, v___y_1100_, v___x_1154_);
v___x_1156_ = l_Lean_Syntax_node1(v___y_1097_, v___y_1100_, v___x_1155_);
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___y_1097_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1160_ = l_Lean_Name_mkStr4(v___y_1092_, v___x_1107_, v___x_1108_, v___x_1159_);
v___x_1161_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___y_1097_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1164_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_1165_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1166_ = l_Lean_addMacroScope(v___y_1098_, v___x_1165_, v___y_1103_);
v___x_1167_ = l_Lean_Name_mkStr3(v___y_1092_, v___y_1093_, v___x_1163_);
v___x_1168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v___x_1125_);
v___x_1169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v___x_1125_);
v___x_1170_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1170_, 0, v___y_1097_);
lean_ctor_set(v___x_1170_, 1, v___x_1164_);
lean_ctor_set(v___x_1170_, 2, v___x_1166_);
lean_ctor_set(v___x_1170_, 3, v___x_1169_);
v___x_1171_ = l_Lean_Syntax_node2(v___y_1097_, v___x_1160_, v___x_1162_, v___x_1170_);
v___x_1172_ = l_Lean_Syntax_node4(v___y_1097_, v___x_1146_, v___x_1149_, v___x_1156_, v___x_1158_, v___x_1171_);
v___x_1173_ = lean_array_push(v___x_1147_, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1174_, 0, v___y_1097_);
lean_ctor_set(v___x_1174_, 1, v___y_1100_);
lean_ctor_set(v___x_1174_, 2, v___x_1173_);
v___x_1175_ = l_Lean_Syntax_node1(v___y_1097_, v___x_1144_, v___x_1174_);
v___x_1176_ = l_Lean_Syntax_node2(v___y_1097_, v___x_1141_, v___x_1142_, v___x_1175_);
v___x_1177_ = lean_unsigned_to_nat(9u);
v___x_1178_ = lean_mk_empty_array_with_capacity(v___x_1177_);
v___x_1179_ = lean_array_push(v___x_1178_, v___x_1106_);
v___x_1180_ = lean_array_push(v___x_1179_, v___x_1120_);
v___x_1181_ = lean_array_push(v___x_1180_, v___y_1101_);
v___x_1182_ = lean_array_push(v___x_1181_, v___x_1121_);
v___x_1183_ = lean_array_push(v___x_1182_, v___x_1128_);
v___x_1184_ = lean_array_push(v___x_1183_, v___x_1130_);
v___x_1185_ = lean_array_push(v___x_1184_, v___x_1137_);
v___x_1186_ = lean_array_push(v___x_1185_, v___x_1139_);
v___x_1187_ = lean_array_push(v___x_1186_, v___x_1176_);
lean_inc(v___y_1102_);
v___x_1188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1188_, 0, v___y_1097_);
lean_ctor_set(v___x_1188_, 1, v___y_1102_);
lean_ctor_set(v___x_1188_, 2, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
v___jp_1190_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1196_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1198_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___x_1199_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_1200_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1202_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_501_) == 1)
{
lean_object* v_val_1203_; lean_object* v___x_1204_; 
v_val_1203_ = lean_ctor_get(v_doc_x3f_501_, 0);
lean_inc(v_val_1203_);
lean_dec_ref_known(v_doc_x3f_501_, 1);
v___x_1204_ = l_Array_mkArray1___redArg(v_val_1203_);
v___y_1092_ = v___x_1196_;
v___y_1093_ = v___x_1197_;
v___y_1094_ = v___y_1193_;
v___y_1095_ = v___x_1198_;
v___y_1096_ = v___x_1199_;
v___y_1097_ = v___y_1191_;
v___y_1098_ = v_a_1195_;
v___y_1099_ = v___x_1202_;
v___y_1100_ = v___x_1201_;
v___y_1101_ = v___y_1192_;
v___y_1102_ = v___x_1200_;
v___y_1103_ = v___y_1194_;
v___y_1104_ = v___x_1204_;
goto v___jp_1091_;
}
else
{
lean_object* v___x_1205_; 
lean_dec(v_doc_x3f_501_);
v___x_1205_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_1092_ = v___x_1196_;
v___y_1093_ = v___x_1197_;
v___y_1094_ = v___y_1193_;
v___y_1095_ = v___x_1198_;
v___y_1096_ = v___x_1199_;
v___y_1097_ = v___y_1191_;
v___y_1098_ = v_a_1195_;
v___y_1099_ = v___x_1202_;
v___y_1100_ = v___x_1201_;
v___y_1101_ = v___y_1192_;
v___y_1102_ = v___x_1200_;
v___y_1103_ = v___y_1194_;
v___y_1104_ = v___x_1205_;
goto v___jp_1091_;
}
}
v___jp_1206_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_inc_ref_n(v___y_1213_, 4);
v___x_1219_ = l_Array_append___redArg(v___y_1213_, v___y_1218_);
lean_dec_ref(v___y_1218_);
lean_inc_n(v___y_1217_, 10);
lean_inc_n(v___y_1212_, 35);
v___x_1220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1220_, 0, v___y_1212_);
lean_ctor_set(v___x_1220_, 1, v___y_1217_);
lean_ctor_set(v___x_1220_, 2, v___x_1219_);
v___x_1221_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1222_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1223_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1207_, 11);
v___x_1224_ = l_Lean_Name_mkStr4(v___y_1207_, v___x_1221_, v___x_1222_, v___x_1223_);
v___x_1225_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___y_1212_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1228_ = l_Lean_Syntax_SepArray_ofElems(v___x_1227_, v___y_1210_);
lean_dec_ref(v___y_1210_);
v___x_1229_ = l_Array_append___redArg(v___y_1213_, v___x_1228_);
lean_dec_ref(v___x_1228_);
v___x_1230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1230_, 0, v___y_1212_);
lean_ctor_set(v___x_1230_, 1, v___y_1217_);
lean_ctor_set(v___x_1230_, 2, v___x_1229_);
v___x_1231_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___y_1212_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = l_Lean_Syntax_node3(v___y_1212_, v___x_1224_, v___x_1226_, v___x_1230_, v___x_1232_);
v___x_1234_ = l_Lean_Syntax_node1(v___y_1212_, v___y_1217_, v___x_1233_);
lean_inc_ref(v___y_1209_);
v___x_1235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___y_1212_);
lean_ctor_set(v___x_1235_, 1, v___y_1209_);
v___x_1236_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1237_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1208_, 3);
lean_inc_n(v___y_1216_, 3);
v___x_1238_ = l_Lean_addMacroScope(v___y_1216_, v___x_1237_, v___y_1208_);
v___x_1239_ = lean_box(0);
v___x_1240_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1240_, 0, v___y_1212_);
lean_ctor_set(v___x_1240_, 1, v___x_1236_);
lean_ctor_set(v___x_1240_, 2, v___x_1238_);
lean_ctor_set(v___x_1240_, 3, v___x_1239_);
v___x_1241_ = l_Lean_mkIdent(v_k_504_);
v___x_1242_ = l_Lean_Syntax_node2(v___y_1212_, v___y_1217_, v___x_1240_, v___x_1241_);
v___x_1243_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___y_1212_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__39, &l_Lean_Elab_Command_elabElabRulesAux___closed__39_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__39);
v___x_1246_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
lean_inc_ref_n(v___y_1215_, 2);
v___x_1247_ = l_Lean_Name_mkStr4(v___y_1207_, v___y_1215_, v___x_1222_, v___x_1246_);
lean_inc(v___x_1247_);
v___x_1248_ = l_Lean_addMacroScope(v___y_1216_, v___x_1247_, v___y_1208_);
v___x_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1239_);
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v___x_1239_);
v___x_1251_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1251_, 0, v___y_1212_);
lean_ctor_set(v___x_1251_, 1, v___x_1245_);
lean_ctor_set(v___x_1251_, 2, v___x_1248_);
lean_ctor_set(v___x_1251_, 3, v___x_1250_);
v___x_1252_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___y_1212_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1255_ = l_Lean_Name_mkStr4(v___y_1207_, v___x_1221_, v___x_1222_, v___x_1254_);
v___x_1256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___y_1212_);
lean_ctor_set(v___x_1256_, 1, v___x_1254_);
v___x_1257_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_1258_ = l_Lean_Name_mkStr4(v___y_1207_, v___x_1221_, v___x_1222_, v___x_1257_);
v___x_1259_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_1260_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1261_ = l_Lean_addMacroScope(v___y_1216_, v___x_1260_, v___y_1208_);
v___x_1262_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1262_, 0, v___y_1212_);
lean_ctor_set(v___x_1262_, 1, v___x_1259_);
lean_ctor_set(v___x_1262_, 2, v___x_1261_);
lean_ctor_set(v___x_1262_, 3, v___x_1239_);
v___x_1263_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1264_ = l_Lean_Name_mkStr4(v___y_1207_, v___x_1221_, v___x_1222_, v___x_1263_);
v___x_1265_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___y_1212_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = l_Lean_Syntax_node1(v___y_1212_, v___x_1264_, v___x_1266_);
lean_inc(v___x_1267_);
lean_inc_ref(v___x_1262_);
v___x_1268_ = l_Lean_Syntax_node2(v___y_1212_, v___y_1217_, v___x_1262_, v___x_1267_);
v___x_1269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1269_, 0, v___y_1212_);
lean_ctor_set(v___x_1269_, 1, v___y_1217_);
lean_ctor_set(v___x_1269_, 2, v___y_1213_);
v___x_1270_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___y_1212_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1273_ = l_Lean_Name_mkStr4(v___y_1207_, v___x_1221_, v___x_1222_, v___x_1272_);
v___x_1274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___y_1212_);
lean_ctor_set(v___x_1274_, 1, v___x_1272_);
v___x_1275_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1276_ = l_Lean_Name_mkStr4(v___y_1207_, v___x_1221_, v___x_1222_, v___x_1275_);
lean_inc_ref_n(v___x_1269_, 3);
v___x_1277_ = l_Lean_Syntax_node2(v___y_1212_, v___x_1276_, v___x_1269_, v___x_1262_);
v___x_1278_ = l_Lean_Syntax_node1(v___y_1212_, v___y_1217_, v___x_1277_);
v___x_1279_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___y_1212_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1282_ = l_Lean_Name_mkStr4(v___y_1207_, v___x_1221_, v___x_1222_, v___x_1281_);
v___x_1283_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1284_ = l_Lean_Name_mkStr4(v___y_1207_, v___x_1221_, v___x_1222_, v___x_1283_);
v___x_1285_ = l_Array_append___redArg(v___y_1213_, v_a_514_);
lean_dec(v_a_514_);
v___x_1286_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___y_1212_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = l_Lean_Syntax_node1(v___y_1212_, v___y_1217_, v___x_1267_);
v___x_1289_ = l_Lean_Syntax_node1(v___y_1212_, v___y_1217_, v___x_1288_);
v___x_1290_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1291_ = l_Lean_Name_mkStr4(v___y_1207_, v___x_1221_, v___x_1222_, v___x_1290_);
v___x_1292_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___y_1212_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
v___x_1294_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1295_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_1296_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1297_ = l_Lean_addMacroScope(v___y_1216_, v___x_1296_, v___y_1208_);
v___x_1298_ = l_Lean_Name_mkStr3(v___y_1207_, v___y_1215_, v___x_1294_);
v___x_1299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v___x_1239_);
v___x_1300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1239_);
v___x_1301_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1301_, 0, v___y_1212_);
lean_ctor_set(v___x_1301_, 1, v___x_1295_);
lean_ctor_set(v___x_1301_, 2, v___x_1297_);
lean_ctor_set(v___x_1301_, 3, v___x_1300_);
v___x_1302_ = l_Lean_Syntax_node2(v___y_1212_, v___x_1291_, v___x_1293_, v___x_1301_);
lean_inc_ref(v___x_1271_);
v___x_1303_ = l_Lean_Syntax_node4(v___y_1212_, v___x_1284_, v___x_1287_, v___x_1289_, v___x_1271_, v___x_1302_);
v___x_1304_ = lean_array_push(v___x_1285_, v___x_1303_);
v___x_1305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1305_, 0, v___y_1212_);
lean_ctor_set(v___x_1305_, 1, v___y_1217_);
lean_ctor_set(v___x_1305_, 2, v___x_1304_);
v___x_1306_ = l_Lean_Syntax_node1(v___y_1212_, v___x_1282_, v___x_1305_);
v___x_1307_ = l_Lean_Syntax_node6(v___y_1212_, v___x_1273_, v___x_1274_, v___x_1269_, v___x_1269_, v___x_1278_, v___x_1280_, v___x_1306_);
v___x_1308_ = l_Lean_Syntax_node4(v___y_1212_, v___x_1258_, v___x_1268_, v___x_1269_, v___x_1271_, v___x_1307_);
v___x_1309_ = l_Lean_Syntax_node2(v___y_1212_, v___x_1255_, v___x_1256_, v___x_1308_);
v___x_1310_ = lean_unsigned_to_nat(9u);
v___x_1311_ = lean_mk_empty_array_with_capacity(v___x_1310_);
v___x_1312_ = lean_array_push(v___x_1311_, v___x_1220_);
v___x_1313_ = lean_array_push(v___x_1312_, v___x_1234_);
v___x_1314_ = lean_array_push(v___x_1313_, v___y_1211_);
v___x_1315_ = lean_array_push(v___x_1314_, v___x_1235_);
v___x_1316_ = lean_array_push(v___x_1315_, v___x_1242_);
v___x_1317_ = lean_array_push(v___x_1316_, v___x_1244_);
v___x_1318_ = lean_array_push(v___x_1317_, v___x_1251_);
v___x_1319_ = lean_array_push(v___x_1318_, v___x_1253_);
v___x_1320_ = lean_array_push(v___x_1319_, v___x_1309_);
lean_inc(v___y_1214_);
v___x_1321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1321_, 0, v___y_1212_);
lean_ctor_set(v___x_1321_, 1, v___y_1214_);
lean_ctor_set(v___x_1321_, 2, v___x_1320_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
v___jp_1323_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1329_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1330_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1331_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_1332_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_1333_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1334_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_501_) == 1)
{
lean_object* v_val_1335_; lean_object* v___x_1336_; 
v_val_1335_ = lean_ctor_get(v_doc_x3f_501_, 0);
lean_inc(v_val_1335_);
lean_dec_ref_known(v_doc_x3f_501_, 1);
v___x_1336_ = l_Array_mkArray1___redArg(v_val_1335_);
v___y_1207_ = v___x_1329_;
v___y_1208_ = v___y_1324_;
v___y_1209_ = v___x_1331_;
v___y_1210_ = v___y_1325_;
v___y_1211_ = v___y_1327_;
v___y_1212_ = v___y_1326_;
v___y_1213_ = v___x_1334_;
v___y_1214_ = v___x_1332_;
v___y_1215_ = v___x_1330_;
v___y_1216_ = v_a_1328_;
v___y_1217_ = v___x_1333_;
v___y_1218_ = v___x_1336_;
goto v___jp_1206_;
}
else
{
lean_object* v___x_1337_; 
lean_dec(v_doc_x3f_501_);
v___x_1337_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_1207_ = v___x_1329_;
v___y_1208_ = v___y_1324_;
v___y_1209_ = v___x_1331_;
v___y_1210_ = v___y_1325_;
v___y_1211_ = v___y_1327_;
v___y_1212_ = v___y_1326_;
v___y_1213_ = v___x_1334_;
v___y_1214_ = v___x_1332_;
v___y_1215_ = v___x_1330_;
v___y_1216_ = v_a_1328_;
v___y_1217_ = v___x_1333_;
v___y_1218_ = v___x_1337_;
goto v___jp_1206_;
}
}
v___jp_1338_:
{
lean_object* v___x_1342_; 
lean_inc(v_attrKind_503_);
v___x_1342_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_503_);
if (lean_obj_tag(v_expty_x3f_506_) == 1)
{
lean_object* v_val_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v_val_1343_ = lean_ctor_get(v_expty_x3f_506_, 0);
lean_inc(v_val_1343_);
lean_dec_ref_known(v_expty_x3f_506_, 1);
v___x_1344_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__58));
v___x_1345_ = lean_name_eq(v_catName_1339_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__60));
v___x_1347_ = lean_name_eq(v_catName_1339_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec(v___x_1342_);
lean_del_object(v___x_516_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_attrKind_503_);
lean_dec(v_doc_x3f_501_);
v___x_1348_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__62, &l_Lean_Elab_Command_elabElabRulesAux___closed__62_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__62);
v___x_1349_ = l_Lean_MessageData_ofName(v_catName_1339_);
v___x_1350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__64, &l_Lean_Elab_Command_elabElabRulesAux___closed__64_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__64);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_val_1343_, v___x_1352_, v___y_1340_, v___y_1341_);
lean_dec(v_val_1343_);
return v___x_1353_;
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec(v_catName_1339_);
v___x_1354_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__66));
lean_inc(v_k_504_);
v___x_1355_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_504_, v_attrKind_503_, v_attrs_x3f_502_, v___x_1354_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = l_Lean_Elab_Command_getRef___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = l_Lean_SourceInfo_fromRef(v_a_1358_, v___x_1345_);
lean_dec(v_a_1358_);
v___x_1360_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_quotContext_x3f_1361_; 
v_quotContext_x3f_1361_ = lean_ctor_get(v___y_1340_, 5);
if (lean_obj_tag(v_quotContext_x3f_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; lean_object* v_a_1364_; 
v_a_1362_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1360_, 1);
v___x_1363_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1341_);
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref(v___x_1363_);
v___y_640_ = v_val_1343_;
v___y_641_ = v___x_1359_;
v___y_642_ = v___x_1342_;
v___y_643_ = v_a_1362_;
v___y_644_ = v_a_1356_;
v_a_645_ = v_a_1364_;
goto v___jp_639_;
}
else
{
lean_object* v_a_1365_; lean_object* v_val_1366_; 
v_a_1365_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1360_, 1);
v_val_1366_ = lean_ctor_get(v_quotContext_x3f_1361_, 0);
lean_inc(v_val_1366_);
v___y_640_ = v_val_1343_;
v___y_641_ = v___x_1359_;
v___y_642_ = v___x_1342_;
v___y_643_ = v_a_1365_;
v___y_644_ = v_a_1356_;
v_a_645_ = v_val_1366_;
goto v___jp_639_;
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v___x_1359_);
lean_dec(v_a_1356_);
lean_dec(v_val_1343_);
lean_dec(v___x_1342_);
lean_del_object(v___x_516_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1367_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1360_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1360_);
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
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
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
else
{
lean_dec(v_a_1356_);
lean_dec(v_val_1343_);
lean_dec(v___x_1342_);
lean_del_object(v___x_516_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
return v___x_1357_;
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec(v_val_1343_);
lean_dec(v___x_1342_);
lean_del_object(v___x_516_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1375_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1355_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1355_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec(v_catName_1339_);
lean_del_object(v___x_516_);
v___x_1383_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__68));
lean_inc(v_k_504_);
v___x_1384_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_504_, v_attrKind_503_, v_attrs_x3f_502_, v___x_1383_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = l_Lean_Elab_Command_getRef___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1388_ = 0;
v___x_1389_ = l_Lean_SourceInfo_fromRef(v_a_1387_, v___x_1388_);
lean_dec(v_a_1387_);
v___x_1390_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_quotContext_x3f_1391_; 
v_quotContext_x3f_1391_ = lean_ctor_get(v___y_1340_, 5);
if (lean_obj_tag(v_quotContext_x3f_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; lean_object* v_a_1394_; 
v_a_1392_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1390_, 1);
v___x_1393_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1341_);
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref(v___x_1393_);
v___y_792_ = v_val_1343_;
v___y_793_ = v_a_1392_;
v___y_794_ = v___x_1342_;
v___y_795_ = v_a_1385_;
v___y_796_ = v___x_1389_;
v_a_797_ = v_a_1394_;
goto v___jp_791_;
}
else
{
lean_object* v_a_1395_; lean_object* v_val_1396_; 
v_a_1395_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1390_, 1);
v_val_1396_ = lean_ctor_get(v_quotContext_x3f_1391_, 0);
lean_inc(v_val_1396_);
v___y_792_ = v_val_1343_;
v___y_793_ = v_a_1395_;
v___y_794_ = v___x_1342_;
v___y_795_ = v_a_1385_;
v___y_796_ = v___x_1389_;
v_a_797_ = v_val_1396_;
goto v___jp_791_;
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec(v___x_1389_);
lean_dec(v_a_1385_);
lean_dec(v_val_1343_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1397_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1390_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1390_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
else
{
lean_dec(v_a_1385_);
lean_dec(v_val_1343_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
return v___x_1386_;
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v_val_1343_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1405_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1384_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1384_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
else
{
lean_object* v___x_1413_; uint8_t v___x_1414_; 
lean_del_object(v___x_516_);
lean_dec(v_expty_x3f_506_);
v___x_1413_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__58));
v___x_1414_ = lean_name_eq(v_catName_1339_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__70));
v___x_1416_ = lean_name_eq(v_catName_1339_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__72));
v___x_1418_ = lean_name_eq(v_catName_1339_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__74));
v___x_1420_ = lean_name_eq(v_catName_1339_, v___x_1419_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__60));
v___x_1422_ = lean_name_eq(v_catName_1339_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_attrKind_503_);
lean_dec(v_doc_x3f_501_);
v___x_1423_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__76, &l_Lean_Elab_Command_elabElabRulesAux___closed__76_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76);
v___x_1424_ = l_Lean_MessageData_ofName(v_catName_1339_);
v___x_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
v___x_1426_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__78, &l_Lean_Elab_Command_elabElabRulesAux___closed__78_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__78);
v___x_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1425_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v___x_1427_, v___y_1340_, v___y_1341_);
return v___x_1428_;
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec(v_catName_1339_);
v___x_1429_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__66));
lean_inc(v_k_504_);
v___x_1430_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_504_, v_attrKind_503_, v_attrs_x3f_502_, v___x_1429_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = l_Lean_Elab_Command_getRef___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v___x_1434_ = l_Lean_SourceInfo_fromRef(v_a_1433_, v___x_1420_);
lean_dec(v_a_1433_);
v___x_1435_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_quotContext_x3f_1436_; 
v_quotContext_x3f_1436_ = lean_ctor_get(v___y_1340_, 5);
if (lean_obj_tag(v_quotContext_x3f_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1438_; lean_object* v_a_1439_; 
v_a_1437_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1437_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1438_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1341_);
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref(v___x_1438_);
v___y_1077_ = v___x_1434_;
v___y_1078_ = v_a_1431_;
v___y_1079_ = v___x_1342_;
v___y_1080_ = v_a_1437_;
v_a_1081_ = v_a_1439_;
goto v___jp_1076_;
}
else
{
lean_object* v_a_1440_; lean_object* v_val_1441_; 
v_a_1440_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1435_, 1);
v_val_1441_ = lean_ctor_get(v_quotContext_x3f_1436_, 0);
lean_inc(v_val_1441_);
v___y_1077_ = v___x_1434_;
v___y_1078_ = v_a_1431_;
v___y_1079_ = v___x_1342_;
v___y_1080_ = v_a_1440_;
v_a_1081_ = v_val_1441_;
goto v___jp_1076_;
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v___x_1434_);
lean_dec(v_a_1431_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1442_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1435_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1435_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_dec(v_a_1431_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
return v___x_1432_;
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1450_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1430_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1430_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
else
{
lean_dec(v_catName_1339_);
v___y_921_ = v___x_1416_;
v___y_922_ = v___x_1342_;
v___y_923_ = v___y_1341_;
v___y_924_ = v___y_1340_;
v___y_925_ = v___x_1417_;
goto v___jp_920_;
}
}
else
{
lean_dec(v_catName_1339_);
v___y_921_ = v___x_1416_;
v___y_922_ = v___x_1342_;
v___y_923_ = v___y_1341_;
v___y_924_ = v___y_1340_;
v___y_925_ = v___x_1417_;
goto v___jp_920_;
}
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec(v_catName_1339_);
v___x_1458_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__80));
lean_inc(v_k_504_);
v___x_1459_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_504_, v_attrKind_503_, v_attrs_x3f_502_, v___x_1458_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1461_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___x_1461_ = l_Lean_Elab_Command_getRef___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v___x_1463_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1414_);
lean_dec(v_a_1462_);
v___x_1464_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_quotContext_x3f_1465_; 
v_quotContext_x3f_1465_ = lean_ctor_get(v___y_1340_, 5);
if (lean_obj_tag(v_quotContext_x3f_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1467_; lean_object* v_a_1468_; 
v_a_1466_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1464_, 1);
v___x_1467_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1341_);
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref(v___x_1467_);
v___y_1191_ = v___x_1463_;
v___y_1192_ = v___x_1342_;
v___y_1193_ = v_a_1460_;
v___y_1194_ = v_a_1466_;
v_a_1195_ = v_a_1468_;
goto v___jp_1190_;
}
else
{
lean_object* v_a_1469_; lean_object* v_val_1470_; 
v_a_1469_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1464_, 1);
v_val_1470_ = lean_ctor_get(v_quotContext_x3f_1465_, 0);
lean_inc(v_val_1470_);
v___y_1191_ = v___x_1463_;
v___y_1192_ = v___x_1342_;
v___y_1193_ = v_a_1460_;
v___y_1194_ = v_a_1469_;
v_a_1195_ = v_val_1470_;
goto v___jp_1190_;
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v___x_1463_);
lean_dec(v_a_1460_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1471_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1464_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1464_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_dec(v_a_1460_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
return v___x_1461_;
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1479_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1459_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1459_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec(v_catName_1339_);
v___x_1487_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__68));
lean_inc(v_k_504_);
v___x_1488_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_504_, v_attrKind_503_, v_attrs_x3f_502_, v___x_1487_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1490_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v___x_1490_ = l_Lean_Elab_Command_getRef___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v___x_1492_ = 0;
v___x_1493_ = l_Lean_SourceInfo_fromRef(v_a_1491_, v___x_1492_);
lean_dec(v_a_1491_);
v___x_1494_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_quotContext_x3f_1495_; 
v_quotContext_x3f_1495_ = lean_ctor_get(v___y_1340_, 5);
if (lean_obj_tag(v_quotContext_x3f_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1497_; lean_object* v_a_1498_; 
v_a_1496_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1494_, 1);
v___x_1497_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1341_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref(v___x_1497_);
v___y_1324_ = v_a_1496_;
v___y_1325_ = v_a_1489_;
v___y_1326_ = v___x_1493_;
v___y_1327_ = v___x_1342_;
v_a_1328_ = v_a_1498_;
goto v___jp_1323_;
}
else
{
lean_object* v_a_1499_; lean_object* v_val_1500_; 
v_a_1499_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1494_, 1);
v_val_1500_ = lean_ctor_get(v_quotContext_x3f_1495_, 0);
lean_inc(v_val_1500_);
v___y_1324_ = v_a_1499_;
v___y_1325_ = v_a_1489_;
v___y_1326_ = v___x_1493_;
v___y_1327_ = v___x_1342_;
v_a_1328_ = v_val_1500_;
goto v___jp_1323_;
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v___x_1493_);
lean_dec(v_a_1489_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1501_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1494_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1494_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
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
else
{
lean_dec(v_a_1489_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
return v___x_1490_;
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1509_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1488_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1488_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
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
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_expty_x3f_506_);
lean_dec(v_k_504_);
lean_dec(v_attrKind_503_);
lean_dec(v_doc_x3f_501_);
v_a_1531_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_513_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_513_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object* v_doc_x3f_1539_, lean_object* v_attrs_x3f_1540_, lean_object* v_attrKind_1541_, lean_object* v_k_1542_, lean_object* v_cat_x3f_1543_, lean_object* v_expty_x3f_1544_, lean_object* v_alts_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Elab_Command_elabElabRulesAux(v_doc_x3f_1539_, v_attrs_x3f_1540_, v_attrKind_1541_, v_k_1542_, v_cat_x3f_1543_, v_expty_x3f_1544_, v_alts_1545_, v_a_1546_, v_a_1547_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
lean_dec(v_cat_x3f_1543_);
lean_dec(v_attrs_x3f_1540_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object* v_00_u03b1_1550_, lean_object* v_ref_1551_, lean_object* v_msg_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_1551_, v_msg_1552_, v___y_1553_, v___y_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object* v_00_u03b1_1557_, lean_object* v_ref_1558_, lean_object* v_msg_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(v_00_u03b1_1557_, v_ref_1558_, v_msg_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v_ref_1558_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4(lean_object* v_msgData_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(v_msgData_1564_, v___y_1566_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___boxed(lean_object* v_msgData_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4(v_msgData_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object* v_00_u03b1_1574_, lean_object* v_msg_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v_msg_1575_, v___y_1576_, v___y_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object* v_00_u03b1_1580_, lean_object* v_msg_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_00_u03b1_1580_, v_msg_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5(lean_object* v_msgData_1586_, lean_object* v_macroStack_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg(v_msgData_1586_, v_macroStack_1587_, v___y_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___boxed(lean_object* v_msgData_1592_, lean_object* v_macroStack_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5(v_msgData_1592_, v_macroStack_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
return v_res_1597_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = lean_box(0);
v___x_1599_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v___x_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg(){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0);
v___x_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___boxed(lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0(lean_object* v_00_u03b1_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___boxed(lean_object* v_00_u03b1_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0(v_00_u03b1_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object* v_x_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object* v_x_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_Elab_Command_elabElabRules___lam__0(v_x_1618_);
lean_dec(v_x_1618_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object* v___x_1624_, lean_object* v___x_1625_, lean_object* v_attrKind_1626_, lean_object* v_expty_x3f_1627_, lean_object* v___f_1628_, lean_object* v_cat_x3f_1629_, lean_object* v___x_1630_, lean_object* v___x_1631_, lean_object* v_attrs_x3f_1632_, lean_object* v___x_1633_, lean_object* v___x_1634_, lean_object* v___x_1635_, lean_object* v_doc_x3f_1636_, lean_object* v_kind_x3f_1637_, lean_object* v_alts_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Elab_Command_getRef___redArg(v___y_1639_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1751_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1751_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1751_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
uint8_t v___x_1647_; lean_object* v___x_1648_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___x_1740_; 
v___x_1647_ = 0;
v___x_1648_ = l_Lean_SourceInfo_fromRef(v_a_1643_, v___x_1647_);
lean_dec(v_a_1643_);
v___x_1740_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1639_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_quotContext_x3f_1741_; 
lean_dec_ref_known(v___x_1740_, 1);
v_quotContext_x3f_1741_ = lean_ctor_get(v___y_1639_, 5);
if (lean_obj_tag(v_quotContext_x3f_1741_) == 0)
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1640_);
lean_dec_ref(v___x_1742_);
goto v___jp_1734_;
}
else
{
goto v___jp_1734_;
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec(v___x_1648_);
lean_del_object(v___x_1645_);
lean_dec(v_kind_x3f_1637_);
lean_dec(v_doc_x3f_1636_);
lean_dec_ref(v___x_1635_);
lean_dec_ref(v___x_1634_);
lean_dec_ref(v___x_1633_);
lean_dec_ref(v___x_1630_);
lean_dec(v_cat_x3f_1629_);
lean_dec_ref(v___f_1628_);
lean_dec(v_expty_x3f_1627_);
lean_dec(v_attrKind_1626_);
lean_dec(v___x_1625_);
lean_dec(v___x_1624_);
v_a_1743_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1740_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1740_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
v___jp_1649_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
lean_inc_ref_n(v___y_1651_, 2);
v___x_1658_ = l_Array_append___redArg(v___y_1651_, v___y_1657_);
lean_dec_ref(v___y_1657_);
lean_inc_n(v___y_1653_, 2);
lean_inc_n(v___x_1648_, 3);
v___x_1659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1648_);
lean_ctor_set(v___x_1659_, 1, v___y_1653_);
lean_ctor_set(v___x_1659_, 2, v___x_1658_);
v___x_1660_ = l_Array_append___redArg(v___y_1651_, v_alts_1638_);
v___x_1661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1648_);
lean_ctor_set(v___x_1661_, 1, v___y_1653_);
lean_ctor_set(v___x_1661_, 2, v___x_1660_);
v___x_1662_ = l_Lean_Syntax_node1(v___x_1648_, v___x_1624_, v___x_1661_);
v___x_1663_ = l_Lean_Syntax_node8(v___x_1648_, v___x_1625_, v___y_1650_, v___y_1652_, v_attrKind_1626_, v___y_1655_, v___y_1654_, v___y_1656_, v___x_1659_, v___x_1662_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1663_);
v___x_1665_ = v___x_1645_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
v___jp_1667_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_inc_ref(v___y_1669_);
v___x_1675_ = l_Array_append___redArg(v___y_1669_, v___y_1674_);
lean_dec_ref(v___y_1674_);
lean_inc(v___y_1671_);
lean_inc(v___x_1648_);
v___x_1676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1648_);
lean_ctor_set(v___x_1676_, 1, v___y_1671_);
lean_ctor_set(v___x_1676_, 2, v___x_1675_);
if (lean_obj_tag(v_expty_x3f_1627_) == 1)
{
lean_object* v_val_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec_ref(v___f_1628_);
v_val_1677_ = lean_ctor_get(v_expty_x3f_1627_, 0);
lean_inc(v_val_1677_);
lean_dec_ref_known(v_expty_x3f_1627_, 1);
v___x_1678_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___x_1648_);
v___x_1679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1648_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = l_Array_mkArray2___redArg(v___x_1679_, v_val_1677_);
v___y_1650_ = v___y_1668_;
v___y_1651_ = v___y_1669_;
v___y_1652_ = v___y_1670_;
v___y_1653_ = v___y_1671_;
v___y_1654_ = v___y_1673_;
v___y_1655_ = v___y_1672_;
v___y_1656_ = v___x_1676_;
v___y_1657_ = v___x_1680_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_apply_1(v___f_1628_, v_expty_x3f_1627_);
v___y_1650_ = v___y_1668_;
v___y_1651_ = v___y_1669_;
v___y_1652_ = v___y_1670_;
v___y_1653_ = v___y_1671_;
v___y_1654_ = v___y_1673_;
v___y_1655_ = v___y_1672_;
v___y_1656_ = v___x_1676_;
v___y_1657_ = v___x_1681_;
goto v___jp_1649_;
}
}
v___jp_1682_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_inc_ref(v___y_1684_);
v___x_1689_ = l_Array_append___redArg(v___y_1684_, v___y_1688_);
lean_dec_ref(v___y_1688_);
lean_inc(v___y_1686_);
lean_inc(v___x_1648_);
v___x_1690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1648_);
lean_ctor_set(v___x_1690_, 1, v___y_1686_);
lean_ctor_set(v___x_1690_, 2, v___x_1689_);
if (lean_obj_tag(v_cat_x3f_1629_) == 1)
{
lean_object* v_val_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v_val_1691_ = lean_ctor_get(v_cat_x3f_1629_, 0);
lean_inc(v_val_1691_);
lean_dec_ref_known(v_cat_x3f_1629_, 1);
v___x_1692_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___x_1648_);
v___x_1693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1648_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = l_Array_mkArray2___redArg(v___x_1693_, v_val_1691_);
v___y_1668_ = v___y_1683_;
v___y_1669_ = v___y_1684_;
v___y_1670_ = v___y_1685_;
v___y_1671_ = v___y_1686_;
v___y_1672_ = v___y_1687_;
v___y_1673_ = v___x_1690_;
v___y_1674_ = v___x_1694_;
goto v___jp_1667_;
}
else
{
lean_object* v___x_1695_; 
lean_inc_ref(v___f_1628_);
v___x_1695_ = lean_apply_1(v___f_1628_, v_cat_x3f_1629_);
v___y_1668_ = v___y_1683_;
v___y_1669_ = v___y_1684_;
v___y_1670_ = v___y_1685_;
v___y_1671_ = v___y_1686_;
v___y_1672_ = v___y_1687_;
v___y_1673_ = v___x_1690_;
v___y_1674_ = v___x_1695_;
goto v___jp_1667_;
}
}
v___jp_1696_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_inc_ref(v___y_1698_);
v___x_1701_ = l_Array_append___redArg(v___y_1698_, v___y_1700_);
lean_dec_ref(v___y_1700_);
lean_inc(v___y_1699_);
lean_inc_n(v___x_1648_, 2);
v___x_1702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1648_);
lean_ctor_set(v___x_1702_, 1, v___y_1699_);
lean_ctor_set(v___x_1702_, 2, v___x_1701_);
v___x_1703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1648_);
lean_ctor_set(v___x_1703_, 1, v___x_1630_);
if (lean_obj_tag(v_kind_x3f_1637_) == 0)
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_mk_empty_array_with_capacity(v___x_1631_);
v___y_1683_ = v___y_1697_;
v___y_1684_ = v___y_1698_;
v___y_1685_ = v___x_1702_;
v___y_1686_ = v___y_1699_;
v___y_1687_ = v___x_1703_;
v___y_1688_ = v___x_1704_;
goto v___jp_1682_;
}
else
{
lean_object* v_val_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_val_1705_ = lean_ctor_get(v_kind_x3f_1637_, 0);
lean_inc(v_val_1705_);
lean_dec_ref_known(v_kind_x3f_1637_, 1);
v___x_1706_ = l_Lean_mkIdent(v_val_1705_);
v___x_1707_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___x_1648_, 4);
v___x_1708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1648_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__2));
v___x_1710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1648_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1648_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_1714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1648_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
v___x_1715_ = l_Array_mkArray5___redArg(v___x_1708_, v___x_1710_, v___x_1712_, v___x_1706_, v___x_1714_);
v___y_1683_ = v___y_1697_;
v___y_1684_ = v___y_1698_;
v___y_1685_ = v___x_1702_;
v___y_1686_ = v___y_1699_;
v___y_1687_ = v___x_1703_;
v___y_1688_ = v___x_1715_;
goto v___jp_1682_;
}
}
v___jp_1716_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_inc_ref(v___y_1717_);
v___x_1720_ = l_Array_append___redArg(v___y_1717_, v___y_1719_);
lean_dec_ref(v___y_1719_);
lean_inc(v___y_1718_);
lean_inc(v___x_1648_);
v___x_1721_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1648_);
lean_ctor_set(v___x_1721_, 1, v___y_1718_);
lean_ctor_set(v___x_1721_, 2, v___x_1720_);
if (lean_obj_tag(v_attrs_x3f_1632_) == 1)
{
lean_object* v_val_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v_val_1722_ = lean_ctor_get(v_attrs_x3f_1632_, 0);
v___x_1723_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
v___x_1724_ = l_Lean_Name_mkStr4(v___x_1633_, v___x_1634_, v___x_1635_, v___x_1723_);
v___x_1725_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___x_1648_, 4);
v___x_1726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1648_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
lean_inc_ref(v___y_1717_);
v___x_1727_ = l_Array_append___redArg(v___y_1717_, v_val_1722_);
lean_inc(v___y_1718_);
v___x_1728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1648_);
lean_ctor_set(v___x_1728_, 1, v___y_1718_);
lean_ctor_set(v___x_1728_, 2, v___x_1727_);
v___x_1729_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1648_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = l_Lean_Syntax_node3(v___x_1648_, v___x_1724_, v___x_1726_, v___x_1728_, v___x_1730_);
v___x_1732_ = l_Array_mkArray1___redArg(v___x_1731_);
v___y_1697_ = v___x_1721_;
v___y_1698_ = v___y_1717_;
v___y_1699_ = v___y_1718_;
v___y_1700_ = v___x_1732_;
goto v___jp_1696_;
}
else
{
lean_object* v___x_1733_; 
lean_dec_ref(v___x_1635_);
lean_dec_ref(v___x_1634_);
lean_dec_ref(v___x_1633_);
v___x_1733_ = lean_mk_empty_array_with_capacity(v___x_1631_);
v___y_1697_ = v___x_1721_;
v___y_1698_ = v___y_1717_;
v___y_1699_ = v___y_1718_;
v___y_1700_ = v___x_1733_;
goto v___jp_1696_;
}
}
v___jp_1734_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1736_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_1636_) == 1)
{
lean_object* v_val_1737_; lean_object* v___x_1738_; 
v_val_1737_ = lean_ctor_get(v_doc_x3f_1636_, 0);
lean_inc(v_val_1737_);
lean_dec_ref_known(v_doc_x3f_1636_, 1);
v___x_1738_ = l_Array_mkArray1___redArg(v_val_1737_);
v___y_1717_ = v___x_1736_;
v___y_1718_ = v___x_1735_;
v___y_1719_ = v___x_1738_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1739_; 
lean_dec(v_doc_x3f_1636_);
v___x_1739_ = lean_mk_empty_array_with_capacity(v___x_1631_);
v___y_1717_ = v___x_1736_;
v___y_1718_ = v___x_1735_;
v___y_1719_ = v___x_1739_;
goto v___jp_1716_;
}
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec(v_kind_x3f_1637_);
lean_dec(v_doc_x3f_1636_);
lean_dec_ref(v___x_1635_);
lean_dec_ref(v___x_1634_);
lean_dec_ref(v___x_1633_);
lean_dec_ref(v___x_1630_);
lean_dec(v_cat_x3f_1629_);
lean_dec_ref(v___f_1628_);
lean_dec(v_expty_x3f_1627_);
lean_dec(v_attrKind_1626_);
lean_dec(v___x_1625_);
lean_dec(v___x_1624_);
v_a_1752_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1642_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1642_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object** _args){
lean_object* v___x_1760_ = _args[0];
lean_object* v___x_1761_ = _args[1];
lean_object* v_attrKind_1762_ = _args[2];
lean_object* v_expty_x3f_1763_ = _args[3];
lean_object* v___f_1764_ = _args[4];
lean_object* v_cat_x3f_1765_ = _args[5];
lean_object* v___x_1766_ = _args[6];
lean_object* v___x_1767_ = _args[7];
lean_object* v_attrs_x3f_1768_ = _args[8];
lean_object* v___x_1769_ = _args[9];
lean_object* v___x_1770_ = _args[10];
lean_object* v___x_1771_ = _args[11];
lean_object* v_doc_x3f_1772_ = _args[12];
lean_object* v_kind_x3f_1773_ = _args[13];
lean_object* v_alts_1774_ = _args[14];
lean_object* v___y_1775_ = _args[15];
lean_object* v___y_1776_ = _args[16];
lean_object* v___y_1777_ = _args[17];
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Elab_Command_elabElabRules___lam__1(v___x_1760_, v___x_1761_, v_attrKind_1762_, v_expty_x3f_1763_, v___f_1764_, v_cat_x3f_1765_, v___x_1766_, v___x_1767_, v_attrs_x3f_1768_, v___x_1769_, v___x_1770_, v___x_1771_, v_doc_x3f_1772_, v_kind_x3f_1773_, v_alts_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v_alts_1774_);
lean_dec(v_attrs_x3f_1768_);
lean_dec(v___x_1767_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object* v___f_1806_, lean_object* v_stx_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1811_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1812_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0));
v___x_1814_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
lean_inc(v_stx_1807_);
v___x_1815_ = l_Lean_Syntax_isOfKind(v_stx_1807_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; 
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1816_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1816_;
}
else
{
lean_object* v___x_1817_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v_expty_x3f_1825_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v_cat_x3f_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v_expty_x3f_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v_cat_x3f_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v_attrs_x3f_1943_; lean_object* v_doc_x3f_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v___x_1817_ = lean_unsigned_to_nat(0u);
v___x_1990_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1817_);
v___x_1991_ = l_Lean_Syntax_isNone(v___x_1990_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; uint8_t v___x_1993_; 
v___x_1992_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1990_);
v___x_1993_ = l_Lean_Syntax_matchesNull(v___x_1990_, v___x_1992_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; 
lean_dec(v___x_1990_);
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1994_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1994_;
}
else
{
lean_object* v_doc_x3f_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v_doc_x3f_1995_ = l_Lean_Syntax_getArg(v___x_1990_, v___x_1817_);
lean_dec(v___x_1990_);
v___x_1996_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__6));
lean_inc(v_doc_x3f_1995_);
v___x_1997_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; 
lean_dec(v_doc_x3f_1995_);
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1998_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1998_;
}
else
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1999_, 0, v_doc_x3f_1995_);
v_doc_x3f_1974_ = v___x_1999_;
v___y_1975_ = v___y_1808_;
v___y_1976_ = v___y_1809_;
goto v___jp_1973_;
}
}
}
else
{
lean_object* v___x_2000_; 
lean_dec(v___x_1990_);
v___x_2000_ = lean_box(0);
v_doc_x3f_1974_ = v___x_2000_;
v___y_1975_ = v___y_1808_;
v___y_1976_ = v___y_1809_;
goto v___jp_1973_;
}
v___jp_1818_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1826_ = lean_unsigned_to_nat(7u);
v___x_1827_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1826_);
lean_dec(v_stx_1807_);
v___x_1828_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1829_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
lean_inc(v___x_1827_);
v___x_1830_ = l_Lean_Syntax_isOfKind(v___x_1827_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; 
lean_dec(v___x_1827_);
lean_dec(v_expty_x3f_1825_);
lean_dec(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___f_1806_);
v___x_1831_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1831_;
}
else
{
lean_object* v___f_1832_; lean_object* v___x_1833_; lean_object* v_alts_1834_; lean_object* v___x_1835_; 
v___f_1832_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lam__1___boxed), 18, 13);
lean_closure_set(v___f_1832_, 0, v___x_1829_);
lean_closure_set(v___f_1832_, 1, v___x_1814_);
lean_closure_set(v___f_1832_, 2, v___y_1821_);
lean_closure_set(v___f_1832_, 3, v_expty_x3f_1825_);
lean_closure_set(v___f_1832_, 4, v___f_1806_);
lean_closure_set(v___f_1832_, 5, v___y_1824_);
lean_closure_set(v___f_1832_, 6, v___x_1813_);
lean_closure_set(v___f_1832_, 7, v___x_1817_);
lean_closure_set(v___f_1832_, 8, v___y_1823_);
lean_closure_set(v___f_1832_, 9, v___x_1811_);
lean_closure_set(v___f_1832_, 10, v___x_1812_);
lean_closure_set(v___f_1832_, 11, v___x_1828_);
lean_closure_set(v___f_1832_, 12, v___y_1820_);
v___x_1833_ = l_Lean_Syntax_getArg(v___x_1827_, v___x_1817_);
lean_dec(v___x_1827_);
v_alts_1834_ = l_Lean_Syntax_getArgs(v___x_1833_);
lean_dec(v___x_1833_);
v___x_1835_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_1834_, v___x_1813_, v___f_1832_, v___y_1819_, v___y_1822_);
lean_dec_ref(v_alts_1834_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1845_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1845_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1845_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1840_ = lean_box(0);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v_a_1836_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1841_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
v_a_1846_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1835_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1835_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
}
v___jp_1854_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1863_ = lean_unsigned_to_nat(6u);
v___x_1864_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1863_);
v___x_1865_ = l_Lean_Syntax_isNone(v___x_1864_);
if (v___x_1865_ == 0)
{
uint8_t v___x_1866_; 
lean_inc(v___x_1864_);
v___x_1866_ = l_Lean_Syntax_matchesNull(v___x_1864_, v___y_1859_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; 
lean_dec(v___x_1864_);
lean_dec(v_cat_x3f_1860_);
lean_dec(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1867_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1867_;
}
else
{
lean_object* v_expty_x3f_1868_; lean_object* v___x_1869_; 
v_expty_x3f_1868_ = l_Lean_Syntax_getArg(v___x_1864_, v___y_1858_);
lean_dec(v___x_1864_);
v___x_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1869_, 0, v_expty_x3f_1868_);
v___y_1819_ = v___y_1861_;
v___y_1820_ = v___y_1855_;
v___y_1821_ = v___y_1856_;
v___y_1822_ = v___y_1862_;
v___y_1823_ = v___y_1857_;
v___y_1824_ = v_cat_x3f_1860_;
v_expty_x3f_1825_ = v___x_1869_;
goto v___jp_1818_;
}
}
else
{
lean_object* v___x_1870_; 
lean_dec(v___x_1864_);
v___x_1870_ = lean_box(0);
v___y_1819_ = v___y_1861_;
v___y_1820_ = v___y_1855_;
v___y_1821_ = v___y_1856_;
v___y_1822_ = v___y_1862_;
v___y_1823_ = v___y_1857_;
v___y_1824_ = v_cat_x3f_1860_;
v_expty_x3f_1825_ = v___x_1870_;
goto v___jp_1818_;
}
}
v___jp_1871_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v___x_1881_ = lean_unsigned_to_nat(7u);
v___x_1882_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1881_);
lean_dec(v_stx_1807_);
v___x_1883_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(v___y_1872_);
v___x_1884_ = l_Lean_Name_mkStr4(v___x_1811_, v___x_1812_, v___y_1872_, v___x_1883_);
lean_inc(v___x_1882_);
v___x_1885_ = l_Lean_Syntax_isOfKind(v___x_1882_, v___x_1884_);
lean_dec(v___x_1884_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; 
lean_dec(v___x_1882_);
lean_dec(v_expty_x3f_1878_);
lean_dec(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec(v___y_1873_);
v___x_1886_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1886_;
}
else
{
lean_object* v___x_1887_; lean_object* v_alts_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1887_ = l_Lean_Syntax_getArg(v___x_1882_, v___x_1817_);
lean_dec(v___x_1882_);
v_alts_1888_ = l_Lean_Syntax_getArgs(v___x_1887_);
lean_dec(v___x_1887_);
v___x_1889_ = l_Lean_TSyntax_getId(v___y_1876_);
lean_dec(v___y_1876_);
v___x_1890_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_1889_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1892_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc_n(v_a_1891_, 2);
lean_dec_ref_known(v___x_1890_, 1);
v___x_1892_ = l_Lean_Elab_Command_elabElabRulesAux(v___y_1877_, v___y_1874_, v___y_1873_, v_a_1891_, v___y_1875_, v_expty_x3f_1878_, v_alts_1888_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1875_);
lean_dec(v___y_1874_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1902_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1902_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1902_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v_a_1891_);
v___x_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
lean_ctor_set(v___x_1898_, 1, v_a_1893_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1898_);
v___x_1900_ = v___x_1895_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec(v_a_1891_);
v_a_1903_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1892_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1892_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec_ref(v_alts_1888_);
lean_dec(v_expty_x3f_1878_);
lean_dec(v___y_1877_);
lean_dec(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec(v___y_1873_);
v_a_1911_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1890_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1890_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
v___jp_1919_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1930_ = lean_unsigned_to_nat(6u);
v___x_1931_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1930_);
v___x_1932_ = l_Lean_Syntax_isNone(v___x_1931_);
if (v___x_1932_ == 0)
{
uint8_t v___x_1933_; 
lean_inc(v___x_1931_);
v___x_1933_ = l_Lean_Syntax_matchesNull(v___x_1931_, v___y_1925_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; 
lean_dec(v___x_1931_);
lean_dec(v_cat_x3f_1927_);
lean_dec(v___y_1926_);
lean_dec(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec(v___y_1921_);
lean_dec(v_stx_1807_);
v___x_1934_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1934_;
}
else
{
lean_object* v_expty_x3f_1935_; lean_object* v___x_1936_; 
v_expty_x3f_1935_ = l_Lean_Syntax_getArg(v___x_1931_, v___y_1922_);
lean_dec(v___x_1931_);
v___x_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1936_, 0, v_expty_x3f_1935_);
v___y_1872_ = v___y_1920_;
v___y_1873_ = v___y_1921_;
v___y_1874_ = v___y_1923_;
v___y_1875_ = v_cat_x3f_1927_;
v___y_1876_ = v___y_1924_;
v___y_1877_ = v___y_1926_;
v_expty_x3f_1878_ = v___x_1936_;
v___y_1879_ = v___y_1928_;
v___y_1880_ = v___y_1929_;
goto v___jp_1871_;
}
}
else
{
lean_object* v___x_1937_; 
lean_dec(v___x_1931_);
v___x_1937_ = lean_box(0);
v___y_1872_ = v___y_1920_;
v___y_1873_ = v___y_1921_;
v___y_1874_ = v___y_1923_;
v___y_1875_ = v_cat_x3f_1927_;
v___y_1876_ = v___y_1924_;
v___y_1877_ = v___y_1926_;
v_expty_x3f_1878_ = v___x_1937_;
v___y_1879_ = v___y_1928_;
v___y_1880_ = v___y_1929_;
goto v___jp_1871_;
}
}
v___jp_1938_:
{
lean_object* v___x_1944_; lean_object* v_attrKind_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1944_ = lean_unsigned_to_nat(2u);
v_attrKind_1945_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1944_);
v___x_1946_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1947_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__3));
lean_inc(v_attrKind_1945_);
v___x_1948_ = l_Lean_Syntax_isOfKind(v_attrKind_1945_, v___x_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; 
lean_dec(v_attrKind_1945_);
lean_dec(v_attrs_x3f_1943_);
lean_dec(v___y_1940_);
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1949_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1949_;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1950_ = lean_unsigned_to_nat(4u);
v___x_1951_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1950_);
lean_inc(v___x_1951_);
v___x_1952_ = l_Lean_Syntax_matchesNull(v___x_1951_, v___x_1817_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; uint8_t v___x_1954_; 
lean_dec_ref(v___f_1806_);
v___x_1953_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1951_);
v___x_1954_ = l_Lean_Syntax_matchesNull(v___x_1951_, v___x_1953_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; 
lean_dec(v___x_1951_);
lean_dec(v_attrKind_1945_);
lean_dec(v_attrs_x3f_1943_);
lean_dec(v___y_1940_);
lean_dec(v_stx_1807_);
v___x_1955_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1955_;
}
else
{
lean_object* v___x_1956_; lean_object* v_kind_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v___x_1956_ = lean_unsigned_to_nat(3u);
v_kind_1957_ = l_Lean_Syntax_getArg(v___x_1951_, v___x_1956_);
lean_dec(v___x_1951_);
v___x_1958_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1953_);
v___x_1959_ = l_Lean_Syntax_isNone(v___x_1958_);
if (v___x_1959_ == 0)
{
uint8_t v___x_1960_; 
lean_inc(v___x_1958_);
v___x_1960_ = l_Lean_Syntax_matchesNull(v___x_1958_, v___x_1944_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; 
lean_dec(v___x_1958_);
lean_dec(v_kind_1957_);
lean_dec(v_attrKind_1945_);
lean_dec(v_attrs_x3f_1943_);
lean_dec(v___y_1940_);
lean_dec(v_stx_1807_);
v___x_1961_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1961_;
}
else
{
lean_object* v_cat_x3f_1962_; lean_object* v___x_1963_; 
v_cat_x3f_1962_ = l_Lean_Syntax_getArg(v___x_1958_, v___y_1942_);
lean_dec(v___x_1958_);
v___x_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1963_, 0, v_cat_x3f_1962_);
v___y_1920_ = v___x_1946_;
v___y_1921_ = v_attrKind_1945_;
v___y_1922_ = v___y_1942_;
v___y_1923_ = v_attrs_x3f_1943_;
v___y_1924_ = v_kind_1957_;
v___y_1925_ = v___x_1944_;
v___y_1926_ = v___y_1940_;
v_cat_x3f_1927_ = v___x_1963_;
v___y_1928_ = v___y_1939_;
v___y_1929_ = v___y_1941_;
goto v___jp_1919_;
}
}
else
{
lean_object* v___x_1964_; 
lean_dec(v___x_1958_);
v___x_1964_ = lean_box(0);
v___y_1920_ = v___x_1946_;
v___y_1921_ = v_attrKind_1945_;
v___y_1922_ = v___y_1942_;
v___y_1923_ = v_attrs_x3f_1943_;
v___y_1924_ = v_kind_1957_;
v___y_1925_ = v___x_1944_;
v___y_1926_ = v___y_1940_;
v_cat_x3f_1927_ = v___x_1964_;
v___y_1928_ = v___y_1939_;
v___y_1929_ = v___y_1941_;
goto v___jp_1919_;
}
}
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
lean_dec(v___x_1951_);
v___x_1965_ = lean_unsigned_to_nat(5u);
v___x_1966_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1965_);
v___x_1967_ = l_Lean_Syntax_isNone(v___x_1966_);
if (v___x_1967_ == 0)
{
uint8_t v___x_1968_; 
lean_inc(v___x_1966_);
v___x_1968_ = l_Lean_Syntax_matchesNull(v___x_1966_, v___x_1944_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; 
lean_dec(v___x_1966_);
lean_dec(v_attrKind_1945_);
lean_dec(v_attrs_x3f_1943_);
lean_dec(v___y_1940_);
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1969_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1969_;
}
else
{
lean_object* v_cat_x3f_1970_; lean_object* v___x_1971_; 
v_cat_x3f_1970_ = l_Lean_Syntax_getArg(v___x_1966_, v___y_1942_);
lean_dec(v___x_1966_);
v___x_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1971_, 0, v_cat_x3f_1970_);
v___y_1855_ = v___y_1940_;
v___y_1856_ = v_attrKind_1945_;
v___y_1857_ = v_attrs_x3f_1943_;
v___y_1858_ = v___y_1942_;
v___y_1859_ = v___x_1944_;
v_cat_x3f_1860_ = v___x_1971_;
v___y_1861_ = v___y_1939_;
v___y_1862_ = v___y_1941_;
goto v___jp_1854_;
}
}
else
{
lean_object* v___x_1972_; 
lean_dec(v___x_1966_);
v___x_1972_ = lean_box(0);
v___y_1855_ = v___y_1940_;
v___y_1856_ = v_attrKind_1945_;
v___y_1857_ = v_attrs_x3f_1943_;
v___y_1858_ = v___y_1942_;
v___y_1859_ = v___x_1944_;
v_cat_x3f_1860_ = v___x_1972_;
v___y_1861_ = v___y_1939_;
v___y_1862_ = v___y_1941_;
goto v___jp_1854_;
}
}
}
}
v___jp_1973_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1977_ = lean_unsigned_to_nat(1u);
v___x_1978_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1977_);
v___x_1979_ = l_Lean_Syntax_isNone(v___x_1978_);
if (v___x_1979_ == 0)
{
uint8_t v___x_1980_; 
lean_inc(v___x_1978_);
v___x_1980_ = l_Lean_Syntax_matchesNull(v___x_1978_, v___x_1977_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; 
lean_dec(v___x_1978_);
lean_dec(v_doc_x3f_1974_);
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1981_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1981_;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1982_ = l_Lean_Syntax_getArg(v___x_1978_, v___x_1817_);
lean_dec(v___x_1978_);
v___x_1983_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v___x_1982_);
v___x_1984_ = l_Lean_Syntax_isOfKind(v___x_1982_, v___x_1983_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; 
lean_dec(v___x_1982_);
lean_dec(v_doc_x3f_1974_);
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1985_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1985_;
}
else
{
lean_object* v___x_1986_; lean_object* v_attrs_x3f_1987_; lean_object* v___x_1988_; 
v___x_1986_ = l_Lean_Syntax_getArg(v___x_1982_, v___x_1977_);
lean_dec(v___x_1982_);
v_attrs_x3f_1987_ = l_Lean_Syntax_getArgs(v___x_1986_);
lean_dec(v___x_1986_);
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v_attrs_x3f_1987_);
v___y_1939_ = v___y_1975_;
v___y_1940_ = v_doc_x3f_1974_;
v___y_1941_ = v___y_1976_;
v___y_1942_ = v___x_1977_;
v_attrs_x3f_1943_ = v___x_1988_;
goto v___jp_1938_;
}
}
}
else
{
lean_object* v___x_1989_; 
lean_dec(v___x_1978_);
v___x_1989_ = lean_box(0);
v___y_1939_ = v___y_1975_;
v___y_1940_ = v_doc_x3f_1974_;
v___y_1941_ = v___y_1976_;
v___y_1942_ = v___x_1977_;
v_attrs_x3f_1943_ = v___x_1989_;
goto v___jp_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object* v___f_2001_, lean_object* v_stx_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_Elab_Command_elabElabRules___lam__2(v___f_2001_, v_stx_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v___f_2014_; lean_object* v___x_2015_; 
v___f_2014_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___closed__1));
v___x_2015_ = l_Lean_Elab_Command_adaptRulesExpander(v___f_2014_, v_a_2010_, v_a_2011_, v_a_2012_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_Elab_Command_elabElabRules(v_a_2016_, v_a_2017_, v_a_2018_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1(){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2028_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2029_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_2030_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2031_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___boxed), 4, 0);
v___x_2032_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2028_, v___x_2029_, v___x_2030_, v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object* v_a_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3(){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2062_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6));
v___x_2063_ = l_Lean_addBuiltinDeclarationRanges(v___x_2061_, v___x_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object* v_a_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t v_sz_2066_, size_t v_i_2067_, lean_object* v_bs_2068_){
_start:
{
uint8_t v___x_2069_; 
v___x_2069_ = lean_usize_dec_lt(v_i_2067_, v_sz_2066_);
if (v___x_2069_ == 0)
{
return v_bs_2068_;
}
else
{
lean_object* v_v_2070_; lean_object* v___x_2071_; lean_object* v_bs_x27_2072_; size_t v___x_2073_; size_t v___x_2074_; lean_object* v___x_2075_; 
v_v_2070_ = lean_array_uget(v_bs_2068_, v_i_2067_);
v___x_2071_ = lean_unsigned_to_nat(0u);
v_bs_x27_2072_ = lean_array_uset(v_bs_2068_, v_i_2067_, v___x_2071_);
v___x_2073_ = ((size_t)1ULL);
v___x_2074_ = lean_usize_add(v_i_2067_, v___x_2073_);
v___x_2075_ = lean_array_uset(v_bs_x27_2072_, v_i_2067_, v_v_2070_);
v_i_2067_ = v___x_2074_;
v_bs_2068_ = v___x_2075_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object* v_sz_2077_, lean_object* v_i_2078_, lean_object* v_bs_2079_){
_start:
{
size_t v_sz_boxed_2080_; size_t v_i_boxed_2081_; lean_object* v_res_2082_; 
v_sz_boxed_2080_ = lean_unbox_usize(v_sz_2077_);
lean_dec(v_sz_2077_);
v_i_boxed_2081_ = lean_unbox_usize(v_i_2078_);
lean_dec(v_i_2078_);
v_res_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_boxed_2080_, v_i_boxed_2081_, v_bs_2079_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t v_sz_2083_, size_t v_i_2084_, lean_object* v_bs_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
uint8_t v___x_2089_; 
v___x_2089_ = lean_usize_dec_lt(v_i_2084_, v_sz_2083_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_bs_2085_);
return v___x_2090_;
}
else
{
lean_object* v_v_2091_; lean_object* v___x_2092_; lean_object* v_bs_x27_2093_; lean_object* v___x_2094_; 
v_v_2091_ = lean_array_uget(v_bs_2085_, v_i_2084_);
v___x_2092_ = lean_unsigned_to_nat(0u);
v_bs_x27_2093_ = lean_array_uset(v_bs_2085_, v_i_2084_, v___x_2092_);
v___x_2094_ = l_Lean_Elab_Command_expandMacroArg(v_v_2091_, v___y_2086_, v___y_2087_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; size_t v___x_2096_; size_t v___x_2097_; lean_object* v___x_2098_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = ((size_t)1ULL);
v___x_2097_ = lean_usize_add(v_i_2084_, v___x_2096_);
v___x_2098_ = lean_array_uset(v_bs_x27_2093_, v_i_2084_, v_a_2095_);
v_i_2084_ = v___x_2097_;
v_bs_2085_ = v___x_2098_;
goto _start;
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref(v_bs_x27_2093_);
v_a_2100_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2094_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2094_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object* v_sz_2108_, lean_object* v_i_2109_, lean_object* v_bs_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
size_t v_sz_boxed_2114_; size_t v_i_boxed_2115_; lean_object* v_res_2116_; 
v_sz_boxed_2114_ = lean_unbox_usize(v_sz_2108_);
lean_dec(v_sz_2108_);
v_i_boxed_2115_ = lean_unbox_usize(v_i_2109_);
lean_dec(v_i_2109_);
v_res_2116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_boxed_2114_, v_i_boxed_2115_, v_bs_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
return v_res_2116_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(lean_object* v_keys_2117_, lean_object* v_i_2118_, lean_object* v_k_2119_){
_start:
{
lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2120_ = lean_array_get_size(v_keys_2117_);
v___x_2121_ = lean_nat_dec_lt(v_i_2118_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_dec(v_i_2118_);
return v___x_2121_;
}
else
{
lean_object* v_k_x27_2122_; uint8_t v___x_2123_; 
v_k_x27_2122_ = lean_array_fget_borrowed(v_keys_2117_, v_i_2118_);
v___x_2123_ = l_Lean_instBEqExtraModUse_beq(v_k_2119_, v_k_x27_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = lean_unsigned_to_nat(1u);
v___x_2125_ = lean_nat_add(v_i_2118_, v___x_2124_);
lean_dec(v_i_2118_);
v_i_2118_ = v___x_2125_;
goto _start;
}
else
{
lean_dec(v_i_2118_);
return v___x_2121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_keys_2127_, lean_object* v_i_2128_, lean_object* v_k_2129_){
_start:
{
uint8_t v_res_2130_; lean_object* v_r_2131_; 
v_res_2130_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_2127_, v_i_2128_, v_k_2129_);
lean_dec_ref(v_k_2129_);
lean_dec_ref(v_keys_2127_);
v_r_2131_ = lean_box(v_res_2130_);
return v_r_2131_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(lean_object* v_x_2132_, size_t v_x_2133_, lean_object* v_x_2134_){
_start:
{
if (lean_obj_tag(v_x_2132_) == 0)
{
lean_object* v_es_2135_; lean_object* v___x_2136_; size_t v___x_2137_; size_t v___x_2138_; lean_object* v_j_2139_; lean_object* v___x_2140_; 
v_es_2135_ = lean_ctor_get(v_x_2132_, 0);
v___x_2136_ = lean_box(2);
v___x_2137_ = ((size_t)31ULL);
v___x_2138_ = lean_usize_land(v_x_2133_, v___x_2137_);
v_j_2139_ = lean_usize_to_nat(v___x_2138_);
v___x_2140_ = lean_array_get_borrowed(v___x_2136_, v_es_2135_, v_j_2139_);
lean_dec(v_j_2139_);
switch(lean_obj_tag(v___x_2140_))
{
case 0:
{
lean_object* v_key_2141_; uint8_t v___x_2142_; 
v_key_2141_ = lean_ctor_get(v___x_2140_, 0);
v___x_2142_ = l_Lean_instBEqExtraModUse_beq(v_x_2134_, v_key_2141_);
return v___x_2142_;
}
case 1:
{
lean_object* v_node_2143_; size_t v___x_2144_; size_t v___x_2145_; 
v_node_2143_ = lean_ctor_get(v___x_2140_, 0);
v___x_2144_ = ((size_t)5ULL);
v___x_2145_ = lean_usize_shift_right(v_x_2133_, v___x_2144_);
v_x_2132_ = v_node_2143_;
v_x_2133_ = v___x_2145_;
goto _start;
}
default: 
{
uint8_t v___x_2147_; 
v___x_2147_ = 0;
return v___x_2147_;
}
}
}
else
{
lean_object* v_ks_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v_ks_2148_ = lean_ctor_get(v_x_2132_, 0);
v___x_2149_ = lean_unsigned_to_nat(0u);
v___x_2150_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_ks_2148_, v___x_2149_, v_x_2134_);
return v___x_2150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_x_2151_, lean_object* v_x_2152_, lean_object* v_x_2153_){
_start:
{
size_t v_x_16585__boxed_2154_; uint8_t v_res_2155_; lean_object* v_r_2156_; 
v_x_16585__boxed_2154_ = lean_unbox_usize(v_x_2152_);
lean_dec(v_x_2152_);
v_res_2155_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2151_, v_x_16585__boxed_2154_, v_x_2153_);
lean_dec_ref(v_x_2153_);
lean_dec_ref(v_x_2151_);
v_r_2156_ = lean_box(v_res_2155_);
return v_r_2156_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(lean_object* v_x_2157_, lean_object* v_x_2158_){
_start:
{
uint64_t v___x_2159_; size_t v___x_2160_; uint8_t v___x_2161_; 
v___x_2159_ = l_Lean_instHashableExtraModUse_hash(v_x_2158_);
v___x_2160_ = lean_uint64_to_usize(v___x_2159_);
v___x_2161_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2157_, v___x_2160_, v_x_2158_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_x_2162_, lean_object* v_x_2163_){
_start:
{
uint8_t v_res_2164_; lean_object* v_r_2165_; 
v_res_2164_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_2162_, v_x_2163_);
lean_dec_ref(v_x_2163_);
lean_dec_ref(v_x_2162_);
v_r_2165_ = lean_box(v_res_2164_);
return v_r_2165_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2166_; double v___x_2167_; 
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = lean_float_of_nat(v___x_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object* v_cls_2171_, lean_object* v_msg_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_Elab_Command_getRef___redArg(v___y_2173_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2178_; lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2227_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___x_2178_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(v_msg_2172_, v___y_2174_);
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2227_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2227_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v_traceState_2184_; lean_object* v_env_2185_; lean_object* v_messages_2186_; lean_object* v_scopes_2187_; lean_object* v_usedQuotCtxts_2188_; lean_object* v_nextMacroScope_2189_; lean_object* v_maxRecDepth_2190_; lean_object* v_ngen_2191_; lean_object* v_auxDeclNGen_2192_; lean_object* v_infoState_2193_; lean_object* v_snapshotTasks_2194_; lean_object* v_prevLinterStates_2195_; lean_object* v_codeQualityEntryTasks_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2226_; 
v___x_2183_ = lean_st_ref_take(v___y_2174_);
v_traceState_2184_ = lean_ctor_get(v___x_2183_, 9);
v_env_2185_ = lean_ctor_get(v___x_2183_, 0);
v_messages_2186_ = lean_ctor_get(v___x_2183_, 1);
v_scopes_2187_ = lean_ctor_get(v___x_2183_, 2);
v_usedQuotCtxts_2188_ = lean_ctor_get(v___x_2183_, 3);
v_nextMacroScope_2189_ = lean_ctor_get(v___x_2183_, 4);
v_maxRecDepth_2190_ = lean_ctor_get(v___x_2183_, 5);
v_ngen_2191_ = lean_ctor_get(v___x_2183_, 6);
v_auxDeclNGen_2192_ = lean_ctor_get(v___x_2183_, 7);
v_infoState_2193_ = lean_ctor_get(v___x_2183_, 8);
v_snapshotTasks_2194_ = lean_ctor_get(v___x_2183_, 10);
v_prevLinterStates_2195_ = lean_ctor_get(v___x_2183_, 11);
v_codeQualityEntryTasks_2196_ = lean_ctor_get(v___x_2183_, 12);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2198_ = v___x_2183_;
v_isShared_2199_ = v_isSharedCheck_2226_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2196_);
lean_inc(v_prevLinterStates_2195_);
lean_inc(v_snapshotTasks_2194_);
lean_inc(v_traceState_2184_);
lean_inc(v_infoState_2193_);
lean_inc(v_auxDeclNGen_2192_);
lean_inc(v_ngen_2191_);
lean_inc(v_maxRecDepth_2190_);
lean_inc(v_nextMacroScope_2189_);
lean_inc(v_usedQuotCtxts_2188_);
lean_inc(v_scopes_2187_);
lean_inc(v_messages_2186_);
lean_inc(v_env_2185_);
lean_dec(v___x_2183_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2226_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
uint64_t v_tid_2200_; lean_object* v_traces_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2225_; 
v_tid_2200_ = lean_ctor_get_uint64(v_traceState_2184_, sizeof(void*)*1);
v_traces_2201_ = lean_ctor_get(v_traceState_2184_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_traceState_2184_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2203_ = v_traceState_2184_;
v_isShared_2204_ = v_isSharedCheck_2225_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_traces_2201_);
lean_dec(v_traceState_2184_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2225_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; double v___x_2207_; uint8_t v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2205_ = lean_box(0);
v___x_2206_ = lean_box(0);
v___x_2207_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0);
v___x_2208_ = 0;
v___x_2209_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2210_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2210_, 0, v_cls_2171_);
lean_ctor_set(v___x_2210_, 1, v___x_2206_);
lean_ctor_set(v___x_2210_, 2, v___x_2209_);
lean_ctor_set_float(v___x_2210_, sizeof(void*)*3, v___x_2207_);
lean_ctor_set_float(v___x_2210_, sizeof(void*)*3 + 8, v___x_2207_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*3 + 16, v___x_2208_);
v___x_2211_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2));
v___x_2212_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2210_);
lean_ctor_set(v___x_2212_, 1, v_a_2179_);
lean_ctor_set(v___x_2212_, 2, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2213_, 0, v_a_2177_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = l_Lean_PersistentArray_push___redArg(v_traces_2201_, v___x_2213_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v___x_2214_);
v___x_2216_ = v___x_2203_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2214_);
lean_ctor_set_uint64(v_reuseFailAlloc_2224_, sizeof(void*)*1, v_tid_2200_);
v___x_2216_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
lean_object* v___x_2218_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 9, v___x_2216_);
v___x_2218_ = v___x_2198_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_env_2185_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_messages_2186_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_scopes_2187_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v_usedQuotCtxts_2188_);
lean_ctor_set(v_reuseFailAlloc_2223_, 4, v_nextMacroScope_2189_);
lean_ctor_set(v_reuseFailAlloc_2223_, 5, v_maxRecDepth_2190_);
lean_ctor_set(v_reuseFailAlloc_2223_, 6, v_ngen_2191_);
lean_ctor_set(v_reuseFailAlloc_2223_, 7, v_auxDeclNGen_2192_);
lean_ctor_set(v_reuseFailAlloc_2223_, 8, v_infoState_2193_);
lean_ctor_set(v_reuseFailAlloc_2223_, 9, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2223_, 10, v_snapshotTasks_2194_);
lean_ctor_set(v_reuseFailAlloc_2223_, 11, v_prevLinterStates_2195_);
lean_ctor_set(v_reuseFailAlloc_2223_, 12, v_codeQualityEntryTasks_2196_);
v___x_2218_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2219_ = lean_st_ref_put(v___y_2174_, v___x_2218_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2205_);
v___x_2221_ = v___x_2181_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2205_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec_ref(v_msg_2172_);
lean_dec(v_cls_2171_);
v_a_2228_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2176_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2176_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object* v_cls_2236_, lean_object* v_msg_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2236_, v_msg_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___lam__0(lean_object* v___x_2242_, lean_object* v_entry_2243_, lean_object* v_s_2244_){
_start:
{
lean_object* v_addEntryFn_2245_; lean_object* v_importedEntries_2246_; lean_object* v_state_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2255_; 
v_addEntryFn_2245_ = lean_ctor_get(v___x_2242_, 3);
lean_inc(v_addEntryFn_2245_);
lean_dec_ref(v___x_2242_);
v_importedEntries_2246_ = lean_ctor_get(v_s_2244_, 0);
v_state_2247_ = lean_ctor_get(v_s_2244_, 1);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_s_2244_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2249_ = v_s_2244_;
v_isShared_2250_ = v_isSharedCheck_2255_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_state_2247_);
lean_inc(v_importedEntries_2246_);
lean_dec(v_s_2244_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2255_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v_state_2251_; lean_object* v___x_2253_; 
v_state_2251_ = lean_apply_2(v_addEntryFn_2245_, v_state_2247_, v_entry_2243_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 1, v_state_2251_);
v___x_2253_ = v___x_2249_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_importedEntries_2246_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_state_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2256_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3));
v___x_2262_ = l_Lean_stringToMessageData(v___x_2261_);
return v___x_2262_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5));
v___x_2265_ = l_Lean_stringToMessageData(v___x_2264_);
return v___x_2265_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2267_ = l_Lean_stringToMessageData(v___x_2266_);
return v___x_2267_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v_cls_2271_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2));
v___x_2272_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9));
v___x_2273_ = l_Lean_Name_append(v___x_2272_, v_cls_2271_);
return v___x_2273_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11));
v___x_2276_ = l_Lean_stringToMessageData(v___x_2275_);
return v___x_2276_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13));
v___x_2279_ = l_Lean_stringToMessageData(v___x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(lean_object* v_mod_2284_, uint8_t v_isMeta_2285_, lean_object* v_hint_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v_env_2311_; uint8_t v_isExporting_2312_; lean_object* v_entry_2313_; lean_object* v___x_2314_; lean_object* v_env_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v___x_2309_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0);
v___x_2310_ = lean_st_ref_get(v___y_2288_);
v_env_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc_ref(v_env_2311_);
lean_dec(v___x_2310_);
v_isExporting_2312_ = lean_ctor_get_uint8(v_env_2311_, sizeof(void*)*13);
lean_dec_ref(v_env_2311_);
lean_inc(v_mod_2284_);
v_entry_2313_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2313_, 0, v_mod_2284_);
lean_ctor_set_uint8(v_entry_2313_, sizeof(void*)*1, v_isExporting_2312_);
lean_ctor_set_uint8(v_entry_2313_, sizeof(void*)*1 + 1, v_isMeta_2285_);
v___x_2314_ = lean_st_ref_get(v___y_2288_);
v_env_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc_ref(v_env_2315_);
lean_dec(v___x_2314_);
v___x_2316_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2317_ = lean_box(1);
v___x_2318_ = lean_box(0);
v___x_2319_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2309_, v___x_2316_, v_env_2315_, v___x_2317_, v___x_2318_);
v___x_2320_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v___x_2319_, v_entry_2313_);
lean_dec(v___x_2319_);
if (v___x_2320_ == 0)
{
lean_object* v___f_2321_; uint8_t v___x_2322_; lean_object* v___y_2324_; lean_object* v_cls_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v_scopes_2370_; lean_object* v___x_2371_; lean_object* v_opts_2372_; uint8_t v_hasTrace_2373_; 
v___f_2321_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_2321_, 0, v___x_2316_);
lean_closure_set(v___f_2321_, 1, v_entry_2313_);
v___x_2322_ = 1;
v_cls_2346_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2));
v___x_2347_ = l_Lean_inheritedTraceOptions;
v___x_2348_ = lean_st_ref_get(v___x_2347_);
v___x_2349_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2350_ = lean_st_ref_get(v___y_2288_);
v_scopes_2370_ = lean_ctor_get(v___x_2350_, 2);
lean_inc(v_scopes_2370_);
lean_dec(v___x_2350_);
v___x_2371_ = l_List_head_x21___redArg(v___x_2349_, v_scopes_2370_);
lean_dec(v_scopes_2370_);
v_opts_2372_ = lean_ctor_get(v___x_2371_, 1);
lean_inc_ref(v_opts_2372_);
lean_dec(v___x_2371_);
v_hasTrace_2373_ = lean_ctor_get_uint8(v_opts_2372_, sizeof(void*)*1);
if (v_hasTrace_2373_ == 0)
{
lean_dec_ref(v_opts_2372_);
lean_dec(v___x_2348_);
lean_dec(v_hint_2286_);
lean_dec(v_mod_2284_);
v___y_2324_ = v___y_2288_;
goto v___jp_2323_;
}
else
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10);
v___x_2375_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2348_, v_opts_2372_, v___x_2374_);
lean_dec_ref(v_opts_2372_);
lean_dec(v___x_2348_);
if (v___x_2375_ == 0)
{
lean_dec(v_hint_2286_);
lean_dec(v_mod_2284_);
v___y_2324_ = v___y_2288_;
goto v___jp_2323_;
}
else
{
lean_object* v___x_2376_; lean_object* v___y_2378_; 
v___x_2376_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12);
if (v_isExporting_2312_ == 0)
{
lean_object* v___x_2385_; 
v___x_2385_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17));
v___y_2378_ = v___x_2385_;
goto v___jp_2377_;
}
else
{
lean_object* v___x_2386_; 
v___x_2386_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18));
v___y_2378_ = v___x_2386_;
goto v___jp_2377_;
}
v___jp_2377_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_inc_ref(v___y_2378_);
v___x_2379_ = l_Lean_stringToMessageData(v___y_2378_);
v___x_2380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2376_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14);
v___x_2382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2380_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
if (v_isMeta_2285_ == 0)
{
lean_object* v___x_2383_; 
v___x_2383_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15));
v___y_2357_ = v___x_2382_;
v___y_2358_ = v___x_2383_;
goto v___jp_2356_;
}
else
{
lean_object* v___x_2384_; 
v___x_2384_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16));
v___y_2357_ = v___x_2382_;
v___y_2358_ = v___x_2384_;
goto v___jp_2356_;
}
}
}
}
v___jp_2323_:
{
lean_object* v___x_2325_; lean_object* v_toEnvExtension_2326_; lean_object* v_env_2327_; lean_object* v_messages_2328_; lean_object* v_scopes_2329_; lean_object* v_usedQuotCtxts_2330_; lean_object* v_nextMacroScope_2331_; lean_object* v_maxRecDepth_2332_; lean_object* v_ngen_2333_; lean_object* v_auxDeclNGen_2334_; lean_object* v_infoState_2335_; lean_object* v_traceState_2336_; lean_object* v_snapshotTasks_2337_; lean_object* v_prevLinterStates_2338_; lean_object* v_codeQualityEntryTasks_2339_; lean_object* v_asyncMode_2340_; uint8_t v_logWrites_2341_; lean_object* v___x_2342_; 
v___x_2325_ = lean_st_ref_take(v___y_2324_);
v_toEnvExtension_2326_ = lean_ctor_get(v___x_2316_, 0);
v_env_2327_ = lean_ctor_get(v___x_2325_, 0);
lean_inc_ref(v_env_2327_);
v_messages_2328_ = lean_ctor_get(v___x_2325_, 1);
lean_inc_ref(v_messages_2328_);
v_scopes_2329_ = lean_ctor_get(v___x_2325_, 2);
lean_inc(v_scopes_2329_);
v_usedQuotCtxts_2330_ = lean_ctor_get(v___x_2325_, 3);
lean_inc(v_usedQuotCtxts_2330_);
v_nextMacroScope_2331_ = lean_ctor_get(v___x_2325_, 4);
lean_inc(v_nextMacroScope_2331_);
v_maxRecDepth_2332_ = lean_ctor_get(v___x_2325_, 5);
lean_inc(v_maxRecDepth_2332_);
v_ngen_2333_ = lean_ctor_get(v___x_2325_, 6);
lean_inc_ref(v_ngen_2333_);
v_auxDeclNGen_2334_ = lean_ctor_get(v___x_2325_, 7);
lean_inc_ref(v_auxDeclNGen_2334_);
v_infoState_2335_ = lean_ctor_get(v___x_2325_, 8);
lean_inc_ref(v_infoState_2335_);
v_traceState_2336_ = lean_ctor_get(v___x_2325_, 9);
lean_inc_ref(v_traceState_2336_);
v_snapshotTasks_2337_ = lean_ctor_get(v___x_2325_, 10);
lean_inc_ref(v_snapshotTasks_2337_);
v_prevLinterStates_2338_ = lean_ctor_get(v___x_2325_, 11);
lean_inc(v_prevLinterStates_2338_);
v_codeQualityEntryTasks_2339_ = lean_ctor_get(v___x_2325_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2339_);
lean_dec(v___x_2325_);
v_asyncMode_2340_ = lean_ctor_get(v_toEnvExtension_2326_, 2);
v_logWrites_2341_ = lean_ctor_get_uint8(v_toEnvExtension_2326_, sizeof(void*)*6);
v___x_2342_ = lean_box(0);
if (v_logWrites_2341_ == 0)
{
lean_object* v___x_2343_; 
lean_inc_ref(v_toEnvExtension_2326_);
v___x_2343_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2326_, v_env_2327_, v___f_2321_, v_asyncMode_2340_, v___x_2318_, v___x_2322_);
v___y_2291_ = v_auxDeclNGen_2334_;
v___y_2292_ = v_snapshotTasks_2337_;
v___y_2293_ = v_usedQuotCtxts_2330_;
v___y_2294_ = v_ngen_2333_;
v___y_2295_ = v_maxRecDepth_2332_;
v___y_2296_ = v___y_2324_;
v___y_2297_ = v_traceState_2336_;
v___y_2298_ = v_prevLinterStates_2338_;
v___y_2299_ = v_scopes_2329_;
v___y_2300_ = v_nextMacroScope_2331_;
v___y_2301_ = v_codeQualityEntryTasks_2339_;
v___y_2302_ = v_messages_2328_;
v___y_2303_ = v___x_2342_;
v___y_2304_ = v_infoState_2335_;
v___y_2305_ = v___x_2343_;
goto v___jp_2290_;
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_inc_ref_n(v_toEnvExtension_2326_, 2);
v___x_2344_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2326_, v_env_2327_);
lean_dec_ref(v_env_2327_);
v___x_2345_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2326_, v___x_2344_, v___f_2321_, v_asyncMode_2340_, v___x_2318_, v___x_2322_);
v___y_2291_ = v_auxDeclNGen_2334_;
v___y_2292_ = v_snapshotTasks_2337_;
v___y_2293_ = v_usedQuotCtxts_2330_;
v___y_2294_ = v_ngen_2333_;
v___y_2295_ = v_maxRecDepth_2332_;
v___y_2296_ = v___y_2324_;
v___y_2297_ = v_traceState_2336_;
v___y_2298_ = v_prevLinterStates_2338_;
v___y_2299_ = v_scopes_2329_;
v___y_2300_ = v_nextMacroScope_2331_;
v___y_2301_ = v_codeQualityEntryTasks_2339_;
v___y_2302_ = v_messages_2328_;
v___y_2303_ = v___x_2342_;
v___y_2304_ = v_infoState_2335_;
v___y_2305_ = v___x_2345_;
goto v___jp_2290_;
}
}
v___jp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___y_2352_);
lean_ctor_set(v___x_2354_, 1, v___y_2353_);
v___x_2355_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2346_, v___x_2354_, v___y_2287_, v___y_2288_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_dec_ref_known(v___x_2355_, 1);
v___y_2324_ = v___y_2288_;
goto v___jp_2323_;
}
else
{
lean_dec_ref(v___f_2321_);
return v___x_2355_;
}
}
v___jp_2356_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; 
lean_inc_ref(v___y_2358_);
v___x_2359_ = l_Lean_stringToMessageData(v___y_2358_);
v___x_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___y_2357_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4);
v___x_2362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2360_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
v___x_2363_ = l_Lean_MessageData_ofName(v_mod_2284_);
v___x_2364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2362_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
v___x_2365_ = l_Lean_Name_isAnonymous(v_hint_2286_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2366_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6);
v___x_2367_ = l_Lean_MessageData_ofName(v_hint_2286_);
v___x_2368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2366_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___y_2352_ = v___x_2364_;
v___y_2353_ = v___x_2368_;
goto v___jp_2351_;
}
else
{
lean_object* v___x_2369_; 
lean_dec(v_hint_2286_);
v___x_2369_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7);
v___y_2352_ = v___x_2364_;
v___y_2353_ = v___x_2369_;
goto v___jp_2351_;
}
}
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
lean_dec_ref_known(v_entry_2313_, 1);
lean_dec(v_hint_2286_);
lean_dec(v_mod_2284_);
v___x_2387_ = lean_box(0);
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
return v___x_2388_;
}
v___jp_2290_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2306_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2306_, 0, v___y_2305_);
lean_ctor_set(v___x_2306_, 1, v___y_2302_);
lean_ctor_set(v___x_2306_, 2, v___y_2299_);
lean_ctor_set(v___x_2306_, 3, v___y_2293_);
lean_ctor_set(v___x_2306_, 4, v___y_2300_);
lean_ctor_set(v___x_2306_, 5, v___y_2295_);
lean_ctor_set(v___x_2306_, 6, v___y_2294_);
lean_ctor_set(v___x_2306_, 7, v___y_2291_);
lean_ctor_set(v___x_2306_, 8, v___y_2304_);
lean_ctor_set(v___x_2306_, 9, v___y_2297_);
lean_ctor_set(v___x_2306_, 10, v___y_2292_);
lean_ctor_set(v___x_2306_, 11, v___y_2298_);
lean_ctor_set(v___x_2306_, 12, v___y_2301_);
v___x_2307_ = lean_st_ref_put(v___y_2296_, v___x_2306_);
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___y_2303_);
return v___x_2308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___boxed(lean_object* v_mod_2389_, lean_object* v_isMeta_2390_, lean_object* v_hint_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
uint8_t v_isMeta_boxed_2395_; lean_object* v_res_2396_; 
v_isMeta_boxed_2395_ = lean_unbox(v_isMeta_2390_);
v_res_2396_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_mod_2389_, v_isMeta_boxed_2395_, v_hint_2391_, v___y_2392_, v___y_2393_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(lean_object* v___x_2397_, lean_object* v_declName_2398_, lean_object* v_as_2399_, size_t v_sz_2400_, size_t v_i_2401_, lean_object* v_b_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
uint8_t v___x_2406_; 
v___x_2406_ = lean_usize_dec_lt(v_i_2401_, v_sz_2400_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; 
lean_dec(v_declName_2398_);
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v_b_2402_);
return v___x_2407_;
}
else
{
lean_object* v___x_2408_; lean_object* v_modules_2409_; lean_object* v___x_2410_; lean_object* v_a_2411_; lean_object* v___x_2412_; lean_object* v_toImport_2413_; lean_object* v_module_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; lean_object* v___x_2417_; 
v___x_2408_ = l_Lean_Environment_header(v___x_2397_);
v_modules_2409_ = lean_ctor_get(v___x_2408_, 3);
lean_inc_ref(v_modules_2409_);
lean_dec_ref(v___x_2408_);
v___x_2410_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2411_ = lean_array_uget_borrowed(v_as_2399_, v_i_2401_);
v___x_2412_ = lean_array_get(v___x_2410_, v_modules_2409_, v_a_2411_);
lean_dec_ref(v_modules_2409_);
v_toImport_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc_ref(v_toImport_2413_);
lean_dec(v___x_2412_);
v_module_2414_ = lean_ctor_get(v_toImport_2413_, 0);
lean_inc(v_module_2414_);
lean_dec_ref(v_toImport_2413_);
v___x_2415_ = lean_box(0);
v___x_2416_ = 0;
lean_inc(v_declName_2398_);
v___x_2417_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2414_, v___x_2416_, v_declName_2398_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2417_) == 0)
{
size_t v___x_2418_; size_t v___x_2419_; 
lean_dec_ref_known(v___x_2417_, 1);
v___x_2418_ = ((size_t)1ULL);
v___x_2419_ = lean_usize_add(v_i_2401_, v___x_2418_);
v_i_2401_ = v___x_2419_;
v_b_2402_ = v___x_2415_;
goto _start;
}
else
{
lean_dec(v_declName_2398_);
return v___x_2417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4___boxed(lean_object* v___x_2421_, lean_object* v_declName_2422_, lean_object* v_as_2423_, lean_object* v_sz_2424_, lean_object* v_i_2425_, lean_object* v_b_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
size_t v_sz_boxed_2430_; size_t v_i_boxed_2431_; lean_object* v_res_2432_; 
v_sz_boxed_2430_ = lean_unbox_usize(v_sz_2424_);
lean_dec(v_sz_2424_);
v_i_boxed_2431_ = lean_unbox_usize(v_i_2425_);
lean_dec(v_i_2425_);
v_res_2432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v___x_2421_, v_declName_2422_, v_as_2423_, v_sz_boxed_2430_, v_i_boxed_2431_, v_b_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec_ref(v_as_2423_);
lean_dec_ref(v___x_2421_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(lean_object* v_a_2433_, lean_object* v_x_2434_){
_start:
{
if (lean_obj_tag(v_x_2434_) == 0)
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_box(0);
return v___x_2435_;
}
else
{
lean_object* v_key_2436_; lean_object* v_value_2437_; lean_object* v_tail_2438_; uint8_t v___x_2439_; 
v_key_2436_ = lean_ctor_get(v_x_2434_, 0);
v_value_2437_ = lean_ctor_get(v_x_2434_, 1);
v_tail_2438_ = lean_ctor_get(v_x_2434_, 2);
v___x_2439_ = lean_name_eq(v_key_2436_, v_a_2433_);
if (v___x_2439_ == 0)
{
v_x_2434_ = v_tail_2438_;
goto _start;
}
else
{
lean_object* v___x_2441_; 
lean_inc(v_value_2437_);
v___x_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2441_, 0, v_value_2437_);
return v___x_2441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_a_2442_, lean_object* v_x_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2442_, v_x_2443_);
lean_dec(v_x_2443_);
lean_dec(v_a_2442_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(lean_object* v_m_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v_buckets_2447_; lean_object* v___x_2448_; uint64_t v___y_2450_; 
v_buckets_2447_ = lean_ctor_get(v_m_2445_, 1);
v___x_2448_ = lean_array_get_size(v_buckets_2447_);
if (lean_obj_tag(v_a_2446_) == 0)
{
uint64_t v___x_2464_; 
v___x_2464_ = 1723ULL;
v___y_2450_ = v___x_2464_;
goto v___jp_2449_;
}
else
{
uint64_t v_hash_2465_; 
v_hash_2465_ = lean_ctor_get_uint64(v_a_2446_, sizeof(void*)*2);
v___y_2450_ = v_hash_2465_;
goto v___jp_2449_;
}
v___jp_2449_:
{
uint64_t v___x_2451_; uint64_t v___x_2452_; uint64_t v_fold_2453_; uint64_t v___x_2454_; uint64_t v___x_2455_; uint64_t v___x_2456_; size_t v___x_2457_; size_t v___x_2458_; size_t v___x_2459_; size_t v___x_2460_; size_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2451_ = 32ULL;
v___x_2452_ = lean_uint64_shift_right(v___y_2450_, v___x_2451_);
v_fold_2453_ = lean_uint64_xor(v___y_2450_, v___x_2452_);
v___x_2454_ = 16ULL;
v___x_2455_ = lean_uint64_shift_right(v_fold_2453_, v___x_2454_);
v___x_2456_ = lean_uint64_xor(v_fold_2453_, v___x_2455_);
v___x_2457_ = lean_uint64_to_usize(v___x_2456_);
v___x_2458_ = lean_usize_of_nat(v___x_2448_);
v___x_2459_ = ((size_t)1ULL);
v___x_2460_ = lean_usize_sub(v___x_2458_, v___x_2459_);
v___x_2461_ = lean_usize_land(v___x_2457_, v___x_2460_);
v___x_2462_ = lean_array_uget_borrowed(v_buckets_2447_, v___x_2461_);
v___x_2463_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2446_, v___x_2462_);
return v___x_2463_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_2466_, v_a_2467_);
lean_dec(v_a_2467_);
lean_dec_ref(v_m_2466_);
return v_res_2468_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object* v_declName_2472_, uint8_t v_isMeta_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v_env_2482_; lean_object* v___y_2484_; lean_object* v___x_2497_; 
v___x_2477_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0);
v___x_2478_ = lean_st_ref_get(v___y_2475_);
v_env_2482_ = lean_ctor_get(v___x_2478_, 0);
lean_inc_ref(v_env_2482_);
lean_dec(v___x_2478_);
v___x_2497_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2482_, v_declName_2472_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_dec_ref(v_env_2482_);
lean_dec(v_declName_2472_);
goto v___jp_2479_;
}
else
{
lean_object* v_val_2498_; lean_object* v___x_2499_; lean_object* v_modules_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; 
v_val_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_val_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2499_ = l_Lean_Environment_header(v_env_2482_);
v_modules_2500_ = lean_ctor_get(v___x_2499_, 3);
lean_inc_ref(v_modules_2500_);
lean_dec_ref(v___x_2499_);
v___x_2501_ = lean_array_get_size(v_modules_2500_);
v___x_2502_ = lean_nat_dec_lt(v_val_2498_, v___x_2501_);
if (v___x_2502_ == 0)
{
lean_dec_ref(v_modules_2500_);
lean_dec(v_val_2498_);
lean_dec_ref(v_env_2482_);
lean_dec(v_declName_2472_);
goto v___jp_2479_;
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___y_2506_; 
v___x_2503_ = lean_array_fget(v_modules_2500_, v_val_2498_);
lean_dec(v_val_2498_);
lean_dec_ref(v_modules_2500_);
v___x_2504_ = lean_st_ref_get(v___y_2475_);
if (v_isMeta_2473_ == 0)
{
lean_dec(v___x_2504_);
v___y_2506_ = v_isMeta_2473_;
goto v___jp_2505_;
}
else
{
lean_object* v_env_2517_; uint8_t v___x_2518_; 
v_env_2517_ = lean_ctor_get(v___x_2504_, 0);
lean_inc_ref(v_env_2517_);
lean_dec(v___x_2504_);
lean_inc(v_declName_2472_);
v___x_2518_ = l_Lean_isMarkedMeta(v_env_2517_, v_declName_2472_);
if (v___x_2518_ == 0)
{
v___y_2506_ = v_isMeta_2473_;
goto v___jp_2505_;
}
else
{
uint8_t v___x_2519_; 
v___x_2519_ = 0;
v___y_2506_ = v___x_2519_;
goto v___jp_2505_;
}
}
v___jp_2505_:
{
lean_object* v_toImport_2507_; lean_object* v_module_2508_; lean_object* v___x_2509_; 
v_toImport_2507_ = lean_ctor_get(v___x_2503_, 0);
lean_inc_ref(v_toImport_2507_);
lean_dec(v___x_2503_);
v_module_2508_ = lean_ctor_get(v_toImport_2507_, 0);
lean_inc(v_module_2508_);
lean_dec_ref(v_toImport_2507_);
lean_inc(v_declName_2472_);
v___x_2509_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2508_, v___y_2506_, v_declName_2472_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_dec_ref_known(v___x_2509_, 1);
v___x_2510_ = l_Lean_indirectModUseExt;
v___x_2511_ = lean_box(1);
v___x_2512_ = lean_box(0);
lean_inc_ref(v_env_2482_);
v___x_2513_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2477_, v___x_2510_, v_env_2482_, v___x_2511_, v___x_2512_);
v___x_2514_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v___x_2513_, v_declName_2472_);
lean_dec(v___x_2513_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v___x_2515_; 
v___x_2515_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1));
v___y_2484_ = v___x_2515_;
goto v___jp_2483_;
}
else
{
lean_object* v_val_2516_; 
v_val_2516_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_val_2516_);
lean_dec_ref_known(v___x_2514_, 1);
v___y_2484_ = v_val_2516_;
goto v___jp_2483_;
}
}
else
{
lean_dec_ref(v_env_2482_);
lean_dec(v_declName_2472_);
return v___x_2509_;
}
}
}
}
v___jp_2479_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = lean_box(0);
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
return v___x_2481_;
}
v___jp_2483_:
{
lean_object* v___x_2485_; size_t v_sz_2486_; size_t v___x_2487_; lean_object* v___x_2488_; 
v___x_2485_ = lean_box(0);
v_sz_2486_ = lean_array_size(v___y_2484_);
v___x_2487_ = ((size_t)0ULL);
v___x_2488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v_env_2482_, v_declName_2472_, v___y_2484_, v_sz_2486_, v___x_2487_, v___x_2485_, v___y_2474_, v___y_2475_);
lean_dec_ref(v___y_2484_);
lean_dec_ref(v_env_2482_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; 
v_unused_2496_ = lean_ctor_get(v___x_2488_, 0);
lean_dec(v_unused_2496_);
v___x_2490_ = v___x_2488_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_dec(v___x_2488_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 0, v___x_2485_);
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2485_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
else
{
return v___x_2488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object* v_declName_2520_, lean_object* v_isMeta_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
uint8_t v_isMeta_boxed_2525_; lean_object* v_res_2526_; 
v_isMeta_boxed_2525_ = lean_unbox(v_isMeta_2521_);
v_res_2526_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_declName_2520_, v_isMeta_boxed_2525_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(lean_object* v_as_x27_2527_, lean_object* v_b_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
if (lean_obj_tag(v_as_x27_2527_) == 0)
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_b_2528_);
return v___x_2532_;
}
else
{
lean_object* v_head_2533_; lean_object* v_tail_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; lean_object* v___x_2537_; 
v_head_2533_ = lean_ctor_get(v_as_x27_2527_, 0);
v_tail_2534_ = lean_ctor_get(v_as_x27_2527_, 1);
v___x_2535_ = lean_box(0);
v___x_2536_ = 1;
lean_inc(v_head_2533_);
v___x_2537_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_head_2533_, v___x_2536_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_dec_ref_known(v___x_2537_, 1);
v_as_x27_2527_ = v_tail_2534_;
v_b_2528_ = v___x_2535_;
goto _start;
}
else
{
return v___x_2537_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_2539_, lean_object* v_b_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_2539_, v_b_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v_as_x27_2539_);
return v_res_2544_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = l_Lean_maxRecDepthErrorMessage;
v___x_2551_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
return v___x_2551_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3);
v___x_2553_ = l_Lean_MessageData_ofFormat(v___x_2552_);
return v___x_2553_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4);
v___x_2555_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2));
v___x_2556_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
lean_ctor_set(v___x_2556_, 1, v___x_2554_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(lean_object* v_ref_2557_){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2559_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v_ref_2557_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___boxed(lean_object* v_ref_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_2562_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object* v_currNamespace_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2568_, 0, v_currNamespace_2565_);
lean_ctor_set(v___x_2568_, 1, v___y_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(v_currNamespace_2569_, v___y_2570_, v___y_2571_);
lean_dec_ref(v___y_2570_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object* v_env_2573_, lean_object* v_declName_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
uint8_t v___x_2577_; lean_object* v_env_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; uint8_t v___x_2581_; 
v___x_2577_ = 0;
v_env_2578_ = l_Lean_Environment_setExporting(v_env_2573_, v___x_2577_);
lean_inc(v_declName_2574_);
v___x_2579_ = l_Lean_mkPrivateName(v_env_2578_, v_declName_2574_);
v___x_2580_ = 1;
lean_inc_ref(v_env_2578_);
v___x_2581_ = l_Lean_Environment_contains(v_env_2578_, v___x_2579_, v___x_2580_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; uint8_t v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2582_ = l_Lean_privateToUserName(v_declName_2574_);
v___x_2583_ = l_Lean_Environment_contains(v_env_2578_, v___x_2582_, v___x_2580_);
v___x_2584_ = lean_box(v___x_2583_);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
lean_ctor_set(v___x_2585_, 1, v___y_2576_);
return v___x_2585_;
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_dec_ref(v_env_2578_);
lean_dec(v_declName_2574_);
v___x_2586_ = lean_box(v___x_2581_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
lean_ctor_set(v___x_2587_, 1, v___y_2576_);
return v___x_2587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object* v_env_2588_, lean_object* v_declName_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(v_env_2588_, v_declName_2589_, v___y_2590_, v___y_2591_);
lean_dec_ref(v___y_2590_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(lean_object* v_x_2593_, lean_object* v___y_2594_){
_start:
{
if (lean_obj_tag(v_x_2593_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2596_; 
v_a_2595_ = lean_ctor_get(v_x_2593_, 0);
lean_inc(v_a_2595_);
v___x_2596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2596_, 0, v_a_2595_);
lean_ctor_set(v___x_2596_, 1, v___y_2594_);
return v___x_2596_;
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2598_; 
v_a_2597_ = lean_ctor_get(v_x_2593_, 0);
lean_inc(v_a_2597_);
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v_a_2597_);
lean_ctor_set(v___x_2598_, 1, v___y_2594_);
return v___x_2598_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_2599_, v___y_2600_);
lean_dec_ref(v_x_2599_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object* v_env_2602_, lean_object* v_stx_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2602_, v_stx_2603_, v___y_2604_, v___y_2605_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
if (lean_obj_tag(v_a_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2616_; 
v_a_2608_ = lean_ctor_get(v___x_2606_, 1);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2616_ == 0)
{
lean_object* v_unused_2617_; 
v_unused_2617_ = lean_ctor_get(v___x_2606_, 0);
lean_dec(v_unused_2617_);
v___x_2610_ = v___x_2606_;
v_isShared_2611_ = v_isSharedCheck_2616_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2606_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2616_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2612_ = lean_box(0);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2612_);
v___x_2614_ = v___x_2610_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_a_2608_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
else
{
lean_object* v_val_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2646_; 
v_val_2618_ = lean_ctor_get(v_a_2607_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_a_2607_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2620_ = v_a_2607_;
v_isShared_2621_ = v_isSharedCheck_2646_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_val_2618_);
lean_dec(v_a_2607_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2646_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v_snd_2622_; 
v_snd_2622_ = lean_ctor_get(v_val_2618_, 1);
lean_inc(v_snd_2622_);
lean_dec(v_val_2618_);
if (lean_obj_tag(v_snd_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2632_; 
lean_del_object(v___x_2620_);
v_a_2623_ = lean_ctor_get(v___x_2606_, 1);
lean_inc(v_a_2623_);
lean_dec_ref_known(v___x_2606_, 2);
v_a_2624_ = lean_ctor_get(v_snd_2622_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_snd_2622_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2626_ = v_snd_2622_;
v_isShared_2627_ = v_isSharedCheck_2632_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v_snd_2622_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2632_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2629_, v_a_2623_);
lean_dec_ref(v___x_2629_);
return v___x_2630_;
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2645_; 
v_a_2633_ = lean_ctor_get(v___x_2606_, 1);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2606_, 2);
v_a_2634_ = lean_ctor_get(v_snd_2622_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_snd_2622_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2636_ = v_snd_2622_;
v_isShared_2637_ = v_isSharedCheck_2645_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v_snd_2622_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2645_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v_a_2634_);
v___x_2639_ = v___x_2620_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2641_; 
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v___x_2639_);
v___x_2641_ = v___x_2636_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2641_, v_a_2633_);
lean_dec_ref(v___x_2641_);
return v___x_2642_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
v_a_2647_ = lean_ctor_get(v___x_2606_, 0);
v_a_2648_ = lean_ctor_get(v___x_2606_, 1);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2606_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_inc(v_a_2647_);
lean_dec(v___x_2606_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2647_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object* v_env_2656_, lean_object* v_stx_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(v_env_2656_, v_stx_2657_, v___y_2658_, v___y_2659_);
lean_dec_ref(v___y_2658_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object* v_env_2661_, lean_object* v_currNamespace_2662_, lean_object* v_openDecls_2663_, lean_object* v_n_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = l_Lean_ResolveName_resolveNamespace(v_env_2661_, v_currNamespace_2662_, v_openDecls_2663_, v_n_2664_);
v___x_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
lean_ctor_set(v___x_2668_, 1, v___y_2666_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object* v_env_2669_, lean_object* v_currNamespace_2670_, lean_object* v_openDecls_2671_, lean_object* v_n_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(v_env_2669_, v_currNamespace_2670_, v_openDecls_2671_, v_n_2672_, v___y_2673_, v___y_2674_);
lean_dec_ref(v___y_2673_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object* v_as_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
if (lean_obj_tag(v_as_2676_) == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2680_ = lean_box(0);
v___x_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
return v___x_2681_;
}
else
{
lean_object* v_head_2682_; lean_object* v_tail_2683_; lean_object* v_fst_2684_; lean_object* v_snd_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v_scopes_2690_; lean_object* v___x_2691_; lean_object* v_opts_2692_; uint8_t v_hasTrace_2693_; 
v_head_2682_ = lean_ctor_get(v_as_2676_, 0);
lean_inc(v_head_2682_);
v_tail_2683_ = lean_ctor_get(v_as_2676_, 1);
lean_inc(v_tail_2683_);
lean_dec_ref_known(v_as_2676_, 2);
v_fst_2684_ = lean_ctor_get(v_head_2682_, 0);
lean_inc(v_fst_2684_);
v_snd_2685_ = lean_ctor_get(v_head_2682_, 1);
lean_inc(v_snd_2685_);
lean_dec(v_head_2682_);
v___x_2686_ = l_Lean_inheritedTraceOptions;
v___x_2687_ = lean_st_ref_get(v___x_2686_);
v___x_2688_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2689_ = lean_st_ref_get(v___y_2678_);
v_scopes_2690_ = lean_ctor_get(v___x_2689_, 2);
lean_inc(v_scopes_2690_);
lean_dec(v___x_2689_);
v___x_2691_ = l_List_head_x21___redArg(v___x_2688_, v_scopes_2690_);
lean_dec(v_scopes_2690_);
v_opts_2692_ = lean_ctor_get(v___x_2691_, 1);
lean_inc_ref(v_opts_2692_);
lean_dec(v___x_2691_);
v_hasTrace_2693_ = lean_ctor_get_uint8(v_opts_2692_, sizeof(void*)*1);
if (v_hasTrace_2693_ == 0)
{
lean_dec_ref(v_opts_2692_);
lean_dec(v___x_2687_);
lean_dec(v_snd_2685_);
lean_dec(v_fst_2684_);
v_as_2676_ = v_tail_2683_;
goto _start;
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2695_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9));
lean_inc(v_fst_2684_);
v___x_2696_ = l_Lean_Name_append(v___x_2695_, v_fst_2684_);
v___x_2697_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2687_, v_opts_2692_, v___x_2696_);
lean_dec(v___x_2696_);
lean_dec_ref(v_opts_2692_);
lean_dec(v___x_2687_);
if (v___x_2697_ == 0)
{
lean_dec(v_snd_2685_);
lean_dec(v_fst_2684_);
v_as_2676_ = v_tail_2683_;
goto _start;
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2699_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2699_, 0, v_snd_2685_);
v___x_2700_ = l_Lean_MessageData_ofFormat(v___x_2699_);
v___x_2701_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_fst_2684_, v___x_2700_, v___y_2677_, v___y_2678_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_dec_ref_known(v___x_2701_, 1);
v_as_2676_ = v_tail_2683_;
goto _start;
}
else
{
lean_dec(v_tail_2683_);
return v___x_2701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object* v_as_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v_as_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object* v_env_2708_, lean_object* v_opts_2709_, lean_object* v_currNamespace_2710_, lean_object* v_openDecls_2711_, lean_object* v_n_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = l_Lean_ResolveName_resolveGlobalName(v_env_2708_, v_opts_2709_, v_currNamespace_2710_, v_openDecls_2711_, v_n_2712_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
lean_ctor_set(v___x_2716_, 1, v___y_2714_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object* v_env_2717_, lean_object* v_opts_2718_, lean_object* v_currNamespace_2719_, lean_object* v_openDecls_2720_, lean_object* v_n_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(v_env_2717_, v_opts_2718_, v_currNamespace_2719_, v_openDecls_2720_, v_n_2721_, v___y_2722_, v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v_opts_2718_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object* v_x_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___x_2730_; lean_object* v_env_2731_; lean_object* v___f_2732_; lean_object* v___f_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v_scopes_2736_; lean_object* v___x_2737_; lean_object* v_opts_2738_; lean_object* v___x_2739_; 
v___x_2730_ = lean_st_ref_get(v___y_2728_);
v_env_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc_ref_n(v_env_2731_, 3);
lean_dec(v___x_2730_);
v___f_2732_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2732_, 0, v_env_2731_);
v___f_2733_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2733_, 0, v_env_2731_);
v___x_2734_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2735_ = lean_st_ref_get(v___y_2728_);
v_scopes_2736_ = lean_ctor_get(v___x_2735_, 2);
lean_inc(v_scopes_2736_);
lean_dec(v___x_2735_);
v___x_2737_ = l_List_head_x21___redArg(v___x_2734_, v_scopes_2736_);
lean_dec(v_scopes_2736_);
v_opts_2738_ = lean_ctor_get(v___x_2737_, 1);
lean_inc_ref(v_opts_2738_);
lean_dec(v___x_2737_);
v___x_2739_ = l_Lean_Elab_Command_getScope___redArg(v___y_2728_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v_currNamespace_2741_; lean_object* v___f_2742_; lean_object* v___x_2743_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v___x_2739_, 1);
v_currNamespace_2741_ = lean_ctor_get(v_a_2740_, 2);
lean_inc_n(v_currNamespace_2741_, 2);
lean_dec(v_a_2740_);
v___f_2742_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2742_, 0, v_currNamespace_2741_);
v___x_2743_ = l_Lean_Elab_Command_getScope___redArg(v___y_2728_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v_openDecls_2745_; lean_object* v___f_2746_; lean_object* v___f_2747_; lean_object* v_methods_2748_; lean_object* v___x_2749_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec_ref_known(v___x_2743_, 1);
v_openDecls_2745_ = lean_ctor_get(v_a_2744_, 3);
lean_inc_n(v_openDecls_2745_, 2);
lean_dec(v_a_2744_);
lean_inc(v_currNamespace_2741_);
lean_inc_ref(v_env_2731_);
v___f_2746_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2746_, 0, v_env_2731_);
lean_closure_set(v___f_2746_, 1, v_currNamespace_2741_);
lean_closure_set(v___f_2746_, 2, v_openDecls_2745_);
v___f_2747_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2747_, 0, v_env_2731_);
lean_closure_set(v___f_2747_, 1, v_opts_2738_);
lean_closure_set(v___f_2747_, 2, v_currNamespace_2741_);
lean_closure_set(v___f_2747_, 3, v_openDecls_2745_);
v_methods_2748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2748_, 0, v___f_2733_);
lean_ctor_set(v_methods_2748_, 1, v___f_2742_);
lean_ctor_set(v_methods_2748_, 2, v___f_2732_);
lean_ctor_set(v_methods_2748_, 3, v___f_2746_);
lean_ctor_set(v_methods_2748_, 4, v___f_2747_);
v___x_2749_ = l_Lean_Elab_Command_getRef___redArg(v___y_2727_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2751_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v___x_2751_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2727_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v_currRecDepth_2753_; lean_object* v_quotContext_x3f_2754_; lean_object* v_a_2756_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2752_);
lean_dec_ref_known(v___x_2751_, 1);
v_currRecDepth_2753_ = lean_ctor_get(v___y_2727_, 2);
v_quotContext_x3f_2754_ = lean_ctor_get(v___y_2727_, 5);
if (lean_obj_tag(v_quotContext_x3f_2754_) == 0)
{
lean_object* v___x_2830_; lean_object* v_a_2831_; 
v___x_2830_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_2728_);
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref(v___x_2830_);
v_a_2756_ = v_a_2831_;
goto v___jp_2755_;
}
else
{
lean_object* v_val_2832_; 
v_val_2832_ = lean_ctor_get(v_quotContext_x3f_2754_, 0);
lean_inc(v_val_2832_);
v_a_2756_ = v_val_2832_;
goto v___jp_2755_;
}
v___jp_2755_:
{
lean_object* v___x_2757_; lean_object* v_maxRecDepth_2758_; lean_object* v___x_2759_; lean_object* v_nextMacroScope_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2757_ = lean_st_ref_get(v___y_2728_);
v_maxRecDepth_2758_ = lean_ctor_get(v___x_2757_, 5);
lean_inc(v_maxRecDepth_2758_);
lean_dec(v___x_2757_);
v___x_2759_ = lean_st_ref_get(v___y_2728_);
v_nextMacroScope_2760_ = lean_ctor_get(v___x_2759_, 4);
lean_inc(v_nextMacroScope_2760_);
lean_dec(v___x_2759_);
lean_inc(v_currRecDepth_2753_);
v___x_2761_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2761_, 0, v_methods_2748_);
lean_ctor_set(v___x_2761_, 1, v_a_2756_);
lean_ctor_set(v___x_2761_, 2, v_a_2752_);
lean_ctor_set(v___x_2761_, 3, v_currRecDepth_2753_);
lean_ctor_set(v___x_2761_, 4, v_maxRecDepth_2758_);
lean_ctor_set(v___x_2761_, 5, v_a_2750_);
v___x_2762_ = lean_box(0);
v___x_2763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2763_, 0, v_nextMacroScope_2760_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
lean_ctor_set(v___x_2763_, 2, v___x_2762_);
v___x_2764_ = lean_apply_2(v_x_2726_, v___x_2761_, v___x_2763_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v_a_2766_; lean_object* v_macroScope_2767_; lean_object* v_traceMsgs_2768_; lean_object* v_expandedMacroDecls_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 1);
lean_inc(v_a_2765_);
v_a_2766_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2764_, 2);
v_macroScope_2767_ = lean_ctor_get(v_a_2765_, 0);
lean_inc(v_macroScope_2767_);
v_traceMsgs_2768_ = lean_ctor_get(v_a_2765_, 1);
lean_inc(v_traceMsgs_2768_);
v_expandedMacroDecls_2769_ = lean_ctor_get(v_a_2765_, 2);
lean_inc(v_expandedMacroDecls_2769_);
lean_dec(v_a_2765_);
v___x_2770_ = lean_box(0);
v___x_2771_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_expandedMacroDecls_2769_, v___x_2770_, v___y_2727_, v___y_2728_);
lean_dec(v_expandedMacroDecls_2769_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v___x_2772_; lean_object* v_env_2773_; lean_object* v_messages_2774_; lean_object* v_scopes_2775_; lean_object* v_usedQuotCtxts_2776_; lean_object* v_maxRecDepth_2777_; lean_object* v_ngen_2778_; lean_object* v_auxDeclNGen_2779_; lean_object* v_infoState_2780_; lean_object* v_traceState_2781_; lean_object* v_snapshotTasks_2782_; lean_object* v_prevLinterStates_2783_; lean_object* v_codeQualityEntryTasks_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2810_; 
lean_dec_ref_known(v___x_2771_, 1);
v___x_2772_ = lean_st_ref_take(v___y_2728_);
v_env_2773_ = lean_ctor_get(v___x_2772_, 0);
v_messages_2774_ = lean_ctor_get(v___x_2772_, 1);
v_scopes_2775_ = lean_ctor_get(v___x_2772_, 2);
v_usedQuotCtxts_2776_ = lean_ctor_get(v___x_2772_, 3);
v_maxRecDepth_2777_ = lean_ctor_get(v___x_2772_, 5);
v_ngen_2778_ = lean_ctor_get(v___x_2772_, 6);
v_auxDeclNGen_2779_ = lean_ctor_get(v___x_2772_, 7);
v_infoState_2780_ = lean_ctor_get(v___x_2772_, 8);
v_traceState_2781_ = lean_ctor_get(v___x_2772_, 9);
v_snapshotTasks_2782_ = lean_ctor_get(v___x_2772_, 10);
v_prevLinterStates_2783_ = lean_ctor_get(v___x_2772_, 11);
v_codeQualityEntryTasks_2784_ = lean_ctor_get(v___x_2772_, 12);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2810_ == 0)
{
lean_object* v_unused_2811_; 
v_unused_2811_ = lean_ctor_get(v___x_2772_, 4);
lean_dec(v_unused_2811_);
v___x_2786_ = v___x_2772_;
v_isShared_2787_ = v_isSharedCheck_2810_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2784_);
lean_inc(v_prevLinterStates_2783_);
lean_inc(v_snapshotTasks_2782_);
lean_inc(v_traceState_2781_);
lean_inc(v_infoState_2780_);
lean_inc(v_auxDeclNGen_2779_);
lean_inc(v_ngen_2778_);
lean_inc(v_maxRecDepth_2777_);
lean_inc(v_usedQuotCtxts_2776_);
lean_inc(v_scopes_2775_);
lean_inc(v_messages_2774_);
lean_inc(v_env_2773_);
lean_dec(v___x_2772_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2810_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 4, v_macroScope_2767_);
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_env_2773_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_messages_2774_);
lean_ctor_set(v_reuseFailAlloc_2809_, 2, v_scopes_2775_);
lean_ctor_set(v_reuseFailAlloc_2809_, 3, v_usedQuotCtxts_2776_);
lean_ctor_set(v_reuseFailAlloc_2809_, 4, v_macroScope_2767_);
lean_ctor_set(v_reuseFailAlloc_2809_, 5, v_maxRecDepth_2777_);
lean_ctor_set(v_reuseFailAlloc_2809_, 6, v_ngen_2778_);
lean_ctor_set(v_reuseFailAlloc_2809_, 7, v_auxDeclNGen_2779_);
lean_ctor_set(v_reuseFailAlloc_2809_, 8, v_infoState_2780_);
lean_ctor_set(v_reuseFailAlloc_2809_, 9, v_traceState_2781_);
lean_ctor_set(v_reuseFailAlloc_2809_, 10, v_snapshotTasks_2782_);
lean_ctor_set(v_reuseFailAlloc_2809_, 11, v_prevLinterStates_2783_);
lean_ctor_set(v_reuseFailAlloc_2809_, 12, v_codeQualityEntryTasks_2784_);
v___x_2789_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2790_ = lean_st_ref_put(v___y_2728_, v___x_2789_);
v___x_2791_ = l_List_reverse___redArg(v_traceMsgs_2768_);
v___x_2792_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v___x_2791_, v___y_2727_, v___y_2728_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2799_ == 0)
{
lean_object* v_unused_2800_; 
v_unused_2800_ = lean_ctor_get(v___x_2792_, 0);
lean_dec(v_unused_2800_);
v___x_2794_ = v___x_2792_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_dec(v___x_2792_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v_a_2766_);
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2766_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2766_);
v_a_2801_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2792_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2792_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec(v_traceMsgs_2768_);
lean_dec(v_macroScope_2767_);
lean_dec(v_a_2766_);
v_a_2812_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2771_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2771_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
else
{
lean_object* v_a_2820_; 
v_a_2820_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2764_, 2);
if (lean_obj_tag(v_a_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v_a_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v_a_2821_ = lean_ctor_get(v_a_2820_, 0);
lean_inc(v_a_2821_);
v_a_2822_ = lean_ctor_get(v_a_2820_, 1);
lean_inc_ref(v_a_2822_);
lean_dec_ref_known(v_a_2820_, 2);
v___x_2823_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0));
v___x_2824_ = lean_string_dec_eq(v_a_2822_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2825_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2825_, 0, v_a_2822_);
v___x_2826_ = l_Lean_MessageData_ofFormat(v___x_2825_);
v___x_2827_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_a_2821_, v___x_2826_, v___y_2727_, v___y_2728_);
lean_dec(v_a_2821_);
return v___x_2827_;
}
else
{
lean_object* v___x_2828_; 
lean_dec_ref(v_a_2822_);
v___x_2828_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_a_2821_);
return v___x_2828_;
}
}
else
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_2829_;
}
}
}
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v_a_2750_);
lean_dec_ref_known(v_methods_2748_, 5);
lean_dec_ref(v_x_2726_);
v_a_2833_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2751_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2751_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec_ref_known(v_methods_2748_, 5);
lean_dec_ref(v_x_2726_);
v_a_2841_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2749_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2749_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec_ref(v___f_2742_);
lean_dec(v_currNamespace_2741_);
lean_dec_ref(v_opts_2738_);
lean_dec_ref(v___f_2733_);
lean_dec_ref(v___f_2732_);
lean_dec_ref(v_env_2731_);
lean_dec_ref(v_x_2726_);
v_a_2849_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2743_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2743_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec_ref(v_opts_2738_);
lean_dec_ref(v___f_2733_);
lean_dec_ref(v___f_2732_);
lean_dec_ref(v_env_2731_);
lean_dec_ref(v_x_2726_);
v_a_2857_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2739_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2739_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object* v_x_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object* v_x_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___x_2955_; uint8_t v___x_2956_; 
v___x_2913_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_2914_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_2955_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
lean_inc(v_x_2909_);
v___x_2956_ = l_Lean_Syntax_isOfKind(v_x_2909_, v___x_2955_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; 
lean_dec(v_x_2909_);
v___x_2957_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_2957_;
}
else
{
lean_object* v___x_2958_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; size_t v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; uint8_t v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; size_t v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; uint8_t v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; size_t v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; uint8_t v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; size_t v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; uint8_t v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; size_t v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; uint8_t v___y_3233_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v_expectedType_x3f_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v_prio_x3f_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v_name_x3f_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v_prec_x3f_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v_attrs_x3f_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v_doc_x3f_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___x_3435_; uint8_t v___x_3436_; 
v___x_2958_ = lean_unsigned_to_nat(0u);
v___x_3435_ = l_Lean_Syntax_getArg(v_x_2909_, v___x_2958_);
v___x_3436_ = l_Lean_Syntax_isNone(v___x_3435_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; uint8_t v___x_3438_; 
v___x_3437_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3435_);
v___x_3438_ = l_Lean_Syntax_matchesNull(v___x_3435_, v___x_3437_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; 
lean_dec(v___x_3435_);
lean_dec(v_x_2909_);
v___x_3439_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3439_;
}
else
{
lean_object* v_doc_x3f_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; 
v_doc_x3f_3440_ = l_Lean_Syntax_getArg(v___x_3435_, v___x_2958_);
lean_dec(v___x_3435_);
v___x_3441_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__6));
lean_inc(v_doc_x3f_3440_);
v___x_3442_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3440_, v___x_3441_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3443_; 
lean_dec(v_doc_x3f_3440_);
lean_dec(v_x_2909_);
v___x_3443_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3443_;
}
else
{
lean_object* v___x_3444_; 
v___x_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3444_, 0, v_doc_x3f_3440_);
v_doc_x3f_3419_ = v___x_3444_;
v___y_3420_ = v_a_2910_;
v___y_3421_ = v_a_2911_;
goto v___jp_3418_;
}
}
}
else
{
lean_object* v___x_3445_; 
lean_dec(v___x_3435_);
v___x_3445_ = lean_box(0);
v_doc_x3f_3419_ = v___x_3445_;
v___y_3420_ = v_a_2910_;
v___y_3421_ = v_a_2911_;
goto v___jp_3418_;
}
v___jp_2959_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
lean_inc_ref_n(v___y_2961_, 2);
v___x_2976_ = l_Array_append___redArg(v___y_2961_, v___y_2975_);
lean_dec_ref(v___y_2975_);
lean_inc_n(v___y_2967_, 3);
lean_inc_n(v___y_2965_, 6);
v___x_2977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2977_, 0, v___y_2965_);
lean_ctor_set(v___x_2977_, 1, v___y_2967_);
lean_ctor_set(v___x_2977_, 2, v___x_2976_);
v___x_2978_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2978_, 0, v___y_2965_);
lean_ctor_set(v___x_2978_, 1, v___y_2967_);
lean_ctor_set(v___x_2978_, 2, v___y_2961_);
lean_inc_ref(v___x_2978_);
lean_inc(v___y_2972_);
v___x_2979_ = l_Lean_Syntax_node1(v___y_2965_, v___y_2972_, v___x_2978_);
lean_inc_ref(v___y_2962_);
v___x_2980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___y_2965_);
lean_ctor_set(v___x_2980_, 1, v___y_2962_);
lean_inc_ref(v___y_2966_);
v___x_2981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___y_2965_);
lean_ctor_set(v___x_2981_, 1, v___y_2966_);
v___x_2982_ = l_Lean_Syntax_node2(v___y_2965_, v___y_2967_, v___x_2981_, v___y_2964_);
if (lean_obj_tag(v___y_2974_) == 1)
{
lean_object* v_val_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v_val_2983_ = lean_ctor_get(v___y_2974_, 0);
lean_inc(v_val_2983_);
lean_dec_ref_known(v___y_2974_, 1);
v___x_2984_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___y_2965_);
v___x_2985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___y_2965_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
v___x_2986_ = l_Array_mkArray2___redArg(v___x_2985_, v_val_2983_);
v___y_2916_ = v___y_2960_;
v___y_2917_ = v___x_2980_;
v___y_2918_ = v___x_2982_;
v___y_2919_ = v___y_2961_;
v___y_2920_ = v___x_2978_;
v___y_2921_ = v___x_2979_;
v___y_2922_ = v___y_2963_;
v___y_2923_ = v___x_2977_;
v___y_2924_ = v___y_2965_;
v___y_2925_ = v___y_2967_;
v___y_2926_ = v___y_2968_;
v___y_2927_ = v___y_2969_;
v___y_2928_ = v___y_2970_;
v___y_2929_ = v___y_2971_;
v___y_2930_ = v___y_2973_;
v___y_2931_ = v___x_2986_;
goto v___jp_2915_;
}
else
{
lean_object* v___x_2987_; 
lean_dec(v___y_2974_);
v___x_2987_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_2916_ = v___y_2960_;
v___y_2917_ = v___x_2980_;
v___y_2918_ = v___x_2982_;
v___y_2919_ = v___y_2961_;
v___y_2920_ = v___x_2978_;
v___y_2921_ = v___x_2979_;
v___y_2922_ = v___y_2963_;
v___y_2923_ = v___x_2977_;
v___y_2924_ = v___y_2965_;
v___y_2925_ = v___y_2967_;
v___y_2926_ = v___y_2968_;
v___y_2927_ = v___y_2969_;
v___y_2928_ = v___y_2970_;
v___y_2929_ = v___y_2971_;
v___y_2930_ = v___y_2973_;
v___y_2931_ = v___x_2987_;
goto v___jp_2915_;
}
}
v___jp_2988_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0));
v___x_3004_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
if (lean_obj_tag(v___y_2993_) == 1)
{
lean_object* v_val_3005_; lean_object* v___x_3006_; 
v_val_3005_ = lean_ctor_get(v___y_2993_, 0);
lean_inc(v_val_3005_);
lean_dec_ref_known(v___y_2993_, 1);
v___x_3006_ = l_Array_mkArray1___redArg(v_val_3005_);
v___y_2960_ = v___y_2989_;
v___y_2961_ = v___y_2990_;
v___y_2962_ = v___x_3003_;
v___y_2963_ = v___y_2991_;
v___y_2964_ = v___y_2992_;
v___y_2965_ = v___y_2994_;
v___y_2966_ = v___y_2995_;
v___y_2967_ = v___y_2996_;
v___y_2968_ = v___y_2997_;
v___y_2969_ = v___y_2998_;
v___y_2970_ = v___y_2999_;
v___y_2971_ = v___x_3004_;
v___y_2972_ = v___y_3000_;
v___y_2973_ = v___y_3001_;
v___y_2974_ = v___y_3002_;
v___y_2975_ = v___x_3006_;
goto v___jp_2959_;
}
else
{
lean_object* v___x_3007_; 
lean_dec(v___y_2993_);
v___x_3007_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_2960_ = v___y_2989_;
v___y_2961_ = v___y_2990_;
v___y_2962_ = v___x_3003_;
v___y_2963_ = v___y_2991_;
v___y_2964_ = v___y_2992_;
v___y_2965_ = v___y_2994_;
v___y_2966_ = v___y_2995_;
v___y_2967_ = v___y_2996_;
v___y_2968_ = v___y_2997_;
v___y_2969_ = v___y_2998_;
v___y_2970_ = v___y_2999_;
v___y_2971_ = v___x_3004_;
v___y_2972_ = v___y_3000_;
v___y_2973_ = v___y_3001_;
v___y_2974_ = v___y_3002_;
v___y_2975_ = v___x_3007_;
goto v___jp_2959_;
}
}
v___jp_3008_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; size_t v_sz_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
lean_inc_ref_n(v___y_3012_, 2);
v___x_3032_ = l_Array_append___redArg(v___y_3012_, v___y_3031_);
lean_dec_ref(v___y_3031_);
lean_inc_n(v___y_3021_, 3);
lean_inc_n(v___y_3024_, 9);
v___x_3033_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3033_, 0, v___y_3024_);
lean_ctor_set(v___x_3033_, 1, v___y_3021_);
lean_ctor_set(v___x_3033_, 2, v___x_3032_);
v___x_3034_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
v___x_3035_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
v___x_3036_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___y_3024_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__6));
v___x_3038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___y_3024_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
v___x_3039_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_3040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___y_3024_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = l_Nat_reprFast(v___y_3018_);
v___x_3042_ = lean_box(2);
v___x_3043_ = l_Lean_Syntax_mkNumLit(v___x_3041_, v___x_3042_);
v___x_3044_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___y_3024_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = l_Lean_Syntax_node5(v___y_3024_, v___x_3034_, v___x_3036_, v___x_3038_, v___x_3040_, v___x_3043_, v___x_3045_);
v___x_3047_ = l_Lean_Syntax_node1(v___y_3024_, v___y_3021_, v___x_3046_);
v_sz_3048_ = lean_array_size(v___y_3019_);
v___x_3049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_3048_, v___y_3013_, v___y_3019_);
v___x_3050_ = l_Array_append___redArg(v___y_3012_, v___x_3049_);
lean_dec_ref(v___x_3049_);
v___x_3051_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3051_, 0, v___y_3024_);
lean_ctor_set(v___x_3051_, 1, v___y_3021_);
lean_ctor_set(v___x_3051_, 2, v___x_3050_);
v___x_3052_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_3053_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___y_3024_);
lean_ctor_set(v___x_3053_, 1, v___x_3052_);
v___x_3054_ = lean_unsigned_to_nat(10u);
v___x_3055_ = lean_mk_empty_array_with_capacity(v___x_3054_);
v___x_3056_ = lean_array_push(v___x_3055_, v___y_3009_);
v___x_3057_ = lean_array_push(v___x_3056_, v___y_3011_);
v___x_3058_ = lean_array_push(v___x_3057_, v___y_3010_);
v___x_3059_ = lean_array_push(v___x_3058_, v___y_3015_);
v___x_3060_ = lean_array_push(v___x_3059_, v___y_3022_);
v___x_3061_ = lean_array_push(v___x_3060_, v___x_3033_);
v___x_3062_ = lean_array_push(v___x_3061_, v___x_3047_);
v___x_3063_ = lean_array_push(v___x_3062_, v___x_3051_);
v___x_3064_ = lean_array_push(v___x_3063_, v___x_3053_);
lean_inc(v___y_3017_);
v___x_3065_ = lean_array_push(v___x_3064_, v___y_3017_);
lean_inc(v___y_3030_);
v___x_3066_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3066_, 0, v___y_3024_);
lean_ctor_set(v___x_3066_, 1, v___y_3030_);
lean_ctor_set(v___x_3066_, 2, v___x_3065_);
v___x_3067_ = l_Lean_Elab_Command_elabSyntax(v___x_3066_, v___y_3023_, v___y_3025_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v___x_3069_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3042_);
lean_ctor_set(v___x_3069_, 1, v_a_3068_);
lean_ctor_set(v___x_3069_, 2, v___y_3014_);
v___x_3070_ = l_Lean_Elab_Command_getRef___redArg(v___y_3023_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v___x_3070_, 1);
v___x_3072_ = l_Lean_SourceInfo_fromRef(v_a_3071_, v___y_3029_);
lean_dec(v_a_3071_);
v___x_3073_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3023_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_quotContext_x3f_3074_; 
lean_dec_ref_known(v___x_3073_, 1);
v_quotContext_x3f_3074_ = lean_ctor_get(v___y_3023_, 5);
if (lean_obj_tag(v_quotContext_x3f_3074_) == 0)
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3025_);
lean_dec_ref(v___x_3075_);
v___y_2989_ = v___x_3044_;
v___y_2990_ = v___y_3012_;
v___y_2991_ = v___y_3016_;
v___y_2992_ = v___y_3017_;
v___y_2993_ = v___y_3020_;
v___y_2994_ = v___x_3072_;
v___y_2995_ = v___x_3052_;
v___y_2996_ = v___y_3021_;
v___y_2997_ = v___y_3023_;
v___y_2998_ = v___y_3025_;
v___y_2999_ = v___y_3026_;
v___y_3000_ = v___y_3027_;
v___y_3001_ = v___x_3069_;
v___y_3002_ = v___y_3028_;
goto v___jp_2988_;
}
else
{
v___y_2989_ = v___x_3044_;
v___y_2990_ = v___y_3012_;
v___y_2991_ = v___y_3016_;
v___y_2992_ = v___y_3017_;
v___y_2993_ = v___y_3020_;
v___y_2994_ = v___x_3072_;
v___y_2995_ = v___x_3052_;
v___y_2996_ = v___y_3021_;
v___y_2997_ = v___y_3023_;
v___y_2998_ = v___y_3025_;
v___y_2999_ = v___y_3026_;
v___y_3000_ = v___y_3027_;
v___y_3001_ = v___x_3069_;
v___y_3002_ = v___y_3028_;
goto v___jp_2988_;
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v___x_3072_);
lean_dec_ref_known(v___x_3069_, 3);
lean_dec(v___y_3028_);
lean_dec(v___y_3026_);
lean_dec(v___y_3020_);
lean_dec(v___y_3017_);
v_a_3076_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3073_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3073_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref_known(v___x_3069_, 3);
lean_dec(v___y_3028_);
lean_dec(v___y_3026_);
lean_dec(v___y_3020_);
lean_dec(v___y_3017_);
v_a_3084_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3070_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3070_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v___y_3028_);
lean_dec(v___y_3026_);
lean_dec(v___y_3020_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3014_);
v_a_3092_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3067_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3067_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
v___jp_3100_:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
lean_inc_ref(v___y_3104_);
v___x_3124_ = l_Array_append___redArg(v___y_3104_, v___y_3123_);
lean_dec_ref(v___y_3123_);
lean_inc(v___y_3113_);
lean_inc(v___y_3115_);
v___x_3125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3125_, 0, v___y_3115_);
lean_ctor_set(v___x_3125_, 1, v___y_3113_);
lean_ctor_set(v___x_3125_, 2, v___x_3124_);
if (lean_obj_tag(v___y_3116_) == 1)
{
lean_object* v_val_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v_val_3126_ = lean_ctor_get(v___y_3116_, 0);
lean_inc(v_val_3126_);
lean_dec_ref_known(v___y_3116_, 1);
v___x_3127_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
v___x_3128_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___y_3115_, 5);
v___x_3129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___y_3115_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__9));
v___x_3131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___y_3115_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v___x_3132_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_3133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___y_3115_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
v___x_3134_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3135_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___y_3115_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = l_Lean_Syntax_node5(v___y_3115_, v___x_3127_, v___x_3129_, v___x_3131_, v___x_3133_, v_val_3126_, v___x_3135_);
v___x_3137_ = l_Array_mkArray1___redArg(v___x_3136_);
v___y_3009_ = v___y_3101_;
v___y_3010_ = v___y_3102_;
v___y_3011_ = v___y_3103_;
v___y_3012_ = v___y_3104_;
v___y_3013_ = v___y_3105_;
v___y_3014_ = v___y_3106_;
v___y_3015_ = v___y_3107_;
v___y_3016_ = v___y_3108_;
v___y_3017_ = v___y_3109_;
v___y_3018_ = v___y_3111_;
v___y_3019_ = v___y_3110_;
v___y_3020_ = v___y_3112_;
v___y_3021_ = v___y_3113_;
v___y_3022_ = v___x_3125_;
v___y_3023_ = v___y_3114_;
v___y_3024_ = v___y_3115_;
v___y_3025_ = v___y_3117_;
v___y_3026_ = v___y_3118_;
v___y_3027_ = v___y_3119_;
v___y_3028_ = v___y_3122_;
v___y_3029_ = v___y_3121_;
v___y_3030_ = v___y_3120_;
v___y_3031_ = v___x_3137_;
goto v___jp_3008_;
}
else
{
lean_object* v___x_3138_; 
lean_dec(v___y_3116_);
v___x_3138_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_3009_ = v___y_3101_;
v___y_3010_ = v___y_3102_;
v___y_3011_ = v___y_3103_;
v___y_3012_ = v___y_3104_;
v___y_3013_ = v___y_3105_;
v___y_3014_ = v___y_3106_;
v___y_3015_ = v___y_3107_;
v___y_3016_ = v___y_3108_;
v___y_3017_ = v___y_3109_;
v___y_3018_ = v___y_3111_;
v___y_3019_ = v___y_3110_;
v___y_3020_ = v___y_3112_;
v___y_3021_ = v___y_3113_;
v___y_3022_ = v___x_3125_;
v___y_3023_ = v___y_3114_;
v___y_3024_ = v___y_3115_;
v___y_3025_ = v___y_3117_;
v___y_3026_ = v___y_3118_;
v___y_3027_ = v___y_3119_;
v___y_3028_ = v___y_3122_;
v___y_3029_ = v___y_3121_;
v___y_3030_ = v___y_3120_;
v___y_3031_ = v___x_3138_;
goto v___jp_3008_;
}
}
v___jp_3139_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_inc_ref(v___y_3144_);
v___x_3164_ = l_Array_append___redArg(v___y_3144_, v___y_3163_);
lean_dec_ref(v___y_3163_);
lean_inc(v___y_3153_);
lean_inc(v___y_3155_);
v___x_3165_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3165_, 0, v___y_3155_);
lean_ctor_set(v___x_3165_, 1, v___y_3153_);
lean_ctor_set(v___x_3165_, 2, v___x_3164_);
v___x_3166_ = l_Lean_SourceInfo_fromRef(v___y_3143_, v___x_2956_);
lean_dec(v___y_3143_);
lean_inc_ref(v___y_3147_);
v___x_3167_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
lean_ctor_set(v___x_3167_, 1, v___y_3147_);
if (lean_obj_tag(v___y_3142_) == 1)
{
lean_object* v_val_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v_val_3168_ = lean_ctor_get(v___y_3142_, 0);
lean_inc(v_val_3168_);
lean_dec_ref_known(v___y_3142_, 1);
v___x_3169_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
v___x_3170_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc_n(v___y_3155_, 2);
v___x_3171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___y_3155_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = l_Lean_Syntax_node2(v___y_3155_, v___x_3169_, v___x_3171_, v_val_3168_);
v___x_3173_ = l_Array_mkArray1___redArg(v___x_3172_);
v___y_3101_ = v___y_3140_;
v___y_3102_ = v___y_3141_;
v___y_3103_ = v___x_3165_;
v___y_3104_ = v___y_3144_;
v___y_3105_ = v___y_3145_;
v___y_3106_ = v___y_3146_;
v___y_3107_ = v___x_3167_;
v___y_3108_ = v___y_3148_;
v___y_3109_ = v___y_3149_;
v___y_3110_ = v___y_3151_;
v___y_3111_ = v___y_3150_;
v___y_3112_ = v___y_3152_;
v___y_3113_ = v___y_3153_;
v___y_3114_ = v___y_3154_;
v___y_3115_ = v___y_3155_;
v___y_3116_ = v___y_3157_;
v___y_3117_ = v___y_3156_;
v___y_3118_ = v___y_3158_;
v___y_3119_ = v___y_3159_;
v___y_3120_ = v___y_3162_;
v___y_3121_ = v___y_3161_;
v___y_3122_ = v___y_3160_;
v___y_3123_ = v___x_3173_;
goto v___jp_3100_;
}
else
{
lean_object* v___x_3174_; 
lean_dec(v___y_3142_);
v___x_3174_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_3101_ = v___y_3140_;
v___y_3102_ = v___y_3141_;
v___y_3103_ = v___x_3165_;
v___y_3104_ = v___y_3144_;
v___y_3105_ = v___y_3145_;
v___y_3106_ = v___y_3146_;
v___y_3107_ = v___x_3167_;
v___y_3108_ = v___y_3148_;
v___y_3109_ = v___y_3149_;
v___y_3110_ = v___y_3151_;
v___y_3111_ = v___y_3150_;
v___y_3112_ = v___y_3152_;
v___y_3113_ = v___y_3153_;
v___y_3114_ = v___y_3154_;
v___y_3115_ = v___y_3155_;
v___y_3116_ = v___y_3157_;
v___y_3117_ = v___y_3156_;
v___y_3118_ = v___y_3158_;
v___y_3119_ = v___y_3159_;
v___y_3120_ = v___y_3162_;
v___y_3121_ = v___y_3161_;
v___y_3122_ = v___y_3160_;
v___y_3123_ = v___x_3174_;
goto v___jp_3100_;
}
}
v___jp_3175_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
lean_inc_ref(v___y_3179_);
v___x_3200_ = l_Array_append___redArg(v___y_3179_, v___y_3199_);
lean_dec_ref(v___y_3199_);
lean_inc(v___y_3189_);
lean_inc(v___y_3191_);
v___x_3201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3201_, 0, v___y_3191_);
lean_ctor_set(v___x_3201_, 1, v___y_3189_);
lean_ctor_set(v___x_3201_, 2, v___x_3200_);
if (lean_obj_tag(v___y_3182_) == 1)
{
lean_object* v_val_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v_val_3202_ = lean_ctor_get(v___y_3182_, 0);
lean_inc(v_val_3202_);
lean_dec_ref_known(v___y_3182_, 1);
v___x_3203_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_3184_);
v___x_3204_ = l_Lean_Name_mkStr4(v___x_2913_, v___x_2914_, v___y_3184_, v___x_3203_);
v___x_3205_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___y_3191_, 4);
v___x_3206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___y_3191_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
lean_inc_ref(v___y_3179_);
v___x_3207_ = l_Array_append___redArg(v___y_3179_, v_val_3202_);
lean_dec(v_val_3202_);
lean_inc(v___y_3189_);
v___x_3208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3208_, 0, v___y_3191_);
lean_ctor_set(v___x_3208_, 1, v___y_3189_);
lean_ctor_set(v___x_3208_, 2, v___x_3207_);
v___x_3209_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_3210_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___y_3191_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = l_Lean_Syntax_node3(v___y_3191_, v___x_3204_, v___x_3206_, v___x_3208_, v___x_3210_);
v___x_3212_ = l_Array_mkArray1___redArg(v___x_3211_);
v___y_3140_ = v___x_3201_;
v___y_3141_ = v___y_3176_;
v___y_3142_ = v___y_3177_;
v___y_3143_ = v___y_3178_;
v___y_3144_ = v___y_3179_;
v___y_3145_ = v___y_3180_;
v___y_3146_ = v___y_3181_;
v___y_3147_ = v___y_3183_;
v___y_3148_ = v___y_3184_;
v___y_3149_ = v___y_3185_;
v___y_3150_ = v___y_3187_;
v___y_3151_ = v___y_3186_;
v___y_3152_ = v___y_3188_;
v___y_3153_ = v___y_3189_;
v___y_3154_ = v___y_3190_;
v___y_3155_ = v___y_3191_;
v___y_3156_ = v___y_3193_;
v___y_3157_ = v___y_3192_;
v___y_3158_ = v___y_3194_;
v___y_3159_ = v___y_3195_;
v___y_3160_ = v___y_3198_;
v___y_3161_ = v___y_3197_;
v___y_3162_ = v___y_3196_;
v___y_3163_ = v___x_3212_;
goto v___jp_3139_;
}
else
{
lean_object* v___x_3213_; 
lean_dec(v___y_3182_);
v___x_3213_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_3140_ = v___x_3201_;
v___y_3141_ = v___y_3176_;
v___y_3142_ = v___y_3177_;
v___y_3143_ = v___y_3178_;
v___y_3144_ = v___y_3179_;
v___y_3145_ = v___y_3180_;
v___y_3146_ = v___y_3181_;
v___y_3147_ = v___y_3183_;
v___y_3148_ = v___y_3184_;
v___y_3149_ = v___y_3185_;
v___y_3150_ = v___y_3187_;
v___y_3151_ = v___y_3186_;
v___y_3152_ = v___y_3188_;
v___y_3153_ = v___y_3189_;
v___y_3154_ = v___y_3190_;
v___y_3155_ = v___y_3191_;
v___y_3156_ = v___y_3193_;
v___y_3157_ = v___y_3192_;
v___y_3158_ = v___y_3194_;
v___y_3159_ = v___y_3195_;
v___y_3160_ = v___y_3198_;
v___y_3161_ = v___y_3197_;
v___y_3162_ = v___y_3196_;
v___y_3163_ = v___x_3213_;
goto v___jp_3139_;
}
}
v___jp_3214_:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3234_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__12));
v___x_3235_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__13));
v___x_3236_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_3237_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v___y_3225_) == 1)
{
lean_object* v_val_3238_; lean_object* v___x_3239_; 
v_val_3238_ = lean_ctor_get(v___y_3225_, 0);
lean_inc(v_val_3238_);
v___x_3239_ = l_Array_mkArray1___redArg(v_val_3238_);
v___y_3176_ = v___y_3215_;
v___y_3177_ = v___y_3216_;
v___y_3178_ = v___y_3217_;
v___y_3179_ = v___x_3237_;
v___y_3180_ = v___y_3218_;
v___y_3181_ = v___y_3219_;
v___y_3182_ = v___y_3220_;
v___y_3183_ = v___x_3234_;
v___y_3184_ = v___y_3221_;
v___y_3185_ = v___y_3222_;
v___y_3186_ = v___y_3223_;
v___y_3187_ = v___y_3224_;
v___y_3188_ = v___y_3225_;
v___y_3189_ = v___x_3236_;
v___y_3190_ = v___y_3226_;
v___y_3191_ = v___y_3227_;
v___y_3192_ = v___y_3229_;
v___y_3193_ = v___y_3228_;
v___y_3194_ = v___y_3230_;
v___y_3195_ = v___y_3231_;
v___y_3196_ = v___x_3235_;
v___y_3197_ = v___y_3233_;
v___y_3198_ = v___y_3232_;
v___y_3199_ = v___x_3239_;
goto v___jp_3175_;
}
else
{
lean_object* v___x_3240_; 
v___x_3240_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_3176_ = v___y_3215_;
v___y_3177_ = v___y_3216_;
v___y_3178_ = v___y_3217_;
v___y_3179_ = v___x_3237_;
v___y_3180_ = v___y_3218_;
v___y_3181_ = v___y_3219_;
v___y_3182_ = v___y_3220_;
v___y_3183_ = v___x_3234_;
v___y_3184_ = v___y_3221_;
v___y_3185_ = v___y_3222_;
v___y_3186_ = v___y_3223_;
v___y_3187_ = v___y_3224_;
v___y_3188_ = v___y_3225_;
v___y_3189_ = v___x_3236_;
v___y_3190_ = v___y_3226_;
v___y_3191_ = v___y_3227_;
v___y_3192_ = v___y_3229_;
v___y_3193_ = v___y_3228_;
v___y_3194_ = v___y_3230_;
v___y_3195_ = v___y_3231_;
v___y_3196_ = v___x_3235_;
v___y_3197_ = v___y_3233_;
v___y_3198_ = v___y_3232_;
v___y_3199_ = v___x_3240_;
goto v___jp_3175_;
}
}
v___jp_3241_:
{
lean_object* v___x_3258_; lean_object* v_args_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3258_ = l_Lean_Syntax_getArg(v___y_3243_, v___y_3250_);
lean_dec(v___y_3243_);
v_args_3259_ = l_Lean_Syntax_getArgs(v___y_3251_);
lean_dec(v___y_3251_);
v___x_3260_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_3260_, 0, v___y_3247_);
v___x_3261_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v___x_3260_, v___y_3256_, v___y_3257_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v_a_3262_; size_t v_sz_3263_; size_t v___x_3264_; lean_object* v___x_3265_; 
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc(v_a_3262_);
lean_dec_ref_known(v___x_3261_, 1);
v_sz_3263_ = lean_array_size(v_args_3259_);
v___x_3264_ = ((size_t)0ULL);
v___x_3265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_3263_, v___x_3264_, v_args_3259_, v___y_3256_, v___y_3257_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3267_; lean_object* v_fst_3268_; lean_object* v_snd_3269_; lean_object* v___x_3270_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v___x_3267_ = l_Array_unzip___redArg(v_a_3266_);
lean_dec(v_a_3266_);
v_fst_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_fst_3268_);
v_snd_3269_ = lean_ctor_get(v___x_3267_, 1);
lean_inc(v_snd_3269_);
lean_dec_ref(v___x_3267_);
v___x_3270_ = l_Lean_Elab_Command_getRef___redArg(v___y_3256_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; uint8_t v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
v___x_3272_ = 0;
v___x_3273_ = l_Lean_SourceInfo_fromRef(v_a_3271_, v___x_3272_);
lean_dec(v_a_3271_);
v___x_3274_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3256_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_quotContext_x3f_3275_; 
lean_dec_ref_known(v___x_3274_, 1);
v_quotContext_x3f_3275_ = lean_ctor_get(v___y_3256_, 5);
if (lean_obj_tag(v_quotContext_x3f_3275_) == 0)
{
lean_object* v___x_3276_; 
v___x_3276_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3257_);
lean_dec_ref(v___x_3276_);
v___y_3215_ = v___y_3242_;
v___y_3216_ = v___y_3244_;
v___y_3217_ = v___y_3245_;
v___y_3218_ = v___x_3264_;
v___y_3219_ = v_snd_3269_;
v___y_3220_ = v___y_3246_;
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3249_;
v___y_3223_ = v_fst_3268_;
v___y_3224_ = v_a_3262_;
v___y_3225_ = v___y_3252_;
v___y_3226_ = v___y_3256_;
v___y_3227_ = v___x_3273_;
v___y_3228_ = v___y_3257_;
v___y_3229_ = v___y_3253_;
v___y_3230_ = v___x_3258_;
v___y_3231_ = v___y_3254_;
v___y_3232_ = v_expectedType_x3f_3255_;
v___y_3233_ = v___x_3272_;
goto v___jp_3214_;
}
else
{
v___y_3215_ = v___y_3242_;
v___y_3216_ = v___y_3244_;
v___y_3217_ = v___y_3245_;
v___y_3218_ = v___x_3264_;
v___y_3219_ = v_snd_3269_;
v___y_3220_ = v___y_3246_;
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3249_;
v___y_3223_ = v_fst_3268_;
v___y_3224_ = v_a_3262_;
v___y_3225_ = v___y_3252_;
v___y_3226_ = v___y_3256_;
v___y_3227_ = v___x_3273_;
v___y_3228_ = v___y_3257_;
v___y_3229_ = v___y_3253_;
v___y_3230_ = v___x_3258_;
v___y_3231_ = v___y_3254_;
v___y_3232_ = v_expectedType_x3f_3255_;
v___y_3233_ = v___x_3272_;
goto v___jp_3214_;
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec(v___x_3273_);
lean_dec(v_snd_3269_);
lean_dec(v_fst_3268_);
lean_dec(v_a_3262_);
lean_dec(v___x_3258_);
lean_dec(v_expectedType_x3f_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3249_);
lean_dec(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec(v___y_3242_);
v_a_3277_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3274_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3274_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec(v_snd_3269_);
lean_dec(v_fst_3268_);
lean_dec(v_a_3262_);
lean_dec(v___x_3258_);
lean_dec(v_expectedType_x3f_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3249_);
lean_dec(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec(v___y_3242_);
v_a_3285_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3270_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3270_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
lean_dec(v_a_3262_);
lean_dec(v___x_3258_);
lean_dec(v_expectedType_x3f_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3249_);
lean_dec(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec(v___y_3242_);
v_a_3293_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3265_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3265_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref(v_args_3259_);
lean_dec(v___x_3258_);
lean_dec(v_expectedType_x3f_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3249_);
lean_dec(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec(v___y_3242_);
v_a_3301_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3261_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3261_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
v___jp_3309_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v___x_3324_ = lean_unsigned_to_nat(8u);
v___x_3325_ = l_Lean_Syntax_getArg(v_x_2909_, v___x_3324_);
v___x_3326_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__15));
lean_inc(v___x_3325_);
v___x_3327_ = l_Lean_Syntax_isOfKind(v___x_3325_, v___x_3326_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; 
lean_dec(v___x_3325_);
lean_dec(v_prio_x3f_3321_);
lean_dec(v___y_3319_);
lean_dec(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec(v___y_3311_);
lean_dec(v_x_2909_);
v___x_3328_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3328_;
}
else
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; uint8_t v___x_3333_; 
v___x_3329_ = lean_unsigned_to_nat(7u);
v___x_3330_ = l_Lean_Syntax_getArg(v_x_2909_, v___x_3329_);
lean_dec(v_x_2909_);
v___x_3331_ = l_Lean_Syntax_getArg(v___x_3325_, v___y_3320_);
v___x_3332_ = l_Lean_Syntax_getArg(v___x_3325_, v___y_3312_);
v___x_3333_ = l_Lean_Syntax_isNone(v___x_3332_);
if (v___x_3333_ == 0)
{
uint8_t v___x_3334_; 
lean_inc(v___x_3332_);
v___x_3334_ = l_Lean_Syntax_matchesNull(v___x_3332_, v___y_3312_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; 
lean_dec(v___x_3332_);
lean_dec(v___x_3331_);
lean_dec(v___x_3330_);
lean_dec(v___x_3325_);
lean_dec(v_prio_x3f_3321_);
lean_dec(v___y_3319_);
lean_dec(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec(v___y_3311_);
v___x_3335_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3335_;
}
else
{
lean_object* v_expectedType_x3f_3336_; lean_object* v___x_3337_; 
v_expectedType_x3f_3336_ = l_Lean_Syntax_getArg(v___x_3332_, v___y_3320_);
lean_dec(v___x_3332_);
v___x_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3337_, 0, v_expectedType_x3f_3336_);
v___y_3242_ = v___y_3311_;
v___y_3243_ = v___x_3325_;
v___y_3244_ = v___y_3315_;
v___y_3245_ = v___y_3317_;
v___y_3246_ = v___y_3319_;
v___y_3247_ = v_prio_x3f_3321_;
v___y_3248_ = v___y_3310_;
v___y_3249_ = v___x_3331_;
v___y_3250_ = v___y_3313_;
v___y_3251_ = v___x_3330_;
v___y_3252_ = v___y_3314_;
v___y_3253_ = v___y_3316_;
v___y_3254_ = v___y_3318_;
v_expectedType_x3f_3255_ = v___x_3337_;
v___y_3256_ = v___y_3322_;
v___y_3257_ = v___y_3323_;
goto v___jp_3241_;
}
}
else
{
lean_object* v___x_3338_; 
lean_dec(v___x_3332_);
v___x_3338_ = lean_box(0);
v___y_3242_ = v___y_3311_;
v___y_3243_ = v___x_3325_;
v___y_3244_ = v___y_3315_;
v___y_3245_ = v___y_3317_;
v___y_3246_ = v___y_3319_;
v___y_3247_ = v_prio_x3f_3321_;
v___y_3248_ = v___y_3310_;
v___y_3249_ = v___x_3331_;
v___y_3250_ = v___y_3313_;
v___y_3251_ = v___x_3330_;
v___y_3252_ = v___y_3314_;
v___y_3253_ = v___y_3316_;
v___y_3254_ = v___y_3318_;
v_expectedType_x3f_3255_ = v___x_3338_;
v___y_3256_ = v___y_3322_;
v___y_3257_ = v___y_3323_;
goto v___jp_3241_;
}
}
}
v___jp_3339_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; uint8_t v___x_3356_; 
v___x_3354_ = lean_unsigned_to_nat(6u);
v___x_3355_ = l_Lean_Syntax_getArg(v_x_2909_, v___x_3354_);
v___x_3356_ = l_Lean_Syntax_isNone(v___x_3355_);
if (v___x_3356_ == 0)
{
uint8_t v___x_3357_; 
lean_inc(v___x_3355_);
v___x_3357_ = l_Lean_Syntax_matchesNull(v___x_3355_, v___y_3349_);
if (v___x_3357_ == 0)
{
lean_object* v___x_3358_; 
lean_dec(v___x_3355_);
lean_dec(v_name_x3f_3351_);
lean_dec(v___y_3350_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec(v___y_3340_);
lean_dec(v_x_2909_);
v___x_3358_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3358_;
}
else
{
lean_object* v___x_3359_; lean_object* v___x_3360_; uint8_t v___x_3361_; 
v___x_3359_ = l_Lean_Syntax_getArg(v___x_3355_, v___x_2958_);
lean_dec(v___x_3355_);
v___x_3360_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
lean_inc(v___x_3359_);
v___x_3361_ = l_Lean_Syntax_isOfKind(v___x_3359_, v___x_3360_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; 
lean_dec(v___x_3359_);
lean_dec(v_name_x3f_3351_);
lean_dec(v___y_3350_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec(v___y_3340_);
lean_dec(v_x_2909_);
v___x_3362_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3362_;
}
else
{
lean_object* v_prio_x3f_3363_; lean_object* v___x_3364_; 
v_prio_x3f_3363_ = l_Lean_Syntax_getArg(v___x_3359_, v___y_3348_);
lean_dec(v___x_3359_);
v___x_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3364_, 0, v_prio_x3f_3363_);
v___y_3310_ = v___y_3341_;
v___y_3311_ = v___y_3340_;
v___y_3312_ = v___y_3342_;
v___y_3313_ = v___y_3343_;
v___y_3314_ = v___y_3344_;
v___y_3315_ = v___y_3345_;
v___y_3316_ = v_name_x3f_3351_;
v___y_3317_ = v___y_3346_;
v___y_3318_ = v___y_3347_;
v___y_3319_ = v___y_3350_;
v___y_3320_ = v___y_3349_;
v_prio_x3f_3321_ = v___x_3364_;
v___y_3322_ = v___y_3352_;
v___y_3323_ = v___y_3353_;
goto v___jp_3309_;
}
}
}
else
{
lean_object* v___x_3365_; 
lean_dec(v___x_3355_);
v___x_3365_ = lean_box(0);
v___y_3310_ = v___y_3341_;
v___y_3311_ = v___y_3340_;
v___y_3312_ = v___y_3342_;
v___y_3313_ = v___y_3343_;
v___y_3314_ = v___y_3344_;
v___y_3315_ = v___y_3345_;
v___y_3316_ = v_name_x3f_3351_;
v___y_3317_ = v___y_3346_;
v___y_3318_ = v___y_3347_;
v___y_3319_ = v___y_3350_;
v___y_3320_ = v___y_3349_;
v_prio_x3f_3321_ = v___x_3365_;
v___y_3322_ = v___y_3352_;
v___y_3323_ = v___y_3353_;
goto v___jp_3309_;
}
}
v___jp_3366_:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3380_ = lean_unsigned_to_nat(5u);
v___x_3381_ = l_Lean_Syntax_getArg(v_x_2909_, v___x_3380_);
v___x_3382_ = l_Lean_Syntax_isNone(v___x_3381_);
if (v___x_3382_ == 0)
{
uint8_t v___x_3383_; 
lean_inc(v___x_3381_);
v___x_3383_ = l_Lean_Syntax_matchesNull(v___x_3381_, v___y_3376_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; 
lean_dec(v___x_3381_);
lean_dec(v_prec_x3f_3377_);
lean_dec(v___y_3375_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec(v___y_3368_);
lean_dec(v_x_2909_);
v___x_3384_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3384_;
}
else
{
lean_object* v___x_3385_; lean_object* v___x_3386_; uint8_t v___x_3387_; 
v___x_3385_ = l_Lean_Syntax_getArg(v___x_3381_, v___x_2958_);
lean_dec(v___x_3381_);
v___x_3386_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
lean_inc(v___x_3385_);
v___x_3387_ = l_Lean_Syntax_isOfKind(v___x_3385_, v___x_3386_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; 
lean_dec(v___x_3385_);
lean_dec(v_prec_x3f_3377_);
lean_dec(v___y_3375_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec(v___y_3368_);
lean_dec(v_x_2909_);
v___x_3388_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3388_;
}
else
{
lean_object* v_name_x3f_3389_; lean_object* v___x_3390_; 
v_name_x3f_3389_ = l_Lean_Syntax_getArg(v___x_3385_, v___y_3374_);
lean_dec(v___x_3385_);
v___x_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3390_, 0, v_name_x3f_3389_);
v___y_3340_ = v___y_3368_;
v___y_3341_ = v___y_3367_;
v___y_3342_ = v___y_3369_;
v___y_3343_ = v___y_3370_;
v___y_3344_ = v___y_3371_;
v___y_3345_ = v_prec_x3f_3377_;
v___y_3346_ = v___y_3372_;
v___y_3347_ = v___y_3373_;
v___y_3348_ = v___y_3374_;
v___y_3349_ = v___y_3376_;
v___y_3350_ = v___y_3375_;
v_name_x3f_3351_ = v___x_3390_;
v___y_3352_ = v___y_3378_;
v___y_3353_ = v___y_3379_;
goto v___jp_3339_;
}
}
}
else
{
lean_object* v___x_3391_; 
lean_dec(v___x_3381_);
v___x_3391_ = lean_box(0);
v___y_3340_ = v___y_3368_;
v___y_3341_ = v___y_3367_;
v___y_3342_ = v___y_3369_;
v___y_3343_ = v___y_3370_;
v___y_3344_ = v___y_3371_;
v___y_3345_ = v_prec_x3f_3377_;
v___y_3346_ = v___y_3372_;
v___y_3347_ = v___y_3373_;
v___y_3348_ = v___y_3374_;
v___y_3349_ = v___y_3376_;
v___y_3350_ = v___y_3375_;
v_name_x3f_3351_ = v___x_3391_;
v___y_3352_ = v___y_3378_;
v___y_3353_ = v___y_3379_;
goto v___jp_3339_;
}
}
v___jp_3392_:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; 
v___x_3398_ = lean_unsigned_to_nat(2u);
v___x_3399_ = l_Lean_Syntax_getArg(v_x_2909_, v___x_3398_);
v___x_3400_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_3401_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__3));
lean_inc(v___x_3399_);
v___x_3402_ = l_Lean_Syntax_isOfKind(v___x_3399_, v___x_3401_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3403_; 
lean_dec(v___x_3399_);
lean_dec(v_attrs_x3f_3395_);
lean_dec(v___y_3393_);
lean_dec(v_x_2909_);
v___x_3403_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3403_;
}
else
{
lean_object* v___x_3404_; lean_object* v_tk_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3404_ = lean_unsigned_to_nat(3u);
v_tk_3405_ = l_Lean_Syntax_getArg(v_x_2909_, v___x_3404_);
v___x_3406_ = lean_unsigned_to_nat(4u);
v___x_3407_ = l_Lean_Syntax_getArg(v_x_2909_, v___x_3406_);
v___x_3408_ = l_Lean_Syntax_isNone(v___x_3407_);
if (v___x_3408_ == 0)
{
uint8_t v___x_3409_; 
lean_inc(v___x_3407_);
v___x_3409_ = l_Lean_Syntax_matchesNull(v___x_3407_, v___y_3394_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; 
lean_dec(v___x_3407_);
lean_dec(v_tk_3405_);
lean_dec(v___x_3399_);
lean_dec(v_attrs_x3f_3395_);
lean_dec(v___y_3393_);
lean_dec(v_x_2909_);
v___x_3410_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3410_;
}
else
{
lean_object* v___x_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; 
v___x_3411_ = l_Lean_Syntax_getArg(v___x_3407_, v___x_2958_);
lean_dec(v___x_3407_);
v___x_3412_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
lean_inc(v___x_3411_);
v___x_3413_ = l_Lean_Syntax_isOfKind(v___x_3411_, v___x_3412_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; 
lean_dec(v___x_3411_);
lean_dec(v_tk_3405_);
lean_dec(v___x_3399_);
lean_dec(v_attrs_x3f_3395_);
lean_dec(v___y_3393_);
lean_dec(v_x_2909_);
v___x_3414_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3414_;
}
else
{
lean_object* v_prec_x3f_3415_; lean_object* v___x_3416_; 
v_prec_x3f_3415_ = l_Lean_Syntax_getArg(v___x_3411_, v___y_3394_);
lean_dec(v___x_3411_);
v___x_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3416_, 0, v_prec_x3f_3415_);
v___y_3367_ = v___x_3400_;
v___y_3368_ = v___x_3399_;
v___y_3369_ = v___x_3398_;
v___y_3370_ = v___x_3406_;
v___y_3371_ = v___y_3393_;
v___y_3372_ = v_tk_3405_;
v___y_3373_ = v___x_3401_;
v___y_3374_ = v___x_3404_;
v___y_3375_ = v_attrs_x3f_3395_;
v___y_3376_ = v___y_3394_;
v_prec_x3f_3377_ = v___x_3416_;
v___y_3378_ = v___y_3396_;
v___y_3379_ = v___y_3397_;
goto v___jp_3366_;
}
}
}
else
{
lean_object* v___x_3417_; 
lean_dec(v___x_3407_);
v___x_3417_ = lean_box(0);
v___y_3367_ = v___x_3400_;
v___y_3368_ = v___x_3399_;
v___y_3369_ = v___x_3398_;
v___y_3370_ = v___x_3406_;
v___y_3371_ = v___y_3393_;
v___y_3372_ = v_tk_3405_;
v___y_3373_ = v___x_3401_;
v___y_3374_ = v___x_3404_;
v___y_3375_ = v_attrs_x3f_3395_;
v___y_3376_ = v___y_3394_;
v_prec_x3f_3377_ = v___x_3417_;
v___y_3378_ = v___y_3396_;
v___y_3379_ = v___y_3397_;
goto v___jp_3366_;
}
}
}
v___jp_3418_:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
v___x_3422_ = lean_unsigned_to_nat(1u);
v___x_3423_ = l_Lean_Syntax_getArg(v_x_2909_, v___x_3422_);
v___x_3424_ = l_Lean_Syntax_isNone(v___x_3423_);
if (v___x_3424_ == 0)
{
uint8_t v___x_3425_; 
lean_inc(v___x_3423_);
v___x_3425_ = l_Lean_Syntax_matchesNull(v___x_3423_, v___x_3422_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; 
lean_dec(v___x_3423_);
lean_dec(v_doc_x3f_3419_);
lean_dec(v_x_2909_);
v___x_3426_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3426_;
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
v___x_3427_ = l_Lean_Syntax_getArg(v___x_3423_, v___x_2958_);
lean_dec(v___x_3423_);
v___x_3428_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v___x_3427_);
v___x_3429_ = l_Lean_Syntax_isOfKind(v___x_3427_, v___x_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; 
lean_dec(v___x_3427_);
lean_dec(v_doc_x3f_3419_);
lean_dec(v_x_2909_);
v___x_3430_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3430_;
}
else
{
lean_object* v___x_3431_; lean_object* v_attrs_x3f_3432_; lean_object* v___x_3433_; 
v___x_3431_ = l_Lean_Syntax_getArg(v___x_3427_, v___x_3422_);
lean_dec(v___x_3427_);
v_attrs_x3f_3432_ = l_Lean_Syntax_getArgs(v___x_3431_);
lean_dec(v___x_3431_);
v___x_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3433_, 0, v_attrs_x3f_3432_);
v___y_3393_ = v_doc_x3f_3419_;
v___y_3394_ = v___x_3422_;
v_attrs_x3f_3395_ = v___x_3433_;
v___y_3396_ = v___y_3420_;
v___y_3397_ = v___y_3421_;
goto v___jp_3392_;
}
}
}
else
{
lean_object* v___x_3434_; 
lean_dec(v___x_3423_);
v___x_3434_ = lean_box(0);
v___y_3393_ = v_doc_x3f_3419_;
v___y_3394_ = v___x_3422_;
v_attrs_x3f_3395_ = v___x_3434_;
v___y_3396_ = v___y_3420_;
v___y_3397_ = v___y_3421_;
goto v___jp_3392_;
}
}
}
v___jp_2915_:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_inc_ref(v___y_2919_);
v___x_2932_ = l_Array_append___redArg(v___y_2919_, v___y_2931_);
lean_dec_ref(v___y_2931_);
lean_inc_n(v___y_2925_, 4);
lean_inc_n(v___y_2924_, 11);
v___x_2933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2933_, 0, v___y_2924_);
lean_ctor_set(v___x_2933_, 1, v___y_2925_);
lean_ctor_set(v___x_2933_, 2, v___x_2932_);
v___x_2934_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref_n(v___y_2922_, 3);
v___x_2935_ = l_Lean_Name_mkStr4(v___x_2913_, v___x_2914_, v___y_2922_, v___x_2934_);
v___x_2936_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_2937_ = l_Lean_Name_mkStr4(v___x_2913_, v___x_2914_, v___y_2922_, v___x_2936_);
v___x_2938_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_2939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___y_2924_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
v___x_2940_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__0));
v___x_2941_ = l_Lean_Name_mkStr4(v___x_2913_, v___x_2914_, v___y_2922_, v___x_2940_);
v___x_2942_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__1));
v___x_2943_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___y_2924_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
lean_inc_ref(v___y_2916_);
v___x_2944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___y_2924_);
lean_ctor_set(v___x_2944_, 1, v___y_2916_);
v___x_2945_ = l_Lean_Syntax_node3(v___y_2924_, v___x_2941_, v___x_2943_, v___y_2930_, v___x_2944_);
v___x_2946_ = l_Lean_Syntax_node1(v___y_2924_, v___y_2925_, v___x_2945_);
v___x_2947_ = l_Lean_Syntax_node1(v___y_2924_, v___y_2925_, v___x_2946_);
v___x_2948_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_2949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___y_2924_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
v___x_2950_ = l_Lean_Syntax_node4(v___y_2924_, v___x_2937_, v___x_2939_, v___x_2947_, v___x_2949_, v___y_2928_);
v___x_2951_ = l_Lean_Syntax_node1(v___y_2924_, v___y_2925_, v___x_2950_);
v___x_2952_ = l_Lean_Syntax_node1(v___y_2924_, v___x_2935_, v___x_2951_);
lean_inc(v___y_2920_);
lean_inc(v___y_2929_);
v___x_2953_ = l_Lean_Syntax_node8(v___y_2924_, v___y_2929_, v___y_2923_, v___y_2920_, v___y_2921_, v___y_2917_, v___y_2920_, v___y_2918_, v___x_2933_, v___x_2952_);
v___x_2954_ = l_Lean_Elab_Command_elabCommand(v___x_2953_, v___y_2926_, v___y_2927_);
return v___x_2954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object* v_x_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Elab_Command_elabElab(v_x_3446_, v_a_3447_, v_a_3448_);
lean_dec(v_a_3448_);
lean_dec_ref(v_a_3447_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object* v_00_u03b1_3451_, lean_object* v_x_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v___x_3455_; 
v___x_3455_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_3452_, v___y_3454_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3456_, lean_object* v_x_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(v_00_u03b1_3456_, v_x_3457_, v___y_3458_, v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec_ref(v_x_3457_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object* v_00_u03b1_3461_, lean_object* v_ref_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v___x_3466_; 
v___x_3466_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_3462_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object* v_00_u03b1_3467_, lean_object* v_ref_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(v_00_u03b1_3467_, v_ref_3468_, v___y_3469_, v___y_3470_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object* v_00_u03b1_3473_, lean_object* v_x_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_3474_, v___y_3475_, v___y_3476_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object* v_00_u03b1_3479_, lean_object* v_x_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(v_00_u03b1_3479_, v_x_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object* v_as_3485_, lean_object* v_as_x27_3486_, lean_object* v_b_3487_, lean_object* v_a_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_3486_, v_b_3487_, v___y_3489_, v___y_3490_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object* v_as_3493_, lean_object* v_as_x27_3494_, lean_object* v_b_3495_, lean_object* v_a_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(v_as_3493_, v_as_x27_3494_, v_b_3495_, v_a_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v_as_x27_3494_);
lean_dec(v_as_3493_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3501_, lean_object* v_m_3502_, lean_object* v_a_3503_){
_start:
{
lean_object* v___x_3504_; 
v___x_3504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_3502_, v_a_3503_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3505_, lean_object* v_m_3506_, lean_object* v_a_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(v_00_u03b2_3505_, v_m_3506_, v_a_3507_);
lean_dec(v_a_3507_);
lean_dec_ref(v_m_3506_);
return v_res_3508_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_3509_, lean_object* v_x_3510_, lean_object* v_x_3511_){
_start:
{
uint8_t v___x_3512_; 
v___x_3512_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_3510_, v_x_3511_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3513_, lean_object* v_x_3514_, lean_object* v_x_3515_){
_start:
{
uint8_t v_res_3516_; lean_object* v_r_3517_; 
v_res_3516_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(v_00_u03b2_3513_, v_x_3514_, v_x_3515_);
lean_dec_ref(v_x_3515_);
lean_dec_ref(v_x_3514_);
v_r_3517_ = lean_box(v_res_3516_);
return v_r_3517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_3518_, lean_object* v_a_3519_, lean_object* v_x_3520_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_3519_, v_x_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_3522_, lean_object* v_a_3523_, lean_object* v_x_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(v_00_u03b2_3522_, v_a_3523_, v_x_3524_);
lean_dec(v_x_3524_);
lean_dec(v_a_3523_);
return v_res_3525_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(lean_object* v_00_u03b2_3526_, lean_object* v_x_3527_, size_t v_x_3528_, lean_object* v_x_3529_){
_start:
{
uint8_t v___x_3530_; 
v___x_3530_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_3527_, v_x_3528_, v_x_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3531_, lean_object* v_x_3532_, lean_object* v_x_3533_, lean_object* v_x_3534_){
_start:
{
size_t v_x_19034__boxed_3535_; uint8_t v_res_3536_; lean_object* v_r_3537_; 
v_x_19034__boxed_3535_ = lean_unbox_usize(v_x_3533_);
lean_dec(v_x_3533_);
v_res_3536_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(v_00_u03b2_3531_, v_x_3532_, v_x_19034__boxed_3535_, v_x_3534_);
lean_dec_ref(v_x_3534_);
lean_dec_ref(v_x_3532_);
v_r_3537_ = lean_box(v_res_3536_);
return v_r_3537_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3538_, lean_object* v_keys_3539_, lean_object* v_vals_3540_, lean_object* v_heq_3541_, lean_object* v_i_3542_, lean_object* v_k_3543_){
_start:
{
uint8_t v___x_3544_; 
v___x_3544_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_3539_, v_i_3542_, v_k_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b2_3545_, lean_object* v_keys_3546_, lean_object* v_vals_3547_, lean_object* v_heq_3548_, lean_object* v_i_3549_, lean_object* v_k_3550_){
_start:
{
uint8_t v_res_3551_; lean_object* v_r_3552_; 
v_res_3551_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(v_00_u03b2_3545_, v_keys_3546_, v_vals_3547_, v_heq_3548_, v_i_3549_, v_k_3550_);
lean_dec_ref(v_k_3550_);
lean_dec_ref(v_vals_3547_);
lean_dec_ref(v_keys_3546_);
v_r_3552_ = lean_box(v_res_3551_);
return v_r_3552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1(){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3560_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3561_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
v___x_3562_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3563_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElab___boxed), 4, 0);
v___x_3564_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3560_, v___x_3561_, v___x_3562_, v___x_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object* v_a_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3(){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3593_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3594_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6));
v___x_3595_ = l_Lean_addBuiltinDeclarationRanges(v___x_3593_, v___x_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object* v_a_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
return v_res_3597_;
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
