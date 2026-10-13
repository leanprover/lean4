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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isQuot(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Parser_Command_visibility_ofAttrKind(lean_object*);
lean_object* l_Array_mkArray5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "invalid elab_rules alternative, expected syntax node kind `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "invalid elab_rules alternative, unexpected syntax node kind `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__18 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__18_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__19 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__19_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__20 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__21 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__21_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__22 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__22_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__23 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__23_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noErrorIfUnused"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__24 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__24_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "no_error_if_unused%"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__25 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__25_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "throwUnsupportedSyntax"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__26 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__26_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__27;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__26_value),LEAN_SCALAR_PTR_LITERAL(225, 251, 194, 35, 13, 152, 147, 184)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__28 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__29 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__30 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__31 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__32 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value;
static const lean_array_object l_Lean_Elab_Command_elabElabRulesAux___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__33 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Term.TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__34 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__34_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__35;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__36 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__36_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expectedType\?"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__37 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__37_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__38;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__37_value),LEAN_SCALAR_PTR_LITERAL(47, 72, 75, 114, 68, 52, 233, 214)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__39 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__39_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__40 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__40_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Elab.Term.withExpectedType"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__41 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__41_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__42;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withExpectedType"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__43 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__43_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Tactic.Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__44 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__44_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__45;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__46 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__46_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cont"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__47 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__47_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__48;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__47_value),LEAN_SCALAR_PTR_LITERAL(53, 231, 177, 147, 174, 255, 200, 174)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__49 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__49_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Elab.Command.CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__50 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__50_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__51;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__52 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__52_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__53 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__53_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__53_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__54 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__54_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doElem"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__55 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__55_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__55_value),LEAN_SCALAR_PTR_LITERAL(224, 169, 39, 82, 97, 101, 60, 174)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__56 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__56_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "syntax category `"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__57 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__57_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__58;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "` does not support expected type specification"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__59 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__59_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__60;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doElem_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__61 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__61_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__61_value),LEAN_SCALAR_PTR_LITERAL(211, 179, 163, 70, 253, 44, 85, 125)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__62 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__62_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__63 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__63_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__63_value),LEAN_SCALAR_PTR_LITERAL(226, 9, 43, 122, 104, 86, 206, 223)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__64 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__64_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__65 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__65_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__65_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__66 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__66_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__67 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__67_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__67_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__68 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__68_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "conv"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__69 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__69_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__69_value),LEAN_SCALAR_PTR_LITERAL(232, 67, 39, 189, 45, 247, 54, 81)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__70 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__70_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "unsupported syntax category `"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__71 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__71_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__72;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "command_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__73 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__73_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__73_value),LEAN_SCALAR_PTR_LITERAL(7, 200, 102, 28, 219, 237, 42, 33)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__74 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__74_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "invalid elab_rules command, specify category using `elab_rules : <cat> ...`"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__75 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__75_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__76;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elab_rules"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 70, 226, 250, 127, 121, 118, 247)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__21_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value;
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
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
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
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 177, 45, 203, 60, 20, 245, 118)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__12_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabTail"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
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
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_box(0);
v___x_61_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg(){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0);
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___boxed(lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object* v_00_u03b1_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object* v_00_u03b1_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(v_00_u03b1_73_, v___y_74_, v___y_75_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0(lean_object* v_k_97_, lean_object* v_attrKind_98_, lean_object* v_attrs_x3f_99_, lean_object* v_kind_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
uint8_t v___x_104_; lean_object* v___x_105_; 
v___x_104_ = 0;
v___x_105_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(v_k_97_, v___x_104_, v___y_101_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_107_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_105_, 1);
v___x_107_ = l_Lean_Elab_Command_getRef___redArg(v___y_101_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_144_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_144_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_144_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_144_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_133_; 
v___x_112_ = l_Lean_SourceInfo_fromRef(v_a_108_, v___x_104_);
lean_dec(v_a_108_);
v___x_133_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_101_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_quotContext_x3f_134_; 
lean_dec_ref_known(v___x_133_, 1);
v_quotContext_x3f_134_ = lean_ctor_get(v___y_101_, 5);
if (lean_obj_tag(v_quotContext_x3f_134_) == 0)
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_102_);
lean_dec_ref(v___x_135_);
goto v___jp_113_;
}
else
{
goto v___jp_113_;
}
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec(v___x_112_);
lean_del_object(v___x_110_);
lean_dec(v_a_106_);
lean_dec(v_kind_100_);
lean_dec(v_attrKind_98_);
v_a_136_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_133_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_133_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
v___jp_113_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_114_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4));
v___x_115_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7));
v___x_116_ = l_Lean_mkIdent(v_kind_100_);
v___x_117_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
lean_inc_n(v___x_112_, 2);
v___x_118_ = l_Lean_Syntax_node1(v___x_112_, v___x_117_, v_a_106_);
v___x_119_ = l_Lean_Syntax_node2(v___x_112_, v___x_115_, v___x_116_, v___x_118_);
v___x_120_ = l_Lean_Syntax_node2(v___x_112_, v___x_114_, v_attrKind_98_, v___x_119_);
if (lean_obj_tag(v_attrs_x3f_99_) == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_mk_empty_array_with_capacity(v___x_121_);
v___x_123_ = lean_array_push(v___x_122_, v___x_120_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_123_);
v___x_125_ = v___x_110_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
else
{
lean_object* v_val_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v_val_127_ = lean_ctor_get(v_attrs_x3f_99_, 0);
v___x_128_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_127_);
v___x_129_ = lean_array_push(v___x_128_, v___x_120_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_129_);
v___x_131_ = v___x_110_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec(v_a_106_);
lean_dec(v_kind_100_);
lean_dec(v_attrKind_98_);
v_a_145_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_107_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_107_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
lean_dec(v_kind_100_);
lean_dec(v_attrKind_98_);
v_a_153_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___x_105_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_105_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object* v_k_161_, lean_object* v_attrKind_162_, lean_object* v_attrs_x3f_163_, lean_object* v_kind_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_161_, v_attrKind_162_, v_attrs_x3f_163_, v_kind_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v_attrs_x3f_163_);
return v_res_168_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(lean_object* v_opts_169_, lean_object* v_opt_170_){
_start:
{
lean_object* v_name_171_; lean_object* v_defValue_172_; lean_object* v_map_173_; lean_object* v___x_174_; 
v_name_171_ = lean_ctor_get(v_opt_170_, 0);
v_defValue_172_ = lean_ctor_get(v_opt_170_, 1);
v_map_173_ = lean_ctor_get(v_opts_169_, 0);
v___x_174_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_173_, v_name_171_);
if (lean_obj_tag(v___x_174_) == 0)
{
uint8_t v___x_175_; 
v___x_175_ = lean_unbox(v_defValue_172_);
return v___x_175_;
}
else
{
lean_object* v_val_176_; 
v_val_176_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_val_176_);
lean_dec_ref_known(v___x_174_, 1);
if (lean_obj_tag(v_val_176_) == 1)
{
uint8_t v_v_177_; 
v_v_177_ = lean_ctor_get_uint8(v_val_176_, 0);
lean_dec_ref_known(v_val_176_, 0);
return v_v_177_;
}
else
{
uint8_t v___x_178_; 
lean_dec(v_val_176_);
v___x_178_ = lean_unbox(v_defValue_172_);
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8___boxed(lean_object* v_opts_179_, lean_object* v_opt_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(v_opts_179_, v_opt_180_);
lean_dec_ref(v_opt_180_);
lean_dec_ref(v_opts_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_box(1);
v___x_184_ = l_Lean_MessageData_ofFormat(v___x_183_);
return v___x_184_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2));
v___x_189_ = l_Lean_MessageData_ofFormat(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
if (lean_obj_tag(v_x_191_) == 0)
{
return v_x_190_;
}
else
{
lean_object* v_head_192_; lean_object* v_tail_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_215_; 
v_head_192_ = lean_ctor_get(v_x_191_, 0);
v_tail_193_ = lean_ctor_get(v_x_191_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_x_191_);
if (v_isSharedCheck_215_ == 0)
{
v___x_195_ = v_x_191_;
v_isShared_196_ = v_isSharedCheck_215_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_tail_193_);
lean_inc(v_head_192_);
lean_dec(v_x_191_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_215_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v_before_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_213_; 
v_before_197_ = lean_ctor_get(v_head_192_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v_head_192_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v_head_192_, 1);
lean_dec(v_unused_214_);
v___x_199_ = v_head_192_;
v_isShared_200_ = v_isSharedCheck_213_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_before_197_);
lean_dec(v_head_192_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_213_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 7);
lean_ctor_set(v___x_199_, 1, v___x_201_);
lean_ctor_set(v___x_199_, 0, v_x_190_);
v___x_203_ = v___x_199_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_x_190_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_201_);
v___x_203_ = v_reuseFailAlloc_212_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_204_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3);
if (v_isShared_196_ == 0)
{
lean_ctor_set_tag(v___x_195_, 7);
lean_ctor_set(v___x_195_, 1, v___x_204_);
lean_ctor_set(v___x_195_, 0, v___x_203_);
v___x_206_ = v___x_195_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_204_);
v___x_206_ = v_reuseFailAlloc_211_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = l_Lean_MessageData_ofSyntax(v_before_197_);
v___x_208_ = l_Lean_indentD(v___x_207_);
v___x_209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_206_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v_x_190_ = v___x_209_;
v_x_191_ = v_tail_193_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1));
v___x_220_ = l_Lean_MessageData_ofFormat(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(lean_object* v_msgData_221_, lean_object* v_macroStack_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_scopes_227_; lean_object* v___x_228_; lean_object* v_opts_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_225_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_226_ = lean_st_ref_get(v___y_223_);
v_scopes_227_ = lean_ctor_get(v___x_226_, 2);
lean_inc(v_scopes_227_);
lean_dec(v___x_226_);
v___x_228_ = l_List_head_x21___redArg(v___x_225_, v_scopes_227_);
lean_dec(v_scopes_227_);
v_opts_229_ = lean_ctor_get(v___x_228_, 1);
lean_inc_ref(v_opts_229_);
lean_dec(v___x_228_);
v___x_230_ = l_Lean_Elab_pp_macroStack;
v___x_231_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(v_opts_229_, v___x_230_);
lean_dec_ref(v_opts_229_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; 
lean_dec(v_macroStack_222_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v_msgData_221_);
return v___x_232_;
}
else
{
if (lean_obj_tag(v_macroStack_222_) == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v_msgData_221_);
return v___x_233_;
}
else
{
lean_object* v_head_234_; lean_object* v_after_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_250_; 
v_head_234_ = lean_ctor_get(v_macroStack_222_, 0);
lean_inc(v_head_234_);
v_after_235_ = lean_ctor_get(v_head_234_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_head_234_);
if (v_isSharedCheck_250_ == 0)
{
lean_object* v_unused_251_; 
v_unused_251_ = lean_ctor_get(v_head_234_, 0);
lean_dec(v_unused_251_);
v___x_237_ = v_head_234_;
v_isShared_238_ = v_isSharedCheck_250_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_after_235_);
lean_dec(v_head_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_250_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 7);
lean_ctor_set(v___x_237_, 1, v___x_239_);
lean_ctor_set(v___x_237_, 0, v_msgData_221_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_msgData_221_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_239_);
v___x_241_ = v_reuseFailAlloc_249_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_msgData_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_242_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2);
v___x_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = l_Lean_MessageData_ofSyntax(v_after_235_);
v___x_245_ = l_Lean_indentD(v___x_244_);
v_msgData_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_246_, 0, v___x_243_);
lean_ctor_set(v_msgData_246_, 1, v___x_245_);
v___x_247_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(v_msgData_246_, v_macroStack_222_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___boxed(lean_object* v_msgData_252_, lean_object* v_macroStack_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_msgData_252_, v_macroStack_253_, v___y_254_);
lean_dec(v___y_254_);
return v_res_256_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_257_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
lean_ctor_set(v___x_262_, 2, v___x_261_);
lean_ctor_set(v___x_262_, 3, v___x_261_);
lean_ctor_set(v___x_262_, 4, v___x_260_);
lean_ctor_set(v___x_262_, 5, v___x_260_);
lean_ctor_set(v___x_262_, 6, v___x_260_);
lean_ctor_set(v___x_262_, 7, v___x_260_);
lean_ctor_set(v___x_262_, 8, v___x_260_);
lean_ctor_set(v___x_262_, 9, v___x_260_);
lean_ctor_set(v___x_262_, 10, v___x_260_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_unsigned_to_nat(32u);
v___x_264_ = lean_mk_empty_array_with_capacity(v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_266_ = ((size_t)5ULL);
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_unsigned_to_nat(32u);
v___x_269_ = lean_mk_empty_array_with_capacity(v___x_268_);
v___x_270_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3);
v___x_271_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_269_);
lean_ctor_set(v___x_271_, 2, v___x_267_);
lean_ctor_set(v___x_271_, 3, v___x_267_);
lean_ctor_set_usize(v___x_271_, 4, v___x_266_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_272_ = lean_box(1);
v___x_273_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4);
v___x_274_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
v___x_275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___x_273_);
lean_ctor_set(v___x_275_, 2, v___x_272_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(lean_object* v_msgData_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; lean_object* v_env_280_; uint8_t v___x_281_; lean_object* v_env_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v_scopes_285_; lean_object* v___x_286_; lean_object* v_opts_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_279_ = lean_st_ref_get(v___y_277_);
v_env_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc_ref(v_env_280_);
lean_dec(v___x_279_);
v___x_281_ = 0;
v_env_282_ = l_Lean_Environment_setRecordingDeps(v_env_280_, v___x_281_);
v___x_283_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_284_ = lean_st_ref_get(v___y_277_);
v_scopes_285_ = lean_ctor_get(v___x_284_, 2);
lean_inc(v_scopes_285_);
lean_dec(v___x_284_);
v___x_286_ = l_List_head_x21___redArg(v___x_283_, v_scopes_285_);
lean_dec(v_scopes_285_);
v_opts_287_ = lean_ctor_get(v___x_286_, 1);
lean_inc_ref(v_opts_287_);
lean_dec(v___x_286_);
v___x_288_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2);
v___x_289_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5);
v___x_290_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_290_, 0, v_env_282_);
lean_ctor_set(v___x_290_, 1, v___x_288_);
lean_ctor_set(v___x_290_, 2, v___x_289_);
lean_ctor_set(v___x_290_, 3, v_opts_287_);
v___x_291_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v_msgData_276_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___boxed(lean_object* v_msgData_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_293_, v___y_294_);
lean_dec(v___y_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(lean_object* v_msg_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Elab_Command_getRef___redArg(v___y_298_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v_macroStack_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_a_306_; lean_object* v___x_307_; lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_316_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_301_, 1);
v_macroStack_303_ = lean_ctor_get(v___y_298_, 4);
v___x_304_ = l_Lean_Elab_getBetterRef(v_a_302_, v_macroStack_303_);
lean_dec(v_a_302_);
v___x_305_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_297_, v___y_299_);
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref(v___x_305_);
lean_inc(v_macroStack_303_);
v___x_307_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_a_306_, v_macroStack_303_, v___y_299_);
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_316_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_304_);
lean_ctor_set(v___x_312_, 1, v_a_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set_tag(v___x_310_, 1);
lean_ctor_set(v___x_310_, 0, v___x_312_);
v___x_314_ = v___x_310_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec_ref(v_msg_297_);
v_a_317_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_301_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_301_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg___boxed(lean_object* v_msg_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object* v_ref_330_, lean_object* v_msg_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Elab_Command_getRef___redArg(v___y_332_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v_fileName_337_; lean_object* v_fileMap_338_; lean_object* v_currRecDepth_339_; lean_object* v_cmdPos_340_; lean_object* v_macroStack_341_; lean_object* v_quotContext_x3f_342_; lean_object* v_currMacroScope_343_; lean_object* v_snap_x3f_344_; lean_object* v_cancelTk_x3f_345_; uint8_t v_suppressElabErrors_346_; lean_object* v_ref_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_335_, 1);
v_fileName_337_ = lean_ctor_get(v___y_332_, 0);
v_fileMap_338_ = lean_ctor_get(v___y_332_, 1);
v_currRecDepth_339_ = lean_ctor_get(v___y_332_, 2);
v_cmdPos_340_ = lean_ctor_get(v___y_332_, 3);
v_macroStack_341_ = lean_ctor_get(v___y_332_, 4);
v_quotContext_x3f_342_ = lean_ctor_get(v___y_332_, 5);
v_currMacroScope_343_ = lean_ctor_get(v___y_332_, 6);
v_snap_x3f_344_ = lean_ctor_get(v___y_332_, 8);
v_cancelTk_x3f_345_ = lean_ctor_get(v___y_332_, 9);
v_suppressElabErrors_346_ = lean_ctor_get_uint8(v___y_332_, sizeof(void*)*10);
v_ref_347_ = l_Lean_replaceRef(v_ref_330_, v_a_336_);
lean_dec(v_a_336_);
lean_inc(v_cancelTk_x3f_345_);
lean_inc(v_snap_x3f_344_);
lean_inc(v_currMacroScope_343_);
lean_inc(v_quotContext_x3f_342_);
lean_inc(v_macroStack_341_);
lean_inc(v_cmdPos_340_);
lean_inc(v_currRecDepth_339_);
lean_inc_ref(v_fileMap_338_);
lean_inc_ref(v_fileName_337_);
v___x_348_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_348_, 0, v_fileName_337_);
lean_ctor_set(v___x_348_, 1, v_fileMap_338_);
lean_ctor_set(v___x_348_, 2, v_currRecDepth_339_);
lean_ctor_set(v___x_348_, 3, v_cmdPos_340_);
lean_ctor_set(v___x_348_, 4, v_macroStack_341_);
lean_ctor_set(v___x_348_, 5, v_quotContext_x3f_342_);
lean_ctor_set(v___x_348_, 6, v_currMacroScope_343_);
lean_ctor_set(v___x_348_, 7, v_ref_347_);
lean_ctor_set(v___x_348_, 8, v_snap_x3f_344_);
lean_ctor_set(v___x_348_, 9, v_cancelTk_x3f_345_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*10, v_suppressElabErrors_346_);
v___x_349_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_331_, v___x_348_, v___y_333_);
lean_dec_ref_known(v___x_348_, 10);
return v___x_349_;
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec_ref(v_msg_331_);
v_a_350_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_335_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_335_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object* v_ref_358_, lean_object* v_msg_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_358_, v_msg_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v_ref_358_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object* v_k_367_, lean_object* v_as_368_, size_t v_sz_369_, size_t v_i_370_, lean_object* v_b_371_){
_start:
{
uint8_t v___x_372_; 
v___x_372_ = lean_usize_dec_lt(v_i_370_, v_sz_369_);
if (v___x_372_ == 0)
{
lean_dec(v_k_367_);
lean_inc_ref(v_b_371_);
return v_b_371_;
}
else
{
lean_object* v___x_373_; lean_object* v_a_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_373_ = lean_box(0);
v_a_374_ = lean_array_uget_borrowed(v_as_368_, v_i_370_);
lean_inc(v_a_374_);
v___x_375_ = l_Lean_Syntax_getKind(v_a_374_);
lean_inc(v_k_367_);
v___x_376_ = l_Lean_Elab_Command_checkRuleKind(v___x_375_, v_k_367_);
lean_dec(v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; size_t v___x_378_; size_t v___x_379_; 
v___x_377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
v___x_378_ = ((size_t)1ULL);
v___x_379_ = lean_usize_add(v_i_370_, v___x_378_);
v_i_370_ = v___x_379_;
v_b_371_ = v___x_377_;
goto _start;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
lean_dec(v_k_367_);
lean_inc(v_a_374_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v_a_374_);
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_373_);
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object* v_k_384_, lean_object* v_as_385_, lean_object* v_sz_386_, lean_object* v_i_387_, lean_object* v_b_388_){
_start:
{
size_t v_sz_boxed_389_; size_t v_i_boxed_390_; lean_object* v_res_391_; 
v_sz_boxed_389_ = lean_unbox_usize(v_sz_386_);
lean_dec(v_sz_386_);
v_i_boxed_390_ = lean_unbox_usize(v_i_387_);
lean_dec(v_i_387_);
v_res_391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_384_, v_as_385_, v_sz_boxed_389_, v_i_boxed_390_, v_b_388_);
lean_dec_ref(v_b_388_);
lean_dec_ref(v_as_385_);
return v_res_391_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2));
v___x_397_ = l_Lean_stringToMessageData(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7(void){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Array_mkArray0___redArg();
return v___x_405_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11));
v___x_412_ = l_Lean_stringToMessageData(v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(lean_object* v_k_413_, size_t v_sz_414_, size_t v_i_415_, lean_object* v_bs_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
uint8_t v___x_420_; 
v___x_420_ = lean_usize_dec_lt(v_i_415_, v_sz_414_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_dec(v_k_413_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v_bs_416_);
return v___x_421_;
}
else
{
lean_object* v_v_422_; lean_object* v___x_423_; lean_object* v_bs_x27_424_; lean_object* v_a_426_; lean_object* v___y_432_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_v_422_ = lean_array_uget(v_bs_416_, v_i_415_);
v___x_423_ = lean_unsigned_to_nat(0u);
v_bs_x27_424_ = lean_array_uset(v_bs_416_, v_i_415_, v___x_423_);
v___x_451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5));
lean_inc(v_v_422_);
v___x_452_ = l_Lean_Syntax_isOfKind(v_v_422_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
lean_dec(v_v_422_);
v___x_453_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
v___y_432_ = v___x_453_;
goto v___jp_431_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = l_Lean_Syntax_getArg(v_v_422_, v___x_454_);
lean_inc(v___x_455_);
v___x_456_ = l_Lean_Syntax_matchesNull(v___x_455_, v___x_454_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_dec(v___x_455_);
lean_dec(v_v_422_);
v___x_457_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
v___y_432_ = v___x_457_;
goto v___jp_431_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___x_475_; lean_object* v_pat_476_; lean_object* v___y_478_; lean_object* v___y_479_; uint8_t v___x_531_; 
v___x_458_ = lean_box(0);
v___x_459_ = l_Lean_Syntax_getArg(v___x_455_, v___x_423_);
lean_dec(v___x_455_);
v___x_460_ = lean_unsigned_to_nat(3u);
v___x_461_ = l_Lean_Syntax_getArg(v_v_422_, v___x_460_);
v___x_475_ = l_Lean_Syntax_getArgs(v___x_459_);
lean_dec(v___x_459_);
v_pat_476_ = lean_array_get_borrowed(v___x_458_, v___x_475_, v___x_423_);
v___x_531_ = l_Lean_Syntax_isQuot(v_pat_476_);
if (v___x_531_ == 0)
{
if (v___x_456_ == 0)
{
v___y_478_ = v___y_417_;
v___y_479_ = v___y_418_;
goto v___jp_477_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
if (lean_obj_tag(v___x_532_) == 0)
{
lean_dec_ref_known(v___x_532_, 1);
v___y_478_ = v___y_417_;
v___y_479_ = v___y_418_;
goto v___jp_477_;
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec_ref(v___x_475_);
lean_dec(v___x_461_);
lean_dec_ref(v_bs_x27_424_);
lean_dec(v_v_422_);
lean_dec(v_k_413_);
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
else
{
v___y_478_ = v___y_417_;
v___y_479_ = v___y_418_;
goto v___jp_477_;
}
v___jp_462_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc_n(v___y_464_, 4);
v___x_466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_466_, 0, v___y_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_468_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
v___x_469_ = l_Array_append___redArg(v___x_468_, v___y_463_);
lean_dec_ref(v___y_463_);
v___x_470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_470_, 0, v___y_464_);
lean_ctor_set(v___x_470_, 1, v___x_467_);
lean_ctor_set(v___x_470_, 2, v___x_469_);
v___x_471_ = l_Lean_Syntax_node1(v___y_464_, v___x_467_, v___x_470_);
v___x_472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_473_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_473_, 0, v___y_464_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = l_Lean_Syntax_node4(v___y_464_, v___x_451_, v___x_466_, v___x_471_, v___x_473_, v___x_461_);
v_a_426_ = v___x_474_;
goto v___jp_425_;
}
v___jp_477_:
{
lean_object* v_quoted_480_; lean_object* v_k_x27_481_; uint8_t v___x_482_; 
lean_inc(v_pat_476_);
v_quoted_480_ = l_Lean_Syntax_getQuotContent(v_pat_476_);
lean_inc(v_quoted_480_);
v_k_x27_481_ = l_Lean_Syntax_getKind(v_quoted_480_);
lean_inc(v_k_413_);
v___x_482_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_481_, v_k_413_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10));
v___x_484_ = lean_name_eq(v_k_x27_481_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v_quoted_480_);
lean_dec_ref(v___x_475_);
lean_dec(v___x_461_);
v___x_485_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12);
v___x_486_ = l_Lean_MessageData_ofName(v_k_x27_481_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_422_, v___x_489_, v___y_478_, v___y_479_);
lean_dec(v_v_422_);
v___y_432_ = v___x_490_;
goto v___jp_431_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; size_t v_sz_493_; size_t v___x_494_; lean_object* v___x_495_; lean_object* v_fst_496_; 
lean_dec(v_k_x27_481_);
v___x_491_ = l_Lean_Syntax_getArgs(v_quoted_480_);
lean_dec(v_quoted_480_);
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
v_sz_493_ = lean_array_size(v___x_491_);
v___x_494_ = ((size_t)0ULL);
lean_inc(v_k_413_);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_413_, v___x_491_, v_sz_493_, v___x_494_, v___x_492_);
lean_dec_ref(v___x_491_);
v_fst_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_fst_496_);
lean_dec_ref(v___x_495_);
if (lean_obj_tag(v_fst_496_) == 0)
{
lean_dec_ref(v___x_475_);
lean_dec(v___x_461_);
v___y_443_ = v___y_478_;
v___y_444_ = v___y_479_;
goto v___jp_442_;
}
else
{
lean_object* v_val_497_; 
v_val_497_ = lean_ctor_get(v_fst_496_, 0);
lean_inc(v_val_497_);
lean_dec_ref_known(v_fst_496_, 1);
if (lean_obj_tag(v_val_497_) == 0)
{
lean_dec_ref(v___x_475_);
lean_dec(v___x_461_);
v___y_443_ = v___y_478_;
v___y_444_ = v___y_479_;
goto v___jp_442_;
}
else
{
lean_object* v_val_498_; lean_object* v_pat_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec(v_v_422_);
v_val_498_ = lean_ctor_get(v_val_497_, 0);
lean_inc(v_val_498_);
lean_dec_ref_known(v_val_497_, 1);
lean_inc(v_pat_476_);
v_pat_499_ = l_Lean_Syntax_setArg(v_pat_476_, v___x_454_, v_val_498_);
v___x_500_ = lean_array_set(v___x_475_, v___x_423_, v_pat_499_);
v___x_501_ = l_Lean_Elab_Command_getRef___redArg(v___y_478_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
v___x_503_ = l_Lean_SourceInfo_fromRef(v_a_502_, v___x_482_);
lean_dec(v_a_502_);
v___x_504_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_478_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_quotContext_x3f_505_; 
lean_dec_ref_known(v___x_504_, 1);
v_quotContext_x3f_505_ = lean_ctor_get(v___y_478_, 5);
if (lean_obj_tag(v_quotContext_x3f_505_) == 0)
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_479_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_dec_ref_known(v___x_506_, 1);
v___y_463_ = v___x_500_;
v___y_464_ = v___x_503_;
goto v___jp_462_;
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec(v___x_503_);
lean_dec_ref(v___x_500_);
lean_dec(v___x_461_);
lean_dec_ref(v_bs_x27_424_);
lean_dec(v_k_413_);
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
else
{
v___y_463_ = v___x_500_;
v___y_464_ = v___x_503_;
goto v___jp_462_;
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec(v___x_503_);
lean_dec_ref(v___x_500_);
lean_dec(v___x_461_);
lean_dec_ref(v_bs_x27_424_);
lean_dec(v_k_413_);
v_a_515_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_504_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_504_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec_ref(v___x_500_);
lean_dec(v___x_461_);
lean_dec_ref(v_bs_x27_424_);
lean_dec(v_k_413_);
v_a_523_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_501_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_501_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_x27_481_);
lean_dec(v_quoted_480_);
lean_dec_ref(v___x_475_);
lean_dec(v___x_461_);
v_a_426_ = v_v_422_;
goto v___jp_425_;
}
}
}
}
v___jp_425_:
{
size_t v___x_427_; size_t v___x_428_; lean_object* v___x_429_; 
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_add(v_i_415_, v___x_427_);
v___x_429_ = lean_array_uset(v_bs_x27_424_, v_i_415_, v_a_426_);
v_i_415_ = v___x_428_;
v_bs_416_ = v___x_429_;
goto _start;
}
v___jp_431_:
{
if (lean_obj_tag(v___y_432_) == 0)
{
lean_object* v_a_433_; 
v_a_433_ = lean_ctor_get(v___y_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref_known(v___y_432_, 1);
v_a_426_ = v_a_433_;
goto v___jp_425_;
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v_bs_x27_424_);
lean_dec(v_k_413_);
v_a_434_ = lean_ctor_get(v___y_432_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___y_432_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___y_432_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___y_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
v___jp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_445_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1);
lean_inc(v_k_413_);
v___x_446_ = l_Lean_MessageData_ofName(v_k_413_);
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_422_, v___x_449_, v___y_443_, v___y_444_);
lean_dec(v_v_422_);
v___y_432_ = v___x_450_;
goto v___jp_431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___boxed(lean_object* v_k_541_, lean_object* v_sz_542_, lean_object* v_i_543_, lean_object* v_bs_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
size_t v_sz_boxed_548_; size_t v_i_boxed_549_; lean_object* v_res_550_; 
v_sz_boxed_548_ = lean_unbox_usize(v_sz_542_);
lean_dec(v_sz_542_);
v_i_boxed_549_ = lean_unbox_usize(v_i_543_);
lean_dec(v_i_543_);
v_res_550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_541_, v_sz_boxed_548_, v_i_boxed_549_, v_bs_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_550_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__4));
v___x_557_ = l_String_toRawSubstring_x27(v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__8));
v___x_563_ = l_String_toRawSubstring_x27(v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__15));
v___x_571_ = l_String_toRawSubstring_x27(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_584_ = l_String_toRawSubstring_x27(v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__35(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_599_ = l_String_toRawSubstring_x27(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__38(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___x_603_ = l_String_toRawSubstring_x27(v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__41));
v___x_609_ = l_String_toRawSubstring_x27(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__45(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__44));
v___x_613_ = l_String_toRawSubstring_x27(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__48(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__47));
v___x_617_ = l_String_toRawSubstring_x27(v___x_616_);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__50));
v___x_622_ = l_String_toRawSubstring_x27(v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__57));
v___x_632_ = l_Lean_stringToMessageData(v___x_631_);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__59));
v___x_635_ = l_Lean_stringToMessageData(v___x_634_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__71));
v___x_653_ = l_Lean_stringToMessageData(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__75));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object* v_doc_x3f_660_, lean_object* v_attrs_x3f_661_, lean_object* v_attrKind_662_, lean_object* v_k_663_, lean_object* v_cat_x3f_664_, lean_object* v_expty_x3f_665_, lean_object* v_alts_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
size_t v_sz_670_; size_t v___x_671_; lean_object* v___x_672_; 
v_sz_670_ = lean_array_size(v_alts_666_);
v___x_671_ = ((size_t)0ULL);
lean_inc(v_k_663_);
v___x_672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_663_, v_sz_670_, v___x_671_, v_alts_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_1689_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_1689_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_1689_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v_a_804_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v_a_956_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v_a_1069_; uint8_t v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v_a_1240_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v_a_1354_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v_a_1487_; lean_object* v_catName_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; 
if (lean_obj_tag(v_cat_x3f_664_) == 1)
{
lean_object* v_val_1676_; lean_object* v___x_1677_; 
v_val_1676_ = lean_ctor_get(v_cat_x3f_664_, 0);
v___x_1677_ = l_Lean_TSyntax_getId(v_val_1676_);
v_catName_1498_ = v___x_1677_;
v___y_1499_ = v_a_667_;
v___y_1500_ = v_a_668_;
goto v___jp_1497_;
}
else
{
if (lean_obj_tag(v_expty_x3f_665_) == 1)
{
lean_object* v___x_1678_; 
v___x_1678_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v_catName_1498_ = v___x_1678_;
v___y_1499_ = v_a_667_;
v___y_1500_ = v_a_668_;
goto v___jp_1497_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_del_object(v___x_675_);
lean_dec(v_a_673_);
lean_dec(v_expty_x3f_665_);
lean_dec(v_k_663_);
lean_dec(v_attrKind_662_);
lean_dec(v_doc_x3f_660_);
v___x_1679_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__76, &l_Lean_Elab_Command_elabElabRulesAux___closed__76_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76);
v___x_1680_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_1679_, v_a_667_, v_a_668_);
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
v___jp_677_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
lean_inc_ref_n(v___y_680_, 4);
v___x_691_ = l_Array_append___redArg(v___y_680_, v___y_690_);
lean_dec_ref(v___y_690_);
lean_inc_n(v___y_681_, 10);
lean_inc_n(v___y_688_, 35);
v___x_692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_692_, 0, v___y_688_);
lean_ctor_set(v___x_692_, 1, v___y_681_);
lean_ctor_set(v___x_692_, 2, v___x_691_);
v___x_693_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_694_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_695_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_684_, 11);
v___x_696_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_695_);
v___x_697_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_698_, 0, v___y_688_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_700_ = l_Lean_Syntax_SepArray_ofElems(v___x_699_, v___y_678_);
lean_dec_ref(v___y_678_);
v___x_701_ = l_Array_append___redArg(v___y_680_, v___x_700_);
lean_dec_ref(v___x_700_);
v___x_702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_702_, 0, v___y_688_);
lean_ctor_set(v___x_702_, 1, v___y_681_);
lean_ctor_set(v___x_702_, 2, v___x_701_);
v___x_703_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_704_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_704_, 0, v___y_688_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = l_Lean_Syntax_node3(v___y_688_, v___x_696_, v___x_698_, v___x_702_, v___x_704_);
v___x_706_ = l_Lean_Syntax_node1(v___y_688_, v___y_681_, v___x_705_);
lean_inc_ref(v___y_686_);
v___x_707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_707_, 0, v___y_688_);
lean_ctor_set(v___x_707_, 1, v___y_686_);
v___x_708_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_709_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_683_, 3);
lean_inc_n(v___y_682_, 3);
v___x_710_ = l_Lean_addMacroScope(v___y_682_, v___x_709_, v___y_683_);
v___x_711_ = lean_box(0);
v___x_712_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_712_, 0, v___y_688_);
lean_ctor_set(v___x_712_, 1, v___x_708_);
lean_ctor_set(v___x_712_, 2, v___x_710_);
lean_ctor_set(v___x_712_, 3, v___x_711_);
v___x_713_ = l_Lean_mkIdent(v_k_663_);
v___x_714_ = l_Lean_Syntax_node2(v___y_688_, v___y_681_, v___x_712_, v___x_713_);
v___x_715_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_716_, 0, v___y_688_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_718_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
v___x_719_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc_ref_n(v___y_685_, 2);
v___x_720_ = l_Lean_Name_mkStr4(v___y_684_, v___y_685_, v___x_718_, v___x_719_);
lean_inc(v___x_720_);
v___x_721_ = l_Lean_addMacroScope(v___y_682_, v___x_720_, v___y_683_);
v___x_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_711_);
v___x_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v___x_711_);
v___x_724_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_724_, 0, v___y_688_);
lean_ctor_set(v___x_724_, 1, v___x_717_);
lean_ctor_set(v___x_724_, 2, v___x_721_);
lean_ctor_set(v___x_724_, 3, v___x_723_);
v___x_725_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_726_, 0, v___y_688_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_728_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_727_);
v___x_729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_729_, 0, v___y_688_);
lean_ctor_set(v___x_729_, 1, v___x_727_);
v___x_730_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_731_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_730_);
v___x_732_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_733_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_734_ = l_Lean_addMacroScope(v___y_682_, v___x_733_, v___y_683_);
v___x_735_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_735_, 0, v___y_688_);
lean_ctor_set(v___x_735_, 1, v___x_732_);
lean_ctor_set(v___x_735_, 2, v___x_734_);
lean_ctor_set(v___x_735_, 3, v___x_711_);
lean_inc_ref(v___x_735_);
v___x_736_ = l_Lean_Syntax_node2(v___y_688_, v___y_681_, v___x_735_, v___y_679_);
v___x_737_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_737_, 0, v___y_688_);
lean_ctor_set(v___x_737_, 1, v___y_681_);
lean_ctor_set(v___x_737_, 2, v___y_680_);
v___x_738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_739_, 0, v___y_688_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_741_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_740_);
v___x_742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_742_, 0, v___y_688_);
lean_ctor_set(v___x_742_, 1, v___x_740_);
v___x_743_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_744_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_743_);
lean_inc_ref_n(v___x_737_, 3);
v___x_745_ = l_Lean_Syntax_node2(v___y_688_, v___x_744_, v___x_737_, v___x_735_);
v___x_746_ = l_Lean_Syntax_node1(v___y_688_, v___y_681_, v___x_745_);
v___x_747_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_748_, 0, v___y_688_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_750_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_749_);
v___x_751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_752_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_751_);
v___x_753_ = l_Array_append___redArg(v___y_680_, v_a_673_);
lean_dec(v_a_673_);
v___x_754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_755_, 0, v___y_688_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_757_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_756_);
v___x_758_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_759_, 0, v___y_688_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_Lean_Syntax_node1(v___y_688_, v___x_757_, v___x_759_);
v___x_761_ = l_Lean_Syntax_node1(v___y_688_, v___y_681_, v___x_760_);
v___x_762_ = l_Lean_Syntax_node1(v___y_688_, v___y_681_, v___x_761_);
v___x_763_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_764_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_763_);
v___x_765_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_766_, 0, v___y_688_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_768_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_769_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_770_ = l_Lean_addMacroScope(v___y_682_, v___x_769_, v___y_683_);
v___x_771_ = l_Lean_Name_mkStr3(v___y_684_, v___y_685_, v___x_767_);
v___x_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v___x_711_);
v___x_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v___x_711_);
v___x_774_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_774_, 0, v___y_688_);
lean_ctor_set(v___x_774_, 1, v___x_768_);
lean_ctor_set(v___x_774_, 2, v___x_770_);
lean_ctor_set(v___x_774_, 3, v___x_773_);
v___x_775_ = l_Lean_Syntax_node2(v___y_688_, v___x_764_, v___x_766_, v___x_774_);
lean_inc_ref(v___x_739_);
v___x_776_ = l_Lean_Syntax_node4(v___y_688_, v___x_752_, v___x_755_, v___x_762_, v___x_739_, v___x_775_);
v___x_777_ = lean_array_push(v___x_753_, v___x_776_);
v___x_778_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_778_, 0, v___y_688_);
lean_ctor_set(v___x_778_, 1, v___y_681_);
lean_ctor_set(v___x_778_, 2, v___x_777_);
v___x_779_ = l_Lean_Syntax_node1(v___y_688_, v___x_750_, v___x_778_);
v___x_780_ = l_Lean_Syntax_node6(v___y_688_, v___x_741_, v___x_742_, v___x_737_, v___x_737_, v___x_746_, v___x_748_, v___x_779_);
v___x_781_ = l_Lean_Syntax_node4(v___y_688_, v___x_731_, v___x_736_, v___x_737_, v___x_739_, v___x_780_);
v___x_782_ = l_Lean_Syntax_node2(v___y_688_, v___x_728_, v___x_729_, v___x_781_);
v___x_783_ = lean_unsigned_to_nat(9u);
v___x_784_ = lean_mk_empty_array_with_capacity(v___x_783_);
v___x_785_ = lean_array_push(v___x_784_, v___x_692_);
v___x_786_ = lean_array_push(v___x_785_, v___x_706_);
v___x_787_ = lean_array_push(v___x_786_, v___y_687_);
v___x_788_ = lean_array_push(v___x_787_, v___x_707_);
v___x_789_ = lean_array_push(v___x_788_, v___x_714_);
v___x_790_ = lean_array_push(v___x_789_, v___x_716_);
v___x_791_ = lean_array_push(v___x_790_, v___x_724_);
v___x_792_ = lean_array_push(v___x_791_, v___x_726_);
v___x_793_ = lean_array_push(v___x_792_, v___x_782_);
lean_inc(v___y_689_);
v___x_794_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_794_, 0, v___y_688_);
lean_ctor_set(v___x_794_, 1, v___y_689_);
lean_ctor_set(v___x_794_, 2, v___x_793_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_794_);
v___x_796_ = v___x_675_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
v___jp_798_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_805_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_806_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_807_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_808_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_809_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_810_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_660_) == 1)
{
lean_object* v_val_811_; lean_object* v___x_812_; 
v_val_811_ = lean_ctor_get(v_doc_x3f_660_, 0);
lean_inc(v_val_811_);
lean_dec_ref_known(v_doc_x3f_660_, 1);
v___x_812_ = l_Array_mkArray1___redArg(v_val_811_);
v___y_678_ = v___y_800_;
v___y_679_ = v___y_799_;
v___y_680_ = v___x_810_;
v___y_681_ = v___x_809_;
v___y_682_ = v_a_804_;
v___y_683_ = v___y_803_;
v___y_684_ = v___x_805_;
v___y_685_ = v___x_806_;
v___y_686_ = v___x_807_;
v___y_687_ = v___y_801_;
v___y_688_ = v___y_802_;
v___y_689_ = v___x_808_;
v___y_690_ = v___x_812_;
goto v___jp_677_;
}
else
{
lean_object* v___x_813_; 
lean_dec(v_doc_x3f_660_);
v___x_813_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_678_ = v___y_800_;
v___y_679_ = v___y_799_;
v___y_680_ = v___x_810_;
v___y_681_ = v___x_809_;
v___y_682_ = v_a_804_;
v___y_683_ = v___y_803_;
v___y_684_ = v___x_805_;
v___y_685_ = v___x_806_;
v___y_686_ = v___x_807_;
v___y_687_ = v___y_801_;
v___y_688_ = v___y_802_;
v___y_689_ = v___x_808_;
v___y_690_ = v___x_813_;
goto v___jp_677_;
}
}
v___jp_814_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
lean_inc_ref_n(v___y_825_, 4);
v___x_828_ = l_Array_append___redArg(v___y_825_, v___y_827_);
lean_dec_ref(v___y_827_);
lean_inc_n(v___y_819_, 12);
lean_inc_n(v___y_817_, 42);
v___x_829_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_829_, 0, v___y_817_);
lean_ctor_set(v___x_829_, 1, v___y_819_);
lean_ctor_set(v___x_829_, 2, v___x_828_);
v___x_830_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_831_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_832_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_821_, 13);
v___x_833_ = l_Lean_Name_mkStr4(v___y_821_, v___x_830_, v___x_831_, v___x_832_);
v___x_834_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_835_, 0, v___y_817_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_837_ = l_Lean_Syntax_SepArray_ofElems(v___x_836_, v___y_824_);
lean_dec_ref(v___y_824_);
v___x_838_ = l_Array_append___redArg(v___y_825_, v___x_837_);
lean_dec_ref(v___x_837_);
v___x_839_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_839_, 0, v___y_817_);
lean_ctor_set(v___x_839_, 1, v___y_819_);
lean_ctor_set(v___x_839_, 2, v___x_838_);
v___x_840_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_841_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_841_, 0, v___y_817_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_Lean_Syntax_node3(v___y_817_, v___x_833_, v___x_835_, v___x_839_, v___x_841_);
v___x_843_ = l_Lean_Syntax_node1(v___y_817_, v___y_819_, v___x_842_);
lean_inc_ref(v___y_816_);
v___x_844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_844_, 0, v___y_817_);
lean_ctor_set(v___x_844_, 1, v___y_816_);
v___x_845_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_846_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_826_, 5);
lean_inc_n(v___y_822_, 5);
v___x_847_ = l_Lean_addMacroScope(v___y_822_, v___x_846_, v___y_826_);
v___x_848_ = lean_box(0);
v___x_849_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_849_, 0, v___y_817_);
lean_ctor_set(v___x_849_, 1, v___x_845_);
lean_ctor_set(v___x_849_, 2, v___x_847_);
lean_ctor_set(v___x_849_, 3, v___x_848_);
v___x_850_ = l_Lean_mkIdent(v_k_663_);
v___x_851_ = l_Lean_Syntax_node2(v___y_817_, v___y_819_, v___x_849_, v___x_850_);
v___x_852_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_853_, 0, v___y_817_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__35, &l_Lean_Elab_Command_elabElabRulesAux___closed__35_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__35);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__36));
lean_inc_ref_n(v___y_818_, 3);
v___x_856_ = l_Lean_Name_mkStr4(v___y_821_, v___y_818_, v___x_831_, v___x_855_);
lean_inc(v___x_856_);
v___x_857_ = l_Lean_addMacroScope(v___y_822_, v___x_856_, v___y_826_);
v___x_858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_848_);
v___x_859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v___x_848_);
v___x_860_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_860_, 0, v___y_817_);
lean_ctor_set(v___x_860_, 1, v___x_854_);
lean_ctor_set(v___x_860_, 2, v___x_857_);
lean_ctor_set(v___x_860_, 3, v___x_859_);
v___x_861_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_862_, 0, v___y_817_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_864_ = l_Lean_Name_mkStr4(v___y_821_, v___x_830_, v___x_831_, v___x_863_);
v___x_865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_865_, 0, v___y_817_);
lean_ctor_set(v___x_865_, 1, v___x_863_);
v___x_866_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_867_ = l_Lean_Name_mkStr4(v___y_821_, v___x_830_, v___x_831_, v___x_866_);
v___x_868_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_869_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_870_ = l_Lean_addMacroScope(v___y_822_, v___x_869_, v___y_826_);
v___x_871_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_871_, 0, v___y_817_);
lean_ctor_set(v___x_871_, 1, v___x_868_);
lean_ctor_set(v___x_871_, 2, v___x_870_);
lean_ctor_set(v___x_871_, 3, v___x_848_);
v___x_872_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__38, &l_Lean_Elab_Command_elabElabRulesAux___closed__38_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__38);
v___x_873_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__39));
v___x_874_ = l_Lean_addMacroScope(v___y_822_, v___x_873_, v___y_826_);
v___x_875_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_875_, 0, v___y_817_);
lean_ctor_set(v___x_875_, 1, v___x_872_);
lean_ctor_set(v___x_875_, 2, v___x_874_);
lean_ctor_set(v___x_875_, 3, v___x_848_);
lean_inc_ref(v___x_875_);
lean_inc_ref(v___x_871_);
v___x_876_ = l_Lean_Syntax_node2(v___y_817_, v___y_819_, v___x_871_, v___x_875_);
v___x_877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_877_, 0, v___y_817_);
lean_ctor_set(v___x_877_, 1, v___y_819_);
lean_ctor_set(v___x_877_, 2, v___y_825_);
v___x_878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_879_, 0, v___y_817_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
v___x_881_ = l_Lean_Name_mkStr4(v___y_821_, v___x_830_, v___x_831_, v___x_880_);
v___x_882_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__42, &l_Lean_Elab_Command_elabElabRulesAux___closed__42_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42);
v___x_883_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__43));
v___x_884_ = l_Lean_Name_mkStr4(v___y_821_, v___y_818_, v___x_831_, v___x_883_);
lean_inc(v___x_884_);
v___x_885_ = l_Lean_addMacroScope(v___y_822_, v___x_884_, v___y_826_);
v___x_886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_848_);
v___x_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v___x_848_);
v___x_888_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_888_, 0, v___y_817_);
lean_ctor_set(v___x_888_, 1, v___x_882_);
lean_ctor_set(v___x_888_, 2, v___x_885_);
lean_ctor_set(v___x_888_, 3, v___x_887_);
v___x_889_ = l_Lean_Syntax_node1(v___y_817_, v___y_819_, v___y_815_);
v___x_890_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_891_ = l_Lean_Name_mkStr4(v___y_821_, v___x_830_, v___x_831_, v___x_890_);
v___x_892_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_892_, 0, v___y_817_);
lean_ctor_set(v___x_892_, 1, v___x_890_);
v___x_893_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_894_ = l_Lean_Name_mkStr4(v___y_821_, v___x_830_, v___x_831_, v___x_893_);
lean_inc_ref_n(v___x_877_, 4);
v___x_895_ = l_Lean_Syntax_node2(v___y_817_, v___x_894_, v___x_877_, v___x_871_);
v___x_896_ = l_Lean_Syntax_node1(v___y_817_, v___y_819_, v___x_895_);
v___x_897_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_898_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_898_, 0, v___y_817_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_900_ = l_Lean_Name_mkStr4(v___y_821_, v___x_830_, v___x_831_, v___x_899_);
v___x_901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_902_ = l_Lean_Name_mkStr4(v___y_821_, v___x_830_, v___x_831_, v___x_901_);
v___x_903_ = l_Array_append___redArg(v___y_825_, v_a_673_);
lean_dec(v_a_673_);
v___x_904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_905_, 0, v___y_817_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_907_ = l_Lean_Name_mkStr4(v___y_821_, v___x_830_, v___x_831_, v___x_906_);
v___x_908_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_909_, 0, v___y_817_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_Syntax_node1(v___y_817_, v___x_907_, v___x_909_);
v___x_911_ = l_Lean_Syntax_node1(v___y_817_, v___y_819_, v___x_910_);
v___x_912_ = l_Lean_Syntax_node1(v___y_817_, v___y_819_, v___x_911_);
v___x_913_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_914_ = l_Lean_Name_mkStr4(v___y_821_, v___x_830_, v___x_831_, v___x_913_);
v___x_915_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_916_, 0, v___y_817_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_918_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_919_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_920_ = l_Lean_addMacroScope(v___y_822_, v___x_919_, v___y_826_);
v___x_921_ = l_Lean_Name_mkStr3(v___y_821_, v___y_818_, v___x_917_);
v___x_922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v___x_848_);
v___x_923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_848_);
v___x_924_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_924_, 0, v___y_817_);
lean_ctor_set(v___x_924_, 1, v___x_918_);
lean_ctor_set(v___x_924_, 2, v___x_920_);
lean_ctor_set(v___x_924_, 3, v___x_923_);
v___x_925_ = l_Lean_Syntax_node2(v___y_817_, v___x_914_, v___x_916_, v___x_924_);
lean_inc_ref_n(v___x_879_, 2);
v___x_926_ = l_Lean_Syntax_node4(v___y_817_, v___x_902_, v___x_905_, v___x_912_, v___x_879_, v___x_925_);
v___x_927_ = lean_array_push(v___x_903_, v___x_926_);
v___x_928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_928_, 0, v___y_817_);
lean_ctor_set(v___x_928_, 1, v___y_819_);
lean_ctor_set(v___x_928_, 2, v___x_927_);
v___x_929_ = l_Lean_Syntax_node1(v___y_817_, v___x_900_, v___x_928_);
v___x_930_ = l_Lean_Syntax_node6(v___y_817_, v___x_891_, v___x_892_, v___x_877_, v___x_877_, v___x_896_, v___x_898_, v___x_929_);
lean_inc(v___x_867_);
v___x_931_ = l_Lean_Syntax_node4(v___y_817_, v___x_867_, v___x_889_, v___x_877_, v___x_879_, v___x_930_);
lean_inc_ref(v___x_865_);
lean_inc(v___x_864_);
v___x_932_ = l_Lean_Syntax_node2(v___y_817_, v___x_864_, v___x_865_, v___x_931_);
v___x_933_ = l_Lean_Syntax_node2(v___y_817_, v___y_819_, v___x_875_, v___x_932_);
v___x_934_ = l_Lean_Syntax_node2(v___y_817_, v___x_881_, v___x_888_, v___x_933_);
v___x_935_ = l_Lean_Syntax_node4(v___y_817_, v___x_867_, v___x_876_, v___x_877_, v___x_879_, v___x_934_);
v___x_936_ = l_Lean_Syntax_node2(v___y_817_, v___x_864_, v___x_865_, v___x_935_);
v___x_937_ = lean_unsigned_to_nat(9u);
v___x_938_ = lean_mk_empty_array_with_capacity(v___x_937_);
v___x_939_ = lean_array_push(v___x_938_, v___x_829_);
v___x_940_ = lean_array_push(v___x_939_, v___x_843_);
v___x_941_ = lean_array_push(v___x_940_, v___y_823_);
v___x_942_ = lean_array_push(v___x_941_, v___x_844_);
v___x_943_ = lean_array_push(v___x_942_, v___x_851_);
v___x_944_ = lean_array_push(v___x_943_, v___x_853_);
v___x_945_ = lean_array_push(v___x_944_, v___x_860_);
v___x_946_ = lean_array_push(v___x_945_, v___x_862_);
v___x_947_ = lean_array_push(v___x_946_, v___x_936_);
lean_inc(v___y_820_);
v___x_948_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_948_, 0, v___y_817_);
lean_ctor_set(v___x_948_, 1, v___y_820_);
lean_ctor_set(v___x_948_, 2, v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
v___jp_950_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_957_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_958_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_959_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_960_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_961_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_962_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_660_) == 1)
{
lean_object* v_val_963_; lean_object* v___x_964_; 
v_val_963_ = lean_ctor_get(v_doc_x3f_660_, 0);
lean_inc(v_val_963_);
lean_dec_ref_known(v_doc_x3f_660_, 1);
v___x_964_ = l_Array_mkArray1___redArg(v_val_963_);
v___y_815_ = v___y_951_;
v___y_816_ = v___x_959_;
v___y_817_ = v___y_952_;
v___y_818_ = v___x_958_;
v___y_819_ = v___x_961_;
v___y_820_ = v___x_960_;
v___y_821_ = v___x_957_;
v___y_822_ = v_a_956_;
v___y_823_ = v___y_953_;
v___y_824_ = v___y_954_;
v___y_825_ = v___x_962_;
v___y_826_ = v___y_955_;
v___y_827_ = v___x_964_;
goto v___jp_814_;
}
else
{
lean_object* v___x_965_; 
lean_dec(v_doc_x3f_660_);
v___x_965_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_815_ = v___y_951_;
v___y_816_ = v___x_959_;
v___y_817_ = v___y_952_;
v___y_818_ = v___x_958_;
v___y_819_ = v___x_961_;
v___y_820_ = v___x_960_;
v___y_821_ = v___x_957_;
v___y_822_ = v_a_956_;
v___y_823_ = v___y_953_;
v___y_824_ = v___y_954_;
v___y_825_ = v___x_962_;
v___y_826_ = v___y_955_;
v___y_827_ = v___x_965_;
goto v___jp_814_;
}
}
v___jp_966_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
lean_inc_ref_n(v___y_971_, 3);
v___x_979_ = l_Array_append___redArg(v___y_971_, v___y_978_);
lean_dec_ref(v___y_978_);
lean_inc_n(v___y_977_, 7);
lean_inc_n(v___y_968_, 26);
v___x_980_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_980_, 0, v___y_968_);
lean_ctor_set(v___x_980_, 1, v___y_977_);
lean_ctor_set(v___x_980_, 2, v___x_979_);
v___x_981_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_982_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_983_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_975_, 8);
v___x_984_ = l_Lean_Name_mkStr4(v___y_975_, v___x_981_, v___x_982_, v___x_983_);
v___x_985_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_986_, 0, v___y_968_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_988_ = l_Lean_Syntax_SepArray_ofElems(v___x_987_, v___y_970_);
lean_dec_ref(v___y_970_);
v___x_989_ = l_Array_append___redArg(v___y_971_, v___x_988_);
lean_dec_ref(v___x_988_);
v___x_990_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_990_, 0, v___y_968_);
lean_ctor_set(v___x_990_, 1, v___y_977_);
lean_ctor_set(v___x_990_, 2, v___x_989_);
v___x_991_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_992_, 0, v___y_968_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Lean_Syntax_node3(v___y_968_, v___x_984_, v___x_986_, v___x_990_, v___x_992_);
v___x_994_ = l_Lean_Syntax_node1(v___y_968_, v___y_977_, v___x_993_);
lean_inc_ref(v___y_973_);
v___x_995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_995_, 0, v___y_968_);
lean_ctor_set(v___x_995_, 1, v___y_973_);
v___x_996_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_997_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_967_, 2);
lean_inc_n(v___y_969_, 2);
v___x_998_ = l_Lean_addMacroScope(v___y_969_, v___x_997_, v___y_967_);
v___x_999_ = lean_box(0);
v___x_1000_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1000_, 0, v___y_968_);
lean_ctor_set(v___x_1000_, 1, v___x_996_);
lean_ctor_set(v___x_1000_, 2, v___x_998_);
lean_ctor_set(v___x_1000_, 3, v___x_999_);
v___x_1001_ = l_Lean_mkIdent(v_k_663_);
v___x_1002_ = l_Lean_Syntax_node2(v___y_968_, v___y_977_, v___x_1000_, v___x_1001_);
v___x_1003_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___y_968_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__45, &l_Lean_Elab_Command_elabElabRulesAux___closed__45_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__45);
v___x_1006_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__46));
lean_inc_ref_n(v___y_976_, 2);
v___x_1007_ = l_Lean_Name_mkStr4(v___y_975_, v___y_976_, v___x_1006_, v___x_1006_);
lean_inc(v___x_1007_);
v___x_1008_ = l_Lean_addMacroScope(v___y_969_, v___x_1007_, v___y_967_);
v___x_1009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_999_);
v___x_1010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v___x_999_);
v___x_1011_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1011_, 0, v___y_968_);
lean_ctor_set(v___x_1011_, 1, v___x_1005_);
lean_ctor_set(v___x_1011_, 2, v___x_1008_);
lean_ctor_set(v___x_1011_, 3, v___x_1010_);
v___x_1012_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___y_968_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1015_ = l_Lean_Name_mkStr4(v___y_975_, v___x_981_, v___x_982_, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___y_968_);
lean_ctor_set(v___x_1016_, 1, v___x_1014_);
v___x_1017_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1018_ = l_Lean_Name_mkStr4(v___y_975_, v___x_981_, v___x_982_, v___x_1017_);
v___x_1019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1020_ = l_Lean_Name_mkStr4(v___y_975_, v___x_981_, v___x_982_, v___x_1019_);
v___x_1021_ = l_Array_append___redArg(v___y_971_, v_a_673_);
lean_dec(v_a_673_);
v___x_1022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1023_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___y_968_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1025_ = l_Lean_Name_mkStr4(v___y_975_, v___x_981_, v___x_982_, v___x_1024_);
v___x_1026_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1027_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___y_968_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = l_Lean_Syntax_node1(v___y_968_, v___x_1025_, v___x_1027_);
v___x_1029_ = l_Lean_Syntax_node1(v___y_968_, v___y_977_, v___x_1028_);
v___x_1030_ = l_Lean_Syntax_node1(v___y_968_, v___y_977_, v___x_1029_);
v___x_1031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___y_968_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1034_ = l_Lean_Name_mkStr4(v___y_975_, v___x_981_, v___x_982_, v___x_1033_);
v___x_1035_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1036_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___y_968_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1038_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1039_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1040_ = l_Lean_addMacroScope(v___y_969_, v___x_1039_, v___y_967_);
v___x_1041_ = l_Lean_Name_mkStr3(v___y_975_, v___y_976_, v___x_1037_);
v___x_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___x_999_);
v___x_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___x_999_);
v___x_1044_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1044_, 0, v___y_968_);
lean_ctor_set(v___x_1044_, 1, v___x_1038_);
lean_ctor_set(v___x_1044_, 2, v___x_1040_);
lean_ctor_set(v___x_1044_, 3, v___x_1043_);
v___x_1045_ = l_Lean_Syntax_node2(v___y_968_, v___x_1034_, v___x_1036_, v___x_1044_);
v___x_1046_ = l_Lean_Syntax_node4(v___y_968_, v___x_1020_, v___x_1023_, v___x_1030_, v___x_1032_, v___x_1045_);
v___x_1047_ = lean_array_push(v___x_1021_, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1048_, 0, v___y_968_);
lean_ctor_set(v___x_1048_, 1, v___y_977_);
lean_ctor_set(v___x_1048_, 2, v___x_1047_);
v___x_1049_ = l_Lean_Syntax_node1(v___y_968_, v___x_1018_, v___x_1048_);
v___x_1050_ = l_Lean_Syntax_node2(v___y_968_, v___x_1015_, v___x_1016_, v___x_1049_);
v___x_1051_ = lean_unsigned_to_nat(9u);
v___x_1052_ = lean_mk_empty_array_with_capacity(v___x_1051_);
v___x_1053_ = lean_array_push(v___x_1052_, v___x_980_);
v___x_1054_ = lean_array_push(v___x_1053_, v___x_994_);
v___x_1055_ = lean_array_push(v___x_1054_, v___y_972_);
v___x_1056_ = lean_array_push(v___x_1055_, v___x_995_);
v___x_1057_ = lean_array_push(v___x_1056_, v___x_1002_);
v___x_1058_ = lean_array_push(v___x_1057_, v___x_1004_);
v___x_1059_ = lean_array_push(v___x_1058_, v___x_1011_);
v___x_1060_ = lean_array_push(v___x_1059_, v___x_1013_);
v___x_1061_ = lean_array_push(v___x_1060_, v___x_1050_);
lean_inc(v___y_974_);
v___x_1062_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1062_, 0, v___y_968_);
lean_ctor_set(v___x_1062_, 1, v___y_974_);
lean_ctor_set(v___x_1062_, 2, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
v___jp_1064_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1070_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1072_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1073_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1074_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1075_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_660_) == 1)
{
lean_object* v_val_1076_; lean_object* v___x_1077_; 
v_val_1076_ = lean_ctor_get(v_doc_x3f_660_, 0);
lean_inc(v_val_1076_);
lean_dec_ref_known(v_doc_x3f_660_, 1);
v___x_1077_ = l_Array_mkArray1___redArg(v_val_1076_);
v___y_967_ = v___y_1065_;
v___y_968_ = v___y_1066_;
v___y_969_ = v_a_1069_;
v___y_970_ = v___y_1067_;
v___y_971_ = v___x_1075_;
v___y_972_ = v___y_1068_;
v___y_973_ = v___x_1072_;
v___y_974_ = v___x_1073_;
v___y_975_ = v___x_1070_;
v___y_976_ = v___x_1071_;
v___y_977_ = v___x_1074_;
v___y_978_ = v___x_1077_;
goto v___jp_966_;
}
else
{
lean_object* v___x_1078_; 
lean_dec(v_doc_x3f_660_);
v___x_1078_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_967_ = v___y_1065_;
v___y_968_ = v___y_1066_;
v___y_969_ = v_a_1069_;
v___y_970_ = v___y_1067_;
v___y_971_ = v___x_1075_;
v___y_972_ = v___y_1068_;
v___y_973_ = v___x_1072_;
v___y_974_ = v___x_1073_;
v___y_975_ = v___x_1070_;
v___y_976_ = v___x_1071_;
v___y_977_ = v___x_1074_;
v___y_978_ = v___x_1078_;
goto v___jp_966_;
}
}
v___jp_1079_:
{
lean_object* v___x_1085_; 
lean_inc(v___y_1084_);
lean_inc(v_k_663_);
v___x_1085_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_663_, v_attrKind_662_, v_attrs_x3f_661_, v___y_1084_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1087_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v___x_1087_ = l_Lean_Elab_Command_getRef___redArg(v___y_1082_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1089_ = l_Lean_SourceInfo_fromRef(v_a_1088_, v___y_1080_);
lean_dec(v_a_1088_);
v___x_1090_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1082_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_quotContext_x3f_1091_; 
v_quotContext_x3f_1091_ = lean_ctor_get(v___y_1082_, 5);
if (lean_obj_tag(v_quotContext_x3f_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1093_; lean_object* v_a_1094_; 
v_a_1092_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1090_, 1);
v___x_1093_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1083_);
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref(v___x_1093_);
v___y_1065_ = v_a_1092_;
v___y_1066_ = v___x_1089_;
v___y_1067_ = v_a_1086_;
v___y_1068_ = v___y_1081_;
v_a_1069_ = v_a_1094_;
goto v___jp_1064_;
}
else
{
lean_object* v_a_1095_; lean_object* v_val_1096_; 
v_a_1095_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1090_, 1);
v_val_1096_ = lean_ctor_get(v_quotContext_x3f_1091_, 0);
lean_inc(v_val_1096_);
v___y_1065_ = v_a_1095_;
v___y_1066_ = v___x_1089_;
v___y_1067_ = v_a_1086_;
v___y_1068_ = v___y_1081_;
v_a_1069_ = v_val_1096_;
goto v___jp_1064_;
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v___x_1089_);
lean_dec(v_a_1086_);
lean_dec(v___y_1081_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
v_a_1097_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1090_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1090_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_dec(v_a_1086_);
lean_dec(v___y_1081_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
return v___x_1087_;
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec(v___y_1081_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
v_a_1105_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1085_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1085_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
v___jp_1113_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_inc_ref_n(v___y_1114_, 4);
v___x_1126_ = l_Array_append___redArg(v___y_1114_, v___y_1125_);
lean_dec_ref(v___y_1125_);
lean_inc_n(v___y_1123_, 10);
lean_inc_n(v___y_1118_, 36);
v___x_1127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1127_, 0, v___y_1118_);
lean_ctor_set(v___x_1127_, 1, v___y_1123_);
lean_ctor_set(v___x_1127_, 2, v___x_1126_);
v___x_1128_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1129_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1130_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1124_, 11);
v___x_1131_ = l_Lean_Name_mkStr4(v___y_1124_, v___x_1128_, v___x_1129_, v___x_1130_);
v___x_1132_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___y_1118_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1135_ = l_Lean_Syntax_SepArray_ofElems(v___x_1134_, v___y_1122_);
lean_dec_ref(v___y_1122_);
v___x_1136_ = l_Array_append___redArg(v___y_1114_, v___x_1135_);
lean_dec_ref(v___x_1135_);
v___x_1137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1137_, 0, v___y_1118_);
lean_ctor_set(v___x_1137_, 1, v___y_1123_);
lean_ctor_set(v___x_1137_, 2, v___x_1136_);
v___x_1138_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___y_1118_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = l_Lean_Syntax_node3(v___y_1118_, v___x_1131_, v___x_1133_, v___x_1137_, v___x_1139_);
v___x_1141_ = l_Lean_Syntax_node1(v___y_1118_, v___y_1123_, v___x_1140_);
lean_inc_ref(v___y_1115_);
v___x_1142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___y_1118_);
lean_ctor_set(v___x_1142_, 1, v___y_1115_);
v___x_1143_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1144_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1117_, 4);
lean_inc_n(v___y_1120_, 4);
v___x_1145_ = l_Lean_addMacroScope(v___y_1120_, v___x_1144_, v___y_1117_);
v___x_1146_ = lean_box(0);
v___x_1147_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1147_, 0, v___y_1118_);
lean_ctor_set(v___x_1147_, 1, v___x_1143_);
lean_ctor_set(v___x_1147_, 2, v___x_1145_);
lean_ctor_set(v___x_1147_, 3, v___x_1146_);
v___x_1148_ = l_Lean_mkIdent(v_k_663_);
v___x_1149_ = l_Lean_Syntax_node2(v___y_1118_, v___y_1123_, v___x_1147_, v___x_1148_);
v___x_1150_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___y_1118_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_1153_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
v___x_1154_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc_ref_n(v___y_1116_, 2);
v___x_1155_ = l_Lean_Name_mkStr4(v___y_1124_, v___y_1116_, v___x_1153_, v___x_1154_);
lean_inc(v___x_1155_);
v___x_1156_ = l_Lean_addMacroScope(v___y_1120_, v___x_1155_, v___y_1117_);
v___x_1157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1146_);
v___x_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v___x_1146_);
v___x_1159_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1159_, 0, v___y_1118_);
lean_ctor_set(v___x_1159_, 1, v___x_1152_);
lean_ctor_set(v___x_1159_, 2, v___x_1156_);
lean_ctor_set(v___x_1159_, 3, v___x_1158_);
v___x_1160_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___y_1118_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1163_ = l_Lean_Name_mkStr4(v___y_1124_, v___x_1128_, v___x_1129_, v___x_1162_);
v___x_1164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___y_1118_);
lean_ctor_set(v___x_1164_, 1, v___x_1162_);
v___x_1165_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_1166_ = l_Lean_Name_mkStr4(v___y_1124_, v___x_1128_, v___x_1129_, v___x_1165_);
v___x_1167_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1169_ = l_Lean_addMacroScope(v___y_1120_, v___x_1168_, v___y_1117_);
v___x_1170_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1170_, 0, v___y_1118_);
lean_ctor_set(v___x_1170_, 1, v___x_1167_);
lean_ctor_set(v___x_1170_, 2, v___x_1169_);
lean_ctor_set(v___x_1170_, 3, v___x_1146_);
v___x_1171_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__48, &l_Lean_Elab_Command_elabElabRulesAux___closed__48_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__48);
v___x_1172_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__49));
v___x_1173_ = l_Lean_addMacroScope(v___y_1120_, v___x_1172_, v___y_1117_);
v___x_1174_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1174_, 0, v___y_1118_);
lean_ctor_set(v___x_1174_, 1, v___x_1171_);
lean_ctor_set(v___x_1174_, 2, v___x_1173_);
lean_ctor_set(v___x_1174_, 3, v___x_1146_);
lean_inc_ref(v___x_1170_);
v___x_1175_ = l_Lean_Syntax_node2(v___y_1118_, v___y_1123_, v___x_1170_, v___x_1174_);
v___x_1176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1176_, 0, v___y_1118_);
lean_ctor_set(v___x_1176_, 1, v___y_1123_);
lean_ctor_set(v___x_1176_, 2, v___y_1114_);
v___x_1177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___y_1118_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1180_ = l_Lean_Name_mkStr4(v___y_1124_, v___x_1128_, v___x_1129_, v___x_1179_);
v___x_1181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___y_1118_);
lean_ctor_set(v___x_1181_, 1, v___x_1179_);
v___x_1182_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1183_ = l_Lean_Name_mkStr4(v___y_1124_, v___x_1128_, v___x_1129_, v___x_1182_);
lean_inc_ref_n(v___x_1176_, 3);
v___x_1184_ = l_Lean_Syntax_node2(v___y_1118_, v___x_1183_, v___x_1176_, v___x_1170_);
v___x_1185_ = l_Lean_Syntax_node1(v___y_1118_, v___y_1123_, v___x_1184_);
v___x_1186_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___y_1118_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1189_ = l_Lean_Name_mkStr4(v___y_1124_, v___x_1128_, v___x_1129_, v___x_1188_);
v___x_1190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1191_ = l_Lean_Name_mkStr4(v___y_1124_, v___x_1128_, v___x_1129_, v___x_1190_);
v___x_1192_ = l_Array_append___redArg(v___y_1114_, v_a_673_);
lean_dec(v_a_673_);
v___x_1193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___y_1118_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1196_ = l_Lean_Name_mkStr4(v___y_1124_, v___x_1128_, v___x_1129_, v___x_1195_);
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___y_1118_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = l_Lean_Syntax_node1(v___y_1118_, v___x_1196_, v___x_1198_);
v___x_1200_ = l_Lean_Syntax_node1(v___y_1118_, v___y_1123_, v___x_1199_);
v___x_1201_ = l_Lean_Syntax_node1(v___y_1118_, v___y_1123_, v___x_1200_);
v___x_1202_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1203_ = l_Lean_Name_mkStr4(v___y_1124_, v___x_1128_, v___x_1129_, v___x_1202_);
v___x_1204_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___y_1118_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1207_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1208_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1209_ = l_Lean_addMacroScope(v___y_1120_, v___x_1208_, v___y_1117_);
v___x_1210_ = l_Lean_Name_mkStr3(v___y_1124_, v___y_1116_, v___x_1206_);
v___x_1211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v___x_1146_);
v___x_1212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v___x_1146_);
v___x_1213_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1213_, 0, v___y_1118_);
lean_ctor_set(v___x_1213_, 1, v___x_1207_);
lean_ctor_set(v___x_1213_, 2, v___x_1209_);
lean_ctor_set(v___x_1213_, 3, v___x_1212_);
v___x_1214_ = l_Lean_Syntax_node2(v___y_1118_, v___x_1203_, v___x_1205_, v___x_1213_);
lean_inc_ref(v___x_1178_);
v___x_1215_ = l_Lean_Syntax_node4(v___y_1118_, v___x_1191_, v___x_1194_, v___x_1201_, v___x_1178_, v___x_1214_);
v___x_1216_ = lean_array_push(v___x_1192_, v___x_1215_);
v___x_1217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1217_, 0, v___y_1118_);
lean_ctor_set(v___x_1217_, 1, v___y_1123_);
lean_ctor_set(v___x_1217_, 2, v___x_1216_);
v___x_1218_ = l_Lean_Syntax_node1(v___y_1118_, v___x_1189_, v___x_1217_);
v___x_1219_ = l_Lean_Syntax_node6(v___y_1118_, v___x_1180_, v___x_1181_, v___x_1176_, v___x_1176_, v___x_1185_, v___x_1187_, v___x_1218_);
v___x_1220_ = l_Lean_Syntax_node4(v___y_1118_, v___x_1166_, v___x_1175_, v___x_1176_, v___x_1178_, v___x_1219_);
v___x_1221_ = l_Lean_Syntax_node2(v___y_1118_, v___x_1163_, v___x_1164_, v___x_1220_);
v___x_1222_ = lean_unsigned_to_nat(9u);
v___x_1223_ = lean_mk_empty_array_with_capacity(v___x_1222_);
v___x_1224_ = lean_array_push(v___x_1223_, v___x_1127_);
v___x_1225_ = lean_array_push(v___x_1224_, v___x_1141_);
v___x_1226_ = lean_array_push(v___x_1225_, v___y_1119_);
v___x_1227_ = lean_array_push(v___x_1226_, v___x_1142_);
v___x_1228_ = lean_array_push(v___x_1227_, v___x_1149_);
v___x_1229_ = lean_array_push(v___x_1228_, v___x_1151_);
v___x_1230_ = lean_array_push(v___x_1229_, v___x_1159_);
v___x_1231_ = lean_array_push(v___x_1230_, v___x_1161_);
v___x_1232_ = lean_array_push(v___x_1231_, v___x_1221_);
lean_inc(v___y_1121_);
v___x_1233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1233_, 0, v___y_1118_);
lean_ctor_set(v___x_1233_, 1, v___y_1121_);
lean_ctor_set(v___x_1233_, 2, v___x_1232_);
v___x_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
return v___x_1234_;
}
v___jp_1235_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1241_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1242_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1243_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1244_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1245_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1246_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_660_) == 1)
{
lean_object* v_val_1247_; lean_object* v___x_1248_; 
v_val_1247_ = lean_ctor_get(v_doc_x3f_660_, 0);
lean_inc(v_val_1247_);
lean_dec_ref_known(v_doc_x3f_660_, 1);
v___x_1248_ = l_Array_mkArray1___redArg(v_val_1247_);
v___y_1114_ = v___x_1246_;
v___y_1115_ = v___x_1243_;
v___y_1116_ = v___x_1242_;
v___y_1117_ = v___y_1237_;
v___y_1118_ = v___y_1236_;
v___y_1119_ = v___y_1238_;
v___y_1120_ = v_a_1240_;
v___y_1121_ = v___x_1244_;
v___y_1122_ = v___y_1239_;
v___y_1123_ = v___x_1245_;
v___y_1124_ = v___x_1241_;
v___y_1125_ = v___x_1248_;
goto v___jp_1113_;
}
else
{
lean_object* v___x_1249_; 
lean_dec(v_doc_x3f_660_);
v___x_1249_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_1114_ = v___x_1246_;
v___y_1115_ = v___x_1243_;
v___y_1116_ = v___x_1242_;
v___y_1117_ = v___y_1237_;
v___y_1118_ = v___y_1236_;
v___y_1119_ = v___y_1238_;
v___y_1120_ = v_a_1240_;
v___y_1121_ = v___x_1244_;
v___y_1122_ = v___y_1239_;
v___y_1123_ = v___x_1245_;
v___y_1124_ = v___x_1241_;
v___y_1125_ = v___x_1249_;
goto v___jp_1113_;
}
}
v___jp_1250_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_inc_ref_n(v___y_1253_, 3);
v___x_1264_ = l_Array_append___redArg(v___y_1253_, v___y_1263_);
lean_dec_ref(v___y_1263_);
lean_inc_n(v___y_1256_, 7);
lean_inc_n(v___y_1258_, 26);
v___x_1265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1265_, 0, v___y_1258_);
lean_ctor_set(v___x_1265_, 1, v___y_1256_);
lean_ctor_set(v___x_1265_, 2, v___x_1264_);
v___x_1266_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1267_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1268_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1254_, 8);
v___x_1269_ = l_Lean_Name_mkStr4(v___y_1254_, v___x_1266_, v___x_1267_, v___x_1268_);
v___x_1270_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___y_1258_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1273_ = l_Lean_Syntax_SepArray_ofElems(v___x_1272_, v___y_1252_);
lean_dec_ref(v___y_1252_);
v___x_1274_ = l_Array_append___redArg(v___y_1253_, v___x_1273_);
lean_dec_ref(v___x_1273_);
v___x_1275_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1275_, 0, v___y_1258_);
lean_ctor_set(v___x_1275_, 1, v___y_1256_);
lean_ctor_set(v___x_1275_, 2, v___x_1274_);
v___x_1276_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___y_1258_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = l_Lean_Syntax_node3(v___y_1258_, v___x_1269_, v___x_1271_, v___x_1275_, v___x_1277_);
v___x_1279_ = l_Lean_Syntax_node1(v___y_1258_, v___y_1256_, v___x_1278_);
lean_inc_ref(v___y_1255_);
v___x_1280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___y_1258_);
lean_ctor_set(v___x_1280_, 1, v___y_1255_);
v___x_1281_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1282_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1257_, 2);
lean_inc_n(v___y_1261_, 2);
v___x_1283_ = l_Lean_addMacroScope(v___y_1261_, v___x_1282_, v___y_1257_);
v___x_1284_ = lean_box(0);
v___x_1285_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1285_, 0, v___y_1258_);
lean_ctor_set(v___x_1285_, 1, v___x_1281_);
lean_ctor_set(v___x_1285_, 2, v___x_1283_);
lean_ctor_set(v___x_1285_, 3, v___x_1284_);
v___x_1286_ = l_Lean_mkIdent(v_k_663_);
v___x_1287_ = l_Lean_Syntax_node2(v___y_1258_, v___y_1256_, v___x_1285_, v___x_1286_);
v___x_1288_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___y_1258_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__51, &l_Lean_Elab_Command_elabElabRulesAux___closed__51_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51);
v___x_1291_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__52));
lean_inc_ref(v___y_1262_);
lean_inc_ref_n(v___y_1260_, 2);
v___x_1292_ = l_Lean_Name_mkStr4(v___y_1254_, v___y_1260_, v___y_1262_, v___x_1291_);
lean_inc(v___x_1292_);
v___x_1293_ = l_Lean_addMacroScope(v___y_1261_, v___x_1292_, v___y_1257_);
v___x_1294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set(v___x_1294_, 1, v___x_1284_);
v___x_1295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___x_1284_);
v___x_1296_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1296_, 0, v___y_1258_);
lean_ctor_set(v___x_1296_, 1, v___x_1290_);
lean_ctor_set(v___x_1296_, 2, v___x_1293_);
lean_ctor_set(v___x_1296_, 3, v___x_1295_);
v___x_1297_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1298_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___y_1258_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1300_ = l_Lean_Name_mkStr4(v___y_1254_, v___x_1266_, v___x_1267_, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___y_1258_);
lean_ctor_set(v___x_1301_, 1, v___x_1299_);
v___x_1302_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1303_ = l_Lean_Name_mkStr4(v___y_1254_, v___x_1266_, v___x_1267_, v___x_1302_);
v___x_1304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1305_ = l_Lean_Name_mkStr4(v___y_1254_, v___x_1266_, v___x_1267_, v___x_1304_);
v___x_1306_ = l_Array_append___redArg(v___y_1253_, v_a_673_);
lean_dec(v_a_673_);
v___x_1307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___y_1258_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1310_ = l_Lean_Name_mkStr4(v___y_1254_, v___x_1266_, v___x_1267_, v___x_1309_);
v___x_1311_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___y_1258_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = l_Lean_Syntax_node1(v___y_1258_, v___x_1310_, v___x_1312_);
v___x_1314_ = l_Lean_Syntax_node1(v___y_1258_, v___y_1256_, v___x_1313_);
v___x_1315_ = l_Lean_Syntax_node1(v___y_1258_, v___y_1256_, v___x_1314_);
v___x_1316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___y_1258_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1319_ = l_Lean_Name_mkStr4(v___y_1254_, v___x_1266_, v___x_1267_, v___x_1318_);
v___x_1320_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___y_1258_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
v___x_1322_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1323_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1324_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1325_ = l_Lean_addMacroScope(v___y_1261_, v___x_1324_, v___y_1257_);
v___x_1326_ = l_Lean_Name_mkStr3(v___y_1254_, v___y_1260_, v___x_1322_);
v___x_1327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
lean_ctor_set(v___x_1327_, 1, v___x_1284_);
v___x_1328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v___x_1284_);
v___x_1329_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1329_, 0, v___y_1258_);
lean_ctor_set(v___x_1329_, 1, v___x_1323_);
lean_ctor_set(v___x_1329_, 2, v___x_1325_);
lean_ctor_set(v___x_1329_, 3, v___x_1328_);
v___x_1330_ = l_Lean_Syntax_node2(v___y_1258_, v___x_1319_, v___x_1321_, v___x_1329_);
v___x_1331_ = l_Lean_Syntax_node4(v___y_1258_, v___x_1305_, v___x_1308_, v___x_1315_, v___x_1317_, v___x_1330_);
v___x_1332_ = lean_array_push(v___x_1306_, v___x_1331_);
v___x_1333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1333_, 0, v___y_1258_);
lean_ctor_set(v___x_1333_, 1, v___y_1256_);
lean_ctor_set(v___x_1333_, 2, v___x_1332_);
v___x_1334_ = l_Lean_Syntax_node1(v___y_1258_, v___x_1303_, v___x_1333_);
v___x_1335_ = l_Lean_Syntax_node2(v___y_1258_, v___x_1300_, v___x_1301_, v___x_1334_);
v___x_1336_ = lean_unsigned_to_nat(9u);
v___x_1337_ = lean_mk_empty_array_with_capacity(v___x_1336_);
v___x_1338_ = lean_array_push(v___x_1337_, v___x_1265_);
v___x_1339_ = lean_array_push(v___x_1338_, v___x_1279_);
v___x_1340_ = lean_array_push(v___x_1339_, v___y_1259_);
v___x_1341_ = lean_array_push(v___x_1340_, v___x_1280_);
v___x_1342_ = lean_array_push(v___x_1341_, v___x_1287_);
v___x_1343_ = lean_array_push(v___x_1342_, v___x_1289_);
v___x_1344_ = lean_array_push(v___x_1343_, v___x_1296_);
v___x_1345_ = lean_array_push(v___x_1344_, v___x_1298_);
v___x_1346_ = lean_array_push(v___x_1345_, v___x_1335_);
lean_inc(v___y_1251_);
v___x_1347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1347_, 0, v___y_1258_);
lean_ctor_set(v___x_1347_, 1, v___y_1251_);
lean_ctor_set(v___x_1347_, 2, v___x_1346_);
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
return v___x_1348_;
}
v___jp_1349_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1355_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1356_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1357_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1359_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1360_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1361_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_660_) == 1)
{
lean_object* v_val_1362_; lean_object* v___x_1363_; 
v_val_1362_ = lean_ctor_get(v_doc_x3f_660_, 0);
lean_inc(v_val_1362_);
lean_dec_ref_known(v_doc_x3f_660_, 1);
v___x_1363_ = l_Array_mkArray1___redArg(v_val_1362_);
v___y_1251_ = v___x_1359_;
v___y_1252_ = v___y_1350_;
v___y_1253_ = v___x_1361_;
v___y_1254_ = v___x_1355_;
v___y_1255_ = v___x_1358_;
v___y_1256_ = v___x_1360_;
v___y_1257_ = v___y_1352_;
v___y_1258_ = v___y_1351_;
v___y_1259_ = v___y_1353_;
v___y_1260_ = v___x_1356_;
v___y_1261_ = v_a_1354_;
v___y_1262_ = v___x_1357_;
v___y_1263_ = v___x_1363_;
goto v___jp_1250_;
}
else
{
lean_object* v___x_1364_; 
lean_dec(v_doc_x3f_660_);
v___x_1364_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_1251_ = v___x_1359_;
v___y_1252_ = v___y_1350_;
v___y_1253_ = v___x_1361_;
v___y_1254_ = v___x_1355_;
v___y_1255_ = v___x_1358_;
v___y_1256_ = v___x_1360_;
v___y_1257_ = v___y_1352_;
v___y_1258_ = v___y_1351_;
v___y_1259_ = v___y_1353_;
v___y_1260_ = v___x_1356_;
v___y_1261_ = v_a_1354_;
v___y_1262_ = v___x_1357_;
v___y_1263_ = v___x_1364_;
goto v___jp_1250_;
}
}
v___jp_1365_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_inc_ref_n(v___y_1367_, 4);
v___x_1378_ = l_Array_append___redArg(v___y_1367_, v___y_1377_);
lean_dec_ref(v___y_1377_);
lean_inc_n(v___y_1366_, 10);
lean_inc_n(v___y_1373_, 35);
v___x_1379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1379_, 0, v___y_1373_);
lean_ctor_set(v___x_1379_, 1, v___y_1366_);
lean_ctor_set(v___x_1379_, 2, v___x_1378_);
v___x_1380_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1381_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1370_, 11);
v___x_1383_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1380_, v___x_1381_, v___x_1382_);
v___x_1384_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___y_1373_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___x_1386_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1387_ = l_Lean_Syntax_SepArray_ofElems(v___x_1386_, v___y_1376_);
lean_dec_ref(v___y_1376_);
v___x_1388_ = l_Array_append___redArg(v___y_1367_, v___x_1387_);
lean_dec_ref(v___x_1387_);
v___x_1389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1389_, 0, v___y_1373_);
lean_ctor_set(v___x_1389_, 1, v___y_1366_);
lean_ctor_set(v___x_1389_, 2, v___x_1388_);
v___x_1390_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1391_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___y_1373_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
v___x_1392_ = l_Lean_Syntax_node3(v___y_1373_, v___x_1383_, v___x_1385_, v___x_1389_, v___x_1391_);
v___x_1393_ = l_Lean_Syntax_node1(v___y_1373_, v___y_1366_, v___x_1392_);
lean_inc_ref(v___y_1374_);
v___x_1394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___y_1373_);
lean_ctor_set(v___x_1394_, 1, v___y_1374_);
v___x_1395_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1396_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1375_, 3);
lean_inc_n(v___y_1368_, 3);
v___x_1397_ = l_Lean_addMacroScope(v___y_1368_, v___x_1396_, v___y_1375_);
v___x_1398_ = lean_box(0);
v___x_1399_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1399_, 0, v___y_1373_);
lean_ctor_set(v___x_1399_, 1, v___x_1395_);
lean_ctor_set(v___x_1399_, 2, v___x_1397_);
lean_ctor_set(v___x_1399_, 3, v___x_1398_);
v___x_1400_ = l_Lean_mkIdent(v_k_663_);
v___x_1401_ = l_Lean_Syntax_node2(v___y_1373_, v___y_1366_, v___x_1399_, v___x_1400_);
v___x_1402_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___y_1373_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__35, &l_Lean_Elab_Command_elabElabRulesAux___closed__35_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__35);
v___x_1405_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__36));
lean_inc_ref_n(v___y_1371_, 2);
v___x_1406_ = l_Lean_Name_mkStr4(v___y_1370_, v___y_1371_, v___x_1381_, v___x_1405_);
lean_inc(v___x_1406_);
v___x_1407_ = l_Lean_addMacroScope(v___y_1368_, v___x_1406_, v___y_1375_);
v___x_1408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1406_);
lean_ctor_set(v___x_1408_, 1, v___x_1398_);
v___x_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
lean_ctor_set(v___x_1409_, 1, v___x_1398_);
v___x_1410_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1410_, 0, v___y_1373_);
lean_ctor_set(v___x_1410_, 1, v___x_1404_);
lean_ctor_set(v___x_1410_, 2, v___x_1407_);
lean_ctor_set(v___x_1410_, 3, v___x_1409_);
v___x_1411_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___y_1373_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1414_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1380_, v___x_1381_, v___x_1413_);
v___x_1415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___y_1373_);
lean_ctor_set(v___x_1415_, 1, v___x_1413_);
v___x_1416_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_1417_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1380_, v___x_1381_, v___x_1416_);
v___x_1418_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_1419_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1420_ = l_Lean_addMacroScope(v___y_1368_, v___x_1419_, v___y_1375_);
v___x_1421_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1421_, 0, v___y_1373_);
lean_ctor_set(v___x_1421_, 1, v___x_1418_);
lean_ctor_set(v___x_1421_, 2, v___x_1420_);
lean_ctor_set(v___x_1421_, 3, v___x_1398_);
v___x_1422_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1423_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1380_, v___x_1381_, v___x_1422_);
v___x_1424_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1425_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___y_1373_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
v___x_1426_ = l_Lean_Syntax_node1(v___y_1373_, v___x_1423_, v___x_1425_);
lean_inc(v___x_1426_);
lean_inc_ref(v___x_1421_);
v___x_1427_ = l_Lean_Syntax_node2(v___y_1373_, v___y_1366_, v___x_1421_, v___x_1426_);
v___x_1428_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1428_, 0, v___y_1373_);
lean_ctor_set(v___x_1428_, 1, v___y_1366_);
lean_ctor_set(v___x_1428_, 2, v___y_1367_);
v___x_1429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___y_1373_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v___x_1431_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1432_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1380_, v___x_1381_, v___x_1431_);
v___x_1433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___y_1373_);
lean_ctor_set(v___x_1433_, 1, v___x_1431_);
v___x_1434_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1435_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1380_, v___x_1381_, v___x_1434_);
lean_inc_ref_n(v___x_1428_, 3);
v___x_1436_ = l_Lean_Syntax_node2(v___y_1373_, v___x_1435_, v___x_1428_, v___x_1421_);
v___x_1437_ = l_Lean_Syntax_node1(v___y_1373_, v___y_1366_, v___x_1436_);
v___x_1438_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___y_1373_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1441_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1380_, v___x_1381_, v___x_1440_);
v___x_1442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1443_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1380_, v___x_1381_, v___x_1442_);
v___x_1444_ = l_Array_append___redArg(v___y_1367_, v_a_673_);
lean_dec(v_a_673_);
v___x_1445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___y_1373_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = l_Lean_Syntax_node1(v___y_1373_, v___y_1366_, v___x_1426_);
v___x_1448_ = l_Lean_Syntax_node1(v___y_1373_, v___y_1366_, v___x_1447_);
v___x_1449_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1450_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1380_, v___x_1381_, v___x_1449_);
v___x_1451_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___y_1373_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1454_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1455_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1456_ = l_Lean_addMacroScope(v___y_1368_, v___x_1455_, v___y_1375_);
v___x_1457_ = l_Lean_Name_mkStr3(v___y_1370_, v___y_1371_, v___x_1453_);
v___x_1458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
lean_ctor_set(v___x_1458_, 1, v___x_1398_);
v___x_1459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
lean_ctor_set(v___x_1459_, 1, v___x_1398_);
v___x_1460_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1460_, 0, v___y_1373_);
lean_ctor_set(v___x_1460_, 1, v___x_1454_);
lean_ctor_set(v___x_1460_, 2, v___x_1456_);
lean_ctor_set(v___x_1460_, 3, v___x_1459_);
v___x_1461_ = l_Lean_Syntax_node2(v___y_1373_, v___x_1450_, v___x_1452_, v___x_1460_);
lean_inc_ref(v___x_1430_);
v___x_1462_ = l_Lean_Syntax_node4(v___y_1373_, v___x_1443_, v___x_1446_, v___x_1448_, v___x_1430_, v___x_1461_);
v___x_1463_ = lean_array_push(v___x_1444_, v___x_1462_);
v___x_1464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1464_, 0, v___y_1373_);
lean_ctor_set(v___x_1464_, 1, v___y_1366_);
lean_ctor_set(v___x_1464_, 2, v___x_1463_);
v___x_1465_ = l_Lean_Syntax_node1(v___y_1373_, v___x_1441_, v___x_1464_);
v___x_1466_ = l_Lean_Syntax_node6(v___y_1373_, v___x_1432_, v___x_1433_, v___x_1428_, v___x_1428_, v___x_1437_, v___x_1439_, v___x_1465_);
v___x_1467_ = l_Lean_Syntax_node4(v___y_1373_, v___x_1417_, v___x_1427_, v___x_1428_, v___x_1430_, v___x_1466_);
v___x_1468_ = l_Lean_Syntax_node2(v___y_1373_, v___x_1414_, v___x_1415_, v___x_1467_);
v___x_1469_ = lean_unsigned_to_nat(9u);
v___x_1470_ = lean_mk_empty_array_with_capacity(v___x_1469_);
v___x_1471_ = lean_array_push(v___x_1470_, v___x_1379_);
v___x_1472_ = lean_array_push(v___x_1471_, v___x_1393_);
v___x_1473_ = lean_array_push(v___x_1472_, v___y_1372_);
v___x_1474_ = lean_array_push(v___x_1473_, v___x_1394_);
v___x_1475_ = lean_array_push(v___x_1474_, v___x_1401_);
v___x_1476_ = lean_array_push(v___x_1475_, v___x_1403_);
v___x_1477_ = lean_array_push(v___x_1476_, v___x_1410_);
v___x_1478_ = lean_array_push(v___x_1477_, v___x_1412_);
v___x_1479_ = lean_array_push(v___x_1478_, v___x_1468_);
lean_inc(v___y_1369_);
v___x_1480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1480_, 0, v___y_1373_);
lean_ctor_set(v___x_1480_, 1, v___y_1369_);
lean_ctor_set(v___x_1480_, 2, v___x_1479_);
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
return v___x_1481_;
}
v___jp_1482_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1488_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1489_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1490_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1491_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1492_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1493_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_660_) == 1)
{
lean_object* v_val_1494_; lean_object* v___x_1495_; 
v_val_1494_ = lean_ctor_get(v_doc_x3f_660_, 0);
lean_inc(v_val_1494_);
lean_dec_ref_known(v_doc_x3f_660_, 1);
v___x_1495_ = l_Array_mkArray1___redArg(v_val_1494_);
v___y_1366_ = v___x_1492_;
v___y_1367_ = v___x_1493_;
v___y_1368_ = v_a_1487_;
v___y_1369_ = v___x_1491_;
v___y_1370_ = v___x_1488_;
v___y_1371_ = v___x_1489_;
v___y_1372_ = v___y_1484_;
v___y_1373_ = v___y_1483_;
v___y_1374_ = v___x_1490_;
v___y_1375_ = v___y_1486_;
v___y_1376_ = v___y_1485_;
v___y_1377_ = v___x_1495_;
goto v___jp_1365_;
}
else
{
lean_object* v___x_1496_; 
lean_dec(v_doc_x3f_660_);
v___x_1496_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_1366_ = v___x_1492_;
v___y_1367_ = v___x_1493_;
v___y_1368_ = v_a_1487_;
v___y_1369_ = v___x_1491_;
v___y_1370_ = v___x_1488_;
v___y_1371_ = v___x_1489_;
v___y_1372_ = v___y_1484_;
v___y_1373_ = v___y_1483_;
v___y_1374_ = v___x_1490_;
v___y_1375_ = v___y_1486_;
v___y_1376_ = v___y_1485_;
v___y_1377_ = v___x_1496_;
goto v___jp_1365_;
}
}
v___jp_1497_:
{
lean_object* v___x_1501_; 
lean_inc(v_attrKind_662_);
v___x_1501_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_662_);
if (lean_obj_tag(v_expty_x3f_665_) == 1)
{
lean_object* v_val_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
v_val_1502_ = lean_ctor_get(v_expty_x3f_665_, 0);
lean_inc(v_val_1502_);
lean_dec_ref_known(v_expty_x3f_665_, 1);
v___x_1503_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_1504_ = lean_name_eq(v_catName_1498_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
v___x_1506_ = lean_name_eq(v_catName_1498_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_dec(v___x_1501_);
lean_del_object(v___x_675_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_attrKind_662_);
lean_dec(v_doc_x3f_660_);
v___x_1507_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__58, &l_Lean_Elab_Command_elabElabRulesAux___closed__58_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58);
v___x_1508_ = l_Lean_MessageData_ofName(v_catName_1498_);
v___x_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__60, &l_Lean_Elab_Command_elabElabRulesAux___closed__60_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60);
v___x_1511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1509_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_val_1502_, v___x_1511_, v___y_1499_, v___y_1500_);
lean_dec(v_val_1502_);
return v___x_1512_;
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec(v_catName_1498_);
v___x_1513_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(v_k_663_);
v___x_1514_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_663_, v_attrKind_662_, v_attrs_x3f_661_, v___x_1513_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v___x_1516_ = l_Lean_Elab_Command_getRef___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = l_Lean_SourceInfo_fromRef(v_a_1517_, v___x_1504_);
lean_dec(v_a_1517_);
v___x_1519_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_quotContext_x3f_1520_; 
v_quotContext_x3f_1520_ = lean_ctor_get(v___y_1499_, 5);
if (lean_obj_tag(v_quotContext_x3f_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1522_; lean_object* v_a_1523_; 
v_a_1521_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1519_, 1);
v___x_1522_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1500_);
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref(v___x_1522_);
v___y_799_ = v_val_1502_;
v___y_800_ = v_a_1515_;
v___y_801_ = v___x_1501_;
v___y_802_ = v___x_1518_;
v___y_803_ = v_a_1521_;
v_a_804_ = v_a_1523_;
goto v___jp_798_;
}
else
{
lean_object* v_a_1524_; lean_object* v_val_1525_; 
v_a_1524_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1519_, 1);
v_val_1525_ = lean_ctor_get(v_quotContext_x3f_1520_, 0);
lean_inc(v_val_1525_);
v___y_799_ = v_val_1502_;
v___y_800_ = v_a_1515_;
v___y_801_ = v___x_1501_;
v___y_802_ = v___x_1518_;
v___y_803_ = v_a_1524_;
v_a_804_ = v_val_1525_;
goto v___jp_798_;
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec(v___x_1518_);
lean_dec(v_a_1515_);
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
lean_del_object(v___x_675_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
v_a_1526_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1519_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1519_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
lean_dec(v_a_1515_);
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
lean_del_object(v___x_675_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
return v___x_1516_;
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
lean_del_object(v___x_675_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
v_a_1534_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1514_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1514_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec(v_catName_1498_);
lean_del_object(v___x_675_);
v___x_1542_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(v_k_663_);
v___x_1543_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_663_, v_attrKind_662_, v_attrs_x3f_661_, v___x_1542_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1545_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1545_ = l_Lean_Elab_Command_getRef___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = 0;
v___x_1548_ = l_Lean_SourceInfo_fromRef(v_a_1546_, v___x_1547_);
lean_dec(v_a_1546_);
v___x_1549_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_quotContext_x3f_1550_; 
v_quotContext_x3f_1550_ = lean_ctor_get(v___y_1499_, 5);
if (lean_obj_tag(v_quotContext_x3f_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1552_; lean_object* v_a_1553_; 
v_a_1551_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1552_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1500_);
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1552_);
v___y_951_ = v_val_1502_;
v___y_952_ = v___x_1548_;
v___y_953_ = v___x_1501_;
v___y_954_ = v_a_1544_;
v___y_955_ = v_a_1551_;
v_a_956_ = v_a_1553_;
goto v___jp_950_;
}
else
{
lean_object* v_a_1554_; lean_object* v_val_1555_; 
v_a_1554_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1549_, 1);
v_val_1555_ = lean_ctor_get(v_quotContext_x3f_1550_, 0);
lean_inc(v_val_1555_);
v___y_951_ = v_val_1502_;
v___y_952_ = v___x_1548_;
v___y_953_ = v___x_1501_;
v___y_954_ = v_a_1544_;
v___y_955_ = v_a_1554_;
v_a_956_ = v_val_1555_;
goto v___jp_950_;
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v___x_1548_);
lean_dec(v_a_1544_);
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
v_a_1556_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1549_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1549_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_dec(v_a_1544_);
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
return v___x_1545_;
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
v_a_1564_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1543_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1543_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
else
{
lean_object* v___x_1572_; uint8_t v___x_1573_; 
lean_del_object(v___x_675_);
lean_dec(v_expty_x3f_665_);
v___x_1572_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_1573_ = lean_name_eq(v_catName_1498_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__66));
v___x_1575_ = lean_name_eq(v_catName_1498_, v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__68));
v___x_1577_ = lean_name_eq(v_catName_1498_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; uint8_t v___x_1579_; 
v___x_1578_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__70));
v___x_1579_ = lean_name_eq(v_catName_1498_, v___x_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
v___x_1581_ = lean_name_eq(v_catName_1498_, v___x_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec(v___x_1501_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_attrKind_662_);
lean_dec(v_doc_x3f_660_);
v___x_1582_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__72, &l_Lean_Elab_Command_elabElabRulesAux___closed__72_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72);
v___x_1583_ = l_Lean_MessageData_ofName(v_catName_1498_);
v___x_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_1586_, v___y_1499_, v___y_1500_);
return v___x_1587_;
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec(v_catName_1498_);
v___x_1588_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(v_k_663_);
v___x_1589_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_663_, v_attrKind_662_, v_attrs_x3f_661_, v___x_1588_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1591_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = l_Lean_Elab_Command_getRef___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
v___x_1593_ = l_Lean_SourceInfo_fromRef(v_a_1592_, v___x_1579_);
lean_dec(v_a_1592_);
v___x_1594_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_quotContext_x3f_1595_; 
v_quotContext_x3f_1595_ = lean_ctor_get(v___y_1499_, 5);
if (lean_obj_tag(v_quotContext_x3f_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1597_; lean_object* v_a_1598_; 
v_a_1596_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1594_, 1);
v___x_1597_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1500_);
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref(v___x_1597_);
v___y_1236_ = v___x_1593_;
v___y_1237_ = v_a_1596_;
v___y_1238_ = v___x_1501_;
v___y_1239_ = v_a_1590_;
v_a_1240_ = v_a_1598_;
goto v___jp_1235_;
}
else
{
lean_object* v_a_1599_; lean_object* v_val_1600_; 
v_a_1599_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1594_, 1);
v_val_1600_ = lean_ctor_get(v_quotContext_x3f_1595_, 0);
lean_inc(v_val_1600_);
v___y_1236_ = v___x_1593_;
v___y_1237_ = v_a_1599_;
v___y_1238_ = v___x_1501_;
v___y_1239_ = v_a_1590_;
v_a_1240_ = v_val_1600_;
goto v___jp_1235_;
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v___x_1593_);
lean_dec(v_a_1590_);
lean_dec(v___x_1501_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
v_a_1601_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1594_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1594_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
else
{
lean_dec(v_a_1590_);
lean_dec(v___x_1501_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
return v___x_1591_;
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec(v___x_1501_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
v_a_1609_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1589_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1589_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
else
{
lean_dec(v_catName_1498_);
v___y_1080_ = v___x_1575_;
v___y_1081_ = v___x_1501_;
v___y_1082_ = v___y_1499_;
v___y_1083_ = v___y_1500_;
v___y_1084_ = v___x_1576_;
goto v___jp_1079_;
}
}
else
{
lean_dec(v_catName_1498_);
v___y_1080_ = v___x_1575_;
v___y_1081_ = v___x_1501_;
v___y_1082_ = v___y_1499_;
v___y_1083_ = v___y_1500_;
v___y_1084_ = v___x_1576_;
goto v___jp_1079_;
}
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
lean_dec(v_catName_1498_);
v___x_1617_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__74));
lean_inc(v_k_663_);
v___x_1618_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_663_, v_attrKind_662_, v_attrs_x3f_661_, v___x_1617_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1620_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1620_ = l_Lean_Elab_Command_getRef___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v___x_1622_ = l_Lean_SourceInfo_fromRef(v_a_1621_, v___x_1573_);
lean_dec(v_a_1621_);
v___x_1623_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_quotContext_x3f_1624_; 
v_quotContext_x3f_1624_ = lean_ctor_get(v___y_1499_, 5);
if (lean_obj_tag(v_quotContext_x3f_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1626_; lean_object* v_a_1627_; 
v_a_1625_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1623_, 1);
v___x_1626_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1500_);
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref(v___x_1626_);
v___y_1350_ = v_a_1619_;
v___y_1351_ = v___x_1622_;
v___y_1352_ = v_a_1625_;
v___y_1353_ = v___x_1501_;
v_a_1354_ = v_a_1627_;
goto v___jp_1349_;
}
else
{
lean_object* v_a_1628_; lean_object* v_val_1629_; 
v_a_1628_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1623_, 1);
v_val_1629_ = lean_ctor_get(v_quotContext_x3f_1624_, 0);
lean_inc(v_val_1629_);
v___y_1350_ = v_a_1619_;
v___y_1351_ = v___x_1622_;
v___y_1352_ = v_a_1628_;
v___y_1353_ = v___x_1501_;
v_a_1354_ = v_val_1629_;
goto v___jp_1349_;
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec(v___x_1622_);
lean_dec(v_a_1619_);
lean_dec(v___x_1501_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
v_a_1630_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1623_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1623_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_dec(v_a_1619_);
lean_dec(v___x_1501_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
return v___x_1620_;
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec(v___x_1501_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
v_a_1638_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1618_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1618_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec(v_catName_1498_);
v___x_1646_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(v_k_663_);
v___x_1647_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_663_, v_attrKind_662_, v_attrs_x3f_661_, v___x_1646_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = l_Lean_Elab_Command_getRef___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; uint8_t v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v___x_1651_ = 0;
v___x_1652_ = l_Lean_SourceInfo_fromRef(v_a_1650_, v___x_1651_);
lean_dec(v_a_1650_);
v___x_1653_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_quotContext_x3f_1654_; 
v_quotContext_x3f_1654_ = lean_ctor_get(v___y_1499_, 5);
if (lean_obj_tag(v_quotContext_x3f_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1656_; lean_object* v_a_1657_; 
v_a_1655_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1653_, 1);
v___x_1656_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1500_);
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref(v___x_1656_);
v___y_1483_ = v___x_1652_;
v___y_1484_ = v___x_1501_;
v___y_1485_ = v_a_1648_;
v___y_1486_ = v_a_1655_;
v_a_1487_ = v_a_1657_;
goto v___jp_1482_;
}
else
{
lean_object* v_a_1658_; lean_object* v_val_1659_; 
v_a_1658_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1653_, 1);
v_val_1659_ = lean_ctor_get(v_quotContext_x3f_1654_, 0);
lean_inc(v_val_1659_);
v___y_1483_ = v___x_1652_;
v___y_1484_ = v___x_1501_;
v___y_1485_ = v_a_1648_;
v___y_1486_ = v_a_1658_;
v_a_1487_ = v_val_1659_;
goto v___jp_1482_;
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v___x_1652_);
lean_dec(v_a_1648_);
lean_dec(v___x_1501_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
v_a_1660_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1653_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1653_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_dec(v_a_1648_);
lean_dec(v___x_1501_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
return v___x_1649_;
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v___x_1501_);
lean_dec(v_a_673_);
lean_dec(v_k_663_);
lean_dec(v_doc_x3f_660_);
v_a_1668_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1647_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1647_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
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
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec(v_expty_x3f_665_);
lean_dec(v_k_663_);
lean_dec(v_attrKind_662_);
lean_dec(v_doc_x3f_660_);
v_a_1690_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_672_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_672_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object* v_doc_x3f_1698_, lean_object* v_attrs_x3f_1699_, lean_object* v_attrKind_1700_, lean_object* v_k_1701_, lean_object* v_cat_x3f_1702_, lean_object* v_expty_x3f_1703_, lean_object* v_alts_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Elab_Command_elabElabRulesAux(v_doc_x3f_1698_, v_attrs_x3f_1699_, v_attrKind_1700_, v_k_1701_, v_cat_x3f_1702_, v_expty_x3f_1703_, v_alts_1704_, v_a_1705_, v_a_1706_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_cat_x3f_1702_);
lean_dec(v_attrs_x3f_1699_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object* v_00_u03b1_1709_, lean_object* v_ref_1710_, lean_object* v_msg_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_1710_, v_msg_1711_, v___y_1712_, v___y_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object* v_00_u03b1_1716_, lean_object* v_ref_1717_, lean_object* v_msg_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(v_00_u03b1_1716_, v_ref_1717_, v_msg_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v_ref_1717_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(lean_object* v_msgData_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_1723_, v___y_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___boxed(lean_object* v_msgData_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(v_msgData_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(lean_object* v_00_u03b1_1733_, lean_object* v_msg_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_1734_, v___y_1735_, v___y_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___boxed(lean_object* v_00_u03b1_1739_, lean_object* v_msg_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(v_00_u03b1_1739_, v_msg_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(lean_object* v_msgData_1745_, lean_object* v_macroStack_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_msgData_1745_, v_macroStack_1746_, v___y_1748_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___boxed(lean_object* v_msgData_1751_, lean_object* v_macroStack_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(v_msgData_1751_, v_macroStack_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object* v_x_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object* v_x_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_Elab_Command_elabElabRules___lam__0(v_x_1759_);
lean_dec(v_x_1759_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object* v___x_1765_, lean_object* v___x_1766_, lean_object* v_attrKind_1767_, lean_object* v_expty_x3f_1768_, lean_object* v___f_1769_, lean_object* v_cat_x3f_1770_, lean_object* v___x_1771_, lean_object* v___x_1772_, lean_object* v_attrs_x3f_1773_, lean_object* v___x_1774_, lean_object* v___x_1775_, lean_object* v___x_1776_, lean_object* v_doc_x3f_1777_, lean_object* v_kind_x3f_1778_, lean_object* v_alts_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_Elab_Command_getRef___redArg(v___y_1780_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1892_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1892_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1892_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___x_1881_; 
v___x_1788_ = 0;
v___x_1789_ = l_Lean_SourceInfo_fromRef(v_a_1784_, v___x_1788_);
lean_dec(v_a_1784_);
v___x_1881_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1780_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_quotContext_x3f_1882_; 
lean_dec_ref_known(v___x_1881_, 1);
v_quotContext_x3f_1882_ = lean_ctor_get(v___y_1780_, 5);
if (lean_obj_tag(v_quotContext_x3f_1882_) == 0)
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1781_);
lean_dec_ref(v___x_1883_);
goto v___jp_1875_;
}
else
{
goto v___jp_1875_;
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v___x_1789_);
lean_del_object(v___x_1786_);
lean_dec(v_kind_x3f_1778_);
lean_dec(v_doc_x3f_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1774_);
lean_dec_ref(v___x_1771_);
lean_dec(v_cat_x3f_1770_);
lean_dec_ref(v___f_1769_);
lean_dec(v_expty_x3f_1768_);
lean_dec(v_attrKind_1767_);
lean_dec(v___x_1766_);
lean_dec(v___x_1765_);
v_a_1884_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1881_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1881_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
v___jp_1790_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
lean_inc_ref_n(v___y_1793_, 2);
v___x_1799_ = l_Array_append___redArg(v___y_1793_, v___y_1798_);
lean_dec_ref(v___y_1798_);
lean_inc_n(v___y_1797_, 2);
lean_inc_n(v___x_1789_, 3);
v___x_1800_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1789_);
lean_ctor_set(v___x_1800_, 1, v___y_1797_);
lean_ctor_set(v___x_1800_, 2, v___x_1799_);
v___x_1801_ = l_Array_append___redArg(v___y_1793_, v_alts_1779_);
v___x_1802_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1789_);
lean_ctor_set(v___x_1802_, 1, v___y_1797_);
lean_ctor_set(v___x_1802_, 2, v___x_1801_);
v___x_1803_ = l_Lean_Syntax_node1(v___x_1789_, v___x_1765_, v___x_1802_);
v___x_1804_ = l_Lean_Syntax_node8(v___x_1789_, v___x_1766_, v___y_1796_, v___y_1794_, v_attrKind_1767_, v___y_1791_, v___y_1792_, v___y_1795_, v___x_1800_, v___x_1803_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1804_);
v___x_1806_ = v___x_1786_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
v___jp_1808_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_inc_ref(v___y_1811_);
v___x_1816_ = l_Array_append___redArg(v___y_1811_, v___y_1815_);
lean_dec_ref(v___y_1815_);
lean_inc(v___y_1814_);
lean_inc(v___x_1789_);
v___x_1817_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1789_);
lean_ctor_set(v___x_1817_, 1, v___y_1814_);
lean_ctor_set(v___x_1817_, 2, v___x_1816_);
if (lean_obj_tag(v_expty_x3f_1768_) == 1)
{
lean_object* v_val_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_dec_ref(v___f_1769_);
v_val_1818_ = lean_ctor_get(v_expty_x3f_1768_, 0);
lean_inc(v_val_1818_);
lean_dec_ref_known(v_expty_x3f_1768_, 1);
v___x_1819_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___x_1789_);
v___x_1820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1789_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = l_Array_mkArray2___redArg(v___x_1820_, v_val_1818_);
v___y_1791_ = v___y_1809_;
v___y_1792_ = v___y_1810_;
v___y_1793_ = v___y_1811_;
v___y_1794_ = v___y_1812_;
v___y_1795_ = v___x_1817_;
v___y_1796_ = v___y_1813_;
v___y_1797_ = v___y_1814_;
v___y_1798_ = v___x_1821_;
goto v___jp_1790_;
}
else
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_apply_1(v___f_1769_, v_expty_x3f_1768_);
v___y_1791_ = v___y_1809_;
v___y_1792_ = v___y_1810_;
v___y_1793_ = v___y_1811_;
v___y_1794_ = v___y_1812_;
v___y_1795_ = v___x_1817_;
v___y_1796_ = v___y_1813_;
v___y_1797_ = v___y_1814_;
v___y_1798_ = v___x_1822_;
goto v___jp_1790_;
}
}
v___jp_1823_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_inc_ref(v___y_1825_);
v___x_1830_ = l_Array_append___redArg(v___y_1825_, v___y_1829_);
lean_dec_ref(v___y_1829_);
lean_inc(v___y_1828_);
lean_inc(v___x_1789_);
v___x_1831_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1789_);
lean_ctor_set(v___x_1831_, 1, v___y_1828_);
lean_ctor_set(v___x_1831_, 2, v___x_1830_);
if (lean_obj_tag(v_cat_x3f_1770_) == 1)
{
lean_object* v_val_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_val_1832_ = lean_ctor_get(v_cat_x3f_1770_, 0);
lean_inc(v_val_1832_);
lean_dec_ref_known(v_cat_x3f_1770_, 1);
v___x_1833_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___x_1789_);
v___x_1834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1789_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = l_Array_mkArray2___redArg(v___x_1834_, v_val_1832_);
v___y_1809_ = v___y_1824_;
v___y_1810_ = v___x_1831_;
v___y_1811_ = v___y_1825_;
v___y_1812_ = v___y_1826_;
v___y_1813_ = v___y_1827_;
v___y_1814_ = v___y_1828_;
v___y_1815_ = v___x_1835_;
goto v___jp_1808_;
}
else
{
lean_object* v___x_1836_; 
lean_inc_ref(v___f_1769_);
v___x_1836_ = lean_apply_1(v___f_1769_, v_cat_x3f_1770_);
v___y_1809_ = v___y_1824_;
v___y_1810_ = v___x_1831_;
v___y_1811_ = v___y_1825_;
v___y_1812_ = v___y_1826_;
v___y_1813_ = v___y_1827_;
v___y_1814_ = v___y_1828_;
v___y_1815_ = v___x_1836_;
goto v___jp_1808_;
}
}
v___jp_1837_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_inc_ref(v___y_1838_);
v___x_1842_ = l_Array_append___redArg(v___y_1838_, v___y_1841_);
lean_dec_ref(v___y_1841_);
lean_inc(v___y_1840_);
lean_inc_n(v___x_1789_, 2);
v___x_1843_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1789_);
lean_ctor_set(v___x_1843_, 1, v___y_1840_);
lean_ctor_set(v___x_1843_, 2, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1789_);
lean_ctor_set(v___x_1844_, 1, v___x_1771_);
if (lean_obj_tag(v_kind_x3f_1778_) == 0)
{
lean_object* v___x_1845_; 
v___x_1845_ = lean_mk_empty_array_with_capacity(v___x_1772_);
v___y_1824_ = v___x_1844_;
v___y_1825_ = v___y_1838_;
v___y_1826_ = v___x_1843_;
v___y_1827_ = v___y_1839_;
v___y_1828_ = v___y_1840_;
v___y_1829_ = v___x_1845_;
goto v___jp_1823_;
}
else
{
lean_object* v_val_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_val_1846_ = lean_ctor_get(v_kind_x3f_1778_, 0);
lean_inc(v_val_1846_);
lean_dec_ref_known(v_kind_x3f_1778_, 1);
v___x_1847_ = l_Lean_mkIdent(v_val_1846_);
v___x_1848_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___x_1789_, 4);
v___x_1849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1789_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__2));
v___x_1851_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1789_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1789_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_1855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1789_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = l_Array_mkArray5___redArg(v___x_1849_, v___x_1851_, v___x_1853_, v___x_1847_, v___x_1855_);
v___y_1824_ = v___x_1844_;
v___y_1825_ = v___y_1838_;
v___y_1826_ = v___x_1843_;
v___y_1827_ = v___y_1839_;
v___y_1828_ = v___y_1840_;
v___y_1829_ = v___x_1856_;
goto v___jp_1823_;
}
}
v___jp_1857_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
lean_inc_ref(v___y_1858_);
v___x_1861_ = l_Array_append___redArg(v___y_1858_, v___y_1860_);
lean_dec_ref(v___y_1860_);
lean_inc(v___y_1859_);
lean_inc(v___x_1789_);
v___x_1862_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1789_);
lean_ctor_set(v___x_1862_, 1, v___y_1859_);
lean_ctor_set(v___x_1862_, 2, v___x_1861_);
if (lean_obj_tag(v_attrs_x3f_1773_) == 1)
{
lean_object* v_val_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_val_1863_ = lean_ctor_get(v_attrs_x3f_1773_, 0);
v___x_1864_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
v___x_1865_ = l_Lean_Name_mkStr4(v___x_1774_, v___x_1775_, v___x_1776_, v___x_1864_);
v___x_1866_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___x_1789_, 4);
v___x_1867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1789_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
lean_inc_ref(v___y_1858_);
v___x_1868_ = l_Array_append___redArg(v___y_1858_, v_val_1863_);
lean_inc(v___y_1859_);
v___x_1869_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1789_);
lean_ctor_set(v___x_1869_, 1, v___y_1859_);
lean_ctor_set(v___x_1869_, 2, v___x_1868_);
v___x_1870_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1789_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = l_Lean_Syntax_node3(v___x_1789_, v___x_1865_, v___x_1867_, v___x_1869_, v___x_1871_);
v___x_1873_ = l_Array_mkArray1___redArg(v___x_1872_);
v___y_1838_ = v___y_1858_;
v___y_1839_ = v___x_1862_;
v___y_1840_ = v___y_1859_;
v___y_1841_ = v___x_1873_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1874_; 
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1774_);
v___x_1874_ = lean_mk_empty_array_with_capacity(v___x_1772_);
v___y_1838_ = v___y_1858_;
v___y_1839_ = v___x_1862_;
v___y_1840_ = v___y_1859_;
v___y_1841_ = v___x_1874_;
goto v___jp_1837_;
}
}
v___jp_1875_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1877_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_1777_) == 1)
{
lean_object* v_val_1878_; lean_object* v___x_1879_; 
v_val_1878_ = lean_ctor_get(v_doc_x3f_1777_, 0);
lean_inc(v_val_1878_);
lean_dec_ref_known(v_doc_x3f_1777_, 1);
v___x_1879_ = l_Array_mkArray1___redArg(v_val_1878_);
v___y_1858_ = v___x_1877_;
v___y_1859_ = v___x_1876_;
v___y_1860_ = v___x_1879_;
goto v___jp_1857_;
}
else
{
lean_object* v___x_1880_; 
lean_dec(v_doc_x3f_1777_);
v___x_1880_ = lean_mk_empty_array_with_capacity(v___x_1772_);
v___y_1858_ = v___x_1877_;
v___y_1859_ = v___x_1876_;
v___y_1860_ = v___x_1880_;
goto v___jp_1857_;
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec(v_kind_x3f_1778_);
lean_dec(v_doc_x3f_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1774_);
lean_dec_ref(v___x_1771_);
lean_dec(v_cat_x3f_1770_);
lean_dec_ref(v___f_1769_);
lean_dec(v_expty_x3f_1768_);
lean_dec(v_attrKind_1767_);
lean_dec(v___x_1766_);
lean_dec(v___x_1765_);
v_a_1893_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1783_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1783_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object** _args){
lean_object* v___x_1901_ = _args[0];
lean_object* v___x_1902_ = _args[1];
lean_object* v_attrKind_1903_ = _args[2];
lean_object* v_expty_x3f_1904_ = _args[3];
lean_object* v___f_1905_ = _args[4];
lean_object* v_cat_x3f_1906_ = _args[5];
lean_object* v___x_1907_ = _args[6];
lean_object* v___x_1908_ = _args[7];
lean_object* v_attrs_x3f_1909_ = _args[8];
lean_object* v___x_1910_ = _args[9];
lean_object* v___x_1911_ = _args[10];
lean_object* v___x_1912_ = _args[11];
lean_object* v_doc_x3f_1913_ = _args[12];
lean_object* v_kind_x3f_1914_ = _args[13];
lean_object* v_alts_1915_ = _args[14];
lean_object* v___y_1916_ = _args[15];
lean_object* v___y_1917_ = _args[16];
lean_object* v___y_1918_ = _args[17];
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_Elab_Command_elabElabRules___lam__1(v___x_1901_, v___x_1902_, v_attrKind_1903_, v_expty_x3f_1904_, v___f_1905_, v_cat_x3f_1906_, v___x_1907_, v___x_1908_, v_attrs_x3f_1909_, v___x_1910_, v___x_1911_, v___x_1912_, v_doc_x3f_1913_, v_kind_x3f_1914_, v_alts_1915_, v___y_1916_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec_ref(v_alts_1915_);
lean_dec(v_attrs_x3f_1909_);
lean_dec(v___x_1908_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object* v___f_1948_, lean_object* v_stx_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1953_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1954_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1955_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_1956_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
lean_inc(v_stx_1949_);
v___x_1957_ = l_Lean_Syntax_isOfKind(v_stx_1949_, v___x_1956_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; 
lean_dec(v_stx_1949_);
lean_dec_ref(v___f_1948_);
v___x_1958_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_1958_;
}
else
{
lean_object* v___x_1959_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v_expty_x3f_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v_cat_x3f_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v_expty_x3f_2016_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v_cat_x3f_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v_attrs_x3f_2065_; lean_object* v_doc_x3f_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_2112_ = l_Lean_Syntax_getArg(v_stx_1949_, v___x_1959_);
v___x_2113_ = l_Lean_Syntax_isNone(v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2112_);
v___x_2115_ = l_Lean_Syntax_matchesNull(v___x_2112_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; 
lean_dec(v___x_2112_);
lean_dec(v_stx_1949_);
lean_dec_ref(v___f_1948_);
v___x_2116_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2116_;
}
else
{
lean_object* v_doc_x3f_2117_; 
v_doc_x3f_2117_ = l_Lean_Syntax_getArg(v___x_2112_, v___x_1959_);
lean_dec(v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2120_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(v_doc_x3f_2117_);
v___x_2121_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2117_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; 
lean_dec(v_doc_x3f_2117_);
lean_dec(v_stx_1949_);
lean_dec_ref(v___f_1948_);
v___x_2122_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2122_;
}
else
{
goto v___jp_2118_;
}
}
else
{
goto v___jp_2118_;
}
v___jp_2118_:
{
lean_object* v___x_2119_; 
v___x_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2119_, 0, v_doc_x3f_2117_);
v_doc_x3f_2096_ = v___x_2119_;
v___y_2097_ = v___y_1950_;
v___y_2098_ = v___y_1951_;
goto v___jp_2095_;
}
}
}
else
{
lean_object* v___x_2123_; 
lean_dec(v___x_2112_);
v___x_2123_ = lean_box(0);
v_doc_x3f_2096_ = v___x_2123_;
v___y_2097_ = v___y_1950_;
v___y_2098_ = v___y_1951_;
goto v___jp_2095_;
}
v___jp_1960_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1970_ = lean_unsigned_to_nat(7u);
v___x_1971_ = l_Lean_Syntax_getArg(v_stx_1949_, v___x_1970_);
lean_dec(v_stx_1949_);
v___x_1972_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc_ref(v___y_1961_);
v___x_1973_ = l_Lean_Name_mkStr4(v___x_1953_, v___x_1954_, v___y_1961_, v___x_1972_);
lean_inc(v___x_1971_);
v___x_1974_ = l_Lean_Syntax_isOfKind(v___x_1971_, v___x_1973_);
lean_dec(v___x_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; 
lean_dec(v___x_1971_);
lean_dec(v_expty_x3f_1967_);
lean_dec(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec(v___y_1962_);
v___x_1975_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_1975_;
}
else
{
lean_object* v___x_1976_; lean_object* v_alts_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1976_ = l_Lean_Syntax_getArg(v___x_1971_, v___x_1959_);
lean_dec(v___x_1971_);
v_alts_1977_ = l_Lean_Syntax_getArgs(v___x_1976_);
lean_dec(v___x_1976_);
v___x_1978_ = l_Lean_TSyntax_getId(v___y_1965_);
lean_dec(v___y_1965_);
v___x_1979_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_1978_, v___y_1968_, v___y_1969_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1981_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v___x_1981_ = l_Lean_Elab_Command_elabElabRulesAux(v___y_1964_, v___y_1966_, v___y_1962_, v_a_1980_, v___y_1963_, v_expty_x3f_1967_, v_alts_1977_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1963_);
lean_dec(v___y_1966_);
return v___x_1981_;
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec_ref(v_alts_1977_);
lean_dec(v_expty_x3f_1967_);
lean_dec(v___y_1966_);
lean_dec(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec(v___y_1962_);
v_a_1982_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1979_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1979_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
v___jp_1990_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2001_ = lean_unsigned_to_nat(6u);
v___x_2002_ = l_Lean_Syntax_getArg(v_stx_1949_, v___x_2001_);
v___x_2003_ = l_Lean_Syntax_isNone(v___x_2002_);
if (v___x_2003_ == 0)
{
uint8_t v___x_2004_; 
lean_inc(v___x_2002_);
v___x_2004_ = l_Lean_Syntax_matchesNull(v___x_2002_, v___y_1993_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; 
lean_dec(v___x_2002_);
lean_dec(v_cat_x3f_1998_);
lean_dec(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec(v___y_1992_);
lean_dec(v_stx_1949_);
v___x_2005_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2005_;
}
else
{
lean_object* v_expty_x3f_2006_; lean_object* v___x_2007_; 
v_expty_x3f_2006_ = l_Lean_Syntax_getArg(v___x_2002_, v___y_1994_);
lean_dec(v___x_2002_);
v___x_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2007_, 0, v_expty_x3f_2006_);
v___y_1961_ = v___y_1991_;
v___y_1962_ = v___y_1992_;
v___y_1963_ = v_cat_x3f_1998_;
v___y_1964_ = v___y_1995_;
v___y_1965_ = v___y_1996_;
v___y_1966_ = v___y_1997_;
v_expty_x3f_1967_ = v___x_2007_;
v___y_1968_ = v___y_1999_;
v___y_1969_ = v___y_2000_;
goto v___jp_1960_;
}
}
else
{
lean_object* v___x_2008_; 
lean_dec(v___x_2002_);
v___x_2008_ = lean_box(0);
v___y_1961_ = v___y_1991_;
v___y_1962_ = v___y_1992_;
v___y_1963_ = v_cat_x3f_1998_;
v___y_1964_ = v___y_1995_;
v___y_1965_ = v___y_1996_;
v___y_1966_ = v___y_1997_;
v_expty_x3f_1967_ = v___x_2008_;
v___y_1968_ = v___y_1999_;
v___y_1969_ = v___y_2000_;
goto v___jp_1960_;
}
}
v___jp_2009_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2017_ = lean_unsigned_to_nat(7u);
v___x_2018_ = l_Lean_Syntax_getArg(v_stx_1949_, v___x_2017_);
lean_dec(v_stx_1949_);
v___x_2019_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_2020_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__2));
lean_inc(v___x_2018_);
v___x_2021_ = l_Lean_Syntax_isOfKind(v___x_2018_, v___x_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; 
lean_dec(v___x_2018_);
lean_dec(v_expty_x3f_2016_);
lean_dec(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec(v___y_2010_);
lean_dec_ref(v___f_1948_);
v___x_2022_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2022_;
}
else
{
lean_object* v___f_2023_; lean_object* v___x_2024_; lean_object* v_alts_2025_; lean_object* v___x_2026_; 
v___f_2023_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lam__1___boxed), 18, 13);
lean_closure_set(v___f_2023_, 0, v___x_2020_);
lean_closure_set(v___f_2023_, 1, v___x_1956_);
lean_closure_set(v___f_2023_, 2, v___y_2012_);
lean_closure_set(v___f_2023_, 3, v_expty_x3f_2016_);
lean_closure_set(v___f_2023_, 4, v___f_1948_);
lean_closure_set(v___f_2023_, 5, v___y_2014_);
lean_closure_set(v___f_2023_, 6, v___x_1955_);
lean_closure_set(v___f_2023_, 7, v___x_1959_);
lean_closure_set(v___f_2023_, 8, v___y_2013_);
lean_closure_set(v___f_2023_, 9, v___x_1953_);
lean_closure_set(v___f_2023_, 10, v___x_1954_);
lean_closure_set(v___f_2023_, 11, v___x_2019_);
lean_closure_set(v___f_2023_, 12, v___y_2010_);
v___x_2024_ = l_Lean_Syntax_getArg(v___x_2018_, v___x_1959_);
lean_dec(v___x_2018_);
v_alts_2025_ = l_Lean_Syntax_getArgs(v___x_2024_);
lean_dec(v___x_2024_);
v___x_2026_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_2025_, v___x_1955_, v___f_2023_, v___y_2015_, v___y_2011_);
lean_dec_ref(v_alts_2025_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2026_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
v_a_2035_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2026_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2026_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
v___jp_2043_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2052_ = lean_unsigned_to_nat(6u);
v___x_2053_ = l_Lean_Syntax_getArg(v_stx_1949_, v___x_2052_);
v___x_2054_ = l_Lean_Syntax_isNone(v___x_2053_);
if (v___x_2054_ == 0)
{
uint8_t v___x_2055_; 
lean_inc(v___x_2053_);
v___x_2055_ = l_Lean_Syntax_matchesNull(v___x_2053_, v___y_2047_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
lean_dec(v___x_2053_);
lean_dec(v_cat_x3f_2049_);
lean_dec(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec(v_stx_1949_);
lean_dec_ref(v___f_1948_);
v___x_2056_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2056_;
}
else
{
lean_object* v_expty_x3f_2057_; lean_object* v___x_2058_; 
v_expty_x3f_2057_ = l_Lean_Syntax_getArg(v___x_2053_, v___y_2048_);
lean_dec(v___x_2053_);
v___x_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2058_, 0, v_expty_x3f_2057_);
v___y_2010_ = v___y_2044_;
v___y_2011_ = v___y_2051_;
v___y_2012_ = v___y_2045_;
v___y_2013_ = v___y_2046_;
v___y_2014_ = v_cat_x3f_2049_;
v___y_2015_ = v___y_2050_;
v_expty_x3f_2016_ = v___x_2058_;
goto v___jp_2009_;
}
}
else
{
lean_object* v___x_2059_; 
lean_dec(v___x_2053_);
v___x_2059_ = lean_box(0);
v___y_2010_ = v___y_2044_;
v___y_2011_ = v___y_2051_;
v___y_2012_ = v___y_2045_;
v___y_2013_ = v___y_2046_;
v___y_2014_ = v_cat_x3f_2049_;
v___y_2015_ = v___y_2050_;
v_expty_x3f_2016_ = v___x_2059_;
goto v___jp_2009_;
}
}
v___jp_2060_:
{
lean_object* v___x_2066_; lean_object* v_attrKind_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2066_ = lean_unsigned_to_nat(2u);
v_attrKind_2067_ = l_Lean_Syntax_getArg(v_stx_1949_, v___x_2066_);
v___x_2068_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_2069_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v_attrKind_2067_);
v___x_2070_ = l_Lean_Syntax_isOfKind(v_attrKind_2067_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; 
lean_dec(v_attrKind_2067_);
lean_dec(v_attrs_x3f_2065_);
lean_dec(v___y_2061_);
lean_dec(v_stx_1949_);
lean_dec_ref(v___f_1948_);
v___x_2071_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2071_;
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2072_ = lean_unsigned_to_nat(4u);
v___x_2073_ = l_Lean_Syntax_getArg(v_stx_1949_, v___x_2072_);
lean_inc(v___x_2073_);
v___x_2074_ = l_Lean_Syntax_matchesNull(v___x_2073_, v___x_1959_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
lean_dec_ref(v___f_1948_);
v___x_2075_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2073_);
v___x_2076_ = l_Lean_Syntax_matchesNull(v___x_2073_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
lean_dec(v___x_2073_);
lean_dec(v_attrKind_2067_);
lean_dec(v_attrs_x3f_2065_);
lean_dec(v___y_2061_);
lean_dec(v_stx_1949_);
v___x_2077_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2077_;
}
else
{
lean_object* v___x_2078_; lean_object* v_kind_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2078_ = lean_unsigned_to_nat(3u);
v_kind_2079_ = l_Lean_Syntax_getArg(v___x_2073_, v___x_2078_);
lean_dec(v___x_2073_);
v___x_2080_ = l_Lean_Syntax_getArg(v_stx_1949_, v___x_2075_);
v___x_2081_ = l_Lean_Syntax_isNone(v___x_2080_);
if (v___x_2081_ == 0)
{
uint8_t v___x_2082_; 
lean_inc(v___x_2080_);
v___x_2082_ = l_Lean_Syntax_matchesNull(v___x_2080_, v___x_2066_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; 
lean_dec(v___x_2080_);
lean_dec(v_kind_2079_);
lean_dec(v_attrKind_2067_);
lean_dec(v_attrs_x3f_2065_);
lean_dec(v___y_2061_);
lean_dec(v_stx_1949_);
v___x_2083_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2083_;
}
else
{
lean_object* v_cat_x3f_2084_; lean_object* v___x_2085_; 
v_cat_x3f_2084_ = l_Lean_Syntax_getArg(v___x_2080_, v___y_2064_);
lean_dec(v___x_2080_);
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_cat_x3f_2084_);
v___y_1991_ = v___x_2068_;
v___y_1992_ = v_attrKind_2067_;
v___y_1993_ = v___x_2066_;
v___y_1994_ = v___y_2064_;
v___y_1995_ = v___y_2061_;
v___y_1996_ = v_kind_2079_;
v___y_1997_ = v_attrs_x3f_2065_;
v_cat_x3f_1998_ = v___x_2085_;
v___y_1999_ = v___y_2062_;
v___y_2000_ = v___y_2063_;
goto v___jp_1990_;
}
}
else
{
lean_object* v___x_2086_; 
lean_dec(v___x_2080_);
v___x_2086_ = lean_box(0);
v___y_1991_ = v___x_2068_;
v___y_1992_ = v_attrKind_2067_;
v___y_1993_ = v___x_2066_;
v___y_1994_ = v___y_2064_;
v___y_1995_ = v___y_2061_;
v___y_1996_ = v_kind_2079_;
v___y_1997_ = v_attrs_x3f_2065_;
v_cat_x3f_1998_ = v___x_2086_;
v___y_1999_ = v___y_2062_;
v___y_2000_ = v___y_2063_;
goto v___jp_1990_;
}
}
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
lean_dec(v___x_2073_);
v___x_2087_ = lean_unsigned_to_nat(5u);
v___x_2088_ = l_Lean_Syntax_getArg(v_stx_1949_, v___x_2087_);
v___x_2089_ = l_Lean_Syntax_isNone(v___x_2088_);
if (v___x_2089_ == 0)
{
uint8_t v___x_2090_; 
lean_inc(v___x_2088_);
v___x_2090_ = l_Lean_Syntax_matchesNull(v___x_2088_, v___x_2066_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_dec(v___x_2088_);
lean_dec(v_attrKind_2067_);
lean_dec(v_attrs_x3f_2065_);
lean_dec(v___y_2061_);
lean_dec(v_stx_1949_);
lean_dec_ref(v___f_1948_);
v___x_2091_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2091_;
}
else
{
lean_object* v_cat_x3f_2092_; lean_object* v___x_2093_; 
v_cat_x3f_2092_ = l_Lean_Syntax_getArg(v___x_2088_, v___y_2064_);
lean_dec(v___x_2088_);
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_cat_x3f_2092_);
v___y_2044_ = v___y_2061_;
v___y_2045_ = v_attrKind_2067_;
v___y_2046_ = v_attrs_x3f_2065_;
v___y_2047_ = v___x_2066_;
v___y_2048_ = v___y_2064_;
v_cat_x3f_2049_ = v___x_2093_;
v___y_2050_ = v___y_2062_;
v___y_2051_ = v___y_2063_;
goto v___jp_2043_;
}
}
else
{
lean_object* v___x_2094_; 
lean_dec(v___x_2088_);
v___x_2094_ = lean_box(0);
v___y_2044_ = v___y_2061_;
v___y_2045_ = v_attrKind_2067_;
v___y_2046_ = v_attrs_x3f_2065_;
v___y_2047_ = v___x_2066_;
v___y_2048_ = v___y_2064_;
v_cat_x3f_2049_ = v___x_2094_;
v___y_2050_ = v___y_2062_;
v___y_2051_ = v___y_2063_;
goto v___jp_2043_;
}
}
}
}
v___jp_2095_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2099_ = lean_unsigned_to_nat(1u);
v___x_2100_ = l_Lean_Syntax_getArg(v_stx_1949_, v___x_2099_);
v___x_2101_ = l_Lean_Syntax_isNone(v___x_2100_);
if (v___x_2101_ == 0)
{
uint8_t v___x_2102_; 
lean_inc(v___x_2100_);
v___x_2102_ = l_Lean_Syntax_matchesNull(v___x_2100_, v___x_2099_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; 
lean_dec(v___x_2100_);
lean_dec(v_doc_x3f_2096_);
lean_dec(v_stx_1949_);
lean_dec_ref(v___f_1948_);
v___x_2103_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2103_;
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2104_ = l_Lean_Syntax_getArg(v___x_2100_, v___x_1959_);
lean_dec(v___x_2100_);
v___x_2105_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(v___x_2104_);
v___x_2106_ = l_Lean_Syntax_isOfKind(v___x_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; 
lean_dec(v___x_2104_);
lean_dec(v_doc_x3f_2096_);
lean_dec(v_stx_1949_);
lean_dec_ref(v___f_1948_);
v___x_2107_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2107_;
}
else
{
lean_object* v___x_2108_; lean_object* v_attrs_x3f_2109_; lean_object* v___x_2110_; 
v___x_2108_ = l_Lean_Syntax_getArg(v___x_2104_, v___x_2099_);
lean_dec(v___x_2104_);
v_attrs_x3f_2109_ = l_Lean_Syntax_getArgs(v___x_2108_);
lean_dec(v___x_2108_);
v___x_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2110_, 0, v_attrs_x3f_2109_);
v___y_2061_ = v_doc_x3f_2096_;
v___y_2062_ = v___y_2097_;
v___y_2063_ = v___y_2098_;
v___y_2064_ = v___x_2099_;
v_attrs_x3f_2065_ = v___x_2110_;
goto v___jp_2060_;
}
}
}
else
{
lean_object* v___x_2111_; 
lean_dec(v___x_2100_);
v___x_2111_ = lean_box(0);
v___y_2061_ = v_doc_x3f_2096_;
v___y_2062_ = v___y_2097_;
v___y_2063_ = v___y_2098_;
v___y_2064_ = v___x_2099_;
v_attrs_x3f_2065_ = v___x_2111_;
goto v___jp_2060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object* v___f_2124_, lean_object* v_stx_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_Elab_Command_elabElabRules___lam__2(v___f_2124_, v_stx_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v___f_2137_; lean_object* v___x_2138_; 
v___f_2137_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___closed__1));
v___x_2138_ = l_Lean_Elab_Command_adaptExpander(v___f_2137_, v_a_2133_, v_a_2134_, v_a_2135_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_Elab_Command_elabElabRules(v_a_2139_, v_a_2140_, v_a_2141_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1(){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2151_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2152_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
v___x_2153_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2154_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___boxed), 4, 0);
v___x_2155_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2151_, v___x_2152_, v___x_2153_, v___x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object* v_a_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3(){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2185_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6));
v___x_2186_ = l_Lean_addBuiltinDeclarationRanges(v___x_2184_, v___x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object* v_a_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t v_sz_2189_, size_t v_i_2190_, lean_object* v_bs_2191_){
_start:
{
uint8_t v___x_2192_; 
v___x_2192_ = lean_usize_dec_lt(v_i_2190_, v_sz_2189_);
if (v___x_2192_ == 0)
{
return v_bs_2191_;
}
else
{
lean_object* v_v_2193_; lean_object* v___x_2194_; lean_object* v_bs_x27_2195_; size_t v___x_2196_; size_t v___x_2197_; lean_object* v___x_2198_; 
v_v_2193_ = lean_array_uget(v_bs_2191_, v_i_2190_);
v___x_2194_ = lean_unsigned_to_nat(0u);
v_bs_x27_2195_ = lean_array_uset(v_bs_2191_, v_i_2190_, v___x_2194_);
v___x_2196_ = ((size_t)1ULL);
v___x_2197_ = lean_usize_add(v_i_2190_, v___x_2196_);
v___x_2198_ = lean_array_uset(v_bs_x27_2195_, v_i_2190_, v_v_2193_);
v_i_2190_ = v___x_2197_;
v_bs_2191_ = v___x_2198_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object* v_sz_2200_, lean_object* v_i_2201_, lean_object* v_bs_2202_){
_start:
{
size_t v_sz_boxed_2203_; size_t v_i_boxed_2204_; lean_object* v_res_2205_; 
v_sz_boxed_2203_ = lean_unbox_usize(v_sz_2200_);
lean_dec(v_sz_2200_);
v_i_boxed_2204_ = lean_unbox_usize(v_i_2201_);
lean_dec(v_i_2201_);
v_res_2205_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_boxed_2203_, v_i_boxed_2204_, v_bs_2202_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t v_sz_2206_, size_t v_i_2207_, lean_object* v_bs_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
uint8_t v___x_2212_; 
v___x_2212_ = lean_usize_dec_lt(v_i_2207_, v_sz_2206_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; 
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v_bs_2208_);
return v___x_2213_;
}
else
{
lean_object* v_v_2214_; lean_object* v___x_2215_; lean_object* v_bs_x27_2216_; lean_object* v___x_2217_; 
v_v_2214_ = lean_array_uget(v_bs_2208_, v_i_2207_);
v___x_2215_ = lean_unsigned_to_nat(0u);
v_bs_x27_2216_ = lean_array_uset(v_bs_2208_, v_i_2207_, v___x_2215_);
v___x_2217_ = l_Lean_Elab_Command_expandMacroArg(v_v_2214_, v___y_2209_, v___y_2210_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; size_t v___x_2219_; size_t v___x_2220_; lean_object* v___x_2221_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2219_ = ((size_t)1ULL);
v___x_2220_ = lean_usize_add(v_i_2207_, v___x_2219_);
v___x_2221_ = lean_array_uset(v_bs_x27_2216_, v_i_2207_, v_a_2218_);
v_i_2207_ = v___x_2220_;
v_bs_2208_ = v___x_2221_;
goto _start;
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v_bs_x27_2216_);
v_a_2223_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2217_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2217_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object* v_sz_2231_, lean_object* v_i_2232_, lean_object* v_bs_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
size_t v_sz_boxed_2237_; size_t v_i_boxed_2238_; lean_object* v_res_2239_; 
v_sz_boxed_2237_ = lean_unbox_usize(v_sz_2231_);
lean_dec(v_sz_2231_);
v_i_boxed_2238_ = lean_unbox_usize(v_i_2232_);
lean_dec(v_i_2232_);
v_res_2239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_boxed_2237_, v_i_boxed_2238_, v_bs_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
return v_res_2239_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(lean_object* v_keys_2240_, lean_object* v_i_2241_, lean_object* v_k_2242_){
_start:
{
lean_object* v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = lean_array_get_size(v_keys_2240_);
v___x_2244_ = lean_nat_dec_lt(v_i_2241_, v___x_2243_);
if (v___x_2244_ == 0)
{
lean_dec(v_i_2241_);
return v___x_2244_;
}
else
{
lean_object* v_k_x27_2245_; uint8_t v___x_2246_; 
v_k_x27_2245_ = lean_array_fget_borrowed(v_keys_2240_, v_i_2241_);
v___x_2246_ = l_Lean_instBEqExtraModUse_beq(v_k_2242_, v_k_x27_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = lean_unsigned_to_nat(1u);
v___x_2248_ = lean_nat_add(v_i_2241_, v___x_2247_);
lean_dec(v_i_2241_);
v_i_2241_ = v___x_2248_;
goto _start;
}
else
{
lean_dec(v_i_2241_);
return v___x_2244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_keys_2250_, lean_object* v_i_2251_, lean_object* v_k_2252_){
_start:
{
uint8_t v_res_2253_; lean_object* v_r_2254_; 
v_res_2253_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_2250_, v_i_2251_, v_k_2252_);
lean_dec_ref(v_k_2252_);
lean_dec_ref(v_keys_2250_);
v_r_2254_ = lean_box(v_res_2253_);
return v_r_2254_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(lean_object* v_x_2255_, size_t v_x_2256_, lean_object* v_x_2257_){
_start:
{
if (lean_obj_tag(v_x_2255_) == 0)
{
lean_object* v_es_2258_; lean_object* v___x_2259_; size_t v___x_2260_; size_t v___x_2261_; lean_object* v_j_2262_; lean_object* v___x_2263_; 
v_es_2258_ = lean_ctor_get(v_x_2255_, 0);
v___x_2259_ = lean_box(2);
v___x_2260_ = ((size_t)31ULL);
v___x_2261_ = lean_usize_land(v_x_2256_, v___x_2260_);
v_j_2262_ = lean_usize_to_nat(v___x_2261_);
v___x_2263_ = lean_array_get_borrowed(v___x_2259_, v_es_2258_, v_j_2262_);
lean_dec(v_j_2262_);
switch(lean_obj_tag(v___x_2263_))
{
case 0:
{
lean_object* v_key_2264_; uint8_t v___x_2265_; 
v_key_2264_ = lean_ctor_get(v___x_2263_, 0);
v___x_2265_ = l_Lean_instBEqExtraModUse_beq(v_x_2257_, v_key_2264_);
return v___x_2265_;
}
case 1:
{
lean_object* v_node_2266_; size_t v___x_2267_; size_t v___x_2268_; 
v_node_2266_ = lean_ctor_get(v___x_2263_, 0);
v___x_2267_ = ((size_t)5ULL);
v___x_2268_ = lean_usize_shift_right(v_x_2256_, v___x_2267_);
v_x_2255_ = v_node_2266_;
v_x_2256_ = v___x_2268_;
goto _start;
}
default: 
{
uint8_t v___x_2270_; 
v___x_2270_ = 0;
return v___x_2270_;
}
}
}
else
{
lean_object* v_ks_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v_ks_2271_ = lean_ctor_get(v_x_2255_, 0);
v___x_2272_ = lean_unsigned_to_nat(0u);
v___x_2273_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_ks_2271_, v___x_2272_, v_x_2257_);
return v___x_2273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_x_2274_, lean_object* v_x_2275_, lean_object* v_x_2276_){
_start:
{
size_t v_x_16583__boxed_2277_; uint8_t v_res_2278_; lean_object* v_r_2279_; 
v_x_16583__boxed_2277_ = lean_unbox_usize(v_x_2275_);
lean_dec(v_x_2275_);
v_res_2278_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2274_, v_x_16583__boxed_2277_, v_x_2276_);
lean_dec_ref(v_x_2276_);
lean_dec_ref(v_x_2274_);
v_r_2279_ = lean_box(v_res_2278_);
return v_r_2279_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(lean_object* v_x_2280_, lean_object* v_x_2281_){
_start:
{
uint64_t v___x_2282_; size_t v___x_2283_; uint8_t v___x_2284_; 
v___x_2282_ = l_Lean_instHashableExtraModUse_hash(v_x_2281_);
v___x_2283_ = lean_uint64_to_usize(v___x_2282_);
v___x_2284_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2280_, v___x_2283_, v_x_2281_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_x_2285_, lean_object* v_x_2286_){
_start:
{
uint8_t v_res_2287_; lean_object* v_r_2288_; 
v_res_2287_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_2285_, v_x_2286_);
lean_dec_ref(v_x_2286_);
lean_dec_ref(v_x_2285_);
v_r_2288_ = lean_box(v_res_2287_);
return v_r_2288_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2289_; double v___x_2290_; 
v___x_2289_ = lean_unsigned_to_nat(0u);
v___x_2290_ = lean_float_of_nat(v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object* v_cls_2294_, lean_object* v_msg_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_Elab_Command_getRef___redArg(v___y_2296_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2350_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_2295_, v___y_2297_);
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2350_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2350_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v_traceState_2307_; lean_object* v_env_2308_; lean_object* v_messages_2309_; lean_object* v_scopes_2310_; lean_object* v_usedQuotCtxts_2311_; lean_object* v_nextMacroScope_2312_; lean_object* v_maxRecDepth_2313_; lean_object* v_ngen_2314_; lean_object* v_auxDeclNGen_2315_; lean_object* v_infoState_2316_; lean_object* v_snapshotTasks_2317_; lean_object* v_prevLinterStates_2318_; lean_object* v_codeQualityEntryTasks_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2349_; 
v___x_2306_ = lean_st_ref_take(v___y_2297_);
v_traceState_2307_ = lean_ctor_get(v___x_2306_, 9);
v_env_2308_ = lean_ctor_get(v___x_2306_, 0);
v_messages_2309_ = lean_ctor_get(v___x_2306_, 1);
v_scopes_2310_ = lean_ctor_get(v___x_2306_, 2);
v_usedQuotCtxts_2311_ = lean_ctor_get(v___x_2306_, 3);
v_nextMacroScope_2312_ = lean_ctor_get(v___x_2306_, 4);
v_maxRecDepth_2313_ = lean_ctor_get(v___x_2306_, 5);
v_ngen_2314_ = lean_ctor_get(v___x_2306_, 6);
v_auxDeclNGen_2315_ = lean_ctor_get(v___x_2306_, 7);
v_infoState_2316_ = lean_ctor_get(v___x_2306_, 8);
v_snapshotTasks_2317_ = lean_ctor_get(v___x_2306_, 10);
v_prevLinterStates_2318_ = lean_ctor_get(v___x_2306_, 11);
v_codeQualityEntryTasks_2319_ = lean_ctor_get(v___x_2306_, 12);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2321_ = v___x_2306_;
v_isShared_2322_ = v_isSharedCheck_2349_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2319_);
lean_inc(v_prevLinterStates_2318_);
lean_inc(v_snapshotTasks_2317_);
lean_inc(v_traceState_2307_);
lean_inc(v_infoState_2316_);
lean_inc(v_auxDeclNGen_2315_);
lean_inc(v_ngen_2314_);
lean_inc(v_maxRecDepth_2313_);
lean_inc(v_nextMacroScope_2312_);
lean_inc(v_usedQuotCtxts_2311_);
lean_inc(v_scopes_2310_);
lean_inc(v_messages_2309_);
lean_inc(v_env_2308_);
lean_dec(v___x_2306_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2349_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
uint64_t v_tid_2323_; lean_object* v_traces_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2348_; 
v_tid_2323_ = lean_ctor_get_uint64(v_traceState_2307_, sizeof(void*)*1);
v_traces_2324_ = lean_ctor_get(v_traceState_2307_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_traceState_2307_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2326_ = v_traceState_2307_;
v_isShared_2327_ = v_isSharedCheck_2348_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_traces_2324_);
lean_dec(v_traceState_2307_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2348_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; double v___x_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2328_ = lean_box(0);
v___x_2329_ = lean_box(0);
v___x_2330_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0);
v___x_2331_ = 0;
v___x_2332_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2333_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2333_, 0, v_cls_2294_);
lean_ctor_set(v___x_2333_, 1, v___x_2329_);
lean_ctor_set(v___x_2333_, 2, v___x_2332_);
lean_ctor_set_float(v___x_2333_, sizeof(void*)*3, v___x_2330_);
lean_ctor_set_float(v___x_2333_, sizeof(void*)*3 + 8, v___x_2330_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*3 + 16, v___x_2331_);
v___x_2334_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2));
v___x_2335_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v_a_2302_);
lean_ctor_set(v___x_2335_, 2, v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v_a_2300_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = l_Lean_PersistentArray_push___redArg(v_traces_2324_, v___x_2336_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2337_);
v___x_2339_ = v___x_2326_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2337_);
lean_ctor_set_uint64(v_reuseFailAlloc_2347_, sizeof(void*)*1, v_tid_2323_);
v___x_2339_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2341_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 9, v___x_2339_);
v___x_2341_ = v___x_2321_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_env_2308_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_messages_2309_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_scopes_2310_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v_usedQuotCtxts_2311_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v_nextMacroScope_2312_);
lean_ctor_set(v_reuseFailAlloc_2346_, 5, v_maxRecDepth_2313_);
lean_ctor_set(v_reuseFailAlloc_2346_, 6, v_ngen_2314_);
lean_ctor_set(v_reuseFailAlloc_2346_, 7, v_auxDeclNGen_2315_);
lean_ctor_set(v_reuseFailAlloc_2346_, 8, v_infoState_2316_);
lean_ctor_set(v_reuseFailAlloc_2346_, 9, v___x_2339_);
lean_ctor_set(v_reuseFailAlloc_2346_, 10, v_snapshotTasks_2317_);
lean_ctor_set(v_reuseFailAlloc_2346_, 11, v_prevLinterStates_2318_);
lean_ctor_set(v_reuseFailAlloc_2346_, 12, v_codeQualityEntryTasks_2319_);
v___x_2341_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2342_ = lean_st_ref_put(v___y_2297_, v___x_2341_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2328_);
v___x_2344_ = v___x_2304_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2328_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec_ref(v_msg_2295_);
lean_dec(v_cls_2294_);
v_a_2351_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2299_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2299_);
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
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object* v_cls_2359_, lean_object* v_msg_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2359_, v_msg_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___lam__0(lean_object* v___x_2365_, lean_object* v_entry_2366_, lean_object* v_s_2367_){
_start:
{
lean_object* v_addEntryFn_2368_; lean_object* v_importedEntries_2369_; lean_object* v_state_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2378_; 
v_addEntryFn_2368_ = lean_ctor_get(v___x_2365_, 3);
lean_inc(v_addEntryFn_2368_);
lean_dec_ref(v___x_2365_);
v_importedEntries_2369_ = lean_ctor_get(v_s_2367_, 0);
v_state_2370_ = lean_ctor_get(v_s_2367_, 1);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_s_2367_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2372_ = v_s_2367_;
v_isShared_2373_ = v_isSharedCheck_2378_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_state_2370_);
lean_inc(v_importedEntries_2369_);
lean_dec(v_s_2367_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2378_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v_state_2374_; lean_object* v___x_2376_; 
v_state_2374_ = lean_apply_2(v_addEntryFn_2368_, v_state_2370_, v_entry_2366_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 1, v_state_2374_);
v___x_2376_ = v___x_2372_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_importedEntries_2369_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_state_2374_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2379_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3));
v___x_2385_ = l_Lean_stringToMessageData(v___x_2384_);
return v___x_2385_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5));
v___x_2388_ = l_Lean_stringToMessageData(v___x_2387_);
return v___x_2388_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2390_ = l_Lean_stringToMessageData(v___x_2389_);
return v___x_2390_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_cls_2394_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2));
v___x_2395_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9));
v___x_2396_ = l_Lean_Name_append(v___x_2395_, v_cls_2394_);
return v___x_2396_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11));
v___x_2399_ = l_Lean_stringToMessageData(v___x_2398_);
return v___x_2399_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13));
v___x_2402_ = l_Lean_stringToMessageData(v___x_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(lean_object* v_mod_2407_, uint8_t v_isMeta_2408_, lean_object* v_hint_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v_env_2434_; uint8_t v_isExporting_2435_; lean_object* v_entry_2436_; lean_object* v___x_2437_; lean_object* v_env_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; 
v___x_2432_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0);
v___x_2433_ = lean_st_ref_get(v___y_2411_);
v_env_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc_ref(v_env_2434_);
lean_dec(v___x_2433_);
v_isExporting_2435_ = lean_ctor_get_uint8(v_env_2434_, sizeof(void*)*13);
lean_dec_ref(v_env_2434_);
lean_inc(v_mod_2407_);
v_entry_2436_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2436_, 0, v_mod_2407_);
lean_ctor_set_uint8(v_entry_2436_, sizeof(void*)*1, v_isExporting_2435_);
lean_ctor_set_uint8(v_entry_2436_, sizeof(void*)*1 + 1, v_isMeta_2408_);
v___x_2437_ = lean_st_ref_get(v___y_2411_);
v_env_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc_ref(v_env_2438_);
lean_dec(v___x_2437_);
v___x_2439_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2440_ = lean_box(1);
v___x_2441_ = lean_box(0);
v___x_2442_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2432_, v___x_2439_, v_env_2438_, v___x_2440_, v___x_2441_);
v___x_2443_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v___x_2442_, v_entry_2436_);
lean_dec(v___x_2442_);
if (v___x_2443_ == 0)
{
lean_object* v___f_2444_; uint8_t v___x_2445_; lean_object* v___y_2447_; lean_object* v_cls_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v_scopes_2493_; lean_object* v___x_2494_; lean_object* v_opts_2495_; uint8_t v_hasTrace_2496_; 
v___f_2444_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_2444_, 0, v___x_2439_);
lean_closure_set(v___f_2444_, 1, v_entry_2436_);
v___x_2445_ = 1;
v_cls_2469_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2));
v___x_2470_ = l_Lean_inheritedTraceOptions;
v___x_2471_ = lean_st_ref_get(v___x_2470_);
v___x_2472_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2473_ = lean_st_ref_get(v___y_2411_);
v_scopes_2493_ = lean_ctor_get(v___x_2473_, 2);
lean_inc(v_scopes_2493_);
lean_dec(v___x_2473_);
v___x_2494_ = l_List_head_x21___redArg(v___x_2472_, v_scopes_2493_);
lean_dec(v_scopes_2493_);
v_opts_2495_ = lean_ctor_get(v___x_2494_, 1);
lean_inc_ref(v_opts_2495_);
lean_dec(v___x_2494_);
v_hasTrace_2496_ = lean_ctor_get_uint8(v_opts_2495_, sizeof(void*)*1);
if (v_hasTrace_2496_ == 0)
{
lean_dec_ref(v_opts_2495_);
lean_dec(v___x_2471_);
lean_dec(v_hint_2409_);
lean_dec(v_mod_2407_);
v___y_2447_ = v___y_2411_;
goto v___jp_2446_;
}
else
{
lean_object* v___x_2497_; uint8_t v___x_2498_; 
v___x_2497_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10);
v___x_2498_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2471_, v_opts_2495_, v___x_2497_);
lean_dec_ref(v_opts_2495_);
lean_dec(v___x_2471_);
if (v___x_2498_ == 0)
{
lean_dec(v_hint_2409_);
lean_dec(v_mod_2407_);
v___y_2447_ = v___y_2411_;
goto v___jp_2446_;
}
else
{
lean_object* v___x_2499_; lean_object* v___y_2501_; 
v___x_2499_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12);
if (v_isExporting_2435_ == 0)
{
lean_object* v___x_2508_; 
v___x_2508_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17));
v___y_2501_ = v___x_2508_;
goto v___jp_2500_;
}
else
{
lean_object* v___x_2509_; 
v___x_2509_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18));
v___y_2501_ = v___x_2509_;
goto v___jp_2500_;
}
v___jp_2500_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_inc_ref(v___y_2501_);
v___x_2502_ = l_Lean_stringToMessageData(v___y_2501_);
v___x_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2499_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14);
v___x_2505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
if (v_isMeta_2408_ == 0)
{
lean_object* v___x_2506_; 
v___x_2506_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15));
v___y_2480_ = v___x_2505_;
v___y_2481_ = v___x_2506_;
goto v___jp_2479_;
}
else
{
lean_object* v___x_2507_; 
v___x_2507_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16));
v___y_2480_ = v___x_2505_;
v___y_2481_ = v___x_2507_;
goto v___jp_2479_;
}
}
}
}
v___jp_2446_:
{
lean_object* v___x_2448_; lean_object* v_toEnvExtension_2449_; lean_object* v_env_2450_; lean_object* v_messages_2451_; lean_object* v_scopes_2452_; lean_object* v_usedQuotCtxts_2453_; lean_object* v_nextMacroScope_2454_; lean_object* v_maxRecDepth_2455_; lean_object* v_ngen_2456_; lean_object* v_auxDeclNGen_2457_; lean_object* v_infoState_2458_; lean_object* v_traceState_2459_; lean_object* v_snapshotTasks_2460_; lean_object* v_prevLinterStates_2461_; lean_object* v_codeQualityEntryTasks_2462_; lean_object* v_asyncMode_2463_; uint8_t v_logWrites_2464_; lean_object* v___x_2465_; 
v___x_2448_ = lean_st_ref_take(v___y_2447_);
v_toEnvExtension_2449_ = lean_ctor_get(v___x_2439_, 0);
v_env_2450_ = lean_ctor_get(v___x_2448_, 0);
lean_inc_ref(v_env_2450_);
v_messages_2451_ = lean_ctor_get(v___x_2448_, 1);
lean_inc_ref(v_messages_2451_);
v_scopes_2452_ = lean_ctor_get(v___x_2448_, 2);
lean_inc(v_scopes_2452_);
v_usedQuotCtxts_2453_ = lean_ctor_get(v___x_2448_, 3);
lean_inc(v_usedQuotCtxts_2453_);
v_nextMacroScope_2454_ = lean_ctor_get(v___x_2448_, 4);
lean_inc(v_nextMacroScope_2454_);
v_maxRecDepth_2455_ = lean_ctor_get(v___x_2448_, 5);
lean_inc(v_maxRecDepth_2455_);
v_ngen_2456_ = lean_ctor_get(v___x_2448_, 6);
lean_inc_ref(v_ngen_2456_);
v_auxDeclNGen_2457_ = lean_ctor_get(v___x_2448_, 7);
lean_inc_ref(v_auxDeclNGen_2457_);
v_infoState_2458_ = lean_ctor_get(v___x_2448_, 8);
lean_inc_ref(v_infoState_2458_);
v_traceState_2459_ = lean_ctor_get(v___x_2448_, 9);
lean_inc_ref(v_traceState_2459_);
v_snapshotTasks_2460_ = lean_ctor_get(v___x_2448_, 10);
lean_inc_ref(v_snapshotTasks_2460_);
v_prevLinterStates_2461_ = lean_ctor_get(v___x_2448_, 11);
lean_inc(v_prevLinterStates_2461_);
v_codeQualityEntryTasks_2462_ = lean_ctor_get(v___x_2448_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2462_);
lean_dec(v___x_2448_);
v_asyncMode_2463_ = lean_ctor_get(v_toEnvExtension_2449_, 2);
v_logWrites_2464_ = lean_ctor_get_uint8(v_toEnvExtension_2449_, sizeof(void*)*6);
v___x_2465_ = lean_box(0);
if (v_logWrites_2464_ == 0)
{
lean_object* v___x_2466_; 
lean_inc_ref(v_toEnvExtension_2449_);
v___x_2466_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2449_, v_env_2450_, v___f_2444_, v_asyncMode_2463_, v___x_2441_, v___x_2445_);
v___y_2414_ = v_maxRecDepth_2455_;
v___y_2415_ = v_scopes_2452_;
v___y_2416_ = v_ngen_2456_;
v___y_2417_ = v_infoState_2458_;
v___y_2418_ = v_snapshotTasks_2460_;
v___y_2419_ = v_auxDeclNGen_2457_;
v___y_2420_ = v_traceState_2459_;
v___y_2421_ = v_messages_2451_;
v___y_2422_ = v_usedQuotCtxts_2453_;
v___y_2423_ = v___y_2447_;
v___y_2424_ = v_nextMacroScope_2454_;
v___y_2425_ = v___x_2465_;
v___y_2426_ = v_prevLinterStates_2461_;
v___y_2427_ = v_codeQualityEntryTasks_2462_;
v___y_2428_ = v___x_2466_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
lean_inc_ref_n(v_toEnvExtension_2449_, 2);
v___x_2467_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2449_, v_env_2450_);
lean_dec_ref(v_env_2450_);
v___x_2468_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2449_, v___x_2467_, v___f_2444_, v_asyncMode_2463_, v___x_2441_, v___x_2445_);
v___y_2414_ = v_maxRecDepth_2455_;
v___y_2415_ = v_scopes_2452_;
v___y_2416_ = v_ngen_2456_;
v___y_2417_ = v_infoState_2458_;
v___y_2418_ = v_snapshotTasks_2460_;
v___y_2419_ = v_auxDeclNGen_2457_;
v___y_2420_ = v_traceState_2459_;
v___y_2421_ = v_messages_2451_;
v___y_2422_ = v_usedQuotCtxts_2453_;
v___y_2423_ = v___y_2447_;
v___y_2424_ = v_nextMacroScope_2454_;
v___y_2425_ = v___x_2465_;
v___y_2426_ = v_prevLinterStates_2461_;
v___y_2427_ = v_codeQualityEntryTasks_2462_;
v___y_2428_ = v___x_2468_;
goto v___jp_2413_;
}
}
v___jp_2474_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___y_2475_);
lean_ctor_set(v___x_2477_, 1, v___y_2476_);
v___x_2478_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2469_, v___x_2477_, v___y_2410_, v___y_2411_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_dec_ref_known(v___x_2478_, 1);
v___y_2447_ = v___y_2411_;
goto v___jp_2446_;
}
else
{
lean_dec_ref(v___f_2444_);
return v___x_2478_;
}
}
v___jp_2479_:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; 
lean_inc_ref(v___y_2481_);
v___x_2482_ = l_Lean_stringToMessageData(v___y_2481_);
v___x_2483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___y_2480_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4);
v___x_2485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = l_Lean_MessageData_ofName(v_mod_2407_);
v___x_2487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = l_Lean_Name_isAnonymous(v_hint_2409_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2489_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6);
v___x_2490_ = l_Lean_MessageData_ofName(v_hint_2409_);
v___x_2491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2489_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
v___y_2475_ = v___x_2487_;
v___y_2476_ = v___x_2491_;
goto v___jp_2474_;
}
else
{
lean_object* v___x_2492_; 
lean_dec(v_hint_2409_);
v___x_2492_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7);
v___y_2475_ = v___x_2487_;
v___y_2476_ = v___x_2492_;
goto v___jp_2474_;
}
}
}
else
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
lean_dec_ref_known(v_entry_2436_, 1);
lean_dec(v_hint_2409_);
lean_dec(v_mod_2407_);
v___x_2510_ = lean_box(0);
v___x_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
return v___x_2511_;
}
v___jp_2413_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2429_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2429_, 0, v___y_2428_);
lean_ctor_set(v___x_2429_, 1, v___y_2421_);
lean_ctor_set(v___x_2429_, 2, v___y_2415_);
lean_ctor_set(v___x_2429_, 3, v___y_2422_);
lean_ctor_set(v___x_2429_, 4, v___y_2424_);
lean_ctor_set(v___x_2429_, 5, v___y_2414_);
lean_ctor_set(v___x_2429_, 6, v___y_2416_);
lean_ctor_set(v___x_2429_, 7, v___y_2419_);
lean_ctor_set(v___x_2429_, 8, v___y_2417_);
lean_ctor_set(v___x_2429_, 9, v___y_2420_);
lean_ctor_set(v___x_2429_, 10, v___y_2418_);
lean_ctor_set(v___x_2429_, 11, v___y_2426_);
lean_ctor_set(v___x_2429_, 12, v___y_2427_);
v___x_2430_ = lean_st_ref_put(v___y_2423_, v___x_2429_);
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___y_2425_);
return v___x_2431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___boxed(lean_object* v_mod_2512_, lean_object* v_isMeta_2513_, lean_object* v_hint_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
uint8_t v_isMeta_boxed_2518_; lean_object* v_res_2519_; 
v_isMeta_boxed_2518_ = lean_unbox(v_isMeta_2513_);
v_res_2519_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_mod_2512_, v_isMeta_boxed_2518_, v_hint_2514_, v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(lean_object* v___x_2520_, lean_object* v_declName_2521_, lean_object* v_as_2522_, size_t v_sz_2523_, size_t v_i_2524_, lean_object* v_b_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
uint8_t v___x_2529_; 
v___x_2529_ = lean_usize_dec_lt(v_i_2524_, v_sz_2523_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; 
lean_dec(v_declName_2521_);
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v_b_2525_);
return v___x_2530_;
}
else
{
lean_object* v___x_2531_; lean_object* v_modules_2532_; lean_object* v___x_2533_; lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v_toImport_2536_; lean_object* v_module_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; 
v___x_2531_ = l_Lean_Environment_header(v___x_2520_);
v_modules_2532_ = lean_ctor_get(v___x_2531_, 3);
lean_inc_ref(v_modules_2532_);
lean_dec_ref(v___x_2531_);
v___x_2533_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2534_ = lean_array_uget_borrowed(v_as_2522_, v_i_2524_);
v___x_2535_ = lean_array_get(v___x_2533_, v_modules_2532_, v_a_2534_);
lean_dec_ref(v_modules_2532_);
v_toImport_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc_ref(v_toImport_2536_);
lean_dec(v___x_2535_);
v_module_2537_ = lean_ctor_get(v_toImport_2536_, 0);
lean_inc(v_module_2537_);
lean_dec_ref(v_toImport_2536_);
v___x_2538_ = lean_box(0);
v___x_2539_ = 0;
lean_inc(v_declName_2521_);
v___x_2540_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2537_, v___x_2539_, v_declName_2521_, v___y_2526_, v___y_2527_);
if (lean_obj_tag(v___x_2540_) == 0)
{
size_t v___x_2541_; size_t v___x_2542_; 
lean_dec_ref_known(v___x_2540_, 1);
v___x_2541_ = ((size_t)1ULL);
v___x_2542_ = lean_usize_add(v_i_2524_, v___x_2541_);
v_i_2524_ = v___x_2542_;
v_b_2525_ = v___x_2538_;
goto _start;
}
else
{
lean_dec(v_declName_2521_);
return v___x_2540_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4___boxed(lean_object* v___x_2544_, lean_object* v_declName_2545_, lean_object* v_as_2546_, lean_object* v_sz_2547_, lean_object* v_i_2548_, lean_object* v_b_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
size_t v_sz_boxed_2553_; size_t v_i_boxed_2554_; lean_object* v_res_2555_; 
v_sz_boxed_2553_ = lean_unbox_usize(v_sz_2547_);
lean_dec(v_sz_2547_);
v_i_boxed_2554_ = lean_unbox_usize(v_i_2548_);
lean_dec(v_i_2548_);
v_res_2555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v___x_2544_, v_declName_2545_, v_as_2546_, v_sz_boxed_2553_, v_i_boxed_2554_, v_b_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec_ref(v_as_2546_);
lean_dec_ref(v___x_2544_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(lean_object* v_a_2556_, lean_object* v_x_2557_){
_start:
{
if (lean_obj_tag(v_x_2557_) == 0)
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_box(0);
return v___x_2558_;
}
else
{
lean_object* v_key_2559_; lean_object* v_value_2560_; lean_object* v_tail_2561_; uint8_t v___x_2562_; 
v_key_2559_ = lean_ctor_get(v_x_2557_, 0);
v_value_2560_ = lean_ctor_get(v_x_2557_, 1);
v_tail_2561_ = lean_ctor_get(v_x_2557_, 2);
v___x_2562_ = lean_name_eq(v_key_2559_, v_a_2556_);
if (v___x_2562_ == 0)
{
v_x_2557_ = v_tail_2561_;
goto _start;
}
else
{
lean_object* v___x_2564_; 
lean_inc(v_value_2560_);
v___x_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_value_2560_);
return v___x_2564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_a_2565_, lean_object* v_x_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2565_, v_x_2566_);
lean_dec(v_x_2566_);
lean_dec(v_a_2565_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(lean_object* v_m_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v_buckets_2570_; lean_object* v___x_2571_; uint64_t v___y_2573_; 
v_buckets_2570_ = lean_ctor_get(v_m_2568_, 1);
v___x_2571_ = lean_array_get_size(v_buckets_2570_);
if (lean_obj_tag(v_a_2569_) == 0)
{
uint64_t v___x_2587_; 
v___x_2587_ = 1723ULL;
v___y_2573_ = v___x_2587_;
goto v___jp_2572_;
}
else
{
uint64_t v_hash_2588_; 
v_hash_2588_ = lean_ctor_get_uint64(v_a_2569_, sizeof(void*)*2);
v___y_2573_ = v_hash_2588_;
goto v___jp_2572_;
}
v___jp_2572_:
{
uint64_t v___x_2574_; uint64_t v___x_2575_; uint64_t v_fold_2576_; uint64_t v___x_2577_; uint64_t v___x_2578_; uint64_t v___x_2579_; size_t v___x_2580_; size_t v___x_2581_; size_t v___x_2582_; size_t v___x_2583_; size_t v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2574_ = 32ULL;
v___x_2575_ = lean_uint64_shift_right(v___y_2573_, v___x_2574_);
v_fold_2576_ = lean_uint64_xor(v___y_2573_, v___x_2575_);
v___x_2577_ = 16ULL;
v___x_2578_ = lean_uint64_shift_right(v_fold_2576_, v___x_2577_);
v___x_2579_ = lean_uint64_xor(v_fold_2576_, v___x_2578_);
v___x_2580_ = lean_uint64_to_usize(v___x_2579_);
v___x_2581_ = lean_usize_of_nat(v___x_2571_);
v___x_2582_ = ((size_t)1ULL);
v___x_2583_ = lean_usize_sub(v___x_2581_, v___x_2582_);
v___x_2584_ = lean_usize_land(v___x_2580_, v___x_2583_);
v___x_2585_ = lean_array_uget_borrowed(v_buckets_2570_, v___x_2584_);
v___x_2586_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2569_, v___x_2585_);
return v___x_2586_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_2589_, v_a_2590_);
lean_dec(v_a_2590_);
lean_dec_ref(v_m_2589_);
return v_res_2591_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object* v_declName_2595_, uint8_t v_isMeta_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v_env_2605_; lean_object* v___y_2607_; lean_object* v___x_2620_; 
v___x_2600_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0);
v___x_2601_ = lean_st_ref_get(v___y_2598_);
v_env_2605_ = lean_ctor_get(v___x_2601_, 0);
lean_inc_ref(v_env_2605_);
lean_dec(v___x_2601_);
v___x_2620_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2605_, v_declName_2595_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_dec_ref(v_env_2605_);
lean_dec(v_declName_2595_);
goto v___jp_2602_;
}
else
{
lean_object* v_val_2621_; lean_object* v___x_2622_; lean_object* v_modules_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v_val_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_val_2621_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2622_ = l_Lean_Environment_header(v_env_2605_);
v_modules_2623_ = lean_ctor_get(v___x_2622_, 3);
lean_inc_ref(v_modules_2623_);
lean_dec_ref(v___x_2622_);
v___x_2624_ = lean_array_get_size(v_modules_2623_);
v___x_2625_ = lean_nat_dec_lt(v_val_2621_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_dec_ref(v_modules_2623_);
lean_dec(v_val_2621_);
lean_dec_ref(v_env_2605_);
lean_dec(v_declName_2595_);
goto v___jp_2602_;
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; uint8_t v___y_2629_; 
v___x_2626_ = lean_array_fget(v_modules_2623_, v_val_2621_);
lean_dec(v_val_2621_);
lean_dec_ref(v_modules_2623_);
v___x_2627_ = lean_st_ref_get(v___y_2598_);
if (v_isMeta_2596_ == 0)
{
lean_dec(v___x_2627_);
v___y_2629_ = v_isMeta_2596_;
goto v___jp_2628_;
}
else
{
lean_object* v_env_2640_; uint8_t v___x_2641_; 
v_env_2640_ = lean_ctor_get(v___x_2627_, 0);
lean_inc_ref(v_env_2640_);
lean_dec(v___x_2627_);
lean_inc(v_declName_2595_);
v___x_2641_ = l_Lean_isMarkedMeta(v_env_2640_, v_declName_2595_);
if (v___x_2641_ == 0)
{
v___y_2629_ = v_isMeta_2596_;
goto v___jp_2628_;
}
else
{
uint8_t v___x_2642_; 
v___x_2642_ = 0;
v___y_2629_ = v___x_2642_;
goto v___jp_2628_;
}
}
v___jp_2628_:
{
lean_object* v_toImport_2630_; lean_object* v_module_2631_; lean_object* v___x_2632_; 
v_toImport_2630_ = lean_ctor_get(v___x_2626_, 0);
lean_inc_ref(v_toImport_2630_);
lean_dec(v___x_2626_);
v_module_2631_ = lean_ctor_get(v_toImport_2630_, 0);
lean_inc(v_module_2631_);
lean_dec_ref(v_toImport_2630_);
lean_inc(v_declName_2595_);
v___x_2632_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2631_, v___y_2629_, v_declName_2595_, v___y_2597_, v___y_2598_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
lean_dec_ref_known(v___x_2632_, 1);
v___x_2633_ = l_Lean_indirectModUseExt;
v___x_2634_ = lean_box(1);
v___x_2635_ = lean_box(0);
lean_inc_ref(v_env_2605_);
v___x_2636_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2600_, v___x_2633_, v_env_2605_, v___x_2634_, v___x_2635_);
v___x_2637_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v___x_2636_, v_declName_2595_);
lean_dec(v___x_2636_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v___x_2638_; 
v___x_2638_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1));
v___y_2607_ = v___x_2638_;
goto v___jp_2606_;
}
else
{
lean_object* v_val_2639_; 
v_val_2639_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_val_2639_);
lean_dec_ref_known(v___x_2637_, 1);
v___y_2607_ = v_val_2639_;
goto v___jp_2606_;
}
}
else
{
lean_dec_ref(v_env_2605_);
lean_dec(v_declName_2595_);
return v___x_2632_;
}
}
}
}
v___jp_2602_:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = lean_box(0);
v___x_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
return v___x_2604_;
}
v___jp_2606_:
{
lean_object* v___x_2608_; size_t v_sz_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2608_ = lean_box(0);
v_sz_2609_ = lean_array_size(v___y_2607_);
v___x_2610_ = ((size_t)0ULL);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v_env_2605_, v_declName_2595_, v___y_2607_, v_sz_2609_, v___x_2610_, v___x_2608_, v___y_2597_, v___y_2598_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v_env_2605_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2618_ == 0)
{
lean_object* v_unused_2619_; 
v_unused_2619_ = lean_ctor_get(v___x_2611_, 0);
lean_dec(v_unused_2619_);
v___x_2613_ = v___x_2611_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_dec(v___x_2611_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2608_);
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2608_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
else
{
return v___x_2611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object* v_declName_2643_, lean_object* v_isMeta_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
uint8_t v_isMeta_boxed_2648_; lean_object* v_res_2649_; 
v_isMeta_boxed_2648_ = lean_unbox(v_isMeta_2644_);
v_res_2649_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_declName_2643_, v_isMeta_boxed_2648_, v___y_2645_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(lean_object* v_as_x27_2650_, lean_object* v_b_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
if (lean_obj_tag(v_as_x27_2650_) == 0)
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v_b_2651_);
return v___x_2655_;
}
else
{
lean_object* v_head_2656_; lean_object* v_tail_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; lean_object* v___x_2660_; 
v_head_2656_ = lean_ctor_get(v_as_x27_2650_, 0);
v_tail_2657_ = lean_ctor_get(v_as_x27_2650_, 1);
v___x_2658_ = lean_box(0);
v___x_2659_ = 1;
lean_inc(v_head_2656_);
v___x_2660_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_head_2656_, v___x_2659_, v___y_2652_, v___y_2653_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_dec_ref_known(v___x_2660_, 1);
v_as_x27_2650_ = v_tail_2657_;
v_b_2651_ = v___x_2658_;
goto _start;
}
else
{
return v___x_2660_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_2662_, lean_object* v_b_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_2662_, v_b_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v_as_x27_2662_);
return v_res_2667_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = l_Lean_maxRecDepthErrorMessage;
v___x_2674_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
return v___x_2674_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3);
v___x_2676_ = l_Lean_MessageData_ofFormat(v___x_2675_);
return v___x_2676_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2677_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4);
v___x_2678_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2));
v___x_2679_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
lean_ctor_set(v___x_2679_, 1, v___x_2677_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(lean_object* v_ref_2680_){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2682_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5);
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v_ref_2680_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___boxed(lean_object* v_ref_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_2685_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object* v_currNamespace_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2691_, 0, v_currNamespace_2688_);
lean_ctor_set(v___x_2691_, 1, v___y_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(v_currNamespace_2692_, v___y_2693_, v___y_2694_);
lean_dec_ref(v___y_2693_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object* v_env_2696_, lean_object* v_declName_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
uint8_t v___x_2700_; lean_object* v_env_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; uint8_t v___x_2704_; 
v___x_2700_ = 0;
v_env_2701_ = l_Lean_Environment_setExporting(v_env_2696_, v___x_2700_);
lean_inc(v_declName_2697_);
v___x_2702_ = l_Lean_mkPrivateName(v_env_2701_, v_declName_2697_);
v___x_2703_ = 1;
lean_inc_ref(v_env_2701_);
v___x_2704_ = l_Lean_Environment_contains(v_env_2701_, v___x_2702_, v___x_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; uint8_t v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2705_ = l_Lean_privateToUserName(v_declName_2697_);
v___x_2706_ = l_Lean_Environment_contains(v_env_2701_, v___x_2705_, v___x_2703_);
v___x_2707_ = lean_box(v___x_2706_);
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
lean_ctor_set(v___x_2708_, 1, v___y_2699_);
return v___x_2708_;
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_dec_ref(v_env_2701_);
lean_dec(v_declName_2697_);
v___x_2709_ = lean_box(v___x_2704_);
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
lean_ctor_set(v___x_2710_, 1, v___y_2699_);
return v___x_2710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object* v_env_2711_, lean_object* v_declName_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(v_env_2711_, v_declName_2712_, v___y_2713_, v___y_2714_);
lean_dec_ref(v___y_2713_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(lean_object* v_x_2716_, lean_object* v___y_2717_){
_start:
{
if (lean_obj_tag(v_x_2716_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2719_; 
v_a_2718_ = lean_ctor_get(v_x_2716_, 0);
lean_inc(v_a_2718_);
v___x_2719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2719_, 0, v_a_2718_);
lean_ctor_set(v___x_2719_, 1, v___y_2717_);
return v___x_2719_;
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2721_; 
v_a_2720_ = lean_ctor_get(v_x_2716_, 0);
lean_inc(v_a_2720_);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v_a_2720_);
lean_ctor_set(v___x_2721_, 1, v___y_2717_);
return v___x_2721_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_2722_, v___y_2723_);
lean_dec_ref(v_x_2722_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object* v_env_2725_, lean_object* v_stx_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2725_, v_stx_2726_, v___y_2727_, v___y_2728_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
if (lean_obj_tag(v_a_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2739_; 
v_a_2731_ = lean_ctor_get(v___x_2729_, 1);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2739_ == 0)
{
lean_object* v_unused_2740_; 
v_unused_2740_ = lean_ctor_get(v___x_2729_, 0);
lean_dec(v_unused_2740_);
v___x_2733_ = v___x_2729_;
v_isShared_2734_ = v_isSharedCheck_2739_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2729_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2739_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2737_; 
v___x_2735_ = lean_box(0);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v___x_2735_);
v___x_2737_ = v___x_2733_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_a_2731_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
else
{
lean_object* v_val_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2769_; 
v_val_2741_ = lean_ctor_get(v_a_2730_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_a_2730_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2743_ = v_a_2730_;
v_isShared_2744_ = v_isSharedCheck_2769_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_val_2741_);
lean_dec(v_a_2730_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2769_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v_snd_2745_; 
v_snd_2745_ = lean_ctor_get(v_val_2741_, 1);
lean_inc(v_snd_2745_);
lean_dec(v_val_2741_);
if (lean_obj_tag(v_snd_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2755_; 
lean_del_object(v___x_2743_);
v_a_2746_ = lean_ctor_get(v___x_2729_, 1);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___x_2729_, 2);
v_a_2747_ = lean_ctor_get(v_snd_2745_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_snd_2745_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2749_ = v_snd_2745_;
v_isShared_2750_ = v_isSharedCheck_2755_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v_snd_2745_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2755_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2752_, v_a_2746_);
lean_dec_ref(v___x_2752_);
return v___x_2753_;
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2768_; 
v_a_2756_ = lean_ctor_get(v___x_2729_, 1);
lean_inc(v_a_2756_);
lean_dec_ref_known(v___x_2729_, 2);
v_a_2757_ = lean_ctor_get(v_snd_2745_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v_snd_2745_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2759_ = v_snd_2745_;
v_isShared_2760_ = v_isSharedCheck_2768_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v_snd_2745_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2768_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v_a_2757_);
v___x_2762_ = v___x_2743_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2764_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2762_);
v___x_2764_ = v___x_2759_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2764_, v_a_2756_);
lean_dec_ref(v___x_2764_);
return v___x_2765_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
v_a_2770_ = lean_ctor_get(v___x_2729_, 0);
v_a_2771_ = lean_ctor_get(v___x_2729_, 1);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2729_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_inc(v_a_2770_);
lean_dec(v___x_2729_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2770_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object* v_env_2779_, lean_object* v_stx_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(v_env_2779_, v_stx_2780_, v___y_2781_, v___y_2782_);
lean_dec_ref(v___y_2781_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object* v_env_2784_, lean_object* v_currNamespace_2785_, lean_object* v_openDecls_2786_, lean_object* v_n_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = l_Lean_ResolveName_resolveNamespace(v_env_2784_, v_currNamespace_2785_, v_openDecls_2786_, v_n_2787_);
v___x_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
lean_ctor_set(v___x_2791_, 1, v___y_2789_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object* v_env_2792_, lean_object* v_currNamespace_2793_, lean_object* v_openDecls_2794_, lean_object* v_n_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(v_env_2792_, v_currNamespace_2793_, v_openDecls_2794_, v_n_2795_, v___y_2796_, v___y_2797_);
lean_dec_ref(v___y_2796_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object* v_as_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
if (lean_obj_tag(v_as_2799_) == 0)
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_box(0);
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
return v___x_2804_;
}
else
{
lean_object* v_head_2805_; lean_object* v_tail_2806_; lean_object* v_fst_2807_; lean_object* v_snd_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v_scopes_2813_; lean_object* v___x_2814_; lean_object* v_opts_2815_; uint8_t v_hasTrace_2816_; 
v_head_2805_ = lean_ctor_get(v_as_2799_, 0);
lean_inc(v_head_2805_);
v_tail_2806_ = lean_ctor_get(v_as_2799_, 1);
lean_inc(v_tail_2806_);
lean_dec_ref_known(v_as_2799_, 2);
v_fst_2807_ = lean_ctor_get(v_head_2805_, 0);
lean_inc(v_fst_2807_);
v_snd_2808_ = lean_ctor_get(v_head_2805_, 1);
lean_inc(v_snd_2808_);
lean_dec(v_head_2805_);
v___x_2809_ = l_Lean_inheritedTraceOptions;
v___x_2810_ = lean_st_ref_get(v___x_2809_);
v___x_2811_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2812_ = lean_st_ref_get(v___y_2801_);
v_scopes_2813_ = lean_ctor_get(v___x_2812_, 2);
lean_inc(v_scopes_2813_);
lean_dec(v___x_2812_);
v___x_2814_ = l_List_head_x21___redArg(v___x_2811_, v_scopes_2813_);
lean_dec(v_scopes_2813_);
v_opts_2815_ = lean_ctor_get(v___x_2814_, 1);
lean_inc_ref(v_opts_2815_);
lean_dec(v___x_2814_);
v_hasTrace_2816_ = lean_ctor_get_uint8(v_opts_2815_, sizeof(void*)*1);
if (v_hasTrace_2816_ == 0)
{
lean_dec_ref(v_opts_2815_);
lean_dec(v___x_2810_);
lean_dec(v_snd_2808_);
lean_dec(v_fst_2807_);
v_as_2799_ = v_tail_2806_;
goto _start;
}
else
{
lean_object* v___x_2818_; lean_object* v___x_2819_; uint8_t v___x_2820_; 
v___x_2818_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9));
lean_inc(v_fst_2807_);
v___x_2819_ = l_Lean_Name_append(v___x_2818_, v_fst_2807_);
v___x_2820_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2810_, v_opts_2815_, v___x_2819_);
lean_dec(v___x_2819_);
lean_dec_ref(v_opts_2815_);
lean_dec(v___x_2810_);
if (v___x_2820_ == 0)
{
lean_dec(v_snd_2808_);
lean_dec(v_fst_2807_);
v_as_2799_ = v_tail_2806_;
goto _start;
}
else
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2822_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2822_, 0, v_snd_2808_);
v___x_2823_ = l_Lean_MessageData_ofFormat(v___x_2822_);
v___x_2824_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_fst_2807_, v___x_2823_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_dec_ref_known(v___x_2824_, 1);
v_as_2799_ = v_tail_2806_;
goto _start;
}
else
{
lean_dec(v_tail_2806_);
return v___x_2824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object* v_as_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v_as_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object* v_env_2831_, lean_object* v_opts_2832_, lean_object* v_currNamespace_2833_, lean_object* v_openDecls_2834_, lean_object* v_n_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = l_Lean_ResolveName_resolveGlobalName(v_env_2831_, v_opts_2832_, v_currNamespace_2833_, v_openDecls_2834_, v_n_2835_);
v___x_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
lean_ctor_set(v___x_2839_, 1, v___y_2837_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object* v_env_2840_, lean_object* v_opts_2841_, lean_object* v_currNamespace_2842_, lean_object* v_openDecls_2843_, lean_object* v_n_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(v_env_2840_, v_opts_2841_, v_currNamespace_2842_, v_openDecls_2843_, v_n_2844_, v___y_2845_, v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v_opts_2841_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object* v_x_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v___x_2853_; lean_object* v_env_2854_; lean_object* v___f_2855_; lean_object* v___f_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v_scopes_2859_; lean_object* v___x_2860_; lean_object* v_opts_2861_; lean_object* v___x_2862_; 
v___x_2853_ = lean_st_ref_get(v___y_2851_);
v_env_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc_ref_n(v_env_2854_, 3);
lean_dec(v___x_2853_);
v___f_2855_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2855_, 0, v_env_2854_);
v___f_2856_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2856_, 0, v_env_2854_);
v___x_2857_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2858_ = lean_st_ref_get(v___y_2851_);
v_scopes_2859_ = lean_ctor_get(v___x_2858_, 2);
lean_inc(v_scopes_2859_);
lean_dec(v___x_2858_);
v___x_2860_ = l_List_head_x21___redArg(v___x_2857_, v_scopes_2859_);
lean_dec(v_scopes_2859_);
v_opts_2861_ = lean_ctor_get(v___x_2860_, 1);
lean_inc_ref(v_opts_2861_);
lean_dec(v___x_2860_);
v___x_2862_ = l_Lean_Elab_Command_getScope___redArg(v___y_2851_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v_currNamespace_2864_; lean_object* v___f_2865_; lean_object* v___x_2866_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2862_, 1);
v_currNamespace_2864_ = lean_ctor_get(v_a_2863_, 2);
lean_inc_n(v_currNamespace_2864_, 2);
lean_dec(v_a_2863_);
v___f_2865_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2865_, 0, v_currNamespace_2864_);
v___x_2866_ = l_Lean_Elab_Command_getScope___redArg(v___y_2851_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v_openDecls_2868_; lean_object* v___f_2869_; lean_object* v___f_2870_; lean_object* v_methods_2871_; lean_object* v___x_2872_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___x_2866_, 1);
v_openDecls_2868_ = lean_ctor_get(v_a_2867_, 3);
lean_inc_n(v_openDecls_2868_, 2);
lean_dec(v_a_2867_);
lean_inc(v_currNamespace_2864_);
lean_inc_ref(v_env_2854_);
v___f_2869_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2869_, 0, v_env_2854_);
lean_closure_set(v___f_2869_, 1, v_currNamespace_2864_);
lean_closure_set(v___f_2869_, 2, v_openDecls_2868_);
v___f_2870_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2870_, 0, v_env_2854_);
lean_closure_set(v___f_2870_, 1, v_opts_2861_);
lean_closure_set(v___f_2870_, 2, v_currNamespace_2864_);
lean_closure_set(v___f_2870_, 3, v_openDecls_2868_);
v_methods_2871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2871_, 0, v___f_2856_);
lean_ctor_set(v_methods_2871_, 1, v___f_2865_);
lean_ctor_set(v_methods_2871_, 2, v___f_2855_);
lean_ctor_set(v_methods_2871_, 3, v___f_2869_);
lean_ctor_set(v_methods_2871_, 4, v___f_2870_);
v___x_2872_ = l_Lean_Elab_Command_getRef___redArg(v___y_2850_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2874_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2872_, 1);
v___x_2874_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2850_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v_currRecDepth_2876_; lean_object* v_quotContext_x3f_2877_; lean_object* v_a_2879_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v_currRecDepth_2876_ = lean_ctor_get(v___y_2850_, 2);
v_quotContext_x3f_2877_ = lean_ctor_get(v___y_2850_, 5);
if (lean_obj_tag(v_quotContext_x3f_2877_) == 0)
{
lean_object* v___x_2953_; lean_object* v_a_2954_; 
v___x_2953_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_2851_);
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref(v___x_2953_);
v_a_2879_ = v_a_2954_;
goto v___jp_2878_;
}
else
{
lean_object* v_val_2955_; 
v_val_2955_ = lean_ctor_get(v_quotContext_x3f_2877_, 0);
lean_inc(v_val_2955_);
v_a_2879_ = v_val_2955_;
goto v___jp_2878_;
}
v___jp_2878_:
{
lean_object* v___x_2880_; lean_object* v_maxRecDepth_2881_; lean_object* v___x_2882_; lean_object* v_nextMacroScope_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2880_ = lean_st_ref_get(v___y_2851_);
v_maxRecDepth_2881_ = lean_ctor_get(v___x_2880_, 5);
lean_inc(v_maxRecDepth_2881_);
lean_dec(v___x_2880_);
v___x_2882_ = lean_st_ref_get(v___y_2851_);
v_nextMacroScope_2883_ = lean_ctor_get(v___x_2882_, 4);
lean_inc(v_nextMacroScope_2883_);
lean_dec(v___x_2882_);
lean_inc(v_currRecDepth_2876_);
v___x_2884_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2884_, 0, v_methods_2871_);
lean_ctor_set(v___x_2884_, 1, v_a_2879_);
lean_ctor_set(v___x_2884_, 2, v_a_2875_);
lean_ctor_set(v___x_2884_, 3, v_currRecDepth_2876_);
lean_ctor_set(v___x_2884_, 4, v_maxRecDepth_2881_);
lean_ctor_set(v___x_2884_, 5, v_a_2873_);
v___x_2885_ = lean_box(0);
v___x_2886_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2886_, 0, v_nextMacroScope_2883_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
lean_ctor_set(v___x_2886_, 2, v___x_2885_);
v___x_2887_ = lean_apply_2(v_x_2849_, v___x_2884_, v___x_2886_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v_a_2889_; lean_object* v_macroScope_2890_; lean_object* v_traceMsgs_2891_; lean_object* v_expandedMacroDecls_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 1);
lean_inc(v_a_2888_);
v_a_2889_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v___x_2887_, 2);
v_macroScope_2890_ = lean_ctor_get(v_a_2888_, 0);
lean_inc(v_macroScope_2890_);
v_traceMsgs_2891_ = lean_ctor_get(v_a_2888_, 1);
lean_inc(v_traceMsgs_2891_);
v_expandedMacroDecls_2892_ = lean_ctor_get(v_a_2888_, 2);
lean_inc(v_expandedMacroDecls_2892_);
lean_dec(v_a_2888_);
v___x_2893_ = lean_box(0);
v___x_2894_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_expandedMacroDecls_2892_, v___x_2893_, v___y_2850_, v___y_2851_);
lean_dec(v_expandedMacroDecls_2892_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v___x_2895_; lean_object* v_env_2896_; lean_object* v_messages_2897_; lean_object* v_scopes_2898_; lean_object* v_usedQuotCtxts_2899_; lean_object* v_maxRecDepth_2900_; lean_object* v_ngen_2901_; lean_object* v_auxDeclNGen_2902_; lean_object* v_infoState_2903_; lean_object* v_traceState_2904_; lean_object* v_snapshotTasks_2905_; lean_object* v_prevLinterStates_2906_; lean_object* v_codeQualityEntryTasks_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2933_; 
lean_dec_ref_known(v___x_2894_, 1);
v___x_2895_ = lean_st_ref_take(v___y_2851_);
v_env_2896_ = lean_ctor_get(v___x_2895_, 0);
v_messages_2897_ = lean_ctor_get(v___x_2895_, 1);
v_scopes_2898_ = lean_ctor_get(v___x_2895_, 2);
v_usedQuotCtxts_2899_ = lean_ctor_get(v___x_2895_, 3);
v_maxRecDepth_2900_ = lean_ctor_get(v___x_2895_, 5);
v_ngen_2901_ = lean_ctor_get(v___x_2895_, 6);
v_auxDeclNGen_2902_ = lean_ctor_get(v___x_2895_, 7);
v_infoState_2903_ = lean_ctor_get(v___x_2895_, 8);
v_traceState_2904_ = lean_ctor_get(v___x_2895_, 9);
v_snapshotTasks_2905_ = lean_ctor_get(v___x_2895_, 10);
v_prevLinterStates_2906_ = lean_ctor_get(v___x_2895_, 11);
v_codeQualityEntryTasks_2907_ = lean_ctor_get(v___x_2895_, 12);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2933_ == 0)
{
lean_object* v_unused_2934_; 
v_unused_2934_ = lean_ctor_get(v___x_2895_, 4);
lean_dec(v_unused_2934_);
v___x_2909_ = v___x_2895_;
v_isShared_2910_ = v_isSharedCheck_2933_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2907_);
lean_inc(v_prevLinterStates_2906_);
lean_inc(v_snapshotTasks_2905_);
lean_inc(v_traceState_2904_);
lean_inc(v_infoState_2903_);
lean_inc(v_auxDeclNGen_2902_);
lean_inc(v_ngen_2901_);
lean_inc(v_maxRecDepth_2900_);
lean_inc(v_usedQuotCtxts_2899_);
lean_inc(v_scopes_2898_);
lean_inc(v_messages_2897_);
lean_inc(v_env_2896_);
lean_dec(v___x_2895_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2933_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 4, v_macroScope_2890_);
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_env_2896_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_messages_2897_);
lean_ctor_set(v_reuseFailAlloc_2932_, 2, v_scopes_2898_);
lean_ctor_set(v_reuseFailAlloc_2932_, 3, v_usedQuotCtxts_2899_);
lean_ctor_set(v_reuseFailAlloc_2932_, 4, v_macroScope_2890_);
lean_ctor_set(v_reuseFailAlloc_2932_, 5, v_maxRecDepth_2900_);
lean_ctor_set(v_reuseFailAlloc_2932_, 6, v_ngen_2901_);
lean_ctor_set(v_reuseFailAlloc_2932_, 7, v_auxDeclNGen_2902_);
lean_ctor_set(v_reuseFailAlloc_2932_, 8, v_infoState_2903_);
lean_ctor_set(v_reuseFailAlloc_2932_, 9, v_traceState_2904_);
lean_ctor_set(v_reuseFailAlloc_2932_, 10, v_snapshotTasks_2905_);
lean_ctor_set(v_reuseFailAlloc_2932_, 11, v_prevLinterStates_2906_);
lean_ctor_set(v_reuseFailAlloc_2932_, 12, v_codeQualityEntryTasks_2907_);
v___x_2912_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2913_ = lean_st_ref_put(v___y_2851_, v___x_2912_);
v___x_2914_ = l_List_reverse___redArg(v_traceMsgs_2891_);
v___x_2915_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v___x_2914_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2922_ == 0)
{
lean_object* v_unused_2923_; 
v_unused_2923_ = lean_ctor_get(v___x_2915_, 0);
lean_dec(v_unused_2923_);
v___x_2917_ = v___x_2915_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_dec(v___x_2915_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 0, v_a_2889_);
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2889_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec(v_a_2889_);
v_a_2924_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2915_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2915_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec(v_traceMsgs_2891_);
lean_dec(v_macroScope_2890_);
lean_dec(v_a_2889_);
v_a_2935_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2894_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2894_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
else
{
lean_object* v_a_2943_; 
v_a_2943_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2943_);
lean_dec_ref_known(v___x_2887_, 2);
if (lean_obj_tag(v_a_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v_a_2945_; lean_object* v___x_2946_; uint8_t v___x_2947_; 
v_a_2944_ = lean_ctor_get(v_a_2943_, 0);
lean_inc(v_a_2944_);
v_a_2945_ = lean_ctor_get(v_a_2943_, 1);
lean_inc_ref(v_a_2945_);
lean_dec_ref_known(v_a_2943_, 2);
v___x_2946_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0));
v___x_2947_ = lean_string_dec_eq(v_a_2945_, v___x_2946_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_a_2945_);
v___x_2949_ = l_Lean_MessageData_ofFormat(v___x_2948_);
v___x_2950_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_a_2944_, v___x_2949_, v___y_2850_, v___y_2851_);
lean_dec(v_a_2944_);
return v___x_2950_;
}
else
{
lean_object* v___x_2951_; 
lean_dec_ref(v_a_2945_);
v___x_2951_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_a_2944_);
return v___x_2951_;
}
}
else
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2952_;
}
}
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec(v_a_2873_);
lean_dec_ref_known(v_methods_2871_, 5);
lean_dec_ref(v_x_2849_);
v_a_2956_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2874_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2874_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec_ref_known(v_methods_2871_, 5);
lean_dec_ref(v_x_2849_);
v_a_2964_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2872_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2872_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec_ref(v___f_2865_);
lean_dec(v_currNamespace_2864_);
lean_dec_ref(v_opts_2861_);
lean_dec_ref(v___f_2856_);
lean_dec_ref(v___f_2855_);
lean_dec_ref(v_env_2854_);
lean_dec_ref(v_x_2849_);
v_a_2972_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2866_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2866_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec_ref(v_opts_2861_);
lean_dec_ref(v___f_2856_);
lean_dec_ref(v___f_2855_);
lean_dec_ref(v_env_2854_);
lean_dec_ref(v_x_2849_);
v_a_2980_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2862_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2862_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object* v_x_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_2988_, v___y_2989_, v___y_2990_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object* v_x_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3036_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_3037_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_3078_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
lean_inc(v_x_3032_);
v___x_3079_ = l_Lean_Syntax_isOfKind(v_x_3032_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; 
lean_dec(v_x_3032_);
v___x_3080_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3080_;
}
else
{
lean_object* v___x_3081_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; uint8_t v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; size_t v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; uint8_t v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; size_t v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; uint8_t v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; size_t v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; uint8_t v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; size_t v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3338_; lean_object* v___y_3339_; uint8_t v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; size_t v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v_expectedType_x3f_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v_prio_x3f_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v_name_x3f_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v_prec_x3f_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v_attrs_x3f_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v_doc_x3f_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v___x_3081_ = lean_unsigned_to_nat(0u);
v___x_3558_ = l_Lean_Syntax_getArg(v_x_3032_, v___x_3081_);
v___x_3559_ = l_Lean_Syntax_isNone(v___x_3558_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; uint8_t v___x_3561_; 
v___x_3560_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3558_);
v___x_3561_ = l_Lean_Syntax_matchesNull(v___x_3558_, v___x_3560_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; 
lean_dec(v___x_3558_);
lean_dec(v_x_3032_);
v___x_3562_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3562_;
}
else
{
lean_object* v_doc_x3f_3563_; 
v_doc_x3f_3563_ = l_Lean_Syntax_getArg(v___x_3558_, v___x_3081_);
lean_dec(v___x_3558_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3566_; uint8_t v___x_3567_; 
v___x_3566_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(v_doc_x3f_3563_);
v___x_3567_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3563_, v___x_3566_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; 
lean_dec(v_doc_x3f_3563_);
lean_dec(v_x_3032_);
v___x_3568_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3568_;
}
else
{
goto v___jp_3564_;
}
}
else
{
goto v___jp_3564_;
}
v___jp_3564_:
{
lean_object* v___x_3565_; 
v___x_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3565_, 0, v_doc_x3f_3563_);
v_doc_x3f_3542_ = v___x_3565_;
v___y_3543_ = v_a_3033_;
v___y_3544_ = v_a_3034_;
goto v___jp_3541_;
}
}
}
else
{
lean_object* v___x_3569_; 
lean_dec(v___x_3558_);
v___x_3569_ = lean_box(0);
v_doc_x3f_3542_ = v___x_3569_;
v___y_3543_ = v_a_3033_;
v___y_3544_ = v_a_3034_;
goto v___jp_3541_;
}
v___jp_3082_:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_inc_ref_n(v___y_3088_, 2);
v___x_3099_ = l_Array_append___redArg(v___y_3088_, v___y_3098_);
lean_dec_ref(v___y_3098_);
lean_inc_n(v___y_3090_, 3);
lean_inc_n(v___y_3085_, 6);
v___x_3100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3100_, 0, v___y_3085_);
lean_ctor_set(v___x_3100_, 1, v___y_3090_);
lean_ctor_set(v___x_3100_, 2, v___x_3099_);
v___x_3101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3101_, 0, v___y_3085_);
lean_ctor_set(v___x_3101_, 1, v___y_3090_);
lean_ctor_set(v___x_3101_, 2, v___y_3088_);
lean_inc_ref(v___x_3101_);
lean_inc(v___y_3094_);
v___x_3102_ = l_Lean_Syntax_node1(v___y_3085_, v___y_3094_, v___x_3101_);
lean_inc_ref(v___y_3087_);
v___x_3103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___y_3085_);
lean_ctor_set(v___x_3103_, 1, v___y_3087_);
lean_inc_ref(v___y_3097_);
v___x_3104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___y_3085_);
lean_ctor_set(v___x_3104_, 1, v___y_3097_);
v___x_3105_ = l_Lean_Syntax_node2(v___y_3085_, v___y_3090_, v___x_3104_, v___y_3084_);
if (lean_obj_tag(v___y_3091_) == 1)
{
lean_object* v_val_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_val_3106_ = lean_ctor_get(v___y_3091_, 0);
lean_inc(v_val_3106_);
lean_dec_ref_known(v___y_3091_, 1);
v___x_3107_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___y_3085_);
v___x_3108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___y_3085_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = l_Array_mkArray2___redArg(v___x_3108_, v_val_3106_);
v___y_3039_ = v___y_3083_;
v___y_3040_ = v___y_3085_;
v___y_3041_ = v___y_3086_;
v___y_3042_ = v___x_3103_;
v___y_3043_ = v___x_3100_;
v___y_3044_ = v___y_3088_;
v___y_3045_ = v___x_3102_;
v___y_3046_ = v___y_3089_;
v___y_3047_ = v___y_3090_;
v___y_3048_ = v___x_3101_;
v___y_3049_ = v___y_3092_;
v___y_3050_ = v___y_3093_;
v___y_3051_ = v___x_3105_;
v___y_3052_ = v___y_3095_;
v___y_3053_ = v___y_3096_;
v___y_3054_ = v___x_3109_;
goto v___jp_3038_;
}
else
{
lean_object* v___x_3110_; 
lean_dec(v___y_3091_);
v___x_3110_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3039_ = v___y_3083_;
v___y_3040_ = v___y_3085_;
v___y_3041_ = v___y_3086_;
v___y_3042_ = v___x_3103_;
v___y_3043_ = v___x_3100_;
v___y_3044_ = v___y_3088_;
v___y_3045_ = v___x_3102_;
v___y_3046_ = v___y_3089_;
v___y_3047_ = v___y_3090_;
v___y_3048_ = v___x_3101_;
v___y_3049_ = v___y_3092_;
v___y_3050_ = v___y_3093_;
v___y_3051_ = v___x_3105_;
v___y_3052_ = v___y_3095_;
v___y_3053_ = v___y_3096_;
v___y_3054_ = v___x_3110_;
goto v___jp_3038_;
}
}
v___jp_3111_:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_3127_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
if (lean_obj_tag(v___y_3115_) == 1)
{
lean_object* v_val_3128_; lean_object* v___x_3129_; 
v_val_3128_ = lean_ctor_get(v___y_3115_, 0);
lean_inc(v_val_3128_);
lean_dec_ref_known(v___y_3115_, 1);
v___x_3129_ = l_Array_mkArray1___redArg(v_val_3128_);
v___y_3083_ = v___y_3112_;
v___y_3084_ = v___y_3113_;
v___y_3085_ = v___y_3114_;
v___y_3086_ = v___x_3127_;
v___y_3087_ = v___x_3126_;
v___y_3088_ = v___y_3116_;
v___y_3089_ = v___y_3117_;
v___y_3090_ = v___y_3118_;
v___y_3091_ = v___y_3119_;
v___y_3092_ = v___y_3120_;
v___y_3093_ = v___y_3121_;
v___y_3094_ = v___y_3122_;
v___y_3095_ = v___y_3123_;
v___y_3096_ = v___y_3124_;
v___y_3097_ = v___y_3125_;
v___y_3098_ = v___x_3129_;
goto v___jp_3082_;
}
else
{
lean_object* v___x_3130_; 
lean_dec(v___y_3115_);
v___x_3130_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3083_ = v___y_3112_;
v___y_3084_ = v___y_3113_;
v___y_3085_ = v___y_3114_;
v___y_3086_ = v___x_3127_;
v___y_3087_ = v___x_3126_;
v___y_3088_ = v___y_3116_;
v___y_3089_ = v___y_3117_;
v___y_3090_ = v___y_3118_;
v___y_3091_ = v___y_3119_;
v___y_3092_ = v___y_3120_;
v___y_3093_ = v___y_3121_;
v___y_3094_ = v___y_3122_;
v___y_3095_ = v___y_3123_;
v___y_3096_ = v___y_3124_;
v___y_3097_ = v___y_3125_;
v___y_3098_ = v___x_3130_;
goto v___jp_3082_;
}
}
v___jp_3131_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; size_t v_sz_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
lean_inc_ref_n(v___y_3141_, 2);
v___x_3155_ = l_Array_append___redArg(v___y_3141_, v___y_3154_);
lean_dec_ref(v___y_3154_);
lean_inc_n(v___y_3144_, 3);
lean_inc_n(v___y_3149_, 9);
v___x_3156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3156_, 0, v___y_3149_);
lean_ctor_set(v___x_3156_, 1, v___y_3144_);
lean_ctor_set(v___x_3156_, 2, v___x_3155_);
v___x_3157_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
v___x_3158_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
v___x_3159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___y_3149_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__6));
v___x_3161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___y_3149_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_3163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___y_3149_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = l_Nat_reprFast(v___y_3152_);
v___x_3165_ = lean_box(2);
v___x_3166_ = l_Lean_Syntax_mkNumLit(v___x_3164_, v___x_3165_);
v___x_3167_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___y_3149_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = l_Lean_Syntax_node5(v___y_3149_, v___x_3157_, v___x_3159_, v___x_3161_, v___x_3163_, v___x_3166_, v___x_3168_);
v___x_3170_ = l_Lean_Syntax_node1(v___y_3149_, v___y_3144_, v___x_3169_);
v_sz_3171_ = lean_array_size(v___y_3153_);
v___x_3172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_3171_, v___y_3150_, v___y_3153_);
v___x_3173_ = l_Array_append___redArg(v___y_3141_, v___x_3172_);
lean_dec_ref(v___x_3172_);
v___x_3174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3174_, 0, v___y_3149_);
lean_ctor_set(v___x_3174_, 1, v___y_3144_);
lean_ctor_set(v___x_3174_, 2, v___x_3173_);
v___x_3175_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_3176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___y_3149_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = lean_unsigned_to_nat(10u);
v___x_3178_ = lean_mk_empty_array_with_capacity(v___x_3177_);
v___x_3179_ = lean_array_push(v___x_3178_, v___y_3136_);
v___x_3180_ = lean_array_push(v___x_3179_, v___y_3134_);
v___x_3181_ = lean_array_push(v___x_3180_, v___y_3140_);
v___x_3182_ = lean_array_push(v___x_3181_, v___y_3133_);
v___x_3183_ = lean_array_push(v___x_3182_, v___y_3151_);
v___x_3184_ = lean_array_push(v___x_3183_, v___x_3156_);
v___x_3185_ = lean_array_push(v___x_3184_, v___x_3170_);
v___x_3186_ = lean_array_push(v___x_3185_, v___x_3174_);
v___x_3187_ = lean_array_push(v___x_3186_, v___x_3176_);
lean_inc(v___y_3135_);
v___x_3188_ = lean_array_push(v___x_3187_, v___y_3135_);
lean_inc(v___y_3137_);
v___x_3189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3189_, 0, v___y_3149_);
lean_ctor_set(v___x_3189_, 1, v___y_3137_);
lean_ctor_set(v___x_3189_, 2, v___x_3188_);
v___x_3190_ = l_Lean_Elab_Command_elabSyntax(v___x_3189_, v___y_3147_, v___y_3142_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref_known(v___x_3190_, 1);
v___x_3192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3165_);
lean_ctor_set(v___x_3192_, 1, v_a_3191_);
lean_ctor_set(v___x_3192_, 2, v___y_3143_);
v___x_3193_ = l_Lean_Elab_Command_getRef___redArg(v___y_3147_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_a_3194_);
lean_dec_ref_known(v___x_3193_, 1);
v___x_3195_ = l_Lean_SourceInfo_fromRef(v_a_3194_, v___y_3138_);
lean_dec(v_a_3194_);
v___x_3196_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3147_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_quotContext_x3f_3197_; 
lean_dec_ref_known(v___x_3196_, 1);
v_quotContext_x3f_3197_ = lean_ctor_get(v___y_3147_, 5);
if (lean_obj_tag(v_quotContext_x3f_3197_) == 0)
{
lean_object* v___x_3198_; 
v___x_3198_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3142_);
lean_dec_ref(v___x_3198_);
v___y_3112_ = v___y_3132_;
v___y_3113_ = v___y_3135_;
v___y_3114_ = v___x_3195_;
v___y_3115_ = v___y_3139_;
v___y_3116_ = v___y_3141_;
v___y_3117_ = v___y_3142_;
v___y_3118_ = v___y_3144_;
v___y_3119_ = v___y_3146_;
v___y_3120_ = v___y_3147_;
v___y_3121_ = v___y_3145_;
v___y_3122_ = v___y_3148_;
v___y_3123_ = v___x_3192_;
v___y_3124_ = v___x_3167_;
v___y_3125_ = v___x_3175_;
goto v___jp_3111_;
}
else
{
v___y_3112_ = v___y_3132_;
v___y_3113_ = v___y_3135_;
v___y_3114_ = v___x_3195_;
v___y_3115_ = v___y_3139_;
v___y_3116_ = v___y_3141_;
v___y_3117_ = v___y_3142_;
v___y_3118_ = v___y_3144_;
v___y_3119_ = v___y_3146_;
v___y_3120_ = v___y_3147_;
v___y_3121_ = v___y_3145_;
v___y_3122_ = v___y_3148_;
v___y_3123_ = v___x_3192_;
v___y_3124_ = v___x_3167_;
v___y_3125_ = v___x_3175_;
goto v___jp_3111_;
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec(v___x_3195_);
lean_dec_ref_known(v___x_3192_, 3);
lean_dec(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec(v___y_3139_);
lean_dec(v___y_3135_);
v_a_3199_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3196_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3196_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec_ref_known(v___x_3192_, 3);
lean_dec(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec(v___y_3139_);
lean_dec(v___y_3135_);
v_a_3207_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3193_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3193_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_dec(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3139_);
lean_dec(v___y_3135_);
v_a_3215_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3190_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3190_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
v___jp_3223_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
lean_inc_ref(v___y_3234_);
v___x_3247_ = l_Array_append___redArg(v___y_3234_, v___y_3246_);
lean_dec_ref(v___y_3246_);
lean_inc(v___y_3237_);
lean_inc(v___y_3243_);
v___x_3248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3248_, 0, v___y_3243_);
lean_ctor_set(v___x_3248_, 1, v___y_3237_);
lean_ctor_set(v___x_3248_, 2, v___x_3247_);
if (lean_obj_tag(v___y_3233_) == 1)
{
lean_object* v_val_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v_val_3249_ = lean_ctor_get(v___y_3233_, 0);
lean_inc(v_val_3249_);
lean_dec_ref_known(v___y_3233_, 1);
v___x_3250_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
v___x_3251_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___y_3243_, 5);
v___x_3252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___y_3243_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__9));
v___x_3254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___y_3243_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_3256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___y_3243_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___y_3243_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
v___x_3259_ = l_Lean_Syntax_node5(v___y_3243_, v___x_3250_, v___x_3252_, v___x_3254_, v___x_3256_, v_val_3249_, v___x_3258_);
v___x_3260_ = l_Array_mkArray1___redArg(v___x_3259_);
v___y_3132_ = v___y_3224_;
v___y_3133_ = v___y_3225_;
v___y_3134_ = v___y_3226_;
v___y_3135_ = v___y_3227_;
v___y_3136_ = v___y_3228_;
v___y_3137_ = v___y_3229_;
v___y_3138_ = v___y_3230_;
v___y_3139_ = v___y_3231_;
v___y_3140_ = v___y_3232_;
v___y_3141_ = v___y_3234_;
v___y_3142_ = v___y_3235_;
v___y_3143_ = v___y_3236_;
v___y_3144_ = v___y_3237_;
v___y_3145_ = v___y_3240_;
v___y_3146_ = v___y_3239_;
v___y_3147_ = v___y_3238_;
v___y_3148_ = v___y_3241_;
v___y_3149_ = v___y_3243_;
v___y_3150_ = v___y_3242_;
v___y_3151_ = v___x_3248_;
v___y_3152_ = v___y_3245_;
v___y_3153_ = v___y_3244_;
v___y_3154_ = v___x_3260_;
goto v___jp_3131_;
}
else
{
lean_object* v___x_3261_; 
lean_dec(v___y_3233_);
v___x_3261_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3132_ = v___y_3224_;
v___y_3133_ = v___y_3225_;
v___y_3134_ = v___y_3226_;
v___y_3135_ = v___y_3227_;
v___y_3136_ = v___y_3228_;
v___y_3137_ = v___y_3229_;
v___y_3138_ = v___y_3230_;
v___y_3139_ = v___y_3231_;
v___y_3140_ = v___y_3232_;
v___y_3141_ = v___y_3234_;
v___y_3142_ = v___y_3235_;
v___y_3143_ = v___y_3236_;
v___y_3144_ = v___y_3237_;
v___y_3145_ = v___y_3240_;
v___y_3146_ = v___y_3239_;
v___y_3147_ = v___y_3238_;
v___y_3148_ = v___y_3241_;
v___y_3149_ = v___y_3243_;
v___y_3150_ = v___y_3242_;
v___y_3151_ = v___x_3248_;
v___y_3152_ = v___y_3245_;
v___y_3153_ = v___y_3244_;
v___y_3154_ = v___x_3261_;
goto v___jp_3131_;
}
}
v___jp_3262_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_inc_ref(v___y_3270_);
v___x_3287_ = l_Array_append___redArg(v___y_3270_, v___y_3286_);
lean_dec_ref(v___y_3286_);
lean_inc(v___y_3274_);
lean_inc(v___y_3282_);
v___x_3288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3288_, 0, v___y_3282_);
lean_ctor_set(v___x_3288_, 1, v___y_3274_);
lean_ctor_set(v___x_3288_, 2, v___x_3287_);
v___x_3289_ = l_Lean_SourceInfo_fromRef(v___y_3275_, v___x_3079_);
lean_dec(v___y_3275_);
lean_inc_ref(v___y_3283_);
v___x_3290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
lean_ctor_set(v___x_3290_, 1, v___y_3283_);
if (lean_obj_tag(v___y_3279_) == 1)
{
lean_object* v_val_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_val_3291_ = lean_ctor_get(v___y_3279_, 0);
lean_inc(v_val_3291_);
lean_dec_ref_known(v___y_3279_, 1);
v___x_3292_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
v___x_3293_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc_n(v___y_3282_, 2);
v___x_3294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___y_3282_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = l_Lean_Syntax_node2(v___y_3282_, v___x_3292_, v___x_3294_, v_val_3291_);
v___x_3296_ = l_Array_mkArray1___redArg(v___x_3295_);
v___y_3224_ = v___y_3263_;
v___y_3225_ = v___x_3290_;
v___y_3226_ = v___x_3288_;
v___y_3227_ = v___y_3264_;
v___y_3228_ = v___y_3265_;
v___y_3229_ = v___y_3266_;
v___y_3230_ = v___y_3267_;
v___y_3231_ = v___y_3268_;
v___y_3232_ = v___y_3269_;
v___y_3233_ = v___y_3271_;
v___y_3234_ = v___y_3270_;
v___y_3235_ = v___y_3272_;
v___y_3236_ = v___y_3273_;
v___y_3237_ = v___y_3274_;
v___y_3238_ = v___y_3278_;
v___y_3239_ = v___y_3277_;
v___y_3240_ = v___y_3276_;
v___y_3241_ = v___y_3280_;
v___y_3242_ = v___y_3281_;
v___y_3243_ = v___y_3282_;
v___y_3244_ = v___y_3285_;
v___y_3245_ = v___y_3284_;
v___y_3246_ = v___x_3296_;
goto v___jp_3223_;
}
else
{
lean_object* v___x_3297_; 
lean_dec(v___y_3279_);
v___x_3297_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3224_ = v___y_3263_;
v___y_3225_ = v___x_3290_;
v___y_3226_ = v___x_3288_;
v___y_3227_ = v___y_3264_;
v___y_3228_ = v___y_3265_;
v___y_3229_ = v___y_3266_;
v___y_3230_ = v___y_3267_;
v___y_3231_ = v___y_3268_;
v___y_3232_ = v___y_3269_;
v___y_3233_ = v___y_3271_;
v___y_3234_ = v___y_3270_;
v___y_3235_ = v___y_3272_;
v___y_3236_ = v___y_3273_;
v___y_3237_ = v___y_3274_;
v___y_3238_ = v___y_3278_;
v___y_3239_ = v___y_3277_;
v___y_3240_ = v___y_3276_;
v___y_3241_ = v___y_3280_;
v___y_3242_ = v___y_3281_;
v___y_3243_ = v___y_3282_;
v___y_3244_ = v___y_3285_;
v___y_3245_ = v___y_3284_;
v___y_3246_ = v___x_3297_;
goto v___jp_3223_;
}
}
v___jp_3298_:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
lean_inc_ref(v___y_3305_);
v___x_3323_ = l_Array_append___redArg(v___y_3305_, v___y_3322_);
lean_dec_ref(v___y_3322_);
lean_inc(v___y_3309_);
lean_inc(v___y_3317_);
v___x_3324_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3324_, 0, v___y_3317_);
lean_ctor_set(v___x_3324_, 1, v___y_3309_);
lean_ctor_set(v___x_3324_, 2, v___x_3323_);
if (lean_obj_tag(v___y_3319_) == 1)
{
lean_object* v_val_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_val_3325_ = lean_ctor_get(v___y_3319_, 0);
lean_inc(v_val_3325_);
lean_dec_ref_known(v___y_3319_, 1);
v___x_3326_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_3299_);
v___x_3327_ = l_Lean_Name_mkStr4(v___x_3036_, v___x_3037_, v___y_3299_, v___x_3326_);
v___x_3328_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___y_3317_, 4);
v___x_3329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___y_3317_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
lean_inc_ref(v___y_3305_);
v___x_3330_ = l_Array_append___redArg(v___y_3305_, v_val_3325_);
lean_dec(v_val_3325_);
lean_inc(v___y_3309_);
v___x_3331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3331_, 0, v___y_3317_);
lean_ctor_set(v___x_3331_, 1, v___y_3309_);
lean_ctor_set(v___x_3331_, 2, v___x_3330_);
v___x_3332_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_3333_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___y_3317_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v___x_3334_ = l_Lean_Syntax_node3(v___y_3317_, v___x_3327_, v___x_3329_, v___x_3331_, v___x_3333_);
v___x_3335_ = l_Array_mkArray1___redArg(v___x_3334_);
v___y_3263_ = v___y_3299_;
v___y_3264_ = v___y_3300_;
v___y_3265_ = v___x_3324_;
v___y_3266_ = v___y_3301_;
v___y_3267_ = v___y_3302_;
v___y_3268_ = v___y_3303_;
v___y_3269_ = v___y_3304_;
v___y_3270_ = v___y_3305_;
v___y_3271_ = v___y_3306_;
v___y_3272_ = v___y_3307_;
v___y_3273_ = v___y_3308_;
v___y_3274_ = v___y_3309_;
v___y_3275_ = v___y_3310_;
v___y_3276_ = v___y_3313_;
v___y_3277_ = v___y_3312_;
v___y_3278_ = v___y_3311_;
v___y_3279_ = v___y_3314_;
v___y_3280_ = v___y_3315_;
v___y_3281_ = v___y_3316_;
v___y_3282_ = v___y_3317_;
v___y_3283_ = v___y_3318_;
v___y_3284_ = v___y_3321_;
v___y_3285_ = v___y_3320_;
v___y_3286_ = v___x_3335_;
goto v___jp_3262_;
}
else
{
lean_object* v___x_3336_; 
lean_dec(v___y_3319_);
v___x_3336_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3263_ = v___y_3299_;
v___y_3264_ = v___y_3300_;
v___y_3265_ = v___x_3324_;
v___y_3266_ = v___y_3301_;
v___y_3267_ = v___y_3302_;
v___y_3268_ = v___y_3303_;
v___y_3269_ = v___y_3304_;
v___y_3270_ = v___y_3305_;
v___y_3271_ = v___y_3306_;
v___y_3272_ = v___y_3307_;
v___y_3273_ = v___y_3308_;
v___y_3274_ = v___y_3309_;
v___y_3275_ = v___y_3310_;
v___y_3276_ = v___y_3313_;
v___y_3277_ = v___y_3312_;
v___y_3278_ = v___y_3311_;
v___y_3279_ = v___y_3314_;
v___y_3280_ = v___y_3315_;
v___y_3281_ = v___y_3316_;
v___y_3282_ = v___y_3317_;
v___y_3283_ = v___y_3318_;
v___y_3284_ = v___y_3321_;
v___y_3285_ = v___y_3320_;
v___y_3286_ = v___x_3336_;
goto v___jp_3262_;
}
}
v___jp_3337_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3357_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__12));
v___x_3358_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__13));
v___x_3359_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_3360_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v___y_3341_) == 1)
{
lean_object* v_val_3361_; lean_object* v___x_3362_; 
v_val_3361_ = lean_ctor_get(v___y_3341_, 0);
lean_inc(v_val_3361_);
v___x_3362_ = l_Array_mkArray1___redArg(v_val_3361_);
v___y_3299_ = v___y_3338_;
v___y_3300_ = v___y_3339_;
v___y_3301_ = v___x_3358_;
v___y_3302_ = v___y_3340_;
v___y_3303_ = v___y_3341_;
v___y_3304_ = v___y_3342_;
v___y_3305_ = v___x_3360_;
v___y_3306_ = v___y_3343_;
v___y_3307_ = v___y_3344_;
v___y_3308_ = v___y_3345_;
v___y_3309_ = v___x_3359_;
v___y_3310_ = v___y_3346_;
v___y_3311_ = v___y_3347_;
v___y_3312_ = v___y_3348_;
v___y_3313_ = v___y_3349_;
v___y_3314_ = v___y_3350_;
v___y_3315_ = v___y_3351_;
v___y_3316_ = v___y_3353_;
v___y_3317_ = v___y_3352_;
v___y_3318_ = v___x_3357_;
v___y_3319_ = v___y_3354_;
v___y_3320_ = v___y_3356_;
v___y_3321_ = v___y_3355_;
v___y_3322_ = v___x_3362_;
goto v___jp_3298_;
}
else
{
lean_object* v___x_3363_; 
v___x_3363_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3299_ = v___y_3338_;
v___y_3300_ = v___y_3339_;
v___y_3301_ = v___x_3358_;
v___y_3302_ = v___y_3340_;
v___y_3303_ = v___y_3341_;
v___y_3304_ = v___y_3342_;
v___y_3305_ = v___x_3360_;
v___y_3306_ = v___y_3343_;
v___y_3307_ = v___y_3344_;
v___y_3308_ = v___y_3345_;
v___y_3309_ = v___x_3359_;
v___y_3310_ = v___y_3346_;
v___y_3311_ = v___y_3347_;
v___y_3312_ = v___y_3348_;
v___y_3313_ = v___y_3349_;
v___y_3314_ = v___y_3350_;
v___y_3315_ = v___y_3351_;
v___y_3316_ = v___y_3353_;
v___y_3317_ = v___y_3352_;
v___y_3318_ = v___x_3357_;
v___y_3319_ = v___y_3354_;
v___y_3320_ = v___y_3356_;
v___y_3321_ = v___y_3355_;
v___y_3322_ = v___x_3363_;
goto v___jp_3298_;
}
}
v___jp_3364_:
{
lean_object* v___x_3381_; lean_object* v_args_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3381_ = l_Lean_Syntax_getArg(v___y_3376_, v___y_3368_);
lean_dec(v___y_3376_);
v_args_3382_ = l_Lean_Syntax_getArgs(v___y_3375_);
lean_dec(v___y_3375_);
v___x_3383_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_3383_, 0, v___y_3367_);
v___x_3384_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v___x_3383_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; size_t v_sz_3386_; size_t v___x_3387_; lean_object* v___x_3388_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v_sz_3386_ = lean_array_size(v_args_3382_);
v___x_3387_ = ((size_t)0ULL);
v___x_3388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_3386_, v___x_3387_, v_args_3382_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; lean_object* v_fst_3391_; lean_object* v_snd_3392_; lean_object* v___x_3393_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3390_ = l_Array_unzip___redArg(v_a_3389_);
lean_dec(v_a_3389_);
v_fst_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_fst_3391_);
v_snd_3392_ = lean_ctor_get(v___x_3390_, 1);
lean_inc(v_snd_3392_);
lean_dec_ref(v___x_3390_);
v___x_3393_ = l_Lean_Elab_Command_getRef___redArg(v___y_3379_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; uint8_t v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
lean_dec_ref_known(v___x_3393_, 1);
v___x_3395_ = 0;
v___x_3396_ = l_Lean_SourceInfo_fromRef(v_a_3394_, v___x_3395_);
lean_dec(v_a_3394_);
v___x_3397_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3379_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_quotContext_x3f_3398_; 
lean_dec_ref_known(v___x_3397_, 1);
v_quotContext_x3f_3398_ = lean_ctor_get(v___y_3379_, 5);
if (lean_obj_tag(v_quotContext_x3f_3398_) == 0)
{
lean_object* v___x_3399_; 
v___x_3399_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3380_);
lean_dec_ref(v___x_3399_);
v___y_3338_ = v___y_3365_;
v___y_3339_ = v___y_3366_;
v___y_3340_ = v___x_3395_;
v___y_3341_ = v___y_3369_;
v___y_3342_ = v___y_3370_;
v___y_3343_ = v___y_3371_;
v___y_3344_ = v___y_3380_;
v___y_3345_ = v_snd_3392_;
v___y_3346_ = v___y_3372_;
v___y_3347_ = v___y_3379_;
v___y_3348_ = v_expectedType_x3f_3378_;
v___y_3349_ = v___x_3381_;
v___y_3350_ = v___y_3373_;
v___y_3351_ = v___y_3374_;
v___y_3352_ = v___x_3396_;
v___y_3353_ = v___x_3387_;
v___y_3354_ = v___y_3377_;
v___y_3355_ = v_a_3385_;
v___y_3356_ = v_fst_3391_;
goto v___jp_3337_;
}
else
{
v___y_3338_ = v___y_3365_;
v___y_3339_ = v___y_3366_;
v___y_3340_ = v___x_3395_;
v___y_3341_ = v___y_3369_;
v___y_3342_ = v___y_3370_;
v___y_3343_ = v___y_3371_;
v___y_3344_ = v___y_3380_;
v___y_3345_ = v_snd_3392_;
v___y_3346_ = v___y_3372_;
v___y_3347_ = v___y_3379_;
v___y_3348_ = v_expectedType_x3f_3378_;
v___y_3349_ = v___x_3381_;
v___y_3350_ = v___y_3373_;
v___y_3351_ = v___y_3374_;
v___y_3352_ = v___x_3396_;
v___y_3353_ = v___x_3387_;
v___y_3354_ = v___y_3377_;
v___y_3355_ = v_a_3385_;
v___y_3356_ = v_fst_3391_;
goto v___jp_3337_;
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v___x_3396_);
lean_dec(v_snd_3392_);
lean_dec(v_fst_3391_);
lean_dec(v_a_3385_);
lean_dec(v___x_3381_);
lean_dec(v_expectedType_x3f_3378_);
lean_dec(v___y_3377_);
lean_dec(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec(v___y_3366_);
v_a_3400_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3397_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3397_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec(v_snd_3392_);
lean_dec(v_fst_3391_);
lean_dec(v_a_3385_);
lean_dec(v___x_3381_);
lean_dec(v_expectedType_x3f_3378_);
lean_dec(v___y_3377_);
lean_dec(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec(v___y_3366_);
v_a_3408_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3393_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3393_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec(v_a_3385_);
lean_dec(v___x_3381_);
lean_dec(v_expectedType_x3f_3378_);
lean_dec(v___y_3377_);
lean_dec(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec(v___y_3366_);
v_a_3416_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3388_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3388_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v_args_3382_);
lean_dec(v___x_3381_);
lean_dec(v_expectedType_x3f_3378_);
lean_dec(v___y_3377_);
lean_dec(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec(v___y_3366_);
v_a_3424_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3384_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3384_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
v___jp_3432_:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; 
v___x_3447_ = lean_unsigned_to_nat(8u);
v___x_3448_ = l_Lean_Syntax_getArg(v_x_3032_, v___x_3447_);
v___x_3449_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__15));
lean_inc(v___x_3448_);
v___x_3450_ = l_Lean_Syntax_isOfKind(v___x_3448_, v___x_3449_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; 
lean_dec(v___x_3448_);
lean_dec(v_prio_x3f_3444_);
lean_dec(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec(v___y_3436_);
lean_dec(v_x_3032_);
v___x_3451_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3451_;
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; 
v___x_3452_ = lean_unsigned_to_nat(7u);
v___x_3453_ = l_Lean_Syntax_getArg(v_x_3032_, v___x_3452_);
lean_dec(v_x_3032_);
v___x_3454_ = l_Lean_Syntax_getArg(v___x_3448_, v___y_3434_);
v___x_3455_ = l_Lean_Syntax_getArg(v___x_3448_, v___y_3435_);
v___x_3456_ = l_Lean_Syntax_isNone(v___x_3455_);
if (v___x_3456_ == 0)
{
uint8_t v___x_3457_; 
lean_inc(v___x_3455_);
v___x_3457_ = l_Lean_Syntax_matchesNull(v___x_3455_, v___y_3435_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; 
lean_dec(v___x_3455_);
lean_dec(v___x_3454_);
lean_dec(v___x_3453_);
lean_dec(v___x_3448_);
lean_dec(v_prio_x3f_3444_);
lean_dec(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec(v___y_3436_);
v___x_3458_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3458_;
}
else
{
lean_object* v_expectedType_x3f_3459_; lean_object* v___x_3460_; 
v_expectedType_x3f_3459_ = l_Lean_Syntax_getArg(v___x_3455_, v___y_3434_);
lean_dec(v___x_3455_);
v___x_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3460_, 0, v_expectedType_x3f_3459_);
v___y_3365_ = v___y_3433_;
v___y_3366_ = v___x_3454_;
v___y_3367_ = v_prio_x3f_3444_;
v___y_3368_ = v___y_3440_;
v___y_3369_ = v___y_3439_;
v___y_3370_ = v___y_3441_;
v___y_3371_ = v___y_3442_;
v___y_3372_ = v___y_3443_;
v___y_3373_ = v___y_3436_;
v___y_3374_ = v___y_3437_;
v___y_3375_ = v___x_3453_;
v___y_3376_ = v___x_3448_;
v___y_3377_ = v___y_3438_;
v_expectedType_x3f_3378_ = v___x_3460_;
v___y_3379_ = v___y_3445_;
v___y_3380_ = v___y_3446_;
goto v___jp_3364_;
}
}
else
{
lean_object* v___x_3461_; 
lean_dec(v___x_3455_);
v___x_3461_ = lean_box(0);
v___y_3365_ = v___y_3433_;
v___y_3366_ = v___x_3454_;
v___y_3367_ = v_prio_x3f_3444_;
v___y_3368_ = v___y_3440_;
v___y_3369_ = v___y_3439_;
v___y_3370_ = v___y_3441_;
v___y_3371_ = v___y_3442_;
v___y_3372_ = v___y_3443_;
v___y_3373_ = v___y_3436_;
v___y_3374_ = v___y_3437_;
v___y_3375_ = v___x_3453_;
v___y_3376_ = v___x_3448_;
v___y_3377_ = v___y_3438_;
v_expectedType_x3f_3378_ = v___x_3461_;
v___y_3379_ = v___y_3445_;
v___y_3380_ = v___y_3446_;
goto v___jp_3364_;
}
}
}
v___jp_3462_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; uint8_t v___x_3479_; 
v___x_3477_ = lean_unsigned_to_nat(6u);
v___x_3478_ = l_Lean_Syntax_getArg(v_x_3032_, v___x_3477_);
v___x_3479_ = l_Lean_Syntax_isNone(v___x_3478_);
if (v___x_3479_ == 0)
{
uint8_t v___x_3480_; 
lean_inc(v___x_3478_);
v___x_3480_ = l_Lean_Syntax_matchesNull(v___x_3478_, v___y_3464_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; 
lean_dec(v___x_3478_);
lean_dec(v_name_x3f_3474_);
lean_dec(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec(v___y_3468_);
lean_dec(v___y_3465_);
lean_dec(v_x_3032_);
v___x_3481_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3481_;
}
else
{
lean_object* v___x_3482_; lean_object* v___x_3483_; uint8_t v___x_3484_; 
v___x_3482_ = l_Lean_Syntax_getArg(v___x_3478_, v___x_3081_);
lean_dec(v___x_3478_);
v___x_3483_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
lean_inc(v___x_3482_);
v___x_3484_ = l_Lean_Syntax_isOfKind(v___x_3482_, v___x_3483_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; 
lean_dec(v___x_3482_);
lean_dec(v_name_x3f_3474_);
lean_dec(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec(v___y_3468_);
lean_dec(v___y_3465_);
lean_dec(v_x_3032_);
v___x_3485_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3485_;
}
else
{
lean_object* v_prio_x3f_3486_; lean_object* v___x_3487_; 
v_prio_x3f_3486_ = l_Lean_Syntax_getArg(v___x_3482_, v___y_3469_);
lean_dec(v___x_3482_);
v___x_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3487_, 0, v_prio_x3f_3486_);
v___y_3433_ = v___y_3463_;
v___y_3434_ = v___y_3464_;
v___y_3435_ = v___y_3466_;
v___y_3436_ = v___y_3465_;
v___y_3437_ = v___y_3467_;
v___y_3438_ = v___y_3468_;
v___y_3439_ = v___y_3471_;
v___y_3440_ = v___y_3470_;
v___y_3441_ = v___y_3472_;
v___y_3442_ = v_name_x3f_3474_;
v___y_3443_ = v___y_3473_;
v_prio_x3f_3444_ = v___x_3487_;
v___y_3445_ = v___y_3475_;
v___y_3446_ = v___y_3476_;
goto v___jp_3432_;
}
}
}
else
{
lean_object* v___x_3488_; 
lean_dec(v___x_3478_);
v___x_3488_ = lean_box(0);
v___y_3433_ = v___y_3463_;
v___y_3434_ = v___y_3464_;
v___y_3435_ = v___y_3466_;
v___y_3436_ = v___y_3465_;
v___y_3437_ = v___y_3467_;
v___y_3438_ = v___y_3468_;
v___y_3439_ = v___y_3471_;
v___y_3440_ = v___y_3470_;
v___y_3441_ = v___y_3472_;
v___y_3442_ = v_name_x3f_3474_;
v___y_3443_ = v___y_3473_;
v_prio_x3f_3444_ = v___x_3488_;
v___y_3445_ = v___y_3475_;
v___y_3446_ = v___y_3476_;
goto v___jp_3432_;
}
}
v___jp_3489_:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; uint8_t v___x_3505_; 
v___x_3503_ = lean_unsigned_to_nat(5u);
v___x_3504_ = l_Lean_Syntax_getArg(v_x_3032_, v___x_3503_);
v___x_3505_ = l_Lean_Syntax_isNone(v___x_3504_);
if (v___x_3505_ == 0)
{
uint8_t v___x_3506_; 
lean_inc(v___x_3504_);
v___x_3506_ = l_Lean_Syntax_matchesNull(v___x_3504_, v___y_3491_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; 
lean_dec(v___x_3504_);
lean_dec(v_prec_x3f_3500_);
lean_dec(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec(v_x_3032_);
v___x_3507_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3507_;
}
else
{
lean_object* v___x_3508_; lean_object* v___x_3509_; uint8_t v___x_3510_; 
v___x_3508_ = l_Lean_Syntax_getArg(v___x_3504_, v___x_3081_);
lean_dec(v___x_3504_);
v___x_3509_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
lean_inc(v___x_3508_);
v___x_3510_ = l_Lean_Syntax_isOfKind(v___x_3508_, v___x_3509_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; 
lean_dec(v___x_3508_);
lean_dec(v_prec_x3f_3500_);
lean_dec(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec(v_x_3032_);
v___x_3511_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3511_;
}
else
{
lean_object* v_name_x3f_3512_; lean_object* v___x_3513_; 
v_name_x3f_3512_ = l_Lean_Syntax_getArg(v___x_3508_, v___y_3497_);
lean_dec(v___x_3508_);
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v_name_x3f_3512_);
v___y_3463_ = v___y_3490_;
v___y_3464_ = v___y_3491_;
v___y_3465_ = v_prec_x3f_3500_;
v___y_3466_ = v___y_3492_;
v___y_3467_ = v___y_3493_;
v___y_3468_ = v___y_3494_;
v___y_3469_ = v___y_3497_;
v___y_3470_ = v___y_3496_;
v___y_3471_ = v___y_3495_;
v___y_3472_ = v___y_3498_;
v___y_3473_ = v___y_3499_;
v_name_x3f_3474_ = v___x_3513_;
v___y_3475_ = v___y_3501_;
v___y_3476_ = v___y_3502_;
goto v___jp_3462_;
}
}
}
else
{
lean_object* v___x_3514_; 
lean_dec(v___x_3504_);
v___x_3514_ = lean_box(0);
v___y_3463_ = v___y_3490_;
v___y_3464_ = v___y_3491_;
v___y_3465_ = v_prec_x3f_3500_;
v___y_3466_ = v___y_3492_;
v___y_3467_ = v___y_3493_;
v___y_3468_ = v___y_3494_;
v___y_3469_ = v___y_3497_;
v___y_3470_ = v___y_3496_;
v___y_3471_ = v___y_3495_;
v___y_3472_ = v___y_3498_;
v___y_3473_ = v___y_3499_;
v_name_x3f_3474_ = v___x_3514_;
v___y_3475_ = v___y_3501_;
v___y_3476_ = v___y_3502_;
goto v___jp_3462_;
}
}
v___jp_3515_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v___x_3521_ = lean_unsigned_to_nat(2u);
v___x_3522_ = l_Lean_Syntax_getArg(v_x_3032_, v___x_3521_);
v___x_3523_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_3524_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v___x_3522_);
v___x_3525_ = l_Lean_Syntax_isOfKind(v___x_3522_, v___x_3524_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; 
lean_dec(v___x_3522_);
lean_dec(v_attrs_x3f_3518_);
lean_dec(v___y_3517_);
lean_dec(v_x_3032_);
v___x_3526_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3526_;
}
else
{
lean_object* v___x_3527_; lean_object* v_tk_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; uint8_t v___x_3531_; 
v___x_3527_ = lean_unsigned_to_nat(3u);
v_tk_3528_ = l_Lean_Syntax_getArg(v_x_3032_, v___x_3527_);
v___x_3529_ = lean_unsigned_to_nat(4u);
v___x_3530_ = l_Lean_Syntax_getArg(v_x_3032_, v___x_3529_);
v___x_3531_ = l_Lean_Syntax_isNone(v___x_3530_);
if (v___x_3531_ == 0)
{
uint8_t v___x_3532_; 
lean_inc(v___x_3530_);
v___x_3532_ = l_Lean_Syntax_matchesNull(v___x_3530_, v___y_3516_);
if (v___x_3532_ == 0)
{
lean_object* v___x_3533_; 
lean_dec(v___x_3530_);
lean_dec(v_tk_3528_);
lean_dec(v___x_3522_);
lean_dec(v_attrs_x3f_3518_);
lean_dec(v___y_3517_);
lean_dec(v_x_3032_);
v___x_3533_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3533_;
}
else
{
lean_object* v___x_3534_; lean_object* v___x_3535_; uint8_t v___x_3536_; 
v___x_3534_ = l_Lean_Syntax_getArg(v___x_3530_, v___x_3081_);
lean_dec(v___x_3530_);
v___x_3535_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
lean_inc(v___x_3534_);
v___x_3536_ = l_Lean_Syntax_isOfKind(v___x_3534_, v___x_3535_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; 
lean_dec(v___x_3534_);
lean_dec(v_tk_3528_);
lean_dec(v___x_3522_);
lean_dec(v_attrs_x3f_3518_);
lean_dec(v___y_3517_);
lean_dec(v_x_3032_);
v___x_3537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3537_;
}
else
{
lean_object* v_prec_x3f_3538_; lean_object* v___x_3539_; 
v_prec_x3f_3538_ = l_Lean_Syntax_getArg(v___x_3534_, v___y_3516_);
lean_dec(v___x_3534_);
v___x_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3539_, 0, v_prec_x3f_3538_);
v___y_3490_ = v___x_3523_;
v___y_3491_ = v___y_3516_;
v___y_3492_ = v___x_3521_;
v___y_3493_ = v___x_3524_;
v___y_3494_ = v_attrs_x3f_3518_;
v___y_3495_ = v___y_3517_;
v___y_3496_ = v___x_3529_;
v___y_3497_ = v___x_3527_;
v___y_3498_ = v___x_3522_;
v___y_3499_ = v_tk_3528_;
v_prec_x3f_3500_ = v___x_3539_;
v___y_3501_ = v___y_3519_;
v___y_3502_ = v___y_3520_;
goto v___jp_3489_;
}
}
}
else
{
lean_object* v___x_3540_; 
lean_dec(v___x_3530_);
v___x_3540_ = lean_box(0);
v___y_3490_ = v___x_3523_;
v___y_3491_ = v___y_3516_;
v___y_3492_ = v___x_3521_;
v___y_3493_ = v___x_3524_;
v___y_3494_ = v_attrs_x3f_3518_;
v___y_3495_ = v___y_3517_;
v___y_3496_ = v___x_3529_;
v___y_3497_ = v___x_3527_;
v___y_3498_ = v___x_3522_;
v___y_3499_ = v_tk_3528_;
v_prec_x3f_3500_ = v___x_3540_;
v___y_3501_ = v___y_3519_;
v___y_3502_ = v___y_3520_;
goto v___jp_3489_;
}
}
}
v___jp_3541_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v___x_3545_ = lean_unsigned_to_nat(1u);
v___x_3546_ = l_Lean_Syntax_getArg(v_x_3032_, v___x_3545_);
v___x_3547_ = l_Lean_Syntax_isNone(v___x_3546_);
if (v___x_3547_ == 0)
{
uint8_t v___x_3548_; 
lean_inc(v___x_3546_);
v___x_3548_ = l_Lean_Syntax_matchesNull(v___x_3546_, v___x_3545_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
lean_dec(v___x_3546_);
lean_dec(v_doc_x3f_3542_);
lean_dec(v_x_3032_);
v___x_3549_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3549_;
}
else
{
lean_object* v___x_3550_; lean_object* v___x_3551_; uint8_t v___x_3552_; 
v___x_3550_ = l_Lean_Syntax_getArg(v___x_3546_, v___x_3081_);
lean_dec(v___x_3546_);
v___x_3551_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(v___x_3550_);
v___x_3552_ = l_Lean_Syntax_isOfKind(v___x_3550_, v___x_3551_);
if (v___x_3552_ == 0)
{
lean_object* v___x_3553_; 
lean_dec(v___x_3550_);
lean_dec(v_doc_x3f_3542_);
lean_dec(v_x_3032_);
v___x_3553_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3553_;
}
else
{
lean_object* v___x_3554_; lean_object* v_attrs_x3f_3555_; lean_object* v___x_3556_; 
v___x_3554_ = l_Lean_Syntax_getArg(v___x_3550_, v___x_3545_);
lean_dec(v___x_3550_);
v_attrs_x3f_3555_ = l_Lean_Syntax_getArgs(v___x_3554_);
lean_dec(v___x_3554_);
v___x_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3556_, 0, v_attrs_x3f_3555_);
v___y_3516_ = v___x_3545_;
v___y_3517_ = v_doc_x3f_3542_;
v_attrs_x3f_3518_ = v___x_3556_;
v___y_3519_ = v___y_3543_;
v___y_3520_ = v___y_3544_;
goto v___jp_3515_;
}
}
}
else
{
lean_object* v___x_3557_; 
lean_dec(v___x_3546_);
v___x_3557_ = lean_box(0);
v___y_3516_ = v___x_3545_;
v___y_3517_ = v_doc_x3f_3542_;
v_attrs_x3f_3518_ = v___x_3557_;
v___y_3519_ = v___y_3543_;
v___y_3520_ = v___y_3544_;
goto v___jp_3515_;
}
}
}
v___jp_3038_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
lean_inc_ref(v___y_3044_);
v___x_3055_ = l_Array_append___redArg(v___y_3044_, v___y_3054_);
lean_dec_ref(v___y_3054_);
lean_inc_n(v___y_3047_, 4);
lean_inc_n(v___y_3040_, 11);
v___x_3056_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3056_, 0, v___y_3040_);
lean_ctor_set(v___x_3056_, 1, v___y_3047_);
lean_ctor_set(v___x_3056_, 2, v___x_3055_);
v___x_3057_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc_ref_n(v___y_3039_, 3);
v___x_3058_ = l_Lean_Name_mkStr4(v___x_3036_, v___x_3037_, v___y_3039_, v___x_3057_);
v___x_3059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_3060_ = l_Lean_Name_mkStr4(v___x_3036_, v___x_3037_, v___y_3039_, v___x_3059_);
v___x_3061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_3062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___y_3040_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__0));
v___x_3064_ = l_Lean_Name_mkStr4(v___x_3036_, v___x_3037_, v___y_3039_, v___x_3063_);
v___x_3065_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__1));
v___x_3066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___y_3040_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
lean_inc_ref(v___y_3053_);
v___x_3067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___y_3040_);
lean_ctor_set(v___x_3067_, 1, v___y_3053_);
v___x_3068_ = l_Lean_Syntax_node3(v___y_3040_, v___x_3064_, v___x_3066_, v___y_3052_, v___x_3067_);
v___x_3069_ = l_Lean_Syntax_node1(v___y_3040_, v___y_3047_, v___x_3068_);
v___x_3070_ = l_Lean_Syntax_node1(v___y_3040_, v___y_3047_, v___x_3069_);
v___x_3071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_3072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___y_3040_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = l_Lean_Syntax_node4(v___y_3040_, v___x_3060_, v___x_3062_, v___x_3070_, v___x_3072_, v___y_3050_);
v___x_3074_ = l_Lean_Syntax_node1(v___y_3040_, v___y_3047_, v___x_3073_);
v___x_3075_ = l_Lean_Syntax_node1(v___y_3040_, v___x_3058_, v___x_3074_);
lean_inc(v___y_3048_);
lean_inc(v___y_3041_);
v___x_3076_ = l_Lean_Syntax_node8(v___y_3040_, v___y_3041_, v___y_3043_, v___y_3048_, v___y_3045_, v___y_3042_, v___y_3048_, v___y_3051_, v___x_3056_, v___x_3075_);
v___x_3077_ = l_Lean_Elab_Command_elabCommand(v___x_3076_, v___y_3049_, v___y_3046_);
return v___x_3077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object* v_x_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_Elab_Command_elabElab(v_x_3570_, v_a_3571_, v_a_3572_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object* v_00_u03b1_3575_, lean_object* v_x_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_3576_, v___y_3578_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3580_, lean_object* v_x_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(v_00_u03b1_3580_, v_x_3581_, v___y_3582_, v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec_ref(v_x_3581_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object* v_00_u03b1_3585_, lean_object* v_ref_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_3586_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object* v_00_u03b1_3591_, lean_object* v_ref_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(v_00_u03b1_3591_, v_ref_3592_, v___y_3593_, v___y_3594_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object* v_00_u03b1_3597_, lean_object* v_x_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_3598_, v___y_3599_, v___y_3600_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object* v_00_u03b1_3603_, lean_object* v_x_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(v_00_u03b1_3603_, v_x_3604_, v___y_3605_, v___y_3606_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object* v_as_3609_, lean_object* v_as_x27_3610_, lean_object* v_b_3611_, lean_object* v_a_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_3610_, v_b_3611_, v___y_3613_, v___y_3614_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object* v_as_3617_, lean_object* v_as_x27_3618_, lean_object* v_b_3619_, lean_object* v_a_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(v_as_3617_, v_as_x27_3618_, v_b_3619_, v_a_3620_, v___y_3621_, v___y_3622_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v_as_x27_3618_);
lean_dec(v_as_3617_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3625_, lean_object* v_m_3626_, lean_object* v_a_3627_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_3626_, v_a_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3629_, lean_object* v_m_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(v_00_u03b2_3629_, v_m_3630_, v_a_3631_);
lean_dec(v_a_3631_);
lean_dec_ref(v_m_3630_);
return v_res_3632_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_3633_, lean_object* v_x_3634_, lean_object* v_x_3635_){
_start:
{
uint8_t v___x_3636_; 
v___x_3636_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_3634_, v_x_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3637_, lean_object* v_x_3638_, lean_object* v_x_3639_){
_start:
{
uint8_t v_res_3640_; lean_object* v_r_3641_; 
v_res_3640_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(v_00_u03b2_3637_, v_x_3638_, v_x_3639_);
lean_dec_ref(v_x_3639_);
lean_dec_ref(v_x_3638_);
v_r_3641_ = lean_box(v_res_3640_);
return v_r_3641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_3642_, lean_object* v_a_3643_, lean_object* v_x_3644_){
_start:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_3643_, v_x_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_3646_, lean_object* v_a_3647_, lean_object* v_x_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(v_00_u03b2_3646_, v_a_3647_, v_x_3648_);
lean_dec(v_x_3648_);
lean_dec(v_a_3647_);
return v_res_3649_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(lean_object* v_00_u03b2_3650_, lean_object* v_x_3651_, size_t v_x_3652_, lean_object* v_x_3653_){
_start:
{
uint8_t v___x_3654_; 
v___x_3654_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_3651_, v_x_3652_, v_x_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3655_, lean_object* v_x_3656_, lean_object* v_x_3657_, lean_object* v_x_3658_){
_start:
{
size_t v_x_19034__boxed_3659_; uint8_t v_res_3660_; lean_object* v_r_3661_; 
v_x_19034__boxed_3659_ = lean_unbox_usize(v_x_3657_);
lean_dec(v_x_3657_);
v_res_3660_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(v_00_u03b2_3655_, v_x_3656_, v_x_19034__boxed_3659_, v_x_3658_);
lean_dec_ref(v_x_3658_);
lean_dec_ref(v_x_3656_);
v_r_3661_ = lean_box(v_res_3660_);
return v_r_3661_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3662_, lean_object* v_keys_3663_, lean_object* v_vals_3664_, lean_object* v_heq_3665_, lean_object* v_i_3666_, lean_object* v_k_3667_){
_start:
{
uint8_t v___x_3668_; 
v___x_3668_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_3663_, v_i_3666_, v_k_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b2_3669_, lean_object* v_keys_3670_, lean_object* v_vals_3671_, lean_object* v_heq_3672_, lean_object* v_i_3673_, lean_object* v_k_3674_){
_start:
{
uint8_t v_res_3675_; lean_object* v_r_3676_; 
v_res_3675_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(v_00_u03b2_3669_, v_keys_3670_, v_vals_3671_, v_heq_3672_, v_i_3673_, v_k_3674_);
lean_dec_ref(v_k_3674_);
lean_dec_ref(v_vals_3671_);
lean_dec_ref(v_keys_3670_);
v_r_3676_ = lean_box(v_res_3675_);
return v_r_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1(){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3684_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3685_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
v___x_3686_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3687_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElab___boxed), 4, 0);
v___x_3688_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3684_, v___x_3685_, v___x_3686_, v___x_3687_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object* v_a_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3(){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3717_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3718_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6));
v___x_3719_ = l_Lean_addBuiltinDeclarationRanges(v___x_3717_, v___x_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object* v_a_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
return v_res_3721_;
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
