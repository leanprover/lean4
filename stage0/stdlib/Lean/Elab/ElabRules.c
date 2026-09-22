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
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* v___x_279_; lean_object* v_env_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_scopes_283_; lean_object* v___x_284_; lean_object* v_opts_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_279_ = lean_st_ref_get(v___y_277_);
v_env_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc_ref(v_env_280_);
lean_dec(v___x_279_);
v___x_281_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_282_ = lean_st_ref_get(v___y_277_);
v_scopes_283_ = lean_ctor_get(v___x_282_, 2);
lean_inc(v_scopes_283_);
lean_dec(v___x_282_);
v___x_284_ = l_List_head_x21___redArg(v___x_281_, v_scopes_283_);
lean_dec(v_scopes_283_);
v_opts_285_ = lean_ctor_get(v___x_284_, 1);
lean_inc_ref(v_opts_285_);
lean_dec(v___x_284_);
v___x_286_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2);
v___x_287_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5);
v___x_288_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_288_, 0, v_env_280_);
lean_ctor_set(v___x_288_, 1, v___x_286_);
lean_ctor_set(v___x_288_, 2, v___x_287_);
lean_ctor_set(v___x_288_, 3, v_opts_285_);
v___x_289_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v_msgData_276_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___boxed(lean_object* v_msgData_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_291_, v___y_292_);
lean_dec(v___y_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(lean_object* v_msg_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Elab_Command_getRef___redArg(v___y_296_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v_macroStack_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_a_304_; lean_object* v___x_305_; lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_314_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
lean_dec_ref_known(v___x_299_, 1);
v_macroStack_301_ = lean_ctor_get(v___y_296_, 4);
v___x_302_ = l_Lean_Elab_getBetterRef(v_a_300_, v_macroStack_301_);
lean_dec(v_a_300_);
v___x_303_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_295_, v___y_297_);
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref(v___x_303_);
lean_inc(v_macroStack_301_);
v___x_305_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_a_304_, v_macroStack_301_, v___y_297_);
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_314_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_302_);
lean_ctor_set(v___x_310_, 1, v_a_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 1);
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_312_ = v___x_308_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec_ref(v_msg_295_);
v_a_315_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_299_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_299_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg___boxed(lean_object* v_msg_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object* v_ref_328_, lean_object* v_msg_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Elab_Command_getRef___redArg(v___y_330_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v_fileName_335_; lean_object* v_fileMap_336_; lean_object* v_currRecDepth_337_; lean_object* v_cmdPos_338_; lean_object* v_macroStack_339_; lean_object* v_quotContext_x3f_340_; lean_object* v_currMacroScope_341_; lean_object* v_snap_x3f_342_; lean_object* v_cancelTk_x3f_343_; uint8_t v_suppressElabErrors_344_; lean_object* v_ref_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v_fileName_335_ = lean_ctor_get(v___y_330_, 0);
v_fileMap_336_ = lean_ctor_get(v___y_330_, 1);
v_currRecDepth_337_ = lean_ctor_get(v___y_330_, 2);
v_cmdPos_338_ = lean_ctor_get(v___y_330_, 3);
v_macroStack_339_ = lean_ctor_get(v___y_330_, 4);
v_quotContext_x3f_340_ = lean_ctor_get(v___y_330_, 5);
v_currMacroScope_341_ = lean_ctor_get(v___y_330_, 6);
v_snap_x3f_342_ = lean_ctor_get(v___y_330_, 8);
v_cancelTk_x3f_343_ = lean_ctor_get(v___y_330_, 9);
v_suppressElabErrors_344_ = lean_ctor_get_uint8(v___y_330_, sizeof(void*)*10);
v_ref_345_ = l_Lean_replaceRef(v_ref_328_, v_a_334_);
lean_dec(v_a_334_);
lean_inc(v_cancelTk_x3f_343_);
lean_inc(v_snap_x3f_342_);
lean_inc(v_currMacroScope_341_);
lean_inc(v_quotContext_x3f_340_);
lean_inc(v_macroStack_339_);
lean_inc(v_cmdPos_338_);
lean_inc(v_currRecDepth_337_);
lean_inc_ref(v_fileMap_336_);
lean_inc_ref(v_fileName_335_);
v___x_346_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_346_, 0, v_fileName_335_);
lean_ctor_set(v___x_346_, 1, v_fileMap_336_);
lean_ctor_set(v___x_346_, 2, v_currRecDepth_337_);
lean_ctor_set(v___x_346_, 3, v_cmdPos_338_);
lean_ctor_set(v___x_346_, 4, v_macroStack_339_);
lean_ctor_set(v___x_346_, 5, v_quotContext_x3f_340_);
lean_ctor_set(v___x_346_, 6, v_currMacroScope_341_);
lean_ctor_set(v___x_346_, 7, v_ref_345_);
lean_ctor_set(v___x_346_, 8, v_snap_x3f_342_);
lean_ctor_set(v___x_346_, 9, v_cancelTk_x3f_343_);
lean_ctor_set_uint8(v___x_346_, sizeof(void*)*10, v_suppressElabErrors_344_);
v___x_347_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_329_, v___x_346_, v___y_331_);
lean_dec_ref_known(v___x_346_, 10);
return v___x_347_;
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec_ref(v_msg_329_);
v_a_348_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_333_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_333_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object* v_ref_356_, lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_356_, v_msg_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v_ref_356_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object* v_k_365_, lean_object* v_as_366_, size_t v_sz_367_, size_t v_i_368_, lean_object* v_b_369_){
_start:
{
uint8_t v___x_370_; 
v___x_370_ = lean_usize_dec_lt(v_i_368_, v_sz_367_);
if (v___x_370_ == 0)
{
lean_dec(v_k_365_);
lean_inc_ref(v_b_369_);
return v_b_369_;
}
else
{
lean_object* v___x_371_; lean_object* v_a_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_371_ = lean_box(0);
v_a_372_ = lean_array_uget_borrowed(v_as_366_, v_i_368_);
lean_inc(v_a_372_);
v___x_373_ = l_Lean_Syntax_getKind(v_a_372_);
lean_inc(v_k_365_);
v___x_374_ = l_Lean_Elab_Command_checkRuleKind(v___x_373_, v_k_365_);
lean_dec(v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; size_t v___x_376_; size_t v___x_377_; 
v___x_375_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_add(v_i_368_, v___x_376_);
v_i_368_ = v___x_377_;
v_b_369_ = v___x_375_;
goto _start;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_k_365_);
lean_inc(v_a_372_);
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v_a_372_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_371_);
return v___x_381_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object* v_k_382_, lean_object* v_as_383_, lean_object* v_sz_384_, lean_object* v_i_385_, lean_object* v_b_386_){
_start:
{
size_t v_sz_boxed_387_; size_t v_i_boxed_388_; lean_object* v_res_389_; 
v_sz_boxed_387_ = lean_unbox_usize(v_sz_384_);
lean_dec(v_sz_384_);
v_i_boxed_388_ = lean_unbox_usize(v_i_385_);
lean_dec(v_i_385_);
v_res_389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_382_, v_as_383_, v_sz_boxed_387_, v_i_boxed_388_, v_b_386_);
lean_dec_ref(v_b_386_);
lean_dec_ref(v_as_383_);
return v_res_389_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0));
v___x_392_ = l_Lean_stringToMessageData(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2));
v___x_395_ = l_Lean_stringToMessageData(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7(void){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Array_mkArray0___redArg();
return v___x_403_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11));
v___x_410_ = l_Lean_stringToMessageData(v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(lean_object* v_k_411_, size_t v_sz_412_, size_t v_i_413_, lean_object* v_bs_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
uint8_t v___x_418_; 
v___x_418_ = lean_usize_dec_lt(v_i_413_, v_sz_412_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_dec(v_k_411_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v_bs_414_);
return v___x_419_;
}
else
{
lean_object* v_v_420_; lean_object* v___x_421_; lean_object* v_bs_x27_422_; lean_object* v_a_424_; lean_object* v___y_430_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_v_420_ = lean_array_uget(v_bs_414_, v_i_413_);
v___x_421_ = lean_unsigned_to_nat(0u);
v_bs_x27_422_ = lean_array_uset(v_bs_414_, v_i_413_, v___x_421_);
v___x_449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5));
lean_inc(v_v_420_);
v___x_450_ = l_Lean_Syntax_isOfKind(v_v_420_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
lean_dec(v_v_420_);
v___x_451_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
v___y_430_ = v___x_451_;
goto v___jp_429_;
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_452_ = lean_unsigned_to_nat(1u);
v___x_453_ = l_Lean_Syntax_getArg(v_v_420_, v___x_452_);
lean_inc(v___x_453_);
v___x_454_ = l_Lean_Syntax_matchesNull(v___x_453_, v___x_452_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_dec(v___x_453_);
lean_dec(v_v_420_);
v___x_455_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
v___y_430_ = v___x_455_;
goto v___jp_429_;
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___x_473_; lean_object* v_pat_474_; lean_object* v___y_476_; lean_object* v___y_477_; uint8_t v___x_529_; 
v___x_456_ = lean_box(0);
v___x_457_ = l_Lean_Syntax_getArg(v___x_453_, v___x_421_);
lean_dec(v___x_453_);
v___x_458_ = lean_unsigned_to_nat(3u);
v___x_459_ = l_Lean_Syntax_getArg(v_v_420_, v___x_458_);
v___x_473_ = l_Lean_Syntax_getArgs(v___x_457_);
lean_dec(v___x_457_);
v_pat_474_ = lean_array_get(v___x_456_, v___x_473_, v___x_421_);
v___x_529_ = l_Lean_Syntax_isQuot(v_pat_474_);
if (v___x_529_ == 0)
{
if (v___x_454_ == 0)
{
v___y_476_ = v___y_415_;
v___y_477_ = v___y_416_;
goto v___jp_475_;
}
else
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
if (lean_obj_tag(v___x_530_) == 0)
{
lean_dec_ref_known(v___x_530_, 1);
v___y_476_ = v___y_415_;
v___y_477_ = v___y_416_;
goto v___jp_475_;
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_pat_474_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_459_);
lean_dec_ref(v_bs_x27_422_);
lean_dec(v_v_420_);
lean_dec(v_k_411_);
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
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
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
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
v___y_476_ = v___y_415_;
v___y_477_ = v___y_416_;
goto v___jp_475_;
}
v___jp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc_n(v___y_461_, 4);
v___x_464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_464_, 0, v___y_461_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_466_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
v___x_467_ = l_Array_append___redArg(v___x_466_, v___y_462_);
lean_dec_ref(v___y_462_);
v___x_468_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_468_, 0, v___y_461_);
lean_ctor_set(v___x_468_, 1, v___x_465_);
lean_ctor_set(v___x_468_, 2, v___x_467_);
v___x_469_ = l_Lean_Syntax_node1(v___y_461_, v___x_465_, v___x_468_);
v___x_470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_471_, 0, v___y_461_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = l_Lean_Syntax_node4(v___y_461_, v___x_449_, v___x_464_, v___x_469_, v___x_471_, v___x_459_);
v_a_424_ = v___x_472_;
goto v___jp_423_;
}
v___jp_475_:
{
lean_object* v_quoted_478_; lean_object* v_k_x27_479_; uint8_t v___x_480_; 
lean_inc(v_pat_474_);
v_quoted_478_ = l_Lean_Syntax_getQuotContent(v_pat_474_);
lean_inc(v_quoted_478_);
v_k_x27_479_ = l_Lean_Syntax_getKind(v_quoted_478_);
lean_inc(v_k_411_);
v___x_480_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_479_, v_k_411_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10));
v___x_482_ = lean_name_eq(v_k_x27_479_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v_quoted_478_);
lean_dec(v_pat_474_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_459_);
v___x_483_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12);
v___x_484_ = l_Lean_MessageData_ofName(v_k_x27_479_);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_420_, v___x_487_, v___y_476_, v___y_477_);
lean_dec(v_v_420_);
v___y_430_ = v___x_488_;
goto v___jp_429_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; size_t v_sz_491_; size_t v___x_492_; lean_object* v___x_493_; lean_object* v_fst_494_; 
lean_dec(v_k_x27_479_);
v___x_489_ = l_Lean_Syntax_getArgs(v_quoted_478_);
lean_dec(v_quoted_478_);
v___x_490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
v_sz_491_ = lean_array_size(v___x_489_);
v___x_492_ = ((size_t)0ULL);
lean_inc(v_k_411_);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_411_, v___x_489_, v_sz_491_, v___x_492_, v___x_490_);
lean_dec_ref(v___x_489_);
v_fst_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_fst_494_);
lean_dec_ref(v___x_493_);
if (lean_obj_tag(v_fst_494_) == 0)
{
lean_dec(v_pat_474_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_459_);
v___y_441_ = v___y_476_;
v___y_442_ = v___y_477_;
goto v___jp_440_;
}
else
{
lean_object* v_val_495_; 
v_val_495_ = lean_ctor_get(v_fst_494_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v_fst_494_, 1);
if (lean_obj_tag(v_val_495_) == 0)
{
lean_dec(v_pat_474_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_459_);
v___y_441_ = v___y_476_;
v___y_442_ = v___y_477_;
goto v___jp_440_;
}
else
{
lean_object* v_val_496_; lean_object* v_pat_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v_v_420_);
v_val_496_ = lean_ctor_get(v_val_495_, 0);
lean_inc(v_val_496_);
lean_dec_ref_known(v_val_495_, 1);
v_pat_497_ = l_Lean_Syntax_setArg(v_pat_474_, v___x_452_, v_val_496_);
v___x_498_ = lean_array_set(v___x_473_, v___x_421_, v_pat_497_);
v___x_499_ = l_Lean_Elab_Command_getRef___redArg(v___y_476_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
v___x_501_ = l_Lean_SourceInfo_fromRef(v_a_500_, v___x_480_);
lean_dec(v_a_500_);
v___x_502_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_476_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_quotContext_x3f_503_; 
lean_dec_ref_known(v___x_502_, 1);
v_quotContext_x3f_503_ = lean_ctor_get(v___y_476_, 5);
if (lean_obj_tag(v_quotContext_x3f_503_) == 0)
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_477_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_dec_ref_known(v___x_504_, 1);
v___y_461_ = v___x_501_;
v___y_462_ = v___x_498_;
goto v___jp_460_;
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec(v___x_501_);
lean_dec_ref(v___x_498_);
lean_dec(v___x_459_);
lean_dec_ref(v_bs_x27_422_);
lean_dec(v_k_411_);
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
else
{
v___y_461_ = v___x_501_;
v___y_462_ = v___x_498_;
goto v___jp_460_;
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v___x_501_);
lean_dec_ref(v___x_498_);
lean_dec(v___x_459_);
lean_dec_ref(v_bs_x27_422_);
lean_dec(v_k_411_);
v_a_513_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_502_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_502_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec_ref(v___x_498_);
lean_dec(v___x_459_);
lean_dec_ref(v_bs_x27_422_);
lean_dec(v_k_411_);
v_a_521_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_499_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_499_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
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
}
}
}
else
{
lean_dec(v_k_x27_479_);
lean_dec(v_quoted_478_);
lean_dec(v_pat_474_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_459_);
v_a_424_ = v_v_420_;
goto v___jp_423_;
}
}
}
}
v___jp_423_:
{
size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
v___x_425_ = ((size_t)1ULL);
v___x_426_ = lean_usize_add(v_i_413_, v___x_425_);
v___x_427_ = lean_array_uset(v_bs_x27_422_, v_i_413_, v_a_424_);
v_i_413_ = v___x_426_;
v_bs_414_ = v___x_427_;
goto _start;
}
v___jp_429_:
{
if (lean_obj_tag(v___y_430_) == 0)
{
lean_object* v_a_431_; 
v_a_431_ = lean_ctor_get(v___y_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v___y_430_, 1);
v_a_424_ = v_a_431_;
goto v___jp_423_;
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec_ref(v_bs_x27_422_);
lean_dec(v_k_411_);
v_a_432_ = lean_ctor_get(v___y_430_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___y_430_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___y_430_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___y_430_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
v___jp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_443_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1);
lean_inc(v_k_411_);
v___x_444_ = l_Lean_MessageData_ofName(v_k_411_);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_420_, v___x_447_, v___y_441_, v___y_442_);
lean_dec(v_v_420_);
v___y_430_ = v___x_448_;
goto v___jp_429_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___boxed(lean_object* v_k_539_, lean_object* v_sz_540_, lean_object* v_i_541_, lean_object* v_bs_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
size_t v_sz_boxed_546_; size_t v_i_boxed_547_; lean_object* v_res_548_; 
v_sz_boxed_546_ = lean_unbox_usize(v_sz_540_);
lean_dec(v_sz_540_);
v_i_boxed_547_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_res_548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_539_, v_sz_boxed_546_, v_i_boxed_547_, v_bs_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
return v_res_548_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__4));
v___x_555_ = l_String_toRawSubstring_x27(v___x_554_);
return v___x_555_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__8));
v___x_561_ = l_String_toRawSubstring_x27(v___x_560_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__15));
v___x_569_ = l_String_toRawSubstring_x27(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_582_ = l_String_toRawSubstring_x27(v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__35(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_597_ = l_String_toRawSubstring_x27(v___x_596_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__38(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___x_601_ = l_String_toRawSubstring_x27(v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__41));
v___x_607_ = l_String_toRawSubstring_x27(v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__45(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__44));
v___x_611_ = l_String_toRawSubstring_x27(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__48(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__47));
v___x_615_ = l_String_toRawSubstring_x27(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__50));
v___x_620_ = l_String_toRawSubstring_x27(v___x_619_);
return v___x_620_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__57));
v___x_630_ = l_Lean_stringToMessageData(v___x_629_);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__59));
v___x_633_ = l_Lean_stringToMessageData(v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__71));
v___x_651_ = l_Lean_stringToMessageData(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__75));
v___x_657_ = l_Lean_stringToMessageData(v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object* v_doc_x3f_658_, lean_object* v_attrs_x3f_659_, lean_object* v_attrKind_660_, lean_object* v_k_661_, lean_object* v_cat_x3f_662_, lean_object* v_expty_x3f_663_, lean_object* v_alts_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
size_t v_sz_668_; size_t v___x_669_; lean_object* v___x_670_; 
v_sz_668_ = lean_array_size(v_alts_664_);
v___x_669_ = ((size_t)0ULL);
lean_inc(v_k_661_);
v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_661_, v_sz_668_, v___x_669_, v_alts_664_, v_a_665_, v_a_666_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_1687_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_1687_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_1687_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v_a_802_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v_a_954_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v_a_1067_; lean_object* v___y_1078_; uint8_t v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v_a_1238_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v_a_1352_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v_a_1485_; lean_object* v_catName_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; 
if (lean_obj_tag(v_cat_x3f_662_) == 1)
{
lean_object* v_val_1674_; lean_object* v___x_1675_; 
v_val_1674_ = lean_ctor_get(v_cat_x3f_662_, 0);
v___x_1675_ = l_Lean_TSyntax_getId(v_val_1674_);
v_catName_1496_ = v___x_1675_;
v___y_1497_ = v_a_665_;
v___y_1498_ = v_a_666_;
goto v___jp_1495_;
}
else
{
if (lean_obj_tag(v_expty_x3f_663_) == 1)
{
lean_object* v___x_1676_; 
v___x_1676_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v_catName_1496_ = v___x_1676_;
v___y_1497_ = v_a_665_;
v___y_1498_ = v_a_666_;
goto v___jp_1495_;
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_del_object(v___x_673_);
lean_dec(v_a_671_);
lean_dec(v_expty_x3f_663_);
lean_dec(v_k_661_);
lean_dec(v_attrKind_660_);
lean_dec(v_doc_x3f_658_);
v___x_1677_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__76, &l_Lean_Elab_Command_elabElabRulesAux___closed__76_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76);
v___x_1678_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_1677_, v_a_665_, v_a_666_);
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
v___jp_675_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
lean_inc_ref_n(v___y_685_, 4);
v___x_689_ = l_Array_append___redArg(v___y_685_, v___y_688_);
lean_dec_ref(v___y_688_);
lean_inc_n(v___y_687_, 10);
lean_inc_n(v___y_681_, 35);
v___x_690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_690_, 0, v___y_681_);
lean_ctor_set(v___x_690_, 1, v___y_687_);
lean_ctor_set(v___x_690_, 2, v___x_689_);
v___x_691_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_692_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_693_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_676_, 11);
v___x_694_ = l_Lean_Name_mkStr4(v___y_676_, v___x_691_, v___x_692_, v___x_693_);
v___x_695_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_696_, 0, v___y_681_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_698_ = l_Lean_Syntax_SepArray_ofElems(v___x_697_, v___y_680_);
lean_dec_ref(v___y_680_);
v___x_699_ = l_Array_append___redArg(v___y_685_, v___x_698_);
lean_dec_ref(v___x_698_);
v___x_700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_700_, 0, v___y_681_);
lean_ctor_set(v___x_700_, 1, v___y_687_);
lean_ctor_set(v___x_700_, 2, v___x_699_);
v___x_701_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_702_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_702_, 0, v___y_681_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = l_Lean_Syntax_node3(v___y_681_, v___x_694_, v___x_696_, v___x_700_, v___x_702_);
v___x_704_ = l_Lean_Syntax_node1(v___y_681_, v___y_687_, v___x_703_);
lean_inc_ref(v___y_682_);
v___x_705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_705_, 0, v___y_681_);
lean_ctor_set(v___x_705_, 1, v___y_682_);
v___x_706_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_707_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_686_, 3);
lean_inc_n(v___y_683_, 3);
v___x_708_ = l_Lean_addMacroScope(v___y_683_, v___x_707_, v___y_686_);
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_710_, 0, v___y_681_);
lean_ctor_set(v___x_710_, 1, v___x_706_);
lean_ctor_set(v___x_710_, 2, v___x_708_);
lean_ctor_set(v___x_710_, 3, v___x_709_);
v___x_711_ = l_Lean_mkIdent(v_k_661_);
v___x_712_ = l_Lean_Syntax_node2(v___y_681_, v___y_687_, v___x_710_, v___x_711_);
v___x_713_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_714_, 0, v___y_681_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_716_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
v___x_717_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc_ref_n(v___y_677_, 2);
v___x_718_ = l_Lean_Name_mkStr4(v___y_676_, v___y_677_, v___x_716_, v___x_717_);
lean_inc(v___x_718_);
v___x_719_ = l_Lean_addMacroScope(v___y_683_, v___x_718_, v___y_686_);
v___x_720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_709_);
v___x_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v___x_709_);
v___x_722_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_722_, 0, v___y_681_);
lean_ctor_set(v___x_722_, 1, v___x_715_);
lean_ctor_set(v___x_722_, 2, v___x_719_);
lean_ctor_set(v___x_722_, 3, v___x_721_);
v___x_723_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_724_, 0, v___y_681_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_726_ = l_Lean_Name_mkStr4(v___y_676_, v___x_691_, v___x_692_, v___x_725_);
v___x_727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_727_, 0, v___y_681_);
lean_ctor_set(v___x_727_, 1, v___x_725_);
v___x_728_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_729_ = l_Lean_Name_mkStr4(v___y_676_, v___x_691_, v___x_692_, v___x_728_);
v___x_730_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_731_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_732_ = l_Lean_addMacroScope(v___y_683_, v___x_731_, v___y_686_);
v___x_733_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_733_, 0, v___y_681_);
lean_ctor_set(v___x_733_, 1, v___x_730_);
lean_ctor_set(v___x_733_, 2, v___x_732_);
lean_ctor_set(v___x_733_, 3, v___x_709_);
lean_inc_ref(v___x_733_);
v___x_734_ = l_Lean_Syntax_node2(v___y_681_, v___y_687_, v___x_733_, v___y_678_);
v___x_735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_735_, 0, v___y_681_);
lean_ctor_set(v___x_735_, 1, v___y_687_);
lean_ctor_set(v___x_735_, 2, v___y_685_);
v___x_736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_737_, 0, v___y_681_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_739_ = l_Lean_Name_mkStr4(v___y_676_, v___x_691_, v___x_692_, v___x_738_);
v___x_740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_740_, 0, v___y_681_);
lean_ctor_set(v___x_740_, 1, v___x_738_);
v___x_741_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_742_ = l_Lean_Name_mkStr4(v___y_676_, v___x_691_, v___x_692_, v___x_741_);
lean_inc_ref_n(v___x_735_, 3);
v___x_743_ = l_Lean_Syntax_node2(v___y_681_, v___x_742_, v___x_735_, v___x_733_);
v___x_744_ = l_Lean_Syntax_node1(v___y_681_, v___y_687_, v___x_743_);
v___x_745_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_746_, 0, v___y_681_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_748_ = l_Lean_Name_mkStr4(v___y_676_, v___x_691_, v___x_692_, v___x_747_);
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_750_ = l_Lean_Name_mkStr4(v___y_676_, v___x_691_, v___x_692_, v___x_749_);
v___x_751_ = l_Array_append___redArg(v___y_685_, v_a_671_);
lean_dec(v_a_671_);
v___x_752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_753_, 0, v___y_681_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_755_ = l_Lean_Name_mkStr4(v___y_676_, v___x_691_, v___x_692_, v___x_754_);
v___x_756_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_757_, 0, v___y_681_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l_Lean_Syntax_node1(v___y_681_, v___x_755_, v___x_757_);
v___x_759_ = l_Lean_Syntax_node1(v___y_681_, v___y_687_, v___x_758_);
v___x_760_ = l_Lean_Syntax_node1(v___y_681_, v___y_687_, v___x_759_);
v___x_761_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_762_ = l_Lean_Name_mkStr4(v___y_676_, v___x_691_, v___x_692_, v___x_761_);
v___x_763_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_764_, 0, v___y_681_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_766_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_767_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_768_ = l_Lean_addMacroScope(v___y_683_, v___x_767_, v___y_686_);
v___x_769_ = l_Lean_Name_mkStr3(v___y_676_, v___y_677_, v___x_765_);
v___x_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_709_);
v___x_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v___x_709_);
v___x_772_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_772_, 0, v___y_681_);
lean_ctor_set(v___x_772_, 1, v___x_766_);
lean_ctor_set(v___x_772_, 2, v___x_768_);
lean_ctor_set(v___x_772_, 3, v___x_771_);
v___x_773_ = l_Lean_Syntax_node2(v___y_681_, v___x_762_, v___x_764_, v___x_772_);
lean_inc_ref(v___x_737_);
v___x_774_ = l_Lean_Syntax_node4(v___y_681_, v___x_750_, v___x_753_, v___x_760_, v___x_737_, v___x_773_);
v___x_775_ = lean_array_push(v___x_751_, v___x_774_);
v___x_776_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_776_, 0, v___y_681_);
lean_ctor_set(v___x_776_, 1, v___y_687_);
lean_ctor_set(v___x_776_, 2, v___x_775_);
v___x_777_ = l_Lean_Syntax_node1(v___y_681_, v___x_748_, v___x_776_);
v___x_778_ = l_Lean_Syntax_node6(v___y_681_, v___x_739_, v___x_740_, v___x_735_, v___x_735_, v___x_744_, v___x_746_, v___x_777_);
v___x_779_ = l_Lean_Syntax_node4(v___y_681_, v___x_729_, v___x_734_, v___x_735_, v___x_737_, v___x_778_);
v___x_780_ = l_Lean_Syntax_node2(v___y_681_, v___x_726_, v___x_727_, v___x_779_);
v___x_781_ = lean_unsigned_to_nat(9u);
v___x_782_ = lean_mk_empty_array_with_capacity(v___x_781_);
v___x_783_ = lean_array_push(v___x_782_, v___x_690_);
v___x_784_ = lean_array_push(v___x_783_, v___x_704_);
v___x_785_ = lean_array_push(v___x_784_, v___y_679_);
v___x_786_ = lean_array_push(v___x_785_, v___x_705_);
v___x_787_ = lean_array_push(v___x_786_, v___x_712_);
v___x_788_ = lean_array_push(v___x_787_, v___x_714_);
v___x_789_ = lean_array_push(v___x_788_, v___x_722_);
v___x_790_ = lean_array_push(v___x_789_, v___x_724_);
v___x_791_ = lean_array_push(v___x_790_, v___x_780_);
lean_inc(v___y_684_);
v___x_792_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_792_, 0, v___y_681_);
lean_ctor_set(v___x_792_, 1, v___y_684_);
lean_ctor_set(v___x_792_, 2, v___x_791_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_792_);
v___x_794_ = v___x_673_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
v___jp_796_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_803_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_804_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_805_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_806_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_807_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_808_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_658_) == 1)
{
lean_object* v_val_809_; lean_object* v___x_810_; 
v_val_809_ = lean_ctor_get(v_doc_x3f_658_, 0);
lean_inc(v_val_809_);
lean_dec_ref_known(v_doc_x3f_658_, 1);
v___x_810_ = l_Array_mkArray1___redArg(v_val_809_);
v___y_676_ = v___x_803_;
v___y_677_ = v___x_804_;
v___y_678_ = v___y_798_;
v___y_679_ = v___y_797_;
v___y_680_ = v___y_799_;
v___y_681_ = v___y_801_;
v___y_682_ = v___x_805_;
v___y_683_ = v_a_802_;
v___y_684_ = v___x_806_;
v___y_685_ = v___x_808_;
v___y_686_ = v___y_800_;
v___y_687_ = v___x_807_;
v___y_688_ = v___x_810_;
goto v___jp_675_;
}
else
{
lean_object* v___x_811_; 
lean_dec(v_doc_x3f_658_);
v___x_811_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_676_ = v___x_803_;
v___y_677_ = v___x_804_;
v___y_678_ = v___y_798_;
v___y_679_ = v___y_797_;
v___y_680_ = v___y_799_;
v___y_681_ = v___y_801_;
v___y_682_ = v___x_805_;
v___y_683_ = v_a_802_;
v___y_684_ = v___x_806_;
v___y_685_ = v___x_808_;
v___y_686_ = v___y_800_;
v___y_687_ = v___x_807_;
v___y_688_ = v___x_811_;
goto v___jp_675_;
}
}
v___jp_812_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
lean_inc_ref_n(v___y_818_, 4);
v___x_826_ = l_Array_append___redArg(v___y_818_, v___y_825_);
lean_dec_ref(v___y_825_);
lean_inc_n(v___y_817_, 12);
lean_inc_n(v___y_824_, 42);
v___x_827_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_827_, 0, v___y_824_);
lean_ctor_set(v___x_827_, 1, v___y_817_);
lean_ctor_set(v___x_827_, 2, v___x_826_);
v___x_828_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_829_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_830_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_823_, 13);
v___x_831_ = l_Lean_Name_mkStr4(v___y_823_, v___x_828_, v___x_829_, v___x_830_);
v___x_832_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_833_, 0, v___y_824_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_835_ = l_Lean_Syntax_SepArray_ofElems(v___x_834_, v___y_813_);
lean_dec_ref(v___y_813_);
v___x_836_ = l_Array_append___redArg(v___y_818_, v___x_835_);
lean_dec_ref(v___x_835_);
v___x_837_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_837_, 0, v___y_824_);
lean_ctor_set(v___x_837_, 1, v___y_817_);
lean_ctor_set(v___x_837_, 2, v___x_836_);
v___x_838_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_839_, 0, v___y_824_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = l_Lean_Syntax_node3(v___y_824_, v___x_831_, v___x_833_, v___x_837_, v___x_839_);
v___x_841_ = l_Lean_Syntax_node1(v___y_824_, v___y_817_, v___x_840_);
lean_inc_ref(v___y_821_);
v___x_842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_842_, 0, v___y_824_);
lean_ctor_set(v___x_842_, 1, v___y_821_);
v___x_843_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_844_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_822_, 5);
lean_inc_n(v___y_820_, 5);
v___x_845_ = l_Lean_addMacroScope(v___y_820_, v___x_844_, v___y_822_);
v___x_846_ = lean_box(0);
v___x_847_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_847_, 0, v___y_824_);
lean_ctor_set(v___x_847_, 1, v___x_843_);
lean_ctor_set(v___x_847_, 2, v___x_845_);
lean_ctor_set(v___x_847_, 3, v___x_846_);
v___x_848_ = l_Lean_mkIdent(v_k_661_);
v___x_849_ = l_Lean_Syntax_node2(v___y_824_, v___y_817_, v___x_847_, v___x_848_);
v___x_850_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_851_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_851_, 0, v___y_824_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__35, &l_Lean_Elab_Command_elabElabRulesAux___closed__35_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__35);
v___x_853_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__36));
lean_inc_ref_n(v___y_819_, 3);
v___x_854_ = l_Lean_Name_mkStr4(v___y_823_, v___y_819_, v___x_829_, v___x_853_);
lean_inc(v___x_854_);
v___x_855_ = l_Lean_addMacroScope(v___y_820_, v___x_854_, v___y_822_);
v___x_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v___x_846_);
v___x_857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v___x_846_);
v___x_858_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_858_, 0, v___y_824_);
lean_ctor_set(v___x_858_, 1, v___x_852_);
lean_ctor_set(v___x_858_, 2, v___x_855_);
lean_ctor_set(v___x_858_, 3, v___x_857_);
v___x_859_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_860_, 0, v___y_824_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_862_ = l_Lean_Name_mkStr4(v___y_823_, v___x_828_, v___x_829_, v___x_861_);
v___x_863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_863_, 0, v___y_824_);
lean_ctor_set(v___x_863_, 1, v___x_861_);
v___x_864_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_865_ = l_Lean_Name_mkStr4(v___y_823_, v___x_828_, v___x_829_, v___x_864_);
v___x_866_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_867_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_868_ = l_Lean_addMacroScope(v___y_820_, v___x_867_, v___y_822_);
v___x_869_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_869_, 0, v___y_824_);
lean_ctor_set(v___x_869_, 1, v___x_866_);
lean_ctor_set(v___x_869_, 2, v___x_868_);
lean_ctor_set(v___x_869_, 3, v___x_846_);
v___x_870_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__38, &l_Lean_Elab_Command_elabElabRulesAux___closed__38_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__38);
v___x_871_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__39));
v___x_872_ = l_Lean_addMacroScope(v___y_820_, v___x_871_, v___y_822_);
v___x_873_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_873_, 0, v___y_824_);
lean_ctor_set(v___x_873_, 1, v___x_870_);
lean_ctor_set(v___x_873_, 2, v___x_872_);
lean_ctor_set(v___x_873_, 3, v___x_846_);
lean_inc_ref(v___x_873_);
lean_inc_ref(v___x_869_);
v___x_874_ = l_Lean_Syntax_node2(v___y_824_, v___y_817_, v___x_869_, v___x_873_);
v___x_875_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_875_, 0, v___y_824_);
lean_ctor_set(v___x_875_, 1, v___y_817_);
lean_ctor_set(v___x_875_, 2, v___y_818_);
v___x_876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_877_, 0, v___y_824_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
v___x_879_ = l_Lean_Name_mkStr4(v___y_823_, v___x_828_, v___x_829_, v___x_878_);
v___x_880_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__42, &l_Lean_Elab_Command_elabElabRulesAux___closed__42_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42);
v___x_881_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__43));
v___x_882_ = l_Lean_Name_mkStr4(v___y_823_, v___y_819_, v___x_829_, v___x_881_);
lean_inc(v___x_882_);
v___x_883_ = l_Lean_addMacroScope(v___y_820_, v___x_882_, v___y_822_);
v___x_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set(v___x_884_, 1, v___x_846_);
v___x_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_846_);
v___x_886_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_886_, 0, v___y_824_);
lean_ctor_set(v___x_886_, 1, v___x_880_);
lean_ctor_set(v___x_886_, 2, v___x_883_);
lean_ctor_set(v___x_886_, 3, v___x_885_);
v___x_887_ = l_Lean_Syntax_node1(v___y_824_, v___y_817_, v___y_814_);
v___x_888_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_889_ = l_Lean_Name_mkStr4(v___y_823_, v___x_828_, v___x_829_, v___x_888_);
v___x_890_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_890_, 0, v___y_824_);
lean_ctor_set(v___x_890_, 1, v___x_888_);
v___x_891_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_892_ = l_Lean_Name_mkStr4(v___y_823_, v___x_828_, v___x_829_, v___x_891_);
lean_inc_ref_n(v___x_875_, 4);
v___x_893_ = l_Lean_Syntax_node2(v___y_824_, v___x_892_, v___x_875_, v___x_869_);
v___x_894_ = l_Lean_Syntax_node1(v___y_824_, v___y_817_, v___x_893_);
v___x_895_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_896_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_896_, 0, v___y_824_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_898_ = l_Lean_Name_mkStr4(v___y_823_, v___x_828_, v___x_829_, v___x_897_);
v___x_899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_900_ = l_Lean_Name_mkStr4(v___y_823_, v___x_828_, v___x_829_, v___x_899_);
v___x_901_ = l_Array_append___redArg(v___y_818_, v_a_671_);
lean_dec(v_a_671_);
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_903_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_903_, 0, v___y_824_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_905_ = l_Lean_Name_mkStr4(v___y_823_, v___x_828_, v___x_829_, v___x_904_);
v___x_906_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_907_, 0, v___y_824_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_Lean_Syntax_node1(v___y_824_, v___x_905_, v___x_907_);
v___x_909_ = l_Lean_Syntax_node1(v___y_824_, v___y_817_, v___x_908_);
v___x_910_ = l_Lean_Syntax_node1(v___y_824_, v___y_817_, v___x_909_);
v___x_911_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_912_ = l_Lean_Name_mkStr4(v___y_823_, v___x_828_, v___x_829_, v___x_911_);
v___x_913_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_914_, 0, v___y_824_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_916_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_917_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_918_ = l_Lean_addMacroScope(v___y_820_, v___x_917_, v___y_822_);
v___x_919_ = l_Lean_Name_mkStr3(v___y_823_, v___y_819_, v___x_915_);
v___x_920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v___x_846_);
v___x_921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_846_);
v___x_922_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_922_, 0, v___y_824_);
lean_ctor_set(v___x_922_, 1, v___x_916_);
lean_ctor_set(v___x_922_, 2, v___x_918_);
lean_ctor_set(v___x_922_, 3, v___x_921_);
v___x_923_ = l_Lean_Syntax_node2(v___y_824_, v___x_912_, v___x_914_, v___x_922_);
lean_inc_ref_n(v___x_877_, 2);
v___x_924_ = l_Lean_Syntax_node4(v___y_824_, v___x_900_, v___x_903_, v___x_910_, v___x_877_, v___x_923_);
v___x_925_ = lean_array_push(v___x_901_, v___x_924_);
v___x_926_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_926_, 0, v___y_824_);
lean_ctor_set(v___x_926_, 1, v___y_817_);
lean_ctor_set(v___x_926_, 2, v___x_925_);
v___x_927_ = l_Lean_Syntax_node1(v___y_824_, v___x_898_, v___x_926_);
v___x_928_ = l_Lean_Syntax_node6(v___y_824_, v___x_889_, v___x_890_, v___x_875_, v___x_875_, v___x_894_, v___x_896_, v___x_927_);
lean_inc(v___x_865_);
v___x_929_ = l_Lean_Syntax_node4(v___y_824_, v___x_865_, v___x_887_, v___x_875_, v___x_877_, v___x_928_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_862_);
v___x_930_ = l_Lean_Syntax_node2(v___y_824_, v___x_862_, v___x_863_, v___x_929_);
v___x_931_ = l_Lean_Syntax_node2(v___y_824_, v___y_817_, v___x_873_, v___x_930_);
v___x_932_ = l_Lean_Syntax_node2(v___y_824_, v___x_879_, v___x_886_, v___x_931_);
v___x_933_ = l_Lean_Syntax_node4(v___y_824_, v___x_865_, v___x_874_, v___x_875_, v___x_877_, v___x_932_);
v___x_934_ = l_Lean_Syntax_node2(v___y_824_, v___x_862_, v___x_863_, v___x_933_);
v___x_935_ = lean_unsigned_to_nat(9u);
v___x_936_ = lean_mk_empty_array_with_capacity(v___x_935_);
v___x_937_ = lean_array_push(v___x_936_, v___x_827_);
v___x_938_ = lean_array_push(v___x_937_, v___x_841_);
v___x_939_ = lean_array_push(v___x_938_, v___y_815_);
v___x_940_ = lean_array_push(v___x_939_, v___x_842_);
v___x_941_ = lean_array_push(v___x_940_, v___x_849_);
v___x_942_ = lean_array_push(v___x_941_, v___x_851_);
v___x_943_ = lean_array_push(v___x_942_, v___x_858_);
v___x_944_ = lean_array_push(v___x_943_, v___x_860_);
v___x_945_ = lean_array_push(v___x_944_, v___x_934_);
lean_inc(v___y_816_);
v___x_946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_946_, 0, v___y_824_);
lean_ctor_set(v___x_946_, 1, v___y_816_);
lean_ctor_set(v___x_946_, 2, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
v___jp_948_:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_955_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_956_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_957_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_958_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_959_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_960_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_658_) == 1)
{
lean_object* v_val_961_; lean_object* v___x_962_; 
v_val_961_ = lean_ctor_get(v_doc_x3f_658_, 0);
lean_inc(v_val_961_);
lean_dec_ref_known(v_doc_x3f_658_, 1);
v___x_962_ = l_Array_mkArray1___redArg(v_val_961_);
v___y_813_ = v___y_949_;
v___y_814_ = v___y_952_;
v___y_815_ = v___y_951_;
v___y_816_ = v___x_958_;
v___y_817_ = v___x_959_;
v___y_818_ = v___x_960_;
v___y_819_ = v___x_956_;
v___y_820_ = v_a_954_;
v___y_821_ = v___x_957_;
v___y_822_ = v___y_950_;
v___y_823_ = v___x_955_;
v___y_824_ = v___y_953_;
v___y_825_ = v___x_962_;
goto v___jp_812_;
}
else
{
lean_object* v___x_963_; 
lean_dec(v_doc_x3f_658_);
v___x_963_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_813_ = v___y_949_;
v___y_814_ = v___y_952_;
v___y_815_ = v___y_951_;
v___y_816_ = v___x_958_;
v___y_817_ = v___x_959_;
v___y_818_ = v___x_960_;
v___y_819_ = v___x_956_;
v___y_820_ = v_a_954_;
v___y_821_ = v___x_957_;
v___y_822_ = v___y_950_;
v___y_823_ = v___x_955_;
v___y_824_ = v___y_953_;
v___y_825_ = v___x_963_;
goto v___jp_812_;
}
}
v___jp_964_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
lean_inc_ref_n(v___y_965_, 3);
v___x_977_ = l_Array_append___redArg(v___y_965_, v___y_976_);
lean_dec_ref(v___y_976_);
lean_inc_n(v___y_972_, 7);
lean_inc_n(v___y_973_, 26);
v___x_978_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_978_, 0, v___y_973_);
lean_ctor_set(v___x_978_, 1, v___y_972_);
lean_ctor_set(v___x_978_, 2, v___x_977_);
v___x_979_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_980_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_981_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_970_, 8);
v___x_982_ = l_Lean_Name_mkStr4(v___y_970_, v___x_979_, v___x_980_, v___x_981_);
v___x_983_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_984_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_984_, 0, v___y_973_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_986_ = l_Lean_Syntax_SepArray_ofElems(v___x_985_, v___y_966_);
lean_dec_ref(v___y_966_);
v___x_987_ = l_Array_append___redArg(v___y_965_, v___x_986_);
lean_dec_ref(v___x_986_);
v___x_988_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_988_, 0, v___y_973_);
lean_ctor_set(v___x_988_, 1, v___y_972_);
lean_ctor_set(v___x_988_, 2, v___x_987_);
v___x_989_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_990_, 0, v___y_973_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Lean_Syntax_node3(v___y_973_, v___x_982_, v___x_984_, v___x_988_, v___x_990_);
v___x_992_ = l_Lean_Syntax_node1(v___y_973_, v___y_972_, v___x_991_);
lean_inc_ref(v___y_974_);
v___x_993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_993_, 0, v___y_973_);
lean_ctor_set(v___x_993_, 1, v___y_974_);
v___x_994_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_995_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_967_, 2);
lean_inc_n(v___y_968_, 2);
v___x_996_ = l_Lean_addMacroScope(v___y_968_, v___x_995_, v___y_967_);
v___x_997_ = lean_box(0);
v___x_998_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_998_, 0, v___y_973_);
lean_ctor_set(v___x_998_, 1, v___x_994_);
lean_ctor_set(v___x_998_, 2, v___x_996_);
lean_ctor_set(v___x_998_, 3, v___x_997_);
v___x_999_ = l_Lean_mkIdent(v_k_661_);
v___x_1000_ = l_Lean_Syntax_node2(v___y_973_, v___y_972_, v___x_998_, v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___y_973_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__45, &l_Lean_Elab_Command_elabElabRulesAux___closed__45_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__45);
v___x_1004_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__46));
lean_inc_ref_n(v___y_975_, 2);
v___x_1005_ = l_Lean_Name_mkStr4(v___y_970_, v___y_975_, v___x_1004_, v___x_1004_);
lean_inc(v___x_1005_);
v___x_1006_ = l_Lean_addMacroScope(v___y_968_, v___x_1005_, v___y_967_);
v___x_1007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_997_);
v___x_1008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_997_);
v___x_1009_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1009_, 0, v___y_973_);
lean_ctor_set(v___x_1009_, 1, v___x_1003_);
lean_ctor_set(v___x_1009_, 2, v___x_1006_);
lean_ctor_set(v___x_1009_, 3, v___x_1008_);
v___x_1010_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___y_973_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1013_ = l_Lean_Name_mkStr4(v___y_970_, v___x_979_, v___x_980_, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___y_973_);
lean_ctor_set(v___x_1014_, 1, v___x_1012_);
v___x_1015_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1016_ = l_Lean_Name_mkStr4(v___y_970_, v___x_979_, v___x_980_, v___x_1015_);
v___x_1017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1018_ = l_Lean_Name_mkStr4(v___y_970_, v___x_979_, v___x_980_, v___x_1017_);
v___x_1019_ = l_Array_append___redArg(v___y_965_, v_a_671_);
lean_dec(v_a_671_);
v___x_1020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1021_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___y_973_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1023_ = l_Lean_Name_mkStr4(v___y_970_, v___x_979_, v___x_980_, v___x_1022_);
v___x_1024_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1025_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___y_973_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = l_Lean_Syntax_node1(v___y_973_, v___x_1023_, v___x_1025_);
v___x_1027_ = l_Lean_Syntax_node1(v___y_973_, v___y_972_, v___x_1026_);
v___x_1028_ = l_Lean_Syntax_node1(v___y_973_, v___y_972_, v___x_1027_);
v___x_1029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1030_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___y_973_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1032_ = l_Lean_Name_mkStr4(v___y_970_, v___x_979_, v___x_980_, v___x_1031_);
v___x_1033_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___y_973_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1036_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1037_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1038_ = l_Lean_addMacroScope(v___y_968_, v___x_1037_, v___y_967_);
v___x_1039_ = l_Lean_Name_mkStr3(v___y_970_, v___y_975_, v___x_1035_);
v___x_1040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v___x_997_);
v___x_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v___x_997_);
v___x_1042_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1042_, 0, v___y_973_);
lean_ctor_set(v___x_1042_, 1, v___x_1036_);
lean_ctor_set(v___x_1042_, 2, v___x_1038_);
lean_ctor_set(v___x_1042_, 3, v___x_1041_);
v___x_1043_ = l_Lean_Syntax_node2(v___y_973_, v___x_1032_, v___x_1034_, v___x_1042_);
v___x_1044_ = l_Lean_Syntax_node4(v___y_973_, v___x_1018_, v___x_1021_, v___x_1028_, v___x_1030_, v___x_1043_);
v___x_1045_ = lean_array_push(v___x_1019_, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1046_, 0, v___y_973_);
lean_ctor_set(v___x_1046_, 1, v___y_972_);
lean_ctor_set(v___x_1046_, 2, v___x_1045_);
v___x_1047_ = l_Lean_Syntax_node1(v___y_973_, v___x_1016_, v___x_1046_);
v___x_1048_ = l_Lean_Syntax_node2(v___y_973_, v___x_1013_, v___x_1014_, v___x_1047_);
v___x_1049_ = lean_unsigned_to_nat(9u);
v___x_1050_ = lean_mk_empty_array_with_capacity(v___x_1049_);
v___x_1051_ = lean_array_push(v___x_1050_, v___x_978_);
v___x_1052_ = lean_array_push(v___x_1051_, v___x_992_);
v___x_1053_ = lean_array_push(v___x_1052_, v___y_969_);
v___x_1054_ = lean_array_push(v___x_1053_, v___x_993_);
v___x_1055_ = lean_array_push(v___x_1054_, v___x_1000_);
v___x_1056_ = lean_array_push(v___x_1055_, v___x_1002_);
v___x_1057_ = lean_array_push(v___x_1056_, v___x_1009_);
v___x_1058_ = lean_array_push(v___x_1057_, v___x_1011_);
v___x_1059_ = lean_array_push(v___x_1058_, v___x_1048_);
lean_inc(v___y_971_);
v___x_1060_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1060_, 0, v___y_973_);
lean_ctor_set(v___x_1060_, 1, v___y_971_);
lean_ctor_set(v___x_1060_, 2, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
v___jp_1062_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1068_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1069_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1070_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1072_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1073_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_658_) == 1)
{
lean_object* v_val_1074_; lean_object* v___x_1075_; 
v_val_1074_ = lean_ctor_get(v_doc_x3f_658_, 0);
lean_inc(v_val_1074_);
lean_dec_ref_known(v_doc_x3f_658_, 1);
v___x_1075_ = l_Array_mkArray1___redArg(v_val_1074_);
v___y_965_ = v___x_1073_;
v___y_966_ = v___y_1063_;
v___y_967_ = v___y_1064_;
v___y_968_ = v_a_1067_;
v___y_969_ = v___y_1065_;
v___y_970_ = v___x_1068_;
v___y_971_ = v___x_1071_;
v___y_972_ = v___x_1072_;
v___y_973_ = v___y_1066_;
v___y_974_ = v___x_1070_;
v___y_975_ = v___x_1069_;
v___y_976_ = v___x_1075_;
goto v___jp_964_;
}
else
{
lean_object* v___x_1076_; 
lean_dec(v_doc_x3f_658_);
v___x_1076_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_965_ = v___x_1073_;
v___y_966_ = v___y_1063_;
v___y_967_ = v___y_1064_;
v___y_968_ = v_a_1067_;
v___y_969_ = v___y_1065_;
v___y_970_ = v___x_1068_;
v___y_971_ = v___x_1071_;
v___y_972_ = v___x_1072_;
v___y_973_ = v___y_1066_;
v___y_974_ = v___x_1070_;
v___y_975_ = v___x_1069_;
v___y_976_ = v___x_1076_;
goto v___jp_964_;
}
}
v___jp_1077_:
{
lean_object* v___x_1083_; 
lean_inc(v___y_1080_);
lean_inc(v_k_661_);
v___x_1083_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_661_, v_attrKind_660_, v_attrs_x3f_659_, v___y_1080_, v___y_1081_, v___y_1082_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1085_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v___x_1085_ = l_Lean_Elab_Command_getRef___redArg(v___y_1081_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v___x_1087_ = l_Lean_SourceInfo_fromRef(v_a_1086_, v___y_1079_);
lean_dec(v_a_1086_);
v___x_1088_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1081_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_quotContext_x3f_1089_; 
v_quotContext_x3f_1089_ = lean_ctor_get(v___y_1081_, 5);
if (lean_obj_tag(v_quotContext_x3f_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1091_; lean_object* v_a_1092_; 
v_a_1090_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1091_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1082_);
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref(v___x_1091_);
v___y_1063_ = v_a_1084_;
v___y_1064_ = v_a_1090_;
v___y_1065_ = v___y_1078_;
v___y_1066_ = v___x_1087_;
v_a_1067_ = v_a_1092_;
goto v___jp_1062_;
}
else
{
lean_object* v_a_1093_; lean_object* v_val_1094_; 
v_a_1093_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1088_, 1);
v_val_1094_ = lean_ctor_get(v_quotContext_x3f_1089_, 0);
lean_inc(v_val_1094_);
v___y_1063_ = v_a_1084_;
v___y_1064_ = v_a_1093_;
v___y_1065_ = v___y_1078_;
v___y_1066_ = v___x_1087_;
v_a_1067_ = v_val_1094_;
goto v___jp_1062_;
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec(v___x_1087_);
lean_dec(v_a_1084_);
lean_dec(v___y_1078_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
v_a_1095_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1088_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1088_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
else
{
lean_dec(v_a_1084_);
lean_dec(v___y_1078_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
return v___x_1085_;
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v___y_1078_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
v_a_1103_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1083_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1083_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
v___jp_1111_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_inc_ref_n(v___y_1117_, 4);
v___x_1124_ = l_Array_append___redArg(v___y_1117_, v___y_1123_);
lean_dec_ref(v___y_1123_);
lean_inc_n(v___y_1121_, 10);
lean_inc_n(v___y_1116_, 36);
v___x_1125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1125_, 0, v___y_1116_);
lean_ctor_set(v___x_1125_, 1, v___y_1121_);
lean_ctor_set(v___x_1125_, 2, v___x_1124_);
v___x_1126_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1127_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1128_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1115_, 11);
v___x_1129_ = l_Lean_Name_mkStr4(v___y_1115_, v___x_1126_, v___x_1127_, v___x_1128_);
v___x_1130_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___y_1116_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1133_ = l_Lean_Syntax_SepArray_ofElems(v___x_1132_, v___y_1114_);
lean_dec_ref(v___y_1114_);
v___x_1134_ = l_Array_append___redArg(v___y_1117_, v___x_1133_);
lean_dec_ref(v___x_1133_);
v___x_1135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1135_, 0, v___y_1116_);
lean_ctor_set(v___x_1135_, 1, v___y_1121_);
lean_ctor_set(v___x_1135_, 2, v___x_1134_);
v___x_1136_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___y_1116_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = l_Lean_Syntax_node3(v___y_1116_, v___x_1129_, v___x_1131_, v___x_1135_, v___x_1137_);
v___x_1139_ = l_Lean_Syntax_node1(v___y_1116_, v___y_1121_, v___x_1138_);
lean_inc_ref(v___y_1120_);
v___x_1140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___y_1116_);
lean_ctor_set(v___x_1140_, 1, v___y_1120_);
v___x_1141_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1142_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1122_, 4);
lean_inc_n(v___y_1112_, 4);
v___x_1143_ = l_Lean_addMacroScope(v___y_1112_, v___x_1142_, v___y_1122_);
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1145_, 0, v___y_1116_);
lean_ctor_set(v___x_1145_, 1, v___x_1141_);
lean_ctor_set(v___x_1145_, 2, v___x_1143_);
lean_ctor_set(v___x_1145_, 3, v___x_1144_);
v___x_1146_ = l_Lean_mkIdent(v_k_661_);
v___x_1147_ = l_Lean_Syntax_node2(v___y_1116_, v___y_1121_, v___x_1145_, v___x_1146_);
v___x_1148_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___y_1116_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_1151_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
v___x_1152_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc_ref_n(v___y_1113_, 2);
v___x_1153_ = l_Lean_Name_mkStr4(v___y_1115_, v___y_1113_, v___x_1151_, v___x_1152_);
lean_inc(v___x_1153_);
v___x_1154_ = l_Lean_addMacroScope(v___y_1112_, v___x_1153_, v___y_1122_);
v___x_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1144_);
v___x_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
lean_ctor_set(v___x_1156_, 1, v___x_1144_);
v___x_1157_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1157_, 0, v___y_1116_);
lean_ctor_set(v___x_1157_, 1, v___x_1150_);
lean_ctor_set(v___x_1157_, 2, v___x_1154_);
lean_ctor_set(v___x_1157_, 3, v___x_1156_);
v___x_1158_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___y_1116_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1161_ = l_Lean_Name_mkStr4(v___y_1115_, v___x_1126_, v___x_1127_, v___x_1160_);
v___x_1162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___y_1116_);
lean_ctor_set(v___x_1162_, 1, v___x_1160_);
v___x_1163_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_1164_ = l_Lean_Name_mkStr4(v___y_1115_, v___x_1126_, v___x_1127_, v___x_1163_);
v___x_1165_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1167_ = l_Lean_addMacroScope(v___y_1112_, v___x_1166_, v___y_1122_);
v___x_1168_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1168_, 0, v___y_1116_);
lean_ctor_set(v___x_1168_, 1, v___x_1165_);
lean_ctor_set(v___x_1168_, 2, v___x_1167_);
lean_ctor_set(v___x_1168_, 3, v___x_1144_);
v___x_1169_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__48, &l_Lean_Elab_Command_elabElabRulesAux___closed__48_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__48);
v___x_1170_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__49));
v___x_1171_ = l_Lean_addMacroScope(v___y_1112_, v___x_1170_, v___y_1122_);
v___x_1172_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1172_, 0, v___y_1116_);
lean_ctor_set(v___x_1172_, 1, v___x_1169_);
lean_ctor_set(v___x_1172_, 2, v___x_1171_);
lean_ctor_set(v___x_1172_, 3, v___x_1144_);
lean_inc_ref(v___x_1168_);
v___x_1173_ = l_Lean_Syntax_node2(v___y_1116_, v___y_1121_, v___x_1168_, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1174_, 0, v___y_1116_);
lean_ctor_set(v___x_1174_, 1, v___y_1121_);
lean_ctor_set(v___x_1174_, 2, v___y_1117_);
v___x_1175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___y_1116_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1178_ = l_Lean_Name_mkStr4(v___y_1115_, v___x_1126_, v___x_1127_, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___y_1116_);
lean_ctor_set(v___x_1179_, 1, v___x_1177_);
v___x_1180_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1181_ = l_Lean_Name_mkStr4(v___y_1115_, v___x_1126_, v___x_1127_, v___x_1180_);
lean_inc_ref_n(v___x_1174_, 3);
v___x_1182_ = l_Lean_Syntax_node2(v___y_1116_, v___x_1181_, v___x_1174_, v___x_1168_);
v___x_1183_ = l_Lean_Syntax_node1(v___y_1116_, v___y_1121_, v___x_1182_);
v___x_1184_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___y_1116_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1187_ = l_Lean_Name_mkStr4(v___y_1115_, v___x_1126_, v___x_1127_, v___x_1186_);
v___x_1188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1189_ = l_Lean_Name_mkStr4(v___y_1115_, v___x_1126_, v___x_1127_, v___x_1188_);
v___x_1190_ = l_Array_append___redArg(v___y_1117_, v_a_671_);
lean_dec(v_a_671_);
v___x_1191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___y_1116_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1194_ = l_Lean_Name_mkStr4(v___y_1115_, v___x_1126_, v___x_1127_, v___x_1193_);
v___x_1195_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___y_1116_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = l_Lean_Syntax_node1(v___y_1116_, v___x_1194_, v___x_1196_);
v___x_1198_ = l_Lean_Syntax_node1(v___y_1116_, v___y_1121_, v___x_1197_);
v___x_1199_ = l_Lean_Syntax_node1(v___y_1116_, v___y_1121_, v___x_1198_);
v___x_1200_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1201_ = l_Lean_Name_mkStr4(v___y_1115_, v___x_1126_, v___x_1127_, v___x_1200_);
v___x_1202_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___y_1116_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1205_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1206_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1207_ = l_Lean_addMacroScope(v___y_1112_, v___x_1206_, v___y_1122_);
v___x_1208_ = l_Lean_Name_mkStr3(v___y_1115_, v___y_1113_, v___x_1204_);
v___x_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1144_);
v___x_1210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___x_1144_);
v___x_1211_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1211_, 0, v___y_1116_);
lean_ctor_set(v___x_1211_, 1, v___x_1205_);
lean_ctor_set(v___x_1211_, 2, v___x_1207_);
lean_ctor_set(v___x_1211_, 3, v___x_1210_);
v___x_1212_ = l_Lean_Syntax_node2(v___y_1116_, v___x_1201_, v___x_1203_, v___x_1211_);
lean_inc_ref(v___x_1176_);
v___x_1213_ = l_Lean_Syntax_node4(v___y_1116_, v___x_1189_, v___x_1192_, v___x_1199_, v___x_1176_, v___x_1212_);
v___x_1214_ = lean_array_push(v___x_1190_, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1215_, 0, v___y_1116_);
lean_ctor_set(v___x_1215_, 1, v___y_1121_);
lean_ctor_set(v___x_1215_, 2, v___x_1214_);
v___x_1216_ = l_Lean_Syntax_node1(v___y_1116_, v___x_1187_, v___x_1215_);
v___x_1217_ = l_Lean_Syntax_node6(v___y_1116_, v___x_1178_, v___x_1179_, v___x_1174_, v___x_1174_, v___x_1183_, v___x_1185_, v___x_1216_);
v___x_1218_ = l_Lean_Syntax_node4(v___y_1116_, v___x_1164_, v___x_1173_, v___x_1174_, v___x_1176_, v___x_1217_);
v___x_1219_ = l_Lean_Syntax_node2(v___y_1116_, v___x_1161_, v___x_1162_, v___x_1218_);
v___x_1220_ = lean_unsigned_to_nat(9u);
v___x_1221_ = lean_mk_empty_array_with_capacity(v___x_1220_);
v___x_1222_ = lean_array_push(v___x_1221_, v___x_1125_);
v___x_1223_ = lean_array_push(v___x_1222_, v___x_1139_);
v___x_1224_ = lean_array_push(v___x_1223_, v___y_1119_);
v___x_1225_ = lean_array_push(v___x_1224_, v___x_1140_);
v___x_1226_ = lean_array_push(v___x_1225_, v___x_1147_);
v___x_1227_ = lean_array_push(v___x_1226_, v___x_1149_);
v___x_1228_ = lean_array_push(v___x_1227_, v___x_1157_);
v___x_1229_ = lean_array_push(v___x_1228_, v___x_1159_);
v___x_1230_ = lean_array_push(v___x_1229_, v___x_1219_);
lean_inc(v___y_1118_);
v___x_1231_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1231_, 0, v___y_1116_);
lean_ctor_set(v___x_1231_, 1, v___y_1118_);
lean_ctor_set(v___x_1231_, 2, v___x_1230_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
v___jp_1233_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1239_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1240_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1241_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1242_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1243_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1244_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_658_) == 1)
{
lean_object* v_val_1245_; lean_object* v___x_1246_; 
v_val_1245_ = lean_ctor_get(v_doc_x3f_658_, 0);
lean_inc(v_val_1245_);
lean_dec_ref_known(v_doc_x3f_658_, 1);
v___x_1246_ = l_Array_mkArray1___redArg(v_val_1245_);
v___y_1112_ = v_a_1238_;
v___y_1113_ = v___x_1240_;
v___y_1114_ = v___y_1234_;
v___y_1115_ = v___x_1239_;
v___y_1116_ = v___y_1235_;
v___y_1117_ = v___x_1244_;
v___y_1118_ = v___x_1242_;
v___y_1119_ = v___y_1236_;
v___y_1120_ = v___x_1241_;
v___y_1121_ = v___x_1243_;
v___y_1122_ = v___y_1237_;
v___y_1123_ = v___x_1246_;
goto v___jp_1111_;
}
else
{
lean_object* v___x_1247_; 
lean_dec(v_doc_x3f_658_);
v___x_1247_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_1112_ = v_a_1238_;
v___y_1113_ = v___x_1240_;
v___y_1114_ = v___y_1234_;
v___y_1115_ = v___x_1239_;
v___y_1116_ = v___y_1235_;
v___y_1117_ = v___x_1244_;
v___y_1118_ = v___x_1242_;
v___y_1119_ = v___y_1236_;
v___y_1120_ = v___x_1241_;
v___y_1121_ = v___x_1243_;
v___y_1122_ = v___y_1237_;
v___y_1123_ = v___x_1247_;
goto v___jp_1111_;
}
}
v___jp_1248_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_inc_ref_n(v___y_1255_, 3);
v___x_1262_ = l_Array_append___redArg(v___y_1255_, v___y_1261_);
lean_dec_ref(v___y_1261_);
lean_inc_n(v___y_1259_, 7);
lean_inc_n(v___y_1253_, 26);
v___x_1263_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1263_, 0, v___y_1253_);
lean_ctor_set(v___x_1263_, 1, v___y_1259_);
lean_ctor_set(v___x_1263_, 2, v___x_1262_);
v___x_1264_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1265_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1266_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1249_, 8);
v___x_1267_ = l_Lean_Name_mkStr4(v___y_1249_, v___x_1264_, v___x_1265_, v___x_1266_);
v___x_1268_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1269_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___y_1253_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1271_ = l_Lean_Syntax_SepArray_ofElems(v___x_1270_, v___y_1260_);
lean_dec_ref(v___y_1260_);
v___x_1272_ = l_Array_append___redArg(v___y_1255_, v___x_1271_);
lean_dec_ref(v___x_1271_);
v___x_1273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1273_, 0, v___y_1253_);
lean_ctor_set(v___x_1273_, 1, v___y_1259_);
lean_ctor_set(v___x_1273_, 2, v___x_1272_);
v___x_1274_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___y_1253_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = l_Lean_Syntax_node3(v___y_1253_, v___x_1267_, v___x_1269_, v___x_1273_, v___x_1275_);
v___x_1277_ = l_Lean_Syntax_node1(v___y_1253_, v___y_1259_, v___x_1276_);
lean_inc_ref(v___y_1250_);
v___x_1278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___y_1253_);
lean_ctor_set(v___x_1278_, 1, v___y_1250_);
v___x_1279_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1280_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1252_, 2);
lean_inc_n(v___y_1254_, 2);
v___x_1281_ = l_Lean_addMacroScope(v___y_1254_, v___x_1280_, v___y_1252_);
v___x_1282_ = lean_box(0);
v___x_1283_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1283_, 0, v___y_1253_);
lean_ctor_set(v___x_1283_, 1, v___x_1279_);
lean_ctor_set(v___x_1283_, 2, v___x_1281_);
lean_ctor_set(v___x_1283_, 3, v___x_1282_);
v___x_1284_ = l_Lean_mkIdent(v_k_661_);
v___x_1285_ = l_Lean_Syntax_node2(v___y_1253_, v___y_1259_, v___x_1283_, v___x_1284_);
v___x_1286_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___y_1253_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__51, &l_Lean_Elab_Command_elabElabRulesAux___closed__51_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51);
v___x_1289_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__52));
lean_inc_ref(v___y_1256_);
lean_inc_ref_n(v___y_1257_, 2);
v___x_1290_ = l_Lean_Name_mkStr4(v___y_1249_, v___y_1257_, v___y_1256_, v___x_1289_);
lean_inc(v___x_1290_);
v___x_1291_ = l_Lean_addMacroScope(v___y_1254_, v___x_1290_, v___y_1252_);
v___x_1292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1290_);
lean_ctor_set(v___x_1292_, 1, v___x_1282_);
v___x_1293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v___x_1282_);
v___x_1294_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1294_, 0, v___y_1253_);
lean_ctor_set(v___x_1294_, 1, v___x_1288_);
lean_ctor_set(v___x_1294_, 2, v___x_1291_);
lean_ctor_set(v___x_1294_, 3, v___x_1293_);
v___x_1295_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___y_1253_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1298_ = l_Lean_Name_mkStr4(v___y_1249_, v___x_1264_, v___x_1265_, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___y_1253_);
lean_ctor_set(v___x_1299_, 1, v___x_1297_);
v___x_1300_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1301_ = l_Lean_Name_mkStr4(v___y_1249_, v___x_1264_, v___x_1265_, v___x_1300_);
v___x_1302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1303_ = l_Lean_Name_mkStr4(v___y_1249_, v___x_1264_, v___x_1265_, v___x_1302_);
v___x_1304_ = l_Array_append___redArg(v___y_1255_, v_a_671_);
lean_dec(v_a_671_);
v___x_1305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___y_1253_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1308_ = l_Lean_Name_mkStr4(v___y_1249_, v___x_1264_, v___x_1265_, v___x_1307_);
v___x_1309_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___y_1253_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = l_Lean_Syntax_node1(v___y_1253_, v___x_1308_, v___x_1310_);
v___x_1312_ = l_Lean_Syntax_node1(v___y_1253_, v___y_1259_, v___x_1311_);
v___x_1313_ = l_Lean_Syntax_node1(v___y_1253_, v___y_1259_, v___x_1312_);
v___x_1314_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___y_1253_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1317_ = l_Lean_Name_mkStr4(v___y_1249_, v___x_1264_, v___x_1265_, v___x_1316_);
v___x_1318_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___y_1253_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1321_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1322_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1323_ = l_Lean_addMacroScope(v___y_1254_, v___x_1322_, v___y_1252_);
v___x_1324_ = l_Lean_Name_mkStr3(v___y_1249_, v___y_1257_, v___x_1320_);
v___x_1325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v___x_1282_);
v___x_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v___x_1282_);
v___x_1327_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1327_, 0, v___y_1253_);
lean_ctor_set(v___x_1327_, 1, v___x_1321_);
lean_ctor_set(v___x_1327_, 2, v___x_1323_);
lean_ctor_set(v___x_1327_, 3, v___x_1326_);
v___x_1328_ = l_Lean_Syntax_node2(v___y_1253_, v___x_1317_, v___x_1319_, v___x_1327_);
v___x_1329_ = l_Lean_Syntax_node4(v___y_1253_, v___x_1303_, v___x_1306_, v___x_1313_, v___x_1315_, v___x_1328_);
v___x_1330_ = lean_array_push(v___x_1304_, v___x_1329_);
v___x_1331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1331_, 0, v___y_1253_);
lean_ctor_set(v___x_1331_, 1, v___y_1259_);
lean_ctor_set(v___x_1331_, 2, v___x_1330_);
v___x_1332_ = l_Lean_Syntax_node1(v___y_1253_, v___x_1301_, v___x_1331_);
v___x_1333_ = l_Lean_Syntax_node2(v___y_1253_, v___x_1298_, v___x_1299_, v___x_1332_);
v___x_1334_ = lean_unsigned_to_nat(9u);
v___x_1335_ = lean_mk_empty_array_with_capacity(v___x_1334_);
v___x_1336_ = lean_array_push(v___x_1335_, v___x_1263_);
v___x_1337_ = lean_array_push(v___x_1336_, v___x_1277_);
v___x_1338_ = lean_array_push(v___x_1337_, v___y_1251_);
v___x_1339_ = lean_array_push(v___x_1338_, v___x_1278_);
v___x_1340_ = lean_array_push(v___x_1339_, v___x_1285_);
v___x_1341_ = lean_array_push(v___x_1340_, v___x_1287_);
v___x_1342_ = lean_array_push(v___x_1341_, v___x_1294_);
v___x_1343_ = lean_array_push(v___x_1342_, v___x_1296_);
v___x_1344_ = lean_array_push(v___x_1343_, v___x_1333_);
lean_inc(v___y_1258_);
v___x_1345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1345_, 0, v___y_1253_);
lean_ctor_set(v___x_1345_, 1, v___y_1258_);
lean_ctor_set(v___x_1345_, 2, v___x_1344_);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
v___jp_1347_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1353_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1354_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1355_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1356_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1357_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1359_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_658_) == 1)
{
lean_object* v_val_1360_; lean_object* v___x_1361_; 
v_val_1360_ = lean_ctor_get(v_doc_x3f_658_, 0);
lean_inc(v_val_1360_);
lean_dec_ref_known(v_doc_x3f_658_, 1);
v___x_1361_ = l_Array_mkArray1___redArg(v_val_1360_);
v___y_1249_ = v___x_1353_;
v___y_1250_ = v___x_1356_;
v___y_1251_ = v___y_1348_;
v___y_1252_ = v___y_1349_;
v___y_1253_ = v___y_1350_;
v___y_1254_ = v_a_1352_;
v___y_1255_ = v___x_1359_;
v___y_1256_ = v___x_1355_;
v___y_1257_ = v___x_1354_;
v___y_1258_ = v___x_1357_;
v___y_1259_ = v___x_1358_;
v___y_1260_ = v___y_1351_;
v___y_1261_ = v___x_1361_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1362_; 
lean_dec(v_doc_x3f_658_);
v___x_1362_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_1249_ = v___x_1353_;
v___y_1250_ = v___x_1356_;
v___y_1251_ = v___y_1348_;
v___y_1252_ = v___y_1349_;
v___y_1253_ = v___y_1350_;
v___y_1254_ = v_a_1352_;
v___y_1255_ = v___x_1359_;
v___y_1256_ = v___x_1355_;
v___y_1257_ = v___x_1354_;
v___y_1258_ = v___x_1357_;
v___y_1259_ = v___x_1358_;
v___y_1260_ = v___y_1351_;
v___y_1261_ = v___x_1362_;
goto v___jp_1248_;
}
}
v___jp_1363_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_inc_ref_n(v___y_1372_, 4);
v___x_1376_ = l_Array_append___redArg(v___y_1372_, v___y_1375_);
lean_dec_ref(v___y_1375_);
lean_inc_n(v___y_1369_, 10);
lean_inc_n(v___y_1374_, 35);
v___x_1377_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1377_, 0, v___y_1374_);
lean_ctor_set(v___x_1377_, 1, v___y_1369_);
lean_ctor_set(v___x_1377_, 2, v___x_1376_);
v___x_1378_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1379_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1380_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1366_, 11);
v___x_1381_ = l_Lean_Name_mkStr4(v___y_1366_, v___x_1378_, v___x_1379_, v___x_1380_);
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___y_1374_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1385_ = l_Lean_Syntax_SepArray_ofElems(v___x_1384_, v___y_1365_);
lean_dec_ref(v___y_1365_);
v___x_1386_ = l_Array_append___redArg(v___y_1372_, v___x_1385_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1387_, 0, v___y_1374_);
lean_ctor_set(v___x_1387_, 1, v___y_1369_);
lean_ctor_set(v___x_1387_, 2, v___x_1386_);
v___x_1388_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___y_1374_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = l_Lean_Syntax_node3(v___y_1374_, v___x_1381_, v___x_1383_, v___x_1387_, v___x_1389_);
v___x_1391_ = l_Lean_Syntax_node1(v___y_1374_, v___y_1369_, v___x_1390_);
lean_inc_ref(v___y_1371_);
v___x_1392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___y_1374_);
lean_ctor_set(v___x_1392_, 1, v___y_1371_);
v___x_1393_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1394_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1368_, 3);
lean_inc_n(v___y_1370_, 3);
v___x_1395_ = l_Lean_addMacroScope(v___y_1370_, v___x_1394_, v___y_1368_);
v___x_1396_ = lean_box(0);
v___x_1397_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1397_, 0, v___y_1374_);
lean_ctor_set(v___x_1397_, 1, v___x_1393_);
lean_ctor_set(v___x_1397_, 2, v___x_1395_);
lean_ctor_set(v___x_1397_, 3, v___x_1396_);
v___x_1398_ = l_Lean_mkIdent(v_k_661_);
v___x_1399_ = l_Lean_Syntax_node2(v___y_1374_, v___y_1369_, v___x_1397_, v___x_1398_);
v___x_1400_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___y_1374_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___x_1402_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__35, &l_Lean_Elab_Command_elabElabRulesAux___closed__35_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__35);
v___x_1403_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__36));
lean_inc_ref_n(v___y_1373_, 2);
v___x_1404_ = l_Lean_Name_mkStr4(v___y_1366_, v___y_1373_, v___x_1379_, v___x_1403_);
lean_inc(v___x_1404_);
v___x_1405_ = l_Lean_addMacroScope(v___y_1370_, v___x_1404_, v___y_1368_);
v___x_1406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1404_);
lean_ctor_set(v___x_1406_, 1, v___x_1396_);
v___x_1407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v___x_1396_);
v___x_1408_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1408_, 0, v___y_1374_);
lean_ctor_set(v___x_1408_, 1, v___x_1402_);
lean_ctor_set(v___x_1408_, 2, v___x_1405_);
lean_ctor_set(v___x_1408_, 3, v___x_1407_);
v___x_1409_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___y_1374_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1412_ = l_Lean_Name_mkStr4(v___y_1366_, v___x_1378_, v___x_1379_, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___y_1374_);
lean_ctor_set(v___x_1413_, 1, v___x_1411_);
v___x_1414_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_1415_ = l_Lean_Name_mkStr4(v___y_1366_, v___x_1378_, v___x_1379_, v___x_1414_);
v___x_1416_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_1417_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1418_ = l_Lean_addMacroScope(v___y_1370_, v___x_1417_, v___y_1368_);
v___x_1419_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1419_, 0, v___y_1374_);
lean_ctor_set(v___x_1419_, 1, v___x_1416_);
lean_ctor_set(v___x_1419_, 2, v___x_1418_);
lean_ctor_set(v___x_1419_, 3, v___x_1396_);
v___x_1420_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1421_ = l_Lean_Name_mkStr4(v___y_1366_, v___x_1378_, v___x_1379_, v___x_1420_);
v___x_1422_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1423_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___y_1374_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = l_Lean_Syntax_node1(v___y_1374_, v___x_1421_, v___x_1423_);
lean_inc(v___x_1424_);
lean_inc_ref(v___x_1419_);
v___x_1425_ = l_Lean_Syntax_node2(v___y_1374_, v___y_1369_, v___x_1419_, v___x_1424_);
v___x_1426_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1426_, 0, v___y_1374_);
lean_ctor_set(v___x_1426_, 1, v___y_1369_);
lean_ctor_set(v___x_1426_, 2, v___y_1372_);
v___x_1427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___y_1374_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1430_ = l_Lean_Name_mkStr4(v___y_1366_, v___x_1378_, v___x_1379_, v___x_1429_);
v___x_1431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___y_1374_);
lean_ctor_set(v___x_1431_, 1, v___x_1429_);
v___x_1432_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1433_ = l_Lean_Name_mkStr4(v___y_1366_, v___x_1378_, v___x_1379_, v___x_1432_);
lean_inc_ref_n(v___x_1426_, 3);
v___x_1434_ = l_Lean_Syntax_node2(v___y_1374_, v___x_1433_, v___x_1426_, v___x_1419_);
v___x_1435_ = l_Lean_Syntax_node1(v___y_1374_, v___y_1369_, v___x_1434_);
v___x_1436_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___y_1374_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1439_ = l_Lean_Name_mkStr4(v___y_1366_, v___x_1378_, v___x_1379_, v___x_1438_);
v___x_1440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1441_ = l_Lean_Name_mkStr4(v___y_1366_, v___x_1378_, v___x_1379_, v___x_1440_);
v___x_1442_ = l_Array_append___redArg(v___y_1372_, v_a_671_);
lean_dec(v_a_671_);
v___x_1443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___y_1374_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = l_Lean_Syntax_node1(v___y_1374_, v___y_1369_, v___x_1424_);
v___x_1446_ = l_Lean_Syntax_node1(v___y_1374_, v___y_1369_, v___x_1445_);
v___x_1447_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1448_ = l_Lean_Name_mkStr4(v___y_1366_, v___x_1378_, v___x_1379_, v___x_1447_);
v___x_1449_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1450_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___y_1374_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1452_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1453_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1454_ = l_Lean_addMacroScope(v___y_1370_, v___x_1453_, v___y_1368_);
v___x_1455_ = l_Lean_Name_mkStr3(v___y_1366_, v___y_1373_, v___x_1451_);
v___x_1456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
lean_ctor_set(v___x_1456_, 1, v___x_1396_);
v___x_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
lean_ctor_set(v___x_1457_, 1, v___x_1396_);
v___x_1458_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1458_, 0, v___y_1374_);
lean_ctor_set(v___x_1458_, 1, v___x_1452_);
lean_ctor_set(v___x_1458_, 2, v___x_1454_);
lean_ctor_set(v___x_1458_, 3, v___x_1457_);
v___x_1459_ = l_Lean_Syntax_node2(v___y_1374_, v___x_1448_, v___x_1450_, v___x_1458_);
lean_inc_ref(v___x_1428_);
v___x_1460_ = l_Lean_Syntax_node4(v___y_1374_, v___x_1441_, v___x_1444_, v___x_1446_, v___x_1428_, v___x_1459_);
v___x_1461_ = lean_array_push(v___x_1442_, v___x_1460_);
v___x_1462_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1462_, 0, v___y_1374_);
lean_ctor_set(v___x_1462_, 1, v___y_1369_);
lean_ctor_set(v___x_1462_, 2, v___x_1461_);
v___x_1463_ = l_Lean_Syntax_node1(v___y_1374_, v___x_1439_, v___x_1462_);
v___x_1464_ = l_Lean_Syntax_node6(v___y_1374_, v___x_1430_, v___x_1431_, v___x_1426_, v___x_1426_, v___x_1435_, v___x_1437_, v___x_1463_);
v___x_1465_ = l_Lean_Syntax_node4(v___y_1374_, v___x_1415_, v___x_1425_, v___x_1426_, v___x_1428_, v___x_1464_);
v___x_1466_ = l_Lean_Syntax_node2(v___y_1374_, v___x_1412_, v___x_1413_, v___x_1465_);
v___x_1467_ = lean_unsigned_to_nat(9u);
v___x_1468_ = lean_mk_empty_array_with_capacity(v___x_1467_);
v___x_1469_ = lean_array_push(v___x_1468_, v___x_1377_);
v___x_1470_ = lean_array_push(v___x_1469_, v___x_1391_);
v___x_1471_ = lean_array_push(v___x_1470_, v___y_1367_);
v___x_1472_ = lean_array_push(v___x_1471_, v___x_1392_);
v___x_1473_ = lean_array_push(v___x_1472_, v___x_1399_);
v___x_1474_ = lean_array_push(v___x_1473_, v___x_1401_);
v___x_1475_ = lean_array_push(v___x_1474_, v___x_1408_);
v___x_1476_ = lean_array_push(v___x_1475_, v___x_1410_);
v___x_1477_ = lean_array_push(v___x_1476_, v___x_1466_);
lean_inc(v___y_1364_);
v___x_1478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1478_, 0, v___y_1374_);
lean_ctor_set(v___x_1478_, 1, v___y_1364_);
lean_ctor_set(v___x_1478_, 2, v___x_1477_);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
return v___x_1479_;
}
v___jp_1480_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1486_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1487_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1488_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1489_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1490_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1491_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_658_) == 1)
{
lean_object* v_val_1492_; lean_object* v___x_1493_; 
v_val_1492_ = lean_ctor_get(v_doc_x3f_658_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v_doc_x3f_658_, 1);
v___x_1493_ = l_Array_mkArray1___redArg(v_val_1492_);
v___y_1364_ = v___x_1489_;
v___y_1365_ = v___y_1481_;
v___y_1366_ = v___x_1486_;
v___y_1367_ = v___y_1482_;
v___y_1368_ = v___y_1483_;
v___y_1369_ = v___x_1490_;
v___y_1370_ = v_a_1485_;
v___y_1371_ = v___x_1488_;
v___y_1372_ = v___x_1491_;
v___y_1373_ = v___x_1487_;
v___y_1374_ = v___y_1484_;
v___y_1375_ = v___x_1493_;
goto v___jp_1363_;
}
else
{
lean_object* v___x_1494_; 
lean_dec(v_doc_x3f_658_);
v___x_1494_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_1364_ = v___x_1489_;
v___y_1365_ = v___y_1481_;
v___y_1366_ = v___x_1486_;
v___y_1367_ = v___y_1482_;
v___y_1368_ = v___y_1483_;
v___y_1369_ = v___x_1490_;
v___y_1370_ = v_a_1485_;
v___y_1371_ = v___x_1488_;
v___y_1372_ = v___x_1491_;
v___y_1373_ = v___x_1487_;
v___y_1374_ = v___y_1484_;
v___y_1375_ = v___x_1494_;
goto v___jp_1363_;
}
}
v___jp_1495_:
{
lean_object* v___x_1499_; 
lean_inc(v_attrKind_660_);
v___x_1499_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_660_);
if (lean_obj_tag(v_expty_x3f_663_) == 1)
{
lean_object* v_val_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; 
v_val_1500_ = lean_ctor_get(v_expty_x3f_663_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v_expty_x3f_663_, 1);
v___x_1501_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_1502_ = lean_name_eq(v_catName_1496_, v___x_1501_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
v___x_1504_ = lean_name_eq(v_catName_1496_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_dec(v___x_1499_);
lean_del_object(v___x_673_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_attrKind_660_);
lean_dec(v_doc_x3f_658_);
v___x_1505_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__58, &l_Lean_Elab_Command_elabElabRulesAux___closed__58_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58);
v___x_1506_ = l_Lean_MessageData_ofName(v_catName_1496_);
v___x_1507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__60, &l_Lean_Elab_Command_elabElabRulesAux___closed__60_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60);
v___x_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_val_1500_, v___x_1509_, v___y_1497_, v___y_1498_);
lean_dec(v_val_1500_);
return v___x_1510_;
}
else
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_dec(v_catName_1496_);
v___x_1511_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(v_k_661_);
v___x_1512_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_661_, v_attrKind_660_, v_attrs_x3f_659_, v___x_1511_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v___x_1514_ = l_Lean_Elab_Command_getRef___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v___x_1516_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1502_);
lean_dec(v_a_1515_);
v___x_1517_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_quotContext_x3f_1518_; 
v_quotContext_x3f_1518_ = lean_ctor_get(v___y_1497_, 5);
if (lean_obj_tag(v_quotContext_x3f_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; lean_object* v_a_1521_; 
v_a_1519_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1517_, 1);
v___x_1520_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1498_);
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref(v___x_1520_);
v___y_797_ = v___x_1499_;
v___y_798_ = v_val_1500_;
v___y_799_ = v_a_1513_;
v___y_800_ = v_a_1519_;
v___y_801_ = v___x_1516_;
v_a_802_ = v_a_1521_;
goto v___jp_796_;
}
else
{
lean_object* v_a_1522_; lean_object* v_val_1523_; 
v_a_1522_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1517_, 1);
v_val_1523_ = lean_ctor_get(v_quotContext_x3f_1518_, 0);
lean_inc(v_val_1523_);
v___y_797_ = v___x_1499_;
v___y_798_ = v_val_1500_;
v___y_799_ = v_a_1513_;
v___y_800_ = v_a_1522_;
v___y_801_ = v___x_1516_;
v_a_802_ = v_val_1523_;
goto v___jp_796_;
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec(v___x_1516_);
lean_dec(v_a_1513_);
lean_dec(v_val_1500_);
lean_dec(v___x_1499_);
lean_del_object(v___x_673_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
v_a_1524_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1517_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1517_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
else
{
lean_dec(v_a_1513_);
lean_dec(v_val_1500_);
lean_dec(v___x_1499_);
lean_del_object(v___x_673_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
return v___x_1514_;
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_val_1500_);
lean_dec(v___x_1499_);
lean_del_object(v___x_673_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
v_a_1532_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1512_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1512_);
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
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec(v_catName_1496_);
lean_del_object(v___x_673_);
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(v_k_661_);
v___x_1541_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_661_, v_attrKind_660_, v_attrs_x3f_659_, v___x_1540_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1543_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1543_ = l_Lean_Elab_Command_getRef___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; uint8_t v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1545_ = 0;
v___x_1546_ = l_Lean_SourceInfo_fromRef(v_a_1544_, v___x_1545_);
lean_dec(v_a_1544_);
v___x_1547_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_quotContext_x3f_1548_; 
v_quotContext_x3f_1548_ = lean_ctor_get(v___y_1497_, 5);
if (lean_obj_tag(v_quotContext_x3f_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1550_; lean_object* v_a_1551_; 
v_a_1549_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1547_, 1);
v___x_1550_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1498_);
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref(v___x_1550_);
v___y_949_ = v_a_1542_;
v___y_950_ = v_a_1549_;
v___y_951_ = v___x_1499_;
v___y_952_ = v_val_1500_;
v___y_953_ = v___x_1546_;
v_a_954_ = v_a_1551_;
goto v___jp_948_;
}
else
{
lean_object* v_a_1552_; lean_object* v_val_1553_; 
v_a_1552_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1547_, 1);
v_val_1553_ = lean_ctor_get(v_quotContext_x3f_1548_, 0);
lean_inc(v_val_1553_);
v___y_949_ = v_a_1542_;
v___y_950_ = v_a_1552_;
v___y_951_ = v___x_1499_;
v___y_952_ = v_val_1500_;
v___y_953_ = v___x_1546_;
v_a_954_ = v_val_1553_;
goto v___jp_948_;
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec(v___x_1546_);
lean_dec(v_a_1542_);
lean_dec(v_val_1500_);
lean_dec(v___x_1499_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
v_a_1554_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1547_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1547_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_dec(v_a_1542_);
lean_dec(v_val_1500_);
lean_dec(v___x_1499_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
return v___x_1543_;
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec(v_val_1500_);
lean_dec(v___x_1499_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
v_a_1562_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1541_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1541_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
else
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
lean_del_object(v___x_673_);
lean_dec(v_expty_x3f_663_);
v___x_1570_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_1571_ = lean_name_eq(v_catName_1496_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__66));
v___x_1573_ = lean_name_eq(v_catName_1496_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__68));
v___x_1575_ = lean_name_eq(v_catName_1496_, v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__70));
v___x_1577_ = lean_name_eq(v_catName_1496_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; uint8_t v___x_1579_; 
v___x_1578_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
v___x_1579_ = lean_name_eq(v_catName_1496_, v___x_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec(v___x_1499_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_attrKind_660_);
lean_dec(v_doc_x3f_658_);
v___x_1580_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__72, &l_Lean_Elab_Command_elabElabRulesAux___closed__72_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72);
v___x_1581_ = l_Lean_MessageData_ofName(v_catName_1496_);
v___x_1582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_1584_, v___y_1497_, v___y_1498_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec(v_catName_1496_);
v___x_1586_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(v_k_661_);
v___x_1587_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_661_, v_attrKind_660_, v_attrs_x3f_659_, v___x_1586_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = l_Lean_Elab_Command_getRef___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = l_Lean_SourceInfo_fromRef(v_a_1590_, v___x_1577_);
lean_dec(v_a_1590_);
v___x_1592_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_quotContext_x3f_1593_; 
v_quotContext_x3f_1593_ = lean_ctor_get(v___y_1497_, 5);
if (lean_obj_tag(v_quotContext_x3f_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1595_; lean_object* v_a_1596_; 
v_a_1594_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1592_, 1);
v___x_1595_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1498_);
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref(v___x_1595_);
v___y_1234_ = v_a_1588_;
v___y_1235_ = v___x_1591_;
v___y_1236_ = v___x_1499_;
v___y_1237_ = v_a_1594_;
v_a_1238_ = v_a_1596_;
goto v___jp_1233_;
}
else
{
lean_object* v_a_1597_; lean_object* v_val_1598_; 
v_a_1597_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___x_1592_, 1);
v_val_1598_ = lean_ctor_get(v_quotContext_x3f_1593_, 0);
lean_inc(v_val_1598_);
v___y_1234_ = v_a_1588_;
v___y_1235_ = v___x_1591_;
v___y_1236_ = v___x_1499_;
v___y_1237_ = v_a_1597_;
v_a_1238_ = v_val_1598_;
goto v___jp_1233_;
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v___x_1591_);
lean_dec(v_a_1588_);
lean_dec(v___x_1499_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
v_a_1599_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1592_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1592_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
else
{
lean_dec(v_a_1588_);
lean_dec(v___x_1499_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
return v___x_1589_;
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v___x_1499_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
v_a_1607_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1587_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1587_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
else
{
lean_dec(v_catName_1496_);
v___y_1078_ = v___x_1499_;
v___y_1079_ = v___x_1573_;
v___y_1080_ = v___x_1574_;
v___y_1081_ = v___y_1497_;
v___y_1082_ = v___y_1498_;
goto v___jp_1077_;
}
}
else
{
lean_dec(v_catName_1496_);
v___y_1078_ = v___x_1499_;
v___y_1079_ = v___x_1573_;
v___y_1080_ = v___x_1574_;
v___y_1081_ = v___y_1497_;
v___y_1082_ = v___y_1498_;
goto v___jp_1077_;
}
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec(v_catName_1496_);
v___x_1615_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__74));
lean_inc(v_k_661_);
v___x_1616_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_661_, v_attrKind_660_, v_attrs_x3f_659_, v___x_1615_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1618_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v___x_1618_ = l_Lean_Elab_Command_getRef___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1620_ = l_Lean_SourceInfo_fromRef(v_a_1619_, v___x_1571_);
lean_dec(v_a_1619_);
v___x_1621_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_quotContext_x3f_1622_; 
v_quotContext_x3f_1622_ = lean_ctor_get(v___y_1497_, 5);
if (lean_obj_tag(v_quotContext_x3f_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1624_; lean_object* v_a_1625_; 
v_a_1623_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1624_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1498_);
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref(v___x_1624_);
v___y_1348_ = v___x_1499_;
v___y_1349_ = v_a_1623_;
v___y_1350_ = v___x_1620_;
v___y_1351_ = v_a_1617_;
v_a_1352_ = v_a_1625_;
goto v___jp_1347_;
}
else
{
lean_object* v_a_1626_; lean_object* v_val_1627_; 
v_a_1626_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1621_, 1);
v_val_1627_ = lean_ctor_get(v_quotContext_x3f_1622_, 0);
lean_inc(v_val_1627_);
v___y_1348_ = v___x_1499_;
v___y_1349_ = v_a_1626_;
v___y_1350_ = v___x_1620_;
v___y_1351_ = v_a_1617_;
v_a_1352_ = v_val_1627_;
goto v___jp_1347_;
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec(v___x_1620_);
lean_dec(v_a_1617_);
lean_dec(v___x_1499_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
v_a_1628_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1621_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1621_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_dec(v_a_1617_);
lean_dec(v___x_1499_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
return v___x_1618_;
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v___x_1499_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
v_a_1636_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1616_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1616_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_dec(v_catName_1496_);
v___x_1644_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(v_k_661_);
v___x_1645_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_661_, v_attrKind_660_, v_attrs_x3f_659_, v___x_1644_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1647_ = l_Lean_Elab_Command_getRef___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = 0;
v___x_1650_ = l_Lean_SourceInfo_fromRef(v_a_1648_, v___x_1649_);
lean_dec(v_a_1648_);
v___x_1651_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_quotContext_x3f_1652_; 
v_quotContext_x3f_1652_ = lean_ctor_get(v___y_1497_, 5);
if (lean_obj_tag(v_quotContext_x3f_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1654_; lean_object* v_a_1655_; 
v_a_1653_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1654_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1498_);
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref(v___x_1654_);
v___y_1481_ = v_a_1646_;
v___y_1482_ = v___x_1499_;
v___y_1483_ = v_a_1653_;
v___y_1484_ = v___x_1650_;
v_a_1485_ = v_a_1655_;
goto v___jp_1480_;
}
else
{
lean_object* v_a_1656_; lean_object* v_val_1657_; 
v_a_1656_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1651_, 1);
v_val_1657_ = lean_ctor_get(v_quotContext_x3f_1652_, 0);
lean_inc(v_val_1657_);
v___y_1481_ = v_a_1646_;
v___y_1482_ = v___x_1499_;
v___y_1483_ = v_a_1656_;
v___y_1484_ = v___x_1650_;
v_a_1485_ = v_val_1657_;
goto v___jp_1480_;
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v___x_1650_);
lean_dec(v_a_1646_);
lean_dec(v___x_1499_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
v_a_1658_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1651_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1651_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_dec(v_a_1646_);
lean_dec(v___x_1499_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
return v___x_1647_;
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec(v___x_1499_);
lean_dec(v_a_671_);
lean_dec(v_k_661_);
lean_dec(v_doc_x3f_658_);
v_a_1666_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1645_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1645_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
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
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec(v_expty_x3f_663_);
lean_dec(v_k_661_);
lean_dec(v_attrKind_660_);
lean_dec(v_doc_x3f_658_);
v_a_1688_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_670_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_670_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object* v_doc_x3f_1696_, lean_object* v_attrs_x3f_1697_, lean_object* v_attrKind_1698_, lean_object* v_k_1699_, lean_object* v_cat_x3f_1700_, lean_object* v_expty_x3f_1701_, lean_object* v_alts_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Elab_Command_elabElabRulesAux(v_doc_x3f_1696_, v_attrs_x3f_1697_, v_attrKind_1698_, v_k_1699_, v_cat_x3f_1700_, v_expty_x3f_1701_, v_alts_1702_, v_a_1703_, v_a_1704_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_cat_x3f_1700_);
lean_dec(v_attrs_x3f_1697_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object* v_00_u03b1_1707_, lean_object* v_ref_1708_, lean_object* v_msg_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_1708_, v_msg_1709_, v___y_1710_, v___y_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object* v_00_u03b1_1714_, lean_object* v_ref_1715_, lean_object* v_msg_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(v_00_u03b1_1714_, v_ref_1715_, v_msg_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v_ref_1715_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(lean_object* v_msgData_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_1721_, v___y_1723_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___boxed(lean_object* v_msgData_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(v_msgData_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(lean_object* v_00_u03b1_1731_, lean_object* v_msg_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_1732_, v___y_1733_, v___y_1734_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___boxed(lean_object* v_00_u03b1_1737_, lean_object* v_msg_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(v_00_u03b1_1737_, v_msg_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(lean_object* v_msgData_1743_, lean_object* v_macroStack_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_msgData_1743_, v_macroStack_1744_, v___y_1746_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___boxed(lean_object* v_msgData_1749_, lean_object* v_macroStack_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(v_msgData_1749_, v_macroStack_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object* v_x_1755_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object* v_x_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Elab_Command_elabElabRules___lam__0(v_x_1757_);
lean_dec(v_x_1757_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object* v___x_1763_, lean_object* v___x_1764_, lean_object* v_attrKind_1765_, lean_object* v_expty_x3f_1766_, lean_object* v___f_1767_, lean_object* v_cat_x3f_1768_, lean_object* v___x_1769_, lean_object* v___x_1770_, lean_object* v_attrs_x3f_1771_, lean_object* v___x_1772_, lean_object* v___x_1773_, lean_object* v___x_1774_, lean_object* v_doc_x3f_1775_, lean_object* v_kind_x3f_1776_, lean_object* v_alts_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Elab_Command_getRef___redArg(v___y_1778_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1890_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1890_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1890_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
uint8_t v___x_1786_; lean_object* v___x_1787_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___x_1879_; 
v___x_1786_ = 0;
v___x_1787_ = l_Lean_SourceInfo_fromRef(v_a_1782_, v___x_1786_);
lean_dec(v_a_1782_);
v___x_1879_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1778_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_quotContext_x3f_1880_; 
lean_dec_ref_known(v___x_1879_, 1);
v_quotContext_x3f_1880_ = lean_ctor_get(v___y_1778_, 5);
if (lean_obj_tag(v_quotContext_x3f_1880_) == 0)
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1779_);
lean_dec_ref(v___x_1881_);
goto v___jp_1873_;
}
else
{
goto v___jp_1873_;
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v___x_1787_);
lean_del_object(v___x_1784_);
lean_dec(v_kind_x3f_1776_);
lean_dec(v_doc_x3f_1775_);
lean_dec_ref(v___x_1774_);
lean_dec_ref(v___x_1773_);
lean_dec_ref(v___x_1772_);
lean_dec_ref(v___x_1769_);
lean_dec(v_cat_x3f_1768_);
lean_dec_ref(v___f_1767_);
lean_dec(v_expty_x3f_1766_);
lean_dec(v_attrKind_1765_);
lean_dec(v___x_1764_);
lean_dec(v___x_1763_);
v_a_1882_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1879_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1879_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
v___jp_1788_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
lean_inc_ref_n(v___y_1789_, 2);
v___x_1797_ = l_Array_append___redArg(v___y_1789_, v___y_1796_);
lean_dec_ref(v___y_1796_);
lean_inc_n(v___y_1793_, 2);
lean_inc_n(v___x_1787_, 3);
v___x_1798_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1787_);
lean_ctor_set(v___x_1798_, 1, v___y_1793_);
lean_ctor_set(v___x_1798_, 2, v___x_1797_);
v___x_1799_ = l_Array_append___redArg(v___y_1789_, v_alts_1777_);
v___x_1800_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1787_);
lean_ctor_set(v___x_1800_, 1, v___y_1793_);
lean_ctor_set(v___x_1800_, 2, v___x_1799_);
v___x_1801_ = l_Lean_Syntax_node1(v___x_1787_, v___x_1763_, v___x_1800_);
v___x_1802_ = l_Lean_Syntax_node8(v___x_1787_, v___x_1764_, v___y_1791_, v___y_1792_, v_attrKind_1765_, v___y_1795_, v___y_1790_, v___y_1794_, v___x_1798_, v___x_1801_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1802_);
v___x_1804_ = v___x_1784_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
v___jp_1806_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_inc_ref(v___y_1807_);
v___x_1814_ = l_Array_append___redArg(v___y_1807_, v___y_1813_);
lean_dec_ref(v___y_1813_);
lean_inc(v___y_1811_);
lean_inc(v___x_1787_);
v___x_1815_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1787_);
lean_ctor_set(v___x_1815_, 1, v___y_1811_);
lean_ctor_set(v___x_1815_, 2, v___x_1814_);
if (lean_obj_tag(v_expty_x3f_1766_) == 1)
{
lean_object* v_val_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_dec_ref(v___f_1767_);
v_val_1816_ = lean_ctor_get(v_expty_x3f_1766_, 0);
lean_inc(v_val_1816_);
lean_dec_ref_known(v_expty_x3f_1766_, 1);
v___x_1817_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___x_1787_);
v___x_1818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1787_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = l_Array_mkArray2___redArg(v___x_1818_, v_val_1816_);
v___y_1789_ = v___y_1807_;
v___y_1790_ = v___y_1808_;
v___y_1791_ = v___y_1809_;
v___y_1792_ = v___y_1810_;
v___y_1793_ = v___y_1811_;
v___y_1794_ = v___x_1815_;
v___y_1795_ = v___y_1812_;
v___y_1796_ = v___x_1819_;
goto v___jp_1788_;
}
else
{
lean_object* v___x_1820_; 
v___x_1820_ = lean_apply_1(v___f_1767_, v_expty_x3f_1766_);
v___y_1789_ = v___y_1807_;
v___y_1790_ = v___y_1808_;
v___y_1791_ = v___y_1809_;
v___y_1792_ = v___y_1810_;
v___y_1793_ = v___y_1811_;
v___y_1794_ = v___x_1815_;
v___y_1795_ = v___y_1812_;
v___y_1796_ = v___x_1820_;
goto v___jp_1788_;
}
}
v___jp_1821_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_inc_ref(v___y_1822_);
v___x_1828_ = l_Array_append___redArg(v___y_1822_, v___y_1827_);
lean_dec_ref(v___y_1827_);
lean_inc(v___y_1825_);
lean_inc(v___x_1787_);
v___x_1829_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1787_);
lean_ctor_set(v___x_1829_, 1, v___y_1825_);
lean_ctor_set(v___x_1829_, 2, v___x_1828_);
if (lean_obj_tag(v_cat_x3f_1768_) == 1)
{
lean_object* v_val_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_val_1830_ = lean_ctor_get(v_cat_x3f_1768_, 0);
lean_inc(v_val_1830_);
lean_dec_ref_known(v_cat_x3f_1768_, 1);
v___x_1831_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___x_1787_);
v___x_1832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1787_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = l_Array_mkArray2___redArg(v___x_1832_, v_val_1830_);
v___y_1807_ = v___y_1822_;
v___y_1808_ = v___x_1829_;
v___y_1809_ = v___y_1823_;
v___y_1810_ = v___y_1824_;
v___y_1811_ = v___y_1825_;
v___y_1812_ = v___y_1826_;
v___y_1813_ = v___x_1833_;
goto v___jp_1806_;
}
else
{
lean_object* v___x_1834_; 
lean_inc_ref(v___f_1767_);
v___x_1834_ = lean_apply_1(v___f_1767_, v_cat_x3f_1768_);
v___y_1807_ = v___y_1822_;
v___y_1808_ = v___x_1829_;
v___y_1809_ = v___y_1823_;
v___y_1810_ = v___y_1824_;
v___y_1811_ = v___y_1825_;
v___y_1812_ = v___y_1826_;
v___y_1813_ = v___x_1834_;
goto v___jp_1806_;
}
}
v___jp_1835_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_inc_ref(v___y_1836_);
v___x_1840_ = l_Array_append___redArg(v___y_1836_, v___y_1839_);
lean_dec_ref(v___y_1839_);
lean_inc(v___y_1838_);
lean_inc_n(v___x_1787_, 2);
v___x_1841_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1787_);
lean_ctor_set(v___x_1841_, 1, v___y_1838_);
lean_ctor_set(v___x_1841_, 2, v___x_1840_);
v___x_1842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1787_);
lean_ctor_set(v___x_1842_, 1, v___x_1769_);
if (lean_obj_tag(v_kind_x3f_1776_) == 0)
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_mk_empty_array_with_capacity(v___x_1770_);
v___y_1822_ = v___y_1836_;
v___y_1823_ = v___y_1837_;
v___y_1824_ = v___x_1841_;
v___y_1825_ = v___y_1838_;
v___y_1826_ = v___x_1842_;
v___y_1827_ = v___x_1843_;
goto v___jp_1821_;
}
else
{
lean_object* v_val_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v_val_1844_ = lean_ctor_get(v_kind_x3f_1776_, 0);
lean_inc(v_val_1844_);
lean_dec_ref_known(v_kind_x3f_1776_, 1);
v___x_1845_ = l_Lean_mkIdent(v_val_1844_);
v___x_1846_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___x_1787_, 4);
v___x_1847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1787_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__2));
v___x_1849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1787_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1851_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1787_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_1853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1787_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l_Array_mkArray5___redArg(v___x_1847_, v___x_1849_, v___x_1851_, v___x_1845_, v___x_1853_);
v___y_1822_ = v___y_1836_;
v___y_1823_ = v___y_1837_;
v___y_1824_ = v___x_1841_;
v___y_1825_ = v___y_1838_;
v___y_1826_ = v___x_1842_;
v___y_1827_ = v___x_1854_;
goto v___jp_1821_;
}
}
v___jp_1855_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_inc_ref(v___y_1856_);
v___x_1859_ = l_Array_append___redArg(v___y_1856_, v___y_1858_);
lean_dec_ref(v___y_1858_);
lean_inc(v___y_1857_);
lean_inc(v___x_1787_);
v___x_1860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1787_);
lean_ctor_set(v___x_1860_, 1, v___y_1857_);
lean_ctor_set(v___x_1860_, 2, v___x_1859_);
if (lean_obj_tag(v_attrs_x3f_1771_) == 1)
{
lean_object* v_val_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v_val_1861_ = lean_ctor_get(v_attrs_x3f_1771_, 0);
v___x_1862_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
v___x_1863_ = l_Lean_Name_mkStr4(v___x_1772_, v___x_1773_, v___x_1774_, v___x_1862_);
v___x_1864_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___x_1787_, 4);
v___x_1865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1787_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
lean_inc_ref(v___y_1856_);
v___x_1866_ = l_Array_append___redArg(v___y_1856_, v_val_1861_);
lean_inc(v___y_1857_);
v___x_1867_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1787_);
lean_ctor_set(v___x_1867_, 1, v___y_1857_);
lean_ctor_set(v___x_1867_, 2, v___x_1866_);
v___x_1868_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1787_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = l_Lean_Syntax_node3(v___x_1787_, v___x_1863_, v___x_1865_, v___x_1867_, v___x_1869_);
v___x_1871_ = l_Array_mkArray1___redArg(v___x_1870_);
v___y_1836_ = v___y_1856_;
v___y_1837_ = v___x_1860_;
v___y_1838_ = v___y_1857_;
v___y_1839_ = v___x_1871_;
goto v___jp_1835_;
}
else
{
lean_object* v___x_1872_; 
lean_dec_ref(v___x_1774_);
lean_dec_ref(v___x_1773_);
lean_dec_ref(v___x_1772_);
v___x_1872_ = lean_mk_empty_array_with_capacity(v___x_1770_);
v___y_1836_ = v___y_1856_;
v___y_1837_ = v___x_1860_;
v___y_1838_ = v___y_1857_;
v___y_1839_ = v___x_1872_;
goto v___jp_1835_;
}
}
v___jp_1873_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1875_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_1775_) == 1)
{
lean_object* v_val_1876_; lean_object* v___x_1877_; 
v_val_1876_ = lean_ctor_get(v_doc_x3f_1775_, 0);
lean_inc(v_val_1876_);
lean_dec_ref_known(v_doc_x3f_1775_, 1);
v___x_1877_ = l_Array_mkArray1___redArg(v_val_1876_);
v___y_1856_ = v___x_1875_;
v___y_1857_ = v___x_1874_;
v___y_1858_ = v___x_1877_;
goto v___jp_1855_;
}
else
{
lean_object* v___x_1878_; 
lean_dec(v_doc_x3f_1775_);
v___x_1878_ = lean_mk_empty_array_with_capacity(v___x_1770_);
v___y_1856_ = v___x_1875_;
v___y_1857_ = v___x_1874_;
v___y_1858_ = v___x_1878_;
goto v___jp_1855_;
}
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_kind_x3f_1776_);
lean_dec(v_doc_x3f_1775_);
lean_dec_ref(v___x_1774_);
lean_dec_ref(v___x_1773_);
lean_dec_ref(v___x_1772_);
lean_dec_ref(v___x_1769_);
lean_dec(v_cat_x3f_1768_);
lean_dec_ref(v___f_1767_);
lean_dec(v_expty_x3f_1766_);
lean_dec(v_attrKind_1765_);
lean_dec(v___x_1764_);
lean_dec(v___x_1763_);
v_a_1891_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1781_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1781_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object** _args){
lean_object* v___x_1899_ = _args[0];
lean_object* v___x_1900_ = _args[1];
lean_object* v_attrKind_1901_ = _args[2];
lean_object* v_expty_x3f_1902_ = _args[3];
lean_object* v___f_1903_ = _args[4];
lean_object* v_cat_x3f_1904_ = _args[5];
lean_object* v___x_1905_ = _args[6];
lean_object* v___x_1906_ = _args[7];
lean_object* v_attrs_x3f_1907_ = _args[8];
lean_object* v___x_1908_ = _args[9];
lean_object* v___x_1909_ = _args[10];
lean_object* v___x_1910_ = _args[11];
lean_object* v_doc_x3f_1911_ = _args[12];
lean_object* v_kind_x3f_1912_ = _args[13];
lean_object* v_alts_1913_ = _args[14];
lean_object* v___y_1914_ = _args[15];
lean_object* v___y_1915_ = _args[16];
lean_object* v___y_1916_ = _args[17];
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_Elab_Command_elabElabRules___lam__1(v___x_1899_, v___x_1900_, v_attrKind_1901_, v_expty_x3f_1902_, v___f_1903_, v_cat_x3f_1904_, v___x_1905_, v___x_1906_, v_attrs_x3f_1907_, v___x_1908_, v___x_1909_, v___x_1910_, v_doc_x3f_1911_, v_kind_x3f_1912_, v_alts_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec_ref(v_alts_1913_);
lean_dec(v_attrs_x3f_1907_);
lean_dec(v___x_1906_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object* v___f_1946_, lean_object* v_stx_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1951_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1952_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1953_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_1954_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
lean_inc(v_stx_1947_);
v___x_1955_ = l_Lean_Syntax_isOfKind(v_stx_1947_, v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; 
lean_dec(v_stx_1947_);
lean_dec_ref(v___f_1946_);
v___x_1956_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_1956_;
}
else
{
lean_object* v___x_1957_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v_expty_x3f_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v_cat_x3f_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v_expty_x3f_2014_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v_cat_x3f_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v_attrs_x3f_2063_; lean_object* v_doc_x3f_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_2110_ = l_Lean_Syntax_getArg(v_stx_1947_, v___x_1957_);
v___x_2111_ = l_Lean_Syntax_isNone(v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2110_);
v___x_2113_ = l_Lean_Syntax_matchesNull(v___x_2110_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_dec(v___x_2110_);
lean_dec(v_stx_1947_);
lean_dec_ref(v___f_1946_);
v___x_2114_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2114_;
}
else
{
lean_object* v_doc_x3f_2115_; 
v_doc_x3f_2115_ = l_Lean_Syntax_getArg(v___x_2110_, v___x_1957_);
lean_dec(v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(v_doc_x3f_2115_);
v___x_2119_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2115_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; 
lean_dec(v_doc_x3f_2115_);
lean_dec(v_stx_1947_);
lean_dec_ref(v___f_1946_);
v___x_2120_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2120_;
}
else
{
goto v___jp_2116_;
}
}
else
{
goto v___jp_2116_;
}
v___jp_2116_:
{
lean_object* v___x_2117_; 
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v_doc_x3f_2115_);
v_doc_x3f_2094_ = v___x_2117_;
v___y_2095_ = v___y_1948_;
v___y_2096_ = v___y_1949_;
goto v___jp_2093_;
}
}
}
else
{
lean_object* v___x_2121_; 
lean_dec(v___x_2110_);
v___x_2121_ = lean_box(0);
v_doc_x3f_2094_ = v___x_2121_;
v___y_2095_ = v___y_1948_;
v___y_2096_ = v___y_1949_;
goto v___jp_2093_;
}
v___jp_1958_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1968_ = lean_unsigned_to_nat(7u);
v___x_1969_ = l_Lean_Syntax_getArg(v_stx_1947_, v___x_1968_);
lean_dec(v_stx_1947_);
v___x_1970_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc_ref(v___y_1963_);
v___x_1971_ = l_Lean_Name_mkStr4(v___x_1951_, v___x_1952_, v___y_1963_, v___x_1970_);
lean_inc(v___x_1969_);
v___x_1972_ = l_Lean_Syntax_isOfKind(v___x_1969_, v___x_1971_);
lean_dec(v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; 
lean_dec(v___x_1969_);
lean_dec(v_expty_x3f_1965_);
lean_dec(v___y_1964_);
lean_dec(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec(v___y_1959_);
v___x_1973_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_1973_;
}
else
{
lean_object* v___x_1974_; lean_object* v_alts_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1974_ = l_Lean_Syntax_getArg(v___x_1969_, v___x_1957_);
lean_dec(v___x_1969_);
v_alts_1975_ = l_Lean_Syntax_getArgs(v___x_1974_);
lean_dec(v___x_1974_);
v___x_1976_ = l_Lean_TSyntax_getId(v___y_1961_);
lean_dec(v___y_1961_);
v___x_1977_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_1976_, v___y_1966_, v___y_1967_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1979_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1977_, 1);
v___x_1979_ = l_Lean_Elab_Command_elabElabRulesAux(v___y_1962_, v___y_1964_, v___y_1959_, v_a_1978_, v___y_1960_, v_expty_x3f_1965_, v_alts_1975_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1960_);
lean_dec(v___y_1964_);
return v___x_1979_;
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v_alts_1975_);
lean_dec(v_expty_x3f_1965_);
lean_dec(v___y_1964_);
lean_dec(v___y_1962_);
lean_dec(v___y_1960_);
lean_dec(v___y_1959_);
v_a_1980_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1977_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1977_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
v___jp_1988_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_1999_ = lean_unsigned_to_nat(6u);
v___x_2000_ = l_Lean_Syntax_getArg(v_stx_1947_, v___x_1999_);
v___x_2001_ = l_Lean_Syntax_isNone(v___x_2000_);
if (v___x_2001_ == 0)
{
uint8_t v___x_2002_; 
lean_inc(v___x_2000_);
v___x_2002_ = l_Lean_Syntax_matchesNull(v___x_2000_, v___y_1989_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; 
lean_dec(v___x_2000_);
lean_dec(v_cat_x3f_1996_);
lean_dec(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec(v_stx_1947_);
v___x_2003_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2003_;
}
else
{
lean_object* v_expty_x3f_2004_; lean_object* v___x_2005_; 
v_expty_x3f_2004_ = l_Lean_Syntax_getArg(v___x_2000_, v___y_1990_);
lean_dec(v___x_2000_);
v___x_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2005_, 0, v_expty_x3f_2004_);
v___y_1959_ = v___y_1991_;
v___y_1960_ = v_cat_x3f_1996_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1994_;
v___y_1963_ = v___y_1993_;
v___y_1964_ = v___y_1995_;
v_expty_x3f_1965_ = v___x_2005_;
v___y_1966_ = v___y_1997_;
v___y_1967_ = v___y_1998_;
goto v___jp_1958_;
}
}
else
{
lean_object* v___x_2006_; 
lean_dec(v___x_2000_);
v___x_2006_ = lean_box(0);
v___y_1959_ = v___y_1991_;
v___y_1960_ = v_cat_x3f_1996_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1994_;
v___y_1963_ = v___y_1993_;
v___y_1964_ = v___y_1995_;
v_expty_x3f_1965_ = v___x_2006_;
v___y_1966_ = v___y_1997_;
v___y_1967_ = v___y_1998_;
goto v___jp_1958_;
}
}
v___jp_2007_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2015_ = lean_unsigned_to_nat(7u);
v___x_2016_ = l_Lean_Syntax_getArg(v_stx_1947_, v___x_2015_);
lean_dec(v_stx_1947_);
v___x_2017_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_2018_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__2));
lean_inc(v___x_2016_);
v___x_2019_ = l_Lean_Syntax_isOfKind(v___x_2016_, v___x_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; 
lean_dec(v___x_2016_);
lean_dec(v_expty_x3f_2014_);
lean_dec(v___y_2012_);
lean_dec(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___f_1946_);
v___x_2020_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2020_;
}
else
{
lean_object* v___f_2021_; lean_object* v___x_2022_; lean_object* v_alts_2023_; lean_object* v___x_2024_; 
v___f_2021_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lam__1___boxed), 18, 13);
lean_closure_set(v___f_2021_, 0, v___x_2018_);
lean_closure_set(v___f_2021_, 1, v___x_1954_);
lean_closure_set(v___f_2021_, 2, v___y_2012_);
lean_closure_set(v___f_2021_, 3, v_expty_x3f_2014_);
lean_closure_set(v___f_2021_, 4, v___f_1946_);
lean_closure_set(v___f_2021_, 5, v___y_2008_);
lean_closure_set(v___f_2021_, 6, v___x_1953_);
lean_closure_set(v___f_2021_, 7, v___x_1957_);
lean_closure_set(v___f_2021_, 8, v___y_2010_);
lean_closure_set(v___f_2021_, 9, v___x_1951_);
lean_closure_set(v___f_2021_, 10, v___x_1952_);
lean_closure_set(v___f_2021_, 11, v___x_2017_);
lean_closure_set(v___f_2021_, 12, v___y_2009_);
v___x_2022_ = l_Lean_Syntax_getArg(v___x_2016_, v___x_1957_);
lean_dec(v___x_2016_);
v_alts_2023_ = l_Lean_Syntax_getArgs(v___x_2022_);
lean_dec(v___x_2022_);
v___x_2024_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_2023_, v___x_1953_, v___f_2021_, v___y_2013_, v___y_2011_);
lean_dec_ref(v_alts_2023_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
v_a_2033_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2024_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2024_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
v___jp_2041_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; 
v___x_2050_ = lean_unsigned_to_nat(6u);
v___x_2051_ = l_Lean_Syntax_getArg(v_stx_1947_, v___x_2050_);
v___x_2052_ = l_Lean_Syntax_isNone(v___x_2051_);
if (v___x_2052_ == 0)
{
uint8_t v___x_2053_; 
lean_inc(v___x_2051_);
v___x_2053_ = l_Lean_Syntax_matchesNull(v___x_2051_, v___y_2045_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; 
lean_dec(v___x_2051_);
lean_dec(v_cat_x3f_2047_);
lean_dec(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec(v_stx_1947_);
lean_dec_ref(v___f_1946_);
v___x_2054_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2054_;
}
else
{
lean_object* v_expty_x3f_2055_; lean_object* v___x_2056_; 
v_expty_x3f_2055_ = l_Lean_Syntax_getArg(v___x_2051_, v___y_2046_);
lean_dec(v___x_2051_);
v___x_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2056_, 0, v_expty_x3f_2055_);
v___y_2008_ = v_cat_x3f_2047_;
v___y_2009_ = v___y_2043_;
v___y_2010_ = v___y_2042_;
v___y_2011_ = v___y_2049_;
v___y_2012_ = v___y_2044_;
v___y_2013_ = v___y_2048_;
v_expty_x3f_2014_ = v___x_2056_;
goto v___jp_2007_;
}
}
else
{
lean_object* v___x_2057_; 
lean_dec(v___x_2051_);
v___x_2057_ = lean_box(0);
v___y_2008_ = v_cat_x3f_2047_;
v___y_2009_ = v___y_2043_;
v___y_2010_ = v___y_2042_;
v___y_2011_ = v___y_2049_;
v___y_2012_ = v___y_2044_;
v___y_2013_ = v___y_2048_;
v_expty_x3f_2014_ = v___x_2057_;
goto v___jp_2007_;
}
}
v___jp_2058_:
{
lean_object* v___x_2064_; lean_object* v_attrKind_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2064_ = lean_unsigned_to_nat(2u);
v_attrKind_2065_ = l_Lean_Syntax_getArg(v_stx_1947_, v___x_2064_);
v___x_2066_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_2067_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v_attrKind_2065_);
v___x_2068_ = l_Lean_Syntax_isOfKind(v_attrKind_2065_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; 
lean_dec(v_attrKind_2065_);
lean_dec(v_attrs_x3f_2063_);
lean_dec(v___y_2059_);
lean_dec(v_stx_1947_);
lean_dec_ref(v___f_1946_);
v___x_2069_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2069_;
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2070_ = lean_unsigned_to_nat(4u);
v___x_2071_ = l_Lean_Syntax_getArg(v_stx_1947_, v___x_2070_);
lean_inc(v___x_2071_);
v___x_2072_ = l_Lean_Syntax_matchesNull(v___x_2071_, v___x_1957_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; uint8_t v___x_2074_; 
lean_dec_ref(v___f_1946_);
v___x_2073_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2071_);
v___x_2074_ = l_Lean_Syntax_matchesNull(v___x_2071_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; 
lean_dec(v___x_2071_);
lean_dec(v_attrKind_2065_);
lean_dec(v_attrs_x3f_2063_);
lean_dec(v___y_2059_);
lean_dec(v_stx_1947_);
v___x_2075_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2075_;
}
else
{
lean_object* v___x_2076_; lean_object* v_kind_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2076_ = lean_unsigned_to_nat(3u);
v_kind_2077_ = l_Lean_Syntax_getArg(v___x_2071_, v___x_2076_);
lean_dec(v___x_2071_);
v___x_2078_ = l_Lean_Syntax_getArg(v_stx_1947_, v___x_2073_);
v___x_2079_ = l_Lean_Syntax_isNone(v___x_2078_);
if (v___x_2079_ == 0)
{
uint8_t v___x_2080_; 
lean_inc(v___x_2078_);
v___x_2080_ = l_Lean_Syntax_matchesNull(v___x_2078_, v___x_2064_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; 
lean_dec(v___x_2078_);
lean_dec(v_kind_2077_);
lean_dec(v_attrKind_2065_);
lean_dec(v_attrs_x3f_2063_);
lean_dec(v___y_2059_);
lean_dec(v_stx_1947_);
v___x_2081_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2081_;
}
else
{
lean_object* v_cat_x3f_2082_; lean_object* v___x_2083_; 
v_cat_x3f_2082_ = l_Lean_Syntax_getArg(v___x_2078_, v___y_2062_);
lean_dec(v___x_2078_);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_cat_x3f_2082_);
v___y_1989_ = v___x_2064_;
v___y_1990_ = v___y_2062_;
v___y_1991_ = v_attrKind_2065_;
v___y_1992_ = v_kind_2077_;
v___y_1993_ = v___x_2066_;
v___y_1994_ = v___y_2059_;
v___y_1995_ = v_attrs_x3f_2063_;
v_cat_x3f_1996_ = v___x_2083_;
v___y_1997_ = v___y_2061_;
v___y_1998_ = v___y_2060_;
goto v___jp_1988_;
}
}
else
{
lean_object* v___x_2084_; 
lean_dec(v___x_2078_);
v___x_2084_ = lean_box(0);
v___y_1989_ = v___x_2064_;
v___y_1990_ = v___y_2062_;
v___y_1991_ = v_attrKind_2065_;
v___y_1992_ = v_kind_2077_;
v___y_1993_ = v___x_2066_;
v___y_1994_ = v___y_2059_;
v___y_1995_ = v_attrs_x3f_2063_;
v_cat_x3f_1996_ = v___x_2084_;
v___y_1997_ = v___y_2061_;
v___y_1998_ = v___y_2060_;
goto v___jp_1988_;
}
}
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
lean_dec(v___x_2071_);
v___x_2085_ = lean_unsigned_to_nat(5u);
v___x_2086_ = l_Lean_Syntax_getArg(v_stx_1947_, v___x_2085_);
v___x_2087_ = l_Lean_Syntax_isNone(v___x_2086_);
if (v___x_2087_ == 0)
{
uint8_t v___x_2088_; 
lean_inc(v___x_2086_);
v___x_2088_ = l_Lean_Syntax_matchesNull(v___x_2086_, v___x_2064_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
lean_dec(v___x_2086_);
lean_dec(v_attrKind_2065_);
lean_dec(v_attrs_x3f_2063_);
lean_dec(v___y_2059_);
lean_dec(v_stx_1947_);
lean_dec_ref(v___f_1946_);
v___x_2089_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2089_;
}
else
{
lean_object* v_cat_x3f_2090_; lean_object* v___x_2091_; 
v_cat_x3f_2090_ = l_Lean_Syntax_getArg(v___x_2086_, v___y_2062_);
lean_dec(v___x_2086_);
v___x_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2091_, 0, v_cat_x3f_2090_);
v___y_2042_ = v_attrs_x3f_2063_;
v___y_2043_ = v___y_2059_;
v___y_2044_ = v_attrKind_2065_;
v___y_2045_ = v___x_2064_;
v___y_2046_ = v___y_2062_;
v_cat_x3f_2047_ = v___x_2091_;
v___y_2048_ = v___y_2061_;
v___y_2049_ = v___y_2060_;
goto v___jp_2041_;
}
}
else
{
lean_object* v___x_2092_; 
lean_dec(v___x_2086_);
v___x_2092_ = lean_box(0);
v___y_2042_ = v_attrs_x3f_2063_;
v___y_2043_ = v___y_2059_;
v___y_2044_ = v_attrKind_2065_;
v___y_2045_ = v___x_2064_;
v___y_2046_ = v___y_2062_;
v_cat_x3f_2047_ = v___x_2092_;
v___y_2048_ = v___y_2061_;
v___y_2049_ = v___y_2060_;
goto v___jp_2041_;
}
}
}
}
v___jp_2093_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2097_ = lean_unsigned_to_nat(1u);
v___x_2098_ = l_Lean_Syntax_getArg(v_stx_1947_, v___x_2097_);
v___x_2099_ = l_Lean_Syntax_isNone(v___x_2098_);
if (v___x_2099_ == 0)
{
uint8_t v___x_2100_; 
lean_inc(v___x_2098_);
v___x_2100_ = l_Lean_Syntax_matchesNull(v___x_2098_, v___x_2097_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; 
lean_dec(v___x_2098_);
lean_dec(v_doc_x3f_2094_);
lean_dec(v_stx_1947_);
lean_dec_ref(v___f_1946_);
v___x_2101_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2101_;
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2102_ = l_Lean_Syntax_getArg(v___x_2098_, v___x_1957_);
lean_dec(v___x_2098_);
v___x_2103_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(v___x_2102_);
v___x_2104_ = l_Lean_Syntax_isOfKind(v___x_2102_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; 
lean_dec(v___x_2102_);
lean_dec(v_doc_x3f_2094_);
lean_dec(v_stx_1947_);
lean_dec_ref(v___f_1946_);
v___x_2105_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2105_;
}
else
{
lean_object* v___x_2106_; lean_object* v_attrs_x3f_2107_; lean_object* v___x_2108_; 
v___x_2106_ = l_Lean_Syntax_getArg(v___x_2102_, v___x_2097_);
lean_dec(v___x_2102_);
v_attrs_x3f_2107_ = l_Lean_Syntax_getArgs(v___x_2106_);
lean_dec(v___x_2106_);
v___x_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2108_, 0, v_attrs_x3f_2107_);
v___y_2059_ = v_doc_x3f_2094_;
v___y_2060_ = v___y_2096_;
v___y_2061_ = v___y_2095_;
v___y_2062_ = v___x_2097_;
v_attrs_x3f_2063_ = v___x_2108_;
goto v___jp_2058_;
}
}
}
else
{
lean_object* v___x_2109_; 
lean_dec(v___x_2098_);
v___x_2109_ = lean_box(0);
v___y_2059_ = v_doc_x3f_2094_;
v___y_2060_ = v___y_2096_;
v___y_2061_ = v___y_2095_;
v___y_2062_ = v___x_2097_;
v_attrs_x3f_2063_ = v___x_2109_;
goto v___jp_2058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object* v___f_2122_, lean_object* v_stx_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lean_Elab_Command_elabElabRules___lam__2(v___f_2122_, v_stx_2123_, v___y_2124_, v___y_2125_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v___f_2135_; lean_object* v___x_2136_; 
v___f_2135_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___closed__1));
v___x_2136_ = l_Lean_Elab_Command_adaptExpander(v___f_2135_, v_a_2131_, v_a_2132_, v_a_2133_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lean_Elab_Command_elabElabRules(v_a_2137_, v_a_2138_, v_a_2139_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1(){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2149_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2150_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
v___x_2151_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2152_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___boxed), 4, 0);
v___x_2153_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2149_, v___x_2150_, v___x_2151_, v___x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object* v_a_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3(){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2183_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6));
v___x_2184_ = l_Lean_addBuiltinDeclarationRanges(v___x_2182_, v___x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t v_sz_2187_, size_t v_i_2188_, lean_object* v_bs_2189_){
_start:
{
uint8_t v___x_2190_; 
v___x_2190_ = lean_usize_dec_lt(v_i_2188_, v_sz_2187_);
if (v___x_2190_ == 0)
{
return v_bs_2189_;
}
else
{
lean_object* v_v_2191_; lean_object* v___x_2192_; lean_object* v_bs_x27_2193_; size_t v___x_2194_; size_t v___x_2195_; lean_object* v___x_2196_; 
v_v_2191_ = lean_array_uget(v_bs_2189_, v_i_2188_);
v___x_2192_ = lean_unsigned_to_nat(0u);
v_bs_x27_2193_ = lean_array_uset(v_bs_2189_, v_i_2188_, v___x_2192_);
v___x_2194_ = ((size_t)1ULL);
v___x_2195_ = lean_usize_add(v_i_2188_, v___x_2194_);
v___x_2196_ = lean_array_uset(v_bs_x27_2193_, v_i_2188_, v_v_2191_);
v_i_2188_ = v___x_2195_;
v_bs_2189_ = v___x_2196_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object* v_sz_2198_, lean_object* v_i_2199_, lean_object* v_bs_2200_){
_start:
{
size_t v_sz_boxed_2201_; size_t v_i_boxed_2202_; lean_object* v_res_2203_; 
v_sz_boxed_2201_ = lean_unbox_usize(v_sz_2198_);
lean_dec(v_sz_2198_);
v_i_boxed_2202_ = lean_unbox_usize(v_i_2199_);
lean_dec(v_i_2199_);
v_res_2203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_boxed_2201_, v_i_boxed_2202_, v_bs_2200_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t v_sz_2204_, size_t v_i_2205_, lean_object* v_bs_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
uint8_t v___x_2210_; 
v___x_2210_ = lean_usize_dec_lt(v_i_2205_, v_sz_2204_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_bs_2206_);
return v___x_2211_;
}
else
{
lean_object* v_v_2212_; lean_object* v___x_2213_; lean_object* v_bs_x27_2214_; lean_object* v___x_2215_; 
v_v_2212_ = lean_array_uget(v_bs_2206_, v_i_2205_);
v___x_2213_ = lean_unsigned_to_nat(0u);
v_bs_x27_2214_ = lean_array_uset(v_bs_2206_, v_i_2205_, v___x_2213_);
v___x_2215_ = l_Lean_Elab_Command_expandMacroArg(v_v_2212_, v___y_2207_, v___y_2208_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; size_t v___x_2217_; size_t v___x_2218_; lean_object* v___x_2219_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2217_ = ((size_t)1ULL);
v___x_2218_ = lean_usize_add(v_i_2205_, v___x_2217_);
v___x_2219_ = lean_array_uset(v_bs_x27_2214_, v_i_2205_, v_a_2216_);
v_i_2205_ = v___x_2218_;
v_bs_2206_ = v___x_2219_;
goto _start;
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec_ref(v_bs_x27_2214_);
v_a_2221_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2215_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2215_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object* v_sz_2229_, lean_object* v_i_2230_, lean_object* v_bs_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
size_t v_sz_boxed_2235_; size_t v_i_boxed_2236_; lean_object* v_res_2237_; 
v_sz_boxed_2235_ = lean_unbox_usize(v_sz_2229_);
lean_dec(v_sz_2229_);
v_i_boxed_2236_ = lean_unbox_usize(v_i_2230_);
lean_dec(v_i_2230_);
v_res_2237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_boxed_2235_, v_i_boxed_2236_, v_bs_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
return v_res_2237_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(lean_object* v_keys_2238_, lean_object* v_i_2239_, lean_object* v_k_2240_){
_start:
{
lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = lean_array_get_size(v_keys_2238_);
v___x_2242_ = lean_nat_dec_lt(v_i_2239_, v___x_2241_);
if (v___x_2242_ == 0)
{
lean_dec(v_i_2239_);
return v___x_2242_;
}
else
{
lean_object* v_k_x27_2243_; uint8_t v___x_2244_; 
v_k_x27_2243_ = lean_array_fget_borrowed(v_keys_2238_, v_i_2239_);
v___x_2244_ = l_Lean_instBEqExtraModUse_beq(v_k_2240_, v_k_x27_2243_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_nat_add(v_i_2239_, v___x_2245_);
lean_dec(v_i_2239_);
v_i_2239_ = v___x_2246_;
goto _start;
}
else
{
lean_dec(v_i_2239_);
return v___x_2242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_keys_2248_, lean_object* v_i_2249_, lean_object* v_k_2250_){
_start:
{
uint8_t v_res_2251_; lean_object* v_r_2252_; 
v_res_2251_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_2248_, v_i_2249_, v_k_2250_);
lean_dec_ref(v_k_2250_);
lean_dec_ref(v_keys_2248_);
v_r_2252_ = lean_box(v_res_2251_);
return v_r_2252_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(lean_object* v_x_2253_, size_t v_x_2254_, lean_object* v_x_2255_){
_start:
{
if (lean_obj_tag(v_x_2253_) == 0)
{
lean_object* v_es_2256_; lean_object* v___x_2257_; size_t v___x_2258_; size_t v___x_2259_; lean_object* v_j_2260_; lean_object* v___x_2261_; 
v_es_2256_ = lean_ctor_get(v_x_2253_, 0);
v___x_2257_ = lean_box(2);
v___x_2258_ = ((size_t)31ULL);
v___x_2259_ = lean_usize_land(v_x_2254_, v___x_2258_);
v_j_2260_ = lean_usize_to_nat(v___x_2259_);
v___x_2261_ = lean_array_get_borrowed(v___x_2257_, v_es_2256_, v_j_2260_);
lean_dec(v_j_2260_);
switch(lean_obj_tag(v___x_2261_))
{
case 0:
{
lean_object* v_key_2262_; uint8_t v___x_2263_; 
v_key_2262_ = lean_ctor_get(v___x_2261_, 0);
v___x_2263_ = l_Lean_instBEqExtraModUse_beq(v_x_2255_, v_key_2262_);
return v___x_2263_;
}
case 1:
{
lean_object* v_node_2264_; size_t v___x_2265_; size_t v___x_2266_; 
v_node_2264_ = lean_ctor_get(v___x_2261_, 0);
v___x_2265_ = ((size_t)5ULL);
v___x_2266_ = lean_usize_shift_right(v_x_2254_, v___x_2265_);
v_x_2253_ = v_node_2264_;
v_x_2254_ = v___x_2266_;
goto _start;
}
default: 
{
uint8_t v___x_2268_; 
v___x_2268_ = 0;
return v___x_2268_;
}
}
}
else
{
lean_object* v_ks_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
v_ks_2269_ = lean_ctor_get(v_x_2253_, 0);
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_ks_2269_, v___x_2270_, v_x_2255_);
return v___x_2271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_x_2272_, lean_object* v_x_2273_, lean_object* v_x_2274_){
_start:
{
size_t v_x_16495__boxed_2275_; uint8_t v_res_2276_; lean_object* v_r_2277_; 
v_x_16495__boxed_2275_ = lean_unbox_usize(v_x_2273_);
lean_dec(v_x_2273_);
v_res_2276_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2272_, v_x_16495__boxed_2275_, v_x_2274_);
lean_dec_ref(v_x_2274_);
lean_dec_ref(v_x_2272_);
v_r_2277_ = lean_box(v_res_2276_);
return v_r_2277_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(lean_object* v_x_2278_, lean_object* v_x_2279_){
_start:
{
uint64_t v___x_2280_; size_t v___x_2281_; uint8_t v___x_2282_; 
v___x_2280_ = l_Lean_instHashableExtraModUse_hash(v_x_2279_);
v___x_2281_ = lean_uint64_to_usize(v___x_2280_);
v___x_2282_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2278_, v___x_2281_, v_x_2279_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_x_2283_, lean_object* v_x_2284_){
_start:
{
uint8_t v_res_2285_; lean_object* v_r_2286_; 
v_res_2285_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_2283_, v_x_2284_);
lean_dec_ref(v_x_2284_);
lean_dec_ref(v_x_2283_);
v_r_2286_ = lean_box(v_res_2285_);
return v_r_2286_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2287_; double v___x_2288_; 
v___x_2287_ = lean_unsigned_to_nat(0u);
v___x_2288_ = lean_float_of_nat(v___x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object* v_cls_2292_, lean_object* v_msg_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_Elab_Command_getRef___redArg(v___y_2294_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2348_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_2293_, v___y_2295_);
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2348_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2348_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v_traceState_2305_; lean_object* v_env_2306_; lean_object* v_messages_2307_; lean_object* v_scopes_2308_; lean_object* v_usedQuotCtxts_2309_; lean_object* v_nextMacroScope_2310_; lean_object* v_maxRecDepth_2311_; lean_object* v_ngen_2312_; lean_object* v_auxDeclNGen_2313_; lean_object* v_infoState_2314_; lean_object* v_snapshotTasks_2315_; lean_object* v_prevLinterStates_2316_; lean_object* v_codeQualityEntryTasks_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2347_; 
v___x_2304_ = lean_st_ref_take(v___y_2295_);
v_traceState_2305_ = lean_ctor_get(v___x_2304_, 9);
v_env_2306_ = lean_ctor_get(v___x_2304_, 0);
v_messages_2307_ = lean_ctor_get(v___x_2304_, 1);
v_scopes_2308_ = lean_ctor_get(v___x_2304_, 2);
v_usedQuotCtxts_2309_ = lean_ctor_get(v___x_2304_, 3);
v_nextMacroScope_2310_ = lean_ctor_get(v___x_2304_, 4);
v_maxRecDepth_2311_ = lean_ctor_get(v___x_2304_, 5);
v_ngen_2312_ = lean_ctor_get(v___x_2304_, 6);
v_auxDeclNGen_2313_ = lean_ctor_get(v___x_2304_, 7);
v_infoState_2314_ = lean_ctor_get(v___x_2304_, 8);
v_snapshotTasks_2315_ = lean_ctor_get(v___x_2304_, 10);
v_prevLinterStates_2316_ = lean_ctor_get(v___x_2304_, 11);
v_codeQualityEntryTasks_2317_ = lean_ctor_get(v___x_2304_, 12);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2319_ = v___x_2304_;
v_isShared_2320_ = v_isSharedCheck_2347_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2317_);
lean_inc(v_prevLinterStates_2316_);
lean_inc(v_snapshotTasks_2315_);
lean_inc(v_traceState_2305_);
lean_inc(v_infoState_2314_);
lean_inc(v_auxDeclNGen_2313_);
lean_inc(v_ngen_2312_);
lean_inc(v_maxRecDepth_2311_);
lean_inc(v_nextMacroScope_2310_);
lean_inc(v_usedQuotCtxts_2309_);
lean_inc(v_scopes_2308_);
lean_inc(v_messages_2307_);
lean_inc(v_env_2306_);
lean_dec(v___x_2304_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2347_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
uint64_t v_tid_2321_; lean_object* v_traces_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2346_; 
v_tid_2321_ = lean_ctor_get_uint64(v_traceState_2305_, sizeof(void*)*1);
v_traces_2322_ = lean_ctor_get(v_traceState_2305_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_traceState_2305_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2324_ = v_traceState_2305_;
v_isShared_2325_ = v_isSharedCheck_2346_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_traces_2322_);
lean_dec(v_traceState_2305_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2346_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; double v___x_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2326_ = lean_box(0);
v___x_2327_ = lean_box(0);
v___x_2328_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0);
v___x_2329_ = 0;
v___x_2330_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2331_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2331_, 0, v_cls_2292_);
lean_ctor_set(v___x_2331_, 1, v___x_2327_);
lean_ctor_set(v___x_2331_, 2, v___x_2330_);
lean_ctor_set_float(v___x_2331_, sizeof(void*)*3, v___x_2328_);
lean_ctor_set_float(v___x_2331_, sizeof(void*)*3 + 8, v___x_2328_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*3 + 16, v___x_2329_);
v___x_2332_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2));
v___x_2333_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set(v___x_2333_, 1, v_a_2300_);
lean_ctor_set(v___x_2333_, 2, v___x_2332_);
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v_a_2298_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = l_Lean_PersistentArray_push___redArg(v_traces_2322_, v___x_2334_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2335_);
v___x_2337_ = v___x_2324_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2335_);
lean_ctor_set_uint64(v_reuseFailAlloc_2345_, sizeof(void*)*1, v_tid_2321_);
v___x_2337_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2339_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 9, v___x_2337_);
v___x_2339_ = v___x_2319_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_env_2306_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_messages_2307_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_scopes_2308_);
lean_ctor_set(v_reuseFailAlloc_2344_, 3, v_usedQuotCtxts_2309_);
lean_ctor_set(v_reuseFailAlloc_2344_, 4, v_nextMacroScope_2310_);
lean_ctor_set(v_reuseFailAlloc_2344_, 5, v_maxRecDepth_2311_);
lean_ctor_set(v_reuseFailAlloc_2344_, 6, v_ngen_2312_);
lean_ctor_set(v_reuseFailAlloc_2344_, 7, v_auxDeclNGen_2313_);
lean_ctor_set(v_reuseFailAlloc_2344_, 8, v_infoState_2314_);
lean_ctor_set(v_reuseFailAlloc_2344_, 9, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2344_, 10, v_snapshotTasks_2315_);
lean_ctor_set(v_reuseFailAlloc_2344_, 11, v_prevLinterStates_2316_);
lean_ctor_set(v_reuseFailAlloc_2344_, 12, v_codeQualityEntryTasks_2317_);
v___x_2339_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2340_ = lean_st_ref_put(v___y_2295_, v___x_2339_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2326_);
v___x_2342_ = v___x_2302_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2326_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec_ref(v_msg_2293_);
lean_dec(v_cls_2292_);
v_a_2349_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2297_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2297_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object* v_cls_2357_, lean_object* v_msg_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2357_, v_msg_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
return v_res_2362_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2363_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3));
v___x_2369_ = l_Lean_stringToMessageData(v___x_2368_);
return v___x_2369_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5));
v___x_2372_ = l_Lean_stringToMessageData(v___x_2371_);
return v___x_2372_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2374_ = l_Lean_stringToMessageData(v___x_2373_);
return v___x_2374_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v_cls_2378_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2));
v___x_2379_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9));
v___x_2380_ = l_Lean_Name_append(v___x_2379_, v_cls_2378_);
return v___x_2380_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11));
v___x_2383_ = l_Lean_stringToMessageData(v___x_2382_);
return v___x_2383_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13));
v___x_2386_ = l_Lean_stringToMessageData(v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(lean_object* v_mod_2391_, uint8_t v_isMeta_2392_, lean_object* v_hint_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v_env_2399_; uint8_t v_isExporting_2400_; lean_object* v_entry_2401_; lean_object* v___x_2402_; lean_object* v_env_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___y_2408_; lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2397_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0);
v___x_2398_ = lean_st_ref_get(v___y_2395_);
v_env_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc_ref(v_env_2399_);
lean_dec(v___x_2398_);
v_isExporting_2400_ = lean_ctor_get_uint8(v_env_2399_, sizeof(void*)*8);
lean_dec_ref(v_env_2399_);
lean_inc(v_mod_2391_);
v_entry_2401_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2401_, 0, v_mod_2391_);
lean_ctor_set_uint8(v_entry_2401_, sizeof(void*)*1, v_isExporting_2400_);
lean_ctor_set_uint8(v_entry_2401_, sizeof(void*)*1 + 1, v_isMeta_2392_);
v___x_2402_ = lean_st_ref_get(v___y_2395_);
v_env_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc_ref(v_env_2403_);
lean_dec(v___x_2402_);
v___x_2404_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2405_ = lean_box(1);
v___x_2406_ = lean_box(0);
v___x_2436_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2397_, v___x_2404_, v_env_2403_, v___x_2405_, v___x_2406_);
v___x_2437_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v___x_2436_, v_entry_2401_);
lean_dec(v___x_2436_);
if (v___x_2437_ == 0)
{
lean_object* v_cls_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v_scopes_2462_; lean_object* v___x_2463_; lean_object* v_opts_2464_; uint8_t v_hasTrace_2465_; 
v_cls_2438_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2));
v___x_2439_ = l_Lean_inheritedTraceOptions;
v___x_2440_ = lean_st_ref_get(v___x_2439_);
v___x_2441_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2442_ = lean_st_ref_get(v___y_2395_);
v_scopes_2462_ = lean_ctor_get(v___x_2442_, 2);
lean_inc(v_scopes_2462_);
lean_dec(v___x_2442_);
v___x_2463_ = l_List_head_x21___redArg(v___x_2441_, v_scopes_2462_);
lean_dec(v_scopes_2462_);
v_opts_2464_ = lean_ctor_get(v___x_2463_, 1);
lean_inc_ref(v_opts_2464_);
lean_dec(v___x_2463_);
v_hasTrace_2465_ = lean_ctor_get_uint8(v_opts_2464_, sizeof(void*)*1);
if (v_hasTrace_2465_ == 0)
{
lean_dec_ref(v_opts_2464_);
lean_dec(v___x_2440_);
lean_dec(v_hint_2393_);
lean_dec(v_mod_2391_);
v___y_2408_ = v___y_2395_;
goto v___jp_2407_;
}
else
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10);
v___x_2467_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2440_, v_opts_2464_, v___x_2466_);
lean_dec_ref(v_opts_2464_);
lean_dec(v___x_2440_);
if (v___x_2467_ == 0)
{
lean_dec(v_hint_2393_);
lean_dec(v_mod_2391_);
v___y_2408_ = v___y_2395_;
goto v___jp_2407_;
}
else
{
lean_object* v___x_2468_; lean_object* v___y_2470_; 
v___x_2468_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12);
if (v_isExporting_2400_ == 0)
{
lean_object* v___x_2477_; 
v___x_2477_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17));
v___y_2470_ = v___x_2477_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2478_; 
v___x_2478_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18));
v___y_2470_ = v___x_2478_;
goto v___jp_2469_;
}
v___jp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
lean_inc_ref(v___y_2470_);
v___x_2471_ = l_Lean_stringToMessageData(v___y_2470_);
v___x_2472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2468_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14);
v___x_2474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2472_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
if (v_isMeta_2392_ == 0)
{
lean_object* v___x_2475_; 
v___x_2475_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15));
v___y_2449_ = v___x_2474_;
v___y_2450_ = v___x_2475_;
goto v___jp_2448_;
}
else
{
lean_object* v___x_2476_; 
v___x_2476_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16));
v___y_2449_ = v___x_2474_;
v___y_2450_ = v___x_2476_;
goto v___jp_2448_;
}
}
}
}
v___jp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___y_2444_);
lean_ctor_set(v___x_2446_, 1, v___y_2445_);
v___x_2447_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2438_, v___x_2446_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_dec_ref_known(v___x_2447_, 1);
v___y_2408_ = v___y_2395_;
goto v___jp_2407_;
}
else
{
lean_dec_ref_known(v_entry_2401_, 1);
return v___x_2447_;
}
}
v___jp_2448_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
lean_inc_ref(v___y_2450_);
v___x_2451_ = l_Lean_stringToMessageData(v___y_2450_);
v___x_2452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___y_2449_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4);
v___x_2454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = l_Lean_MessageData_ofName(v_mod_2391_);
v___x_2456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = l_Lean_Name_isAnonymous(v_hint_2393_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6);
v___x_2459_ = l_Lean_MessageData_ofName(v_hint_2393_);
v___x_2460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___y_2444_ = v___x_2456_;
v___y_2445_ = v___x_2460_;
goto v___jp_2443_;
}
else
{
lean_object* v___x_2461_; 
lean_dec(v_hint_2393_);
v___x_2461_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7);
v___y_2444_ = v___x_2456_;
v___y_2445_ = v___x_2461_;
goto v___jp_2443_;
}
}
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec_ref_known(v_entry_2401_, 1);
lean_dec(v_hint_2393_);
lean_dec(v_mod_2391_);
v___x_2479_ = lean_box(0);
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
v___jp_2407_:
{
lean_object* v___x_2409_; lean_object* v_toEnvExtension_2410_; lean_object* v_env_2411_; lean_object* v_messages_2412_; lean_object* v_scopes_2413_; lean_object* v_usedQuotCtxts_2414_; lean_object* v_nextMacroScope_2415_; lean_object* v_maxRecDepth_2416_; lean_object* v_ngen_2417_; lean_object* v_auxDeclNGen_2418_; lean_object* v_infoState_2419_; lean_object* v_traceState_2420_; lean_object* v_snapshotTasks_2421_; lean_object* v_prevLinterStates_2422_; lean_object* v_codeQualityEntryTasks_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2435_; 
v___x_2409_ = lean_st_ref_take(v___y_2408_);
v_toEnvExtension_2410_ = lean_ctor_get(v___x_2404_, 0);
v_env_2411_ = lean_ctor_get(v___x_2409_, 0);
v_messages_2412_ = lean_ctor_get(v___x_2409_, 1);
v_scopes_2413_ = lean_ctor_get(v___x_2409_, 2);
v_usedQuotCtxts_2414_ = lean_ctor_get(v___x_2409_, 3);
v_nextMacroScope_2415_ = lean_ctor_get(v___x_2409_, 4);
v_maxRecDepth_2416_ = lean_ctor_get(v___x_2409_, 5);
v_ngen_2417_ = lean_ctor_get(v___x_2409_, 6);
v_auxDeclNGen_2418_ = lean_ctor_get(v___x_2409_, 7);
v_infoState_2419_ = lean_ctor_get(v___x_2409_, 8);
v_traceState_2420_ = lean_ctor_get(v___x_2409_, 9);
v_snapshotTasks_2421_ = lean_ctor_get(v___x_2409_, 10);
v_prevLinterStates_2422_ = lean_ctor_get(v___x_2409_, 11);
v_codeQualityEntryTasks_2423_ = lean_ctor_get(v___x_2409_, 12);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2425_ = v___x_2409_;
v_isShared_2426_ = v_isSharedCheck_2435_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2423_);
lean_inc(v_prevLinterStates_2422_);
lean_inc(v_snapshotTasks_2421_);
lean_inc(v_traceState_2420_);
lean_inc(v_infoState_2419_);
lean_inc(v_auxDeclNGen_2418_);
lean_inc(v_ngen_2417_);
lean_inc(v_maxRecDepth_2416_);
lean_inc(v_nextMacroScope_2415_);
lean_inc(v_usedQuotCtxts_2414_);
lean_inc(v_scopes_2413_);
lean_inc(v_messages_2412_);
lean_inc(v_env_2411_);
lean_dec(v___x_2409_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2435_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v_asyncMode_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
v_asyncMode_2427_ = lean_ctor_get(v_toEnvExtension_2410_, 2);
v___x_2428_ = lean_box(0);
v___x_2429_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2404_, v_env_2411_, v_entry_2401_, v_asyncMode_2427_, v___x_2406_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2429_);
v___x_2431_ = v___x_2425_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_messages_2412_);
lean_ctor_set(v_reuseFailAlloc_2434_, 2, v_scopes_2413_);
lean_ctor_set(v_reuseFailAlloc_2434_, 3, v_usedQuotCtxts_2414_);
lean_ctor_set(v_reuseFailAlloc_2434_, 4, v_nextMacroScope_2415_);
lean_ctor_set(v_reuseFailAlloc_2434_, 5, v_maxRecDepth_2416_);
lean_ctor_set(v_reuseFailAlloc_2434_, 6, v_ngen_2417_);
lean_ctor_set(v_reuseFailAlloc_2434_, 7, v_auxDeclNGen_2418_);
lean_ctor_set(v_reuseFailAlloc_2434_, 8, v_infoState_2419_);
lean_ctor_set(v_reuseFailAlloc_2434_, 9, v_traceState_2420_);
lean_ctor_set(v_reuseFailAlloc_2434_, 10, v_snapshotTasks_2421_);
lean_ctor_set(v_reuseFailAlloc_2434_, 11, v_prevLinterStates_2422_);
lean_ctor_set(v_reuseFailAlloc_2434_, 12, v_codeQualityEntryTasks_2423_);
v___x_2431_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = lean_st_ref_put(v___y_2408_, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2428_);
return v___x_2433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___boxed(lean_object* v_mod_2481_, lean_object* v_isMeta_2482_, lean_object* v_hint_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
uint8_t v_isMeta_boxed_2487_; lean_object* v_res_2488_; 
v_isMeta_boxed_2487_ = lean_unbox(v_isMeta_2482_);
v_res_2488_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_mod_2481_, v_isMeta_boxed_2487_, v_hint_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(lean_object* v___x_2489_, lean_object* v_declName_2490_, lean_object* v_as_2491_, size_t v_sz_2492_, size_t v_i_2493_, lean_object* v_b_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
uint8_t v___x_2498_; 
v___x_2498_ = lean_usize_dec_lt(v_i_2493_, v_sz_2492_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; 
lean_dec(v_declName_2490_);
v___x_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_b_2494_);
return v___x_2499_;
}
else
{
lean_object* v___x_2500_; lean_object* v_modules_2501_; lean_object* v___x_2502_; lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v_toImport_2505_; lean_object* v_module_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; lean_object* v___x_2509_; 
v___x_2500_ = l_Lean_Environment_header(v___x_2489_);
v_modules_2501_ = lean_ctor_get(v___x_2500_, 3);
lean_inc_ref(v_modules_2501_);
lean_dec_ref(v___x_2500_);
v___x_2502_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2503_ = lean_array_uget_borrowed(v_as_2491_, v_i_2493_);
v___x_2504_ = lean_array_get(v___x_2502_, v_modules_2501_, v_a_2503_);
lean_dec_ref(v_modules_2501_);
v_toImport_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc_ref(v_toImport_2505_);
lean_dec(v___x_2504_);
v_module_2506_ = lean_ctor_get(v_toImport_2505_, 0);
lean_inc(v_module_2506_);
lean_dec_ref(v_toImport_2505_);
v___x_2507_ = lean_box(0);
v___x_2508_ = 0;
lean_inc(v_declName_2490_);
v___x_2509_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2506_, v___x_2508_, v_declName_2490_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2509_) == 0)
{
size_t v___x_2510_; size_t v___x_2511_; 
lean_dec_ref_known(v___x_2509_, 1);
v___x_2510_ = ((size_t)1ULL);
v___x_2511_ = lean_usize_add(v_i_2493_, v___x_2510_);
v_i_2493_ = v___x_2511_;
v_b_2494_ = v___x_2507_;
goto _start;
}
else
{
lean_dec(v_declName_2490_);
return v___x_2509_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4___boxed(lean_object* v___x_2513_, lean_object* v_declName_2514_, lean_object* v_as_2515_, lean_object* v_sz_2516_, lean_object* v_i_2517_, lean_object* v_b_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
size_t v_sz_boxed_2522_; size_t v_i_boxed_2523_; lean_object* v_res_2524_; 
v_sz_boxed_2522_ = lean_unbox_usize(v_sz_2516_);
lean_dec(v_sz_2516_);
v_i_boxed_2523_ = lean_unbox_usize(v_i_2517_);
lean_dec(v_i_2517_);
v_res_2524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v___x_2513_, v_declName_2514_, v_as_2515_, v_sz_boxed_2522_, v_i_boxed_2523_, v_b_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec_ref(v_as_2515_);
lean_dec_ref(v___x_2513_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(lean_object* v_a_2525_, lean_object* v_x_2526_){
_start:
{
if (lean_obj_tag(v_x_2526_) == 0)
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_box(0);
return v___x_2527_;
}
else
{
lean_object* v_key_2528_; lean_object* v_value_2529_; lean_object* v_tail_2530_; uint8_t v___x_2531_; 
v_key_2528_ = lean_ctor_get(v_x_2526_, 0);
v_value_2529_ = lean_ctor_get(v_x_2526_, 1);
v_tail_2530_ = lean_ctor_get(v_x_2526_, 2);
v___x_2531_ = lean_name_eq(v_key_2528_, v_a_2525_);
if (v___x_2531_ == 0)
{
v_x_2526_ = v_tail_2530_;
goto _start;
}
else
{
lean_object* v___x_2533_; 
lean_inc(v_value_2529_);
v___x_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2533_, 0, v_value_2529_);
return v___x_2533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_a_2534_, lean_object* v_x_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2534_, v_x_2535_);
lean_dec(v_x_2535_);
lean_dec(v_a_2534_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(lean_object* v_m_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v_buckets_2539_; lean_object* v___x_2540_; uint64_t v___y_2542_; 
v_buckets_2539_ = lean_ctor_get(v_m_2537_, 1);
v___x_2540_ = lean_array_get_size(v_buckets_2539_);
if (lean_obj_tag(v_a_2538_) == 0)
{
uint64_t v___x_2556_; 
v___x_2556_ = 1723ULL;
v___y_2542_ = v___x_2556_;
goto v___jp_2541_;
}
else
{
uint64_t v_hash_2557_; 
v_hash_2557_ = lean_ctor_get_uint64(v_a_2538_, sizeof(void*)*2);
v___y_2542_ = v_hash_2557_;
goto v___jp_2541_;
}
v___jp_2541_:
{
uint64_t v___x_2543_; uint64_t v___x_2544_; uint64_t v_fold_2545_; uint64_t v___x_2546_; uint64_t v___x_2547_; uint64_t v___x_2548_; size_t v___x_2549_; size_t v___x_2550_; size_t v___x_2551_; size_t v___x_2552_; size_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2543_ = 32ULL;
v___x_2544_ = lean_uint64_shift_right(v___y_2542_, v___x_2543_);
v_fold_2545_ = lean_uint64_xor(v___y_2542_, v___x_2544_);
v___x_2546_ = 16ULL;
v___x_2547_ = lean_uint64_shift_right(v_fold_2545_, v___x_2546_);
v___x_2548_ = lean_uint64_xor(v_fold_2545_, v___x_2547_);
v___x_2549_ = lean_uint64_to_usize(v___x_2548_);
v___x_2550_ = lean_usize_of_nat(v___x_2540_);
v___x_2551_ = ((size_t)1ULL);
v___x_2552_ = lean_usize_sub(v___x_2550_, v___x_2551_);
v___x_2553_ = lean_usize_land(v___x_2549_, v___x_2552_);
v___x_2554_ = lean_array_uget_borrowed(v_buckets_2539_, v___x_2553_);
v___x_2555_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2538_, v___x_2554_);
return v___x_2555_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_m_2558_);
return v_res_2560_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object* v_declName_2564_, uint8_t v_isMeta_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v_env_2574_; lean_object* v___y_2576_; lean_object* v___x_2589_; 
v___x_2569_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0);
v___x_2570_ = lean_st_ref_get(v___y_2567_);
v_env_2574_ = lean_ctor_get(v___x_2570_, 0);
lean_inc_ref(v_env_2574_);
lean_dec(v___x_2570_);
v___x_2589_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2574_, v_declName_2564_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_dec_ref(v_env_2574_);
lean_dec(v_declName_2564_);
goto v___jp_2571_;
}
else
{
lean_object* v_val_2590_; lean_object* v___x_2591_; lean_object* v_modules_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; 
v_val_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_val_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2591_ = l_Lean_Environment_header(v_env_2574_);
v_modules_2592_ = lean_ctor_get(v___x_2591_, 3);
lean_inc_ref(v_modules_2592_);
lean_dec_ref(v___x_2591_);
v___x_2593_ = lean_array_get_size(v_modules_2592_);
v___x_2594_ = lean_nat_dec_lt(v_val_2590_, v___x_2593_);
if (v___x_2594_ == 0)
{
lean_dec_ref(v_modules_2592_);
lean_dec(v_val_2590_);
lean_dec_ref(v_env_2574_);
lean_dec(v_declName_2564_);
goto v___jp_2571_;
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2596_; uint8_t v___y_2598_; 
v___x_2595_ = lean_array_fget(v_modules_2592_, v_val_2590_);
lean_dec(v_val_2590_);
lean_dec_ref(v_modules_2592_);
v___x_2596_ = lean_st_ref_get(v___y_2567_);
if (v_isMeta_2565_ == 0)
{
lean_dec(v___x_2596_);
v___y_2598_ = v_isMeta_2565_;
goto v___jp_2597_;
}
else
{
lean_object* v_env_2609_; uint8_t v___x_2610_; 
v_env_2609_ = lean_ctor_get(v___x_2596_, 0);
lean_inc_ref(v_env_2609_);
lean_dec(v___x_2596_);
lean_inc(v_declName_2564_);
v___x_2610_ = l_Lean_isMarkedMeta(v_env_2609_, v_declName_2564_);
if (v___x_2610_ == 0)
{
v___y_2598_ = v_isMeta_2565_;
goto v___jp_2597_;
}
else
{
uint8_t v___x_2611_; 
v___x_2611_ = 0;
v___y_2598_ = v___x_2611_;
goto v___jp_2597_;
}
}
v___jp_2597_:
{
lean_object* v_toImport_2599_; lean_object* v_module_2600_; lean_object* v___x_2601_; 
v_toImport_2599_ = lean_ctor_get(v___x_2595_, 0);
lean_inc_ref(v_toImport_2599_);
lean_dec(v___x_2595_);
v_module_2600_ = lean_ctor_get(v_toImport_2599_, 0);
lean_inc(v_module_2600_);
lean_dec_ref(v_toImport_2599_);
lean_inc(v_declName_2564_);
v___x_2601_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2600_, v___y_2598_, v_declName_2564_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_dec_ref_known(v___x_2601_, 1);
v___x_2602_ = l_Lean_indirectModUseExt;
v___x_2603_ = lean_box(1);
v___x_2604_ = lean_box(0);
lean_inc_ref(v_env_2574_);
v___x_2605_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2569_, v___x_2602_, v_env_2574_, v___x_2603_, v___x_2604_);
v___x_2606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v___x_2605_, v_declName_2564_);
lean_dec(v___x_2605_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v___x_2607_; 
v___x_2607_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1));
v___y_2576_ = v___x_2607_;
goto v___jp_2575_;
}
else
{
lean_object* v_val_2608_; 
v_val_2608_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_val_2608_);
lean_dec_ref_known(v___x_2606_, 1);
v___y_2576_ = v_val_2608_;
goto v___jp_2575_;
}
}
else
{
lean_dec_ref(v_env_2574_);
lean_dec(v_declName_2564_);
return v___x_2601_;
}
}
}
}
v___jp_2571_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = lean_box(0);
v___x_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
return v___x_2573_;
}
v___jp_2575_:
{
lean_object* v___x_2577_; size_t v_sz_2578_; size_t v___x_2579_; lean_object* v___x_2580_; 
v___x_2577_ = lean_box(0);
v_sz_2578_ = lean_array_size(v___y_2576_);
v___x_2579_ = ((size_t)0ULL);
v___x_2580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v_env_2574_, v_declName_2564_, v___y_2576_, v_sz_2578_, v___x_2579_, v___x_2577_, v___y_2566_, v___y_2567_);
lean_dec_ref(v___y_2576_);
lean_dec_ref(v_env_2574_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v___x_2580_, 0);
lean_dec(v_unused_2588_);
v___x_2582_ = v___x_2580_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_dec(v___x_2580_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v___x_2577_);
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2577_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
else
{
return v___x_2580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object* v_declName_2612_, lean_object* v_isMeta_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
uint8_t v_isMeta_boxed_2617_; lean_object* v_res_2618_; 
v_isMeta_boxed_2617_ = lean_unbox(v_isMeta_2613_);
v_res_2618_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_declName_2612_, v_isMeta_boxed_2617_, v___y_2614_, v___y_2615_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(lean_object* v_as_x27_2619_, lean_object* v_b_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
if (lean_obj_tag(v_as_x27_2619_) == 0)
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v_b_2620_);
return v___x_2624_;
}
else
{
lean_object* v_head_2625_; lean_object* v_tail_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; lean_object* v___x_2629_; 
v_head_2625_ = lean_ctor_get(v_as_x27_2619_, 0);
v_tail_2626_ = lean_ctor_get(v_as_x27_2619_, 1);
v___x_2627_ = lean_box(0);
v___x_2628_ = 1;
lean_inc(v_head_2625_);
v___x_2629_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_head_2625_, v___x_2628_, v___y_2621_, v___y_2622_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_dec_ref_known(v___x_2629_, 1);
v_as_x27_2619_ = v_tail_2626_;
v_b_2620_ = v___x_2627_;
goto _start;
}
else
{
return v___x_2629_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_2631_, lean_object* v_b_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_2631_, v_b_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v_as_x27_2631_);
return v_res_2636_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = l_Lean_maxRecDepthErrorMessage;
v___x_2643_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2642_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3);
v___x_2645_ = l_Lean_MessageData_ofFormat(v___x_2644_);
return v___x_2645_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2646_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4);
v___x_2647_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2));
v___x_2648_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
lean_ctor_set(v___x_2648_, 1, v___x_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(lean_object* v_ref_2649_){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2651_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5);
v___x_2652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2652_, 0, v_ref_2649_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___boxed(lean_object* v_ref_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_2654_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object* v_currNamespace_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2660_, 0, v_currNamespace_2657_);
lean_ctor_set(v___x_2660_, 1, v___y_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(v_currNamespace_2661_, v___y_2662_, v___y_2663_);
lean_dec_ref(v___y_2662_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object* v_env_2665_, lean_object* v_declName_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
uint8_t v___x_2669_; lean_object* v_env_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; uint8_t v___x_2673_; 
v___x_2669_ = 0;
v_env_2670_ = l_Lean_Environment_setExporting(v_env_2665_, v___x_2669_);
lean_inc(v_declName_2666_);
v___x_2671_ = l_Lean_mkPrivateName(v_env_2670_, v_declName_2666_);
v___x_2672_ = 1;
lean_inc_ref(v_env_2670_);
v___x_2673_ = l_Lean_Environment_contains(v_env_2670_, v___x_2671_, v___x_2672_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; uint8_t v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2674_ = l_Lean_privateToUserName(v_declName_2666_);
v___x_2675_ = l_Lean_Environment_contains(v_env_2670_, v___x_2674_, v___x_2672_);
v___x_2676_ = lean_box(v___x_2675_);
v___x_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
lean_ctor_set(v___x_2677_, 1, v___y_2668_);
return v___x_2677_;
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_dec_ref(v_env_2670_);
lean_dec(v_declName_2666_);
v___x_2678_ = lean_box(v___x_2673_);
v___x_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
lean_ctor_set(v___x_2679_, 1, v___y_2668_);
return v___x_2679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object* v_env_2680_, lean_object* v_declName_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(v_env_2680_, v_declName_2681_, v___y_2682_, v___y_2683_);
lean_dec_ref(v___y_2682_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(lean_object* v_x_2685_, lean_object* v___y_2686_){
_start:
{
if (lean_obj_tag(v_x_2685_) == 0)
{
lean_object* v_a_2687_; lean_object* v___x_2688_; 
v_a_2687_ = lean_ctor_get(v_x_2685_, 0);
lean_inc(v_a_2687_);
v___x_2688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2688_, 0, v_a_2687_);
lean_ctor_set(v___x_2688_, 1, v___y_2686_);
return v___x_2688_;
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2690_; 
v_a_2689_ = lean_ctor_get(v_x_2685_, 0);
lean_inc(v_a_2689_);
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v_a_2689_);
lean_ctor_set(v___x_2690_, 1, v___y_2686_);
return v___x_2690_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_2691_, v___y_2692_);
lean_dec_ref(v_x_2691_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object* v_env_2694_, lean_object* v_stx_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2694_, v_stx_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
if (lean_obj_tag(v_a_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2708_; 
v_a_2700_ = lean_ctor_get(v___x_2698_, 1);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; 
v_unused_2709_ = lean_ctor_get(v___x_2698_, 0);
lean_dec(v_unused_2709_);
v___x_2702_ = v___x_2698_;
v_isShared_2703_ = v_isSharedCheck_2708_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2698_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2708_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2704_ = lean_box(0);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v___x_2704_);
v___x_2706_ = v___x_2702_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_a_2700_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
else
{
lean_object* v_val_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2738_; 
v_val_2710_ = lean_ctor_get(v_a_2699_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_a_2699_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2712_ = v_a_2699_;
v_isShared_2713_ = v_isSharedCheck_2738_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_val_2710_);
lean_dec(v_a_2699_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2738_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v_snd_2714_; 
v_snd_2714_ = lean_ctor_get(v_val_2710_, 1);
lean_inc(v_snd_2714_);
lean_dec(v_val_2710_);
if (lean_obj_tag(v_snd_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2724_; 
lean_del_object(v___x_2712_);
v_a_2715_ = lean_ctor_get(v___x_2698_, 1);
lean_inc(v_a_2715_);
lean_dec_ref_known(v___x_2698_, 2);
v_a_2716_ = lean_ctor_get(v_snd_2714_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v_snd_2714_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2718_ = v_snd_2714_;
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v_snd_2714_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2721_, v_a_2715_);
lean_dec_ref(v___x_2721_);
return v___x_2722_;
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2737_; 
v_a_2725_ = lean_ctor_get(v___x_2698_, 1);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2698_, 2);
v_a_2726_ = lean_ctor_get(v_snd_2714_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_snd_2714_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2728_ = v_snd_2714_;
v_isShared_2729_ = v_isSharedCheck_2737_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v_snd_2714_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2737_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v_a_2726_);
v___x_2731_ = v___x_2712_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2733_; 
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2731_);
v___x_2733_ = v___x_2728_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2733_, v_a_2725_);
lean_dec_ref(v___x_2733_);
return v___x_2734_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2739_; lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
v_a_2739_ = lean_ctor_get(v___x_2698_, 0);
v_a_2740_ = lean_ctor_get(v___x_2698_, 1);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2698_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_inc(v_a_2739_);
lean_dec(v___x_2698_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2739_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object* v_env_2748_, lean_object* v_stx_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(v_env_2748_, v_stx_2749_, v___y_2750_, v___y_2751_);
lean_dec_ref(v___y_2750_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object* v_env_2753_, lean_object* v_currNamespace_2754_, lean_object* v_openDecls_2755_, lean_object* v_n_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = l_Lean_ResolveName_resolveNamespace(v_env_2753_, v_currNamespace_2754_, v_openDecls_2755_, v_n_2756_);
v___x_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
lean_ctor_set(v___x_2760_, 1, v___y_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object* v_env_2761_, lean_object* v_currNamespace_2762_, lean_object* v_openDecls_2763_, lean_object* v_n_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(v_env_2761_, v_currNamespace_2762_, v_openDecls_2763_, v_n_2764_, v___y_2765_, v___y_2766_);
lean_dec_ref(v___y_2765_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object* v_as_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
if (lean_obj_tag(v_as_2768_) == 0)
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = lean_box(0);
v___x_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
return v___x_2773_;
}
else
{
lean_object* v_head_2774_; lean_object* v_tail_2775_; lean_object* v_fst_2776_; lean_object* v_snd_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v_scopes_2782_; lean_object* v___x_2783_; lean_object* v_opts_2784_; uint8_t v_hasTrace_2785_; 
v_head_2774_ = lean_ctor_get(v_as_2768_, 0);
lean_inc(v_head_2774_);
v_tail_2775_ = lean_ctor_get(v_as_2768_, 1);
lean_inc(v_tail_2775_);
lean_dec_ref_known(v_as_2768_, 2);
v_fst_2776_ = lean_ctor_get(v_head_2774_, 0);
lean_inc(v_fst_2776_);
v_snd_2777_ = lean_ctor_get(v_head_2774_, 1);
lean_inc(v_snd_2777_);
lean_dec(v_head_2774_);
v___x_2778_ = l_Lean_inheritedTraceOptions;
v___x_2779_ = lean_st_ref_get(v___x_2778_);
v___x_2780_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2781_ = lean_st_ref_get(v___y_2770_);
v_scopes_2782_ = lean_ctor_get(v___x_2781_, 2);
lean_inc(v_scopes_2782_);
lean_dec(v___x_2781_);
v___x_2783_ = l_List_head_x21___redArg(v___x_2780_, v_scopes_2782_);
lean_dec(v_scopes_2782_);
v_opts_2784_ = lean_ctor_get(v___x_2783_, 1);
lean_inc_ref(v_opts_2784_);
lean_dec(v___x_2783_);
v_hasTrace_2785_ = lean_ctor_get_uint8(v_opts_2784_, sizeof(void*)*1);
if (v_hasTrace_2785_ == 0)
{
lean_dec_ref(v_opts_2784_);
lean_dec(v___x_2779_);
lean_dec(v_snd_2777_);
lean_dec(v_fst_2776_);
v_as_2768_ = v_tail_2775_;
goto _start;
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v___x_2787_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9));
lean_inc(v_fst_2776_);
v___x_2788_ = l_Lean_Name_append(v___x_2787_, v_fst_2776_);
v___x_2789_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2779_, v_opts_2784_, v___x_2788_);
lean_dec(v___x_2788_);
lean_dec_ref(v_opts_2784_);
lean_dec(v___x_2779_);
if (v___x_2789_ == 0)
{
lean_dec(v_snd_2777_);
lean_dec(v_fst_2776_);
v_as_2768_ = v_tail_2775_;
goto _start;
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_snd_2777_);
v___x_2792_ = l_Lean_MessageData_ofFormat(v___x_2791_);
v___x_2793_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_fst_2776_, v___x_2792_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_dec_ref_known(v___x_2793_, 1);
v_as_2768_ = v_tail_2775_;
goto _start;
}
else
{
lean_dec(v_tail_2775_);
return v___x_2793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object* v_as_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v_as_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object* v_env_2800_, lean_object* v_opts_2801_, lean_object* v_currNamespace_2802_, lean_object* v_openDecls_2803_, lean_object* v_n_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = l_Lean_ResolveName_resolveGlobalName(v_env_2800_, v_opts_2801_, v_currNamespace_2802_, v_openDecls_2803_, v_n_2804_);
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
lean_ctor_set(v___x_2808_, 1, v___y_2806_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object* v_env_2809_, lean_object* v_opts_2810_, lean_object* v_currNamespace_2811_, lean_object* v_openDecls_2812_, lean_object* v_n_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(v_env_2809_, v_opts_2810_, v_currNamespace_2811_, v_openDecls_2812_, v_n_2813_, v___y_2814_, v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec_ref(v_opts_2810_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object* v_x_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; lean_object* v_env_2823_; lean_object* v___f_2824_; lean_object* v___f_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v_scopes_2828_; lean_object* v___x_2829_; lean_object* v_opts_2830_; lean_object* v___x_2831_; 
v___x_2822_ = lean_st_ref_get(v___y_2820_);
v_env_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc_ref_n(v_env_2823_, 3);
lean_dec(v___x_2822_);
v___f_2824_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2824_, 0, v_env_2823_);
v___f_2825_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2825_, 0, v_env_2823_);
v___x_2826_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2827_ = lean_st_ref_get(v___y_2820_);
v_scopes_2828_ = lean_ctor_get(v___x_2827_, 2);
lean_inc(v_scopes_2828_);
lean_dec(v___x_2827_);
v___x_2829_ = l_List_head_x21___redArg(v___x_2826_, v_scopes_2828_);
lean_dec(v_scopes_2828_);
v_opts_2830_ = lean_ctor_get(v___x_2829_, 1);
lean_inc_ref(v_opts_2830_);
lean_dec(v___x_2829_);
v___x_2831_ = l_Lean_Elab_Command_getScope___redArg(v___y_2820_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v_currNamespace_2833_; lean_object* v___f_2834_; lean_object* v___x_2835_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2831_, 1);
v_currNamespace_2833_ = lean_ctor_get(v_a_2832_, 2);
lean_inc_n(v_currNamespace_2833_, 2);
lean_dec(v_a_2832_);
v___f_2834_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2834_, 0, v_currNamespace_2833_);
v___x_2835_ = l_Lean_Elab_Command_getScope___redArg(v___y_2820_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v_openDecls_2837_; lean_object* v___f_2838_; lean_object* v___f_2839_; lean_object* v_methods_2840_; lean_object* v___x_2841_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2835_, 1);
v_openDecls_2837_ = lean_ctor_get(v_a_2836_, 3);
lean_inc_n(v_openDecls_2837_, 2);
lean_dec(v_a_2836_);
lean_inc(v_currNamespace_2833_);
lean_inc_ref(v_env_2823_);
v___f_2838_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2838_, 0, v_env_2823_);
lean_closure_set(v___f_2838_, 1, v_currNamespace_2833_);
lean_closure_set(v___f_2838_, 2, v_openDecls_2837_);
v___f_2839_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2839_, 0, v_env_2823_);
lean_closure_set(v___f_2839_, 1, v_opts_2830_);
lean_closure_set(v___f_2839_, 2, v_currNamespace_2833_);
lean_closure_set(v___f_2839_, 3, v_openDecls_2837_);
v_methods_2840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2840_, 0, v___f_2825_);
lean_ctor_set(v_methods_2840_, 1, v___f_2834_);
lean_ctor_set(v_methods_2840_, 2, v___f_2824_);
lean_ctor_set(v_methods_2840_, 3, v___f_2838_);
lean_ctor_set(v_methods_2840_, 4, v___f_2839_);
v___x_2841_ = l_Lean_Elab_Command_getRef___redArg(v___y_2819_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2843_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2841_, 1);
v___x_2843_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2819_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v_currRecDepth_2845_; lean_object* v_quotContext_x3f_2846_; lean_object* v_a_2848_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v_currRecDepth_2845_ = lean_ctor_get(v___y_2819_, 2);
v_quotContext_x3f_2846_ = lean_ctor_get(v___y_2819_, 5);
if (lean_obj_tag(v_quotContext_x3f_2846_) == 0)
{
lean_object* v___x_2922_; lean_object* v_a_2923_; 
v___x_2922_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_2820_);
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref(v___x_2922_);
v_a_2848_ = v_a_2923_;
goto v___jp_2847_;
}
else
{
lean_object* v_val_2924_; 
v_val_2924_ = lean_ctor_get(v_quotContext_x3f_2846_, 0);
lean_inc(v_val_2924_);
v_a_2848_ = v_val_2924_;
goto v___jp_2847_;
}
v___jp_2847_:
{
lean_object* v___x_2849_; lean_object* v_maxRecDepth_2850_; lean_object* v___x_2851_; lean_object* v_nextMacroScope_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2849_ = lean_st_ref_get(v___y_2820_);
v_maxRecDepth_2850_ = lean_ctor_get(v___x_2849_, 5);
lean_inc(v_maxRecDepth_2850_);
lean_dec(v___x_2849_);
v___x_2851_ = lean_st_ref_get(v___y_2820_);
v_nextMacroScope_2852_ = lean_ctor_get(v___x_2851_, 4);
lean_inc(v_nextMacroScope_2852_);
lean_dec(v___x_2851_);
lean_inc(v_currRecDepth_2845_);
v___x_2853_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2853_, 0, v_methods_2840_);
lean_ctor_set(v___x_2853_, 1, v_a_2848_);
lean_ctor_set(v___x_2853_, 2, v_a_2844_);
lean_ctor_set(v___x_2853_, 3, v_currRecDepth_2845_);
lean_ctor_set(v___x_2853_, 4, v_maxRecDepth_2850_);
lean_ctor_set(v___x_2853_, 5, v_a_2842_);
v___x_2854_ = lean_box(0);
v___x_2855_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2855_, 0, v_nextMacroScope_2852_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
lean_ctor_set(v___x_2855_, 2, v___x_2854_);
v___x_2856_ = lean_apply_2(v_x_2818_, v___x_2853_, v___x_2855_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; lean_object* v_a_2858_; lean_object* v_macroScope_2859_; lean_object* v_traceMsgs_2860_; lean_object* v_expandedMacroDecls_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 1);
lean_inc(v_a_2857_);
v_a_2858_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2856_, 2);
v_macroScope_2859_ = lean_ctor_get(v_a_2857_, 0);
lean_inc(v_macroScope_2859_);
v_traceMsgs_2860_ = lean_ctor_get(v_a_2857_, 1);
lean_inc(v_traceMsgs_2860_);
v_expandedMacroDecls_2861_ = lean_ctor_get(v_a_2857_, 2);
lean_inc(v_expandedMacroDecls_2861_);
lean_dec(v_a_2857_);
v___x_2862_ = lean_box(0);
v___x_2863_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_expandedMacroDecls_2861_, v___x_2862_, v___y_2819_, v___y_2820_);
lean_dec(v_expandedMacroDecls_2861_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v___x_2864_; lean_object* v_env_2865_; lean_object* v_messages_2866_; lean_object* v_scopes_2867_; lean_object* v_usedQuotCtxts_2868_; lean_object* v_maxRecDepth_2869_; lean_object* v_ngen_2870_; lean_object* v_auxDeclNGen_2871_; lean_object* v_infoState_2872_; lean_object* v_traceState_2873_; lean_object* v_snapshotTasks_2874_; lean_object* v_prevLinterStates_2875_; lean_object* v_codeQualityEntryTasks_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2902_; 
lean_dec_ref_known(v___x_2863_, 1);
v___x_2864_ = lean_st_ref_take(v___y_2820_);
v_env_2865_ = lean_ctor_get(v___x_2864_, 0);
v_messages_2866_ = lean_ctor_get(v___x_2864_, 1);
v_scopes_2867_ = lean_ctor_get(v___x_2864_, 2);
v_usedQuotCtxts_2868_ = lean_ctor_get(v___x_2864_, 3);
v_maxRecDepth_2869_ = lean_ctor_get(v___x_2864_, 5);
v_ngen_2870_ = lean_ctor_get(v___x_2864_, 6);
v_auxDeclNGen_2871_ = lean_ctor_get(v___x_2864_, 7);
v_infoState_2872_ = lean_ctor_get(v___x_2864_, 8);
v_traceState_2873_ = lean_ctor_get(v___x_2864_, 9);
v_snapshotTasks_2874_ = lean_ctor_get(v___x_2864_, 10);
v_prevLinterStates_2875_ = lean_ctor_get(v___x_2864_, 11);
v_codeQualityEntryTasks_2876_ = lean_ctor_get(v___x_2864_, 12);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2902_ == 0)
{
lean_object* v_unused_2903_; 
v_unused_2903_ = lean_ctor_get(v___x_2864_, 4);
lean_dec(v_unused_2903_);
v___x_2878_ = v___x_2864_;
v_isShared_2879_ = v_isSharedCheck_2902_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2876_);
lean_inc(v_prevLinterStates_2875_);
lean_inc(v_snapshotTasks_2874_);
lean_inc(v_traceState_2873_);
lean_inc(v_infoState_2872_);
lean_inc(v_auxDeclNGen_2871_);
lean_inc(v_ngen_2870_);
lean_inc(v_maxRecDepth_2869_);
lean_inc(v_usedQuotCtxts_2868_);
lean_inc(v_scopes_2867_);
lean_inc(v_messages_2866_);
lean_inc(v_env_2865_);
lean_dec(v___x_2864_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2902_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 4, v_macroScope_2859_);
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_env_2865_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_messages_2866_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v_scopes_2867_);
lean_ctor_set(v_reuseFailAlloc_2901_, 3, v_usedQuotCtxts_2868_);
lean_ctor_set(v_reuseFailAlloc_2901_, 4, v_macroScope_2859_);
lean_ctor_set(v_reuseFailAlloc_2901_, 5, v_maxRecDepth_2869_);
lean_ctor_set(v_reuseFailAlloc_2901_, 6, v_ngen_2870_);
lean_ctor_set(v_reuseFailAlloc_2901_, 7, v_auxDeclNGen_2871_);
lean_ctor_set(v_reuseFailAlloc_2901_, 8, v_infoState_2872_);
lean_ctor_set(v_reuseFailAlloc_2901_, 9, v_traceState_2873_);
lean_ctor_set(v_reuseFailAlloc_2901_, 10, v_snapshotTasks_2874_);
lean_ctor_set(v_reuseFailAlloc_2901_, 11, v_prevLinterStates_2875_);
lean_ctor_set(v_reuseFailAlloc_2901_, 12, v_codeQualityEntryTasks_2876_);
v___x_2881_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = lean_st_ref_put(v___y_2820_, v___x_2881_);
v___x_2883_ = l_List_reverse___redArg(v_traceMsgs_2860_);
v___x_2884_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v___x_2883_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2891_ == 0)
{
lean_object* v_unused_2892_; 
v_unused_2892_ = lean_ctor_get(v___x_2884_, 0);
lean_dec(v_unused_2892_);
v___x_2886_ = v___x_2884_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_dec(v___x_2884_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v_a_2858_);
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2858_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec(v_a_2858_);
v_a_2893_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2884_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2884_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v_traceMsgs_2860_);
lean_dec(v_macroScope_2859_);
lean_dec(v_a_2858_);
v_a_2904_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2863_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2863_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_a_2912_; 
v_a_2912_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2856_, 2);
if (lean_obj_tag(v_a_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v_a_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; 
v_a_2913_ = lean_ctor_get(v_a_2912_, 0);
lean_inc(v_a_2913_);
v_a_2914_ = lean_ctor_get(v_a_2912_, 1);
lean_inc_ref(v_a_2914_);
lean_dec_ref_known(v_a_2912_, 2);
v___x_2915_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0));
v___x_2916_ = lean_string_dec_eq(v_a_2914_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2917_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2917_, 0, v_a_2914_);
v___x_2918_ = l_Lean_MessageData_ofFormat(v___x_2917_);
v___x_2919_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_a_2913_, v___x_2918_, v___y_2819_, v___y_2820_);
lean_dec(v_a_2913_);
return v___x_2919_;
}
else
{
lean_object* v___x_2920_; 
lean_dec_ref(v_a_2914_);
v___x_2920_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_a_2913_);
return v___x_2920_;
}
}
else
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2921_;
}
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_a_2842_);
lean_dec_ref_known(v_methods_2840_, 5);
lean_dec_ref(v_x_2818_);
v_a_2925_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2843_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2843_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec_ref_known(v_methods_2840_, 5);
lean_dec_ref(v_x_2818_);
v_a_2933_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2841_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2841_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec_ref(v___f_2834_);
lean_dec(v_currNamespace_2833_);
lean_dec_ref(v_opts_2830_);
lean_dec_ref(v___f_2825_);
lean_dec_ref(v___f_2824_);
lean_dec_ref(v_env_2823_);
lean_dec_ref(v_x_2818_);
v_a_2941_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2835_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2835_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v_opts_2830_);
lean_dec_ref(v___f_2825_);
lean_dec_ref(v___f_2824_);
lean_dec_ref(v_env_2823_);
lean_dec_ref(v_x_2818_);
v_a_2949_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2831_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2831_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object* v_x_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_2957_, v___y_2958_, v___y_2959_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object* v_x_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3005_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_3006_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_3047_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
lean_inc(v_x_3001_);
v___x_3048_ = l_Lean_Syntax_isOfKind(v_x_3001_, v___x_3047_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; 
lean_dec(v_x_3001_);
v___x_3049_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3049_;
}
else
{
lean_object* v___x_3050_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; uint8_t v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; size_t v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; uint8_t v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; size_t v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; uint8_t v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; size_t v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; uint8_t v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; size_t v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; uint8_t v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; size_t v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v_expectedType_x3f_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v_prio_x3f_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v_name_x3f_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v_prec_x3f_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v_attrs_x3f_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v_doc_x3f_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___x_3527_; uint8_t v___x_3528_; 
v___x_3050_ = lean_unsigned_to_nat(0u);
v___x_3527_ = l_Lean_Syntax_getArg(v_x_3001_, v___x_3050_);
v___x_3528_ = l_Lean_Syntax_isNone(v___x_3527_);
if (v___x_3528_ == 0)
{
lean_object* v___x_3529_; uint8_t v___x_3530_; 
v___x_3529_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3527_);
v___x_3530_ = l_Lean_Syntax_matchesNull(v___x_3527_, v___x_3529_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3531_; 
lean_dec(v___x_3527_);
lean_dec(v_x_3001_);
v___x_3531_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3531_;
}
else
{
lean_object* v_doc_x3f_3532_; 
v_doc_x3f_3532_ = l_Lean_Syntax_getArg(v___x_3527_, v___x_3050_);
lean_dec(v___x_3527_);
if (v___x_3528_ == 0)
{
lean_object* v___x_3535_; uint8_t v___x_3536_; 
v___x_3535_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(v_doc_x3f_3532_);
v___x_3536_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3532_, v___x_3535_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; 
lean_dec(v_doc_x3f_3532_);
lean_dec(v_x_3001_);
v___x_3537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3537_;
}
else
{
goto v___jp_3533_;
}
}
else
{
goto v___jp_3533_;
}
v___jp_3533_:
{
lean_object* v___x_3534_; 
v___x_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3534_, 0, v_doc_x3f_3532_);
v_doc_x3f_3511_ = v___x_3534_;
v___y_3512_ = v_a_3002_;
v___y_3513_ = v_a_3003_;
goto v___jp_3510_;
}
}
}
else
{
lean_object* v___x_3538_; 
lean_dec(v___x_3527_);
v___x_3538_ = lean_box(0);
v_doc_x3f_3511_ = v___x_3538_;
v___y_3512_ = v_a_3002_;
v___y_3513_ = v_a_3003_;
goto v___jp_3510_;
}
v___jp_3051_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_inc_ref_n(v___y_3059_, 2);
v___x_3068_ = l_Array_append___redArg(v___y_3059_, v___y_3067_);
lean_dec_ref(v___y_3067_);
lean_inc_n(v___y_3055_, 3);
lean_inc_n(v___y_3062_, 6);
v___x_3069_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3069_, 0, v___y_3062_);
lean_ctor_set(v___x_3069_, 1, v___y_3055_);
lean_ctor_set(v___x_3069_, 2, v___x_3068_);
v___x_3070_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3070_, 0, v___y_3062_);
lean_ctor_set(v___x_3070_, 1, v___y_3055_);
lean_ctor_set(v___x_3070_, 2, v___y_3059_);
lean_inc_ref(v___x_3070_);
lean_inc(v___y_3066_);
v___x_3071_ = l_Lean_Syntax_node1(v___y_3062_, v___y_3066_, v___x_3070_);
lean_inc_ref(v___y_3063_);
v___x_3072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___y_3062_);
lean_ctor_set(v___x_3072_, 1, v___y_3063_);
lean_inc_ref(v___y_3065_);
v___x_3073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___y_3062_);
lean_ctor_set(v___x_3073_, 1, v___y_3065_);
v___x_3074_ = l_Lean_Syntax_node2(v___y_3062_, v___y_3055_, v___x_3073_, v___y_3053_);
if (lean_obj_tag(v___y_3058_) == 1)
{
lean_object* v_val_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v_val_3075_ = lean_ctor_get(v___y_3058_, 0);
lean_inc(v_val_3075_);
lean_dec_ref_known(v___y_3058_, 1);
v___x_3076_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___y_3062_);
v___x_3077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___y_3062_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = l_Array_mkArray2___redArg(v___x_3077_, v_val_3075_);
v___y_3008_ = v___y_3052_;
v___y_3009_ = v___x_3074_;
v___y_3010_ = v___y_3054_;
v___y_3011_ = v___y_3055_;
v___y_3012_ = v___x_3070_;
v___y_3013_ = v___y_3056_;
v___y_3014_ = v___y_3057_;
v___y_3015_ = v___y_3059_;
v___y_3016_ = v___y_3060_;
v___y_3017_ = v___x_3072_;
v___y_3018_ = v___y_3061_;
v___y_3019_ = v___y_3062_;
v___y_3020_ = v___y_3064_;
v___y_3021_ = v___x_3069_;
v___y_3022_ = v___x_3071_;
v___y_3023_ = v___x_3078_;
goto v___jp_3007_;
}
else
{
lean_object* v___x_3079_; 
lean_dec(v___y_3058_);
v___x_3079_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3008_ = v___y_3052_;
v___y_3009_ = v___x_3074_;
v___y_3010_ = v___y_3054_;
v___y_3011_ = v___y_3055_;
v___y_3012_ = v___x_3070_;
v___y_3013_ = v___y_3056_;
v___y_3014_ = v___y_3057_;
v___y_3015_ = v___y_3059_;
v___y_3016_ = v___y_3060_;
v___y_3017_ = v___x_3072_;
v___y_3018_ = v___y_3061_;
v___y_3019_ = v___y_3062_;
v___y_3020_ = v___y_3064_;
v___y_3021_ = v___x_3069_;
v___y_3022_ = v___x_3071_;
v___y_3023_ = v___x_3079_;
goto v___jp_3007_;
}
}
v___jp_3080_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_3096_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
if (lean_obj_tag(v___y_3094_) == 1)
{
lean_object* v_val_3097_; lean_object* v___x_3098_; 
v_val_3097_ = lean_ctor_get(v___y_3094_, 0);
lean_inc(v_val_3097_);
lean_dec_ref_known(v___y_3094_, 1);
v___x_3098_ = l_Array_mkArray1___redArg(v_val_3097_);
v___y_3052_ = v___y_3081_;
v___y_3053_ = v___y_3082_;
v___y_3054_ = v___y_3083_;
v___y_3055_ = v___y_3084_;
v___y_3056_ = v___y_3085_;
v___y_3057_ = v___y_3086_;
v___y_3058_ = v___y_3087_;
v___y_3059_ = v___y_3088_;
v___y_3060_ = v___y_3089_;
v___y_3061_ = v___y_3090_;
v___y_3062_ = v___y_3091_;
v___y_3063_ = v___x_3095_;
v___y_3064_ = v___x_3096_;
v___y_3065_ = v___y_3092_;
v___y_3066_ = v___y_3093_;
v___y_3067_ = v___x_3098_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3099_; 
lean_dec(v___y_3094_);
v___x_3099_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3052_ = v___y_3081_;
v___y_3053_ = v___y_3082_;
v___y_3054_ = v___y_3083_;
v___y_3055_ = v___y_3084_;
v___y_3056_ = v___y_3085_;
v___y_3057_ = v___y_3086_;
v___y_3058_ = v___y_3087_;
v___y_3059_ = v___y_3088_;
v___y_3060_ = v___y_3089_;
v___y_3061_ = v___y_3090_;
v___y_3062_ = v___y_3091_;
v___y_3063_ = v___x_3095_;
v___y_3064_ = v___x_3096_;
v___y_3065_ = v___y_3092_;
v___y_3066_ = v___y_3093_;
v___y_3067_ = v___x_3099_;
goto v___jp_3051_;
}
}
v___jp_3100_:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; size_t v_sz_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
lean_inc_ref_n(v___y_3114_, 2);
v___x_3124_ = l_Array_append___redArg(v___y_3114_, v___y_3123_);
lean_dec_ref(v___y_3123_);
lean_inc_n(v___y_3108_, 3);
lean_inc_n(v___y_3101_, 9);
v___x_3125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3125_, 0, v___y_3101_);
lean_ctor_set(v___x_3125_, 1, v___y_3108_);
lean_ctor_set(v___x_3125_, 2, v___x_3124_);
v___x_3126_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
v___x_3127_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
v___x_3128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___y_3101_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
v___x_3129_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__6));
v___x_3130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___y_3101_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_3132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___y_3101_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = l_Nat_reprFast(v___y_3102_);
v___x_3134_ = lean_box(2);
v___x_3135_ = l_Lean_Syntax_mkNumLit(v___x_3133_, v___x_3134_);
v___x_3136_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___y_3101_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v___x_3138_ = l_Lean_Syntax_node5(v___y_3101_, v___x_3126_, v___x_3128_, v___x_3130_, v___x_3132_, v___x_3135_, v___x_3137_);
v___x_3139_ = l_Lean_Syntax_node1(v___y_3101_, v___y_3108_, v___x_3138_);
v_sz_3140_ = lean_array_size(v___y_3117_);
v___x_3141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_3140_, v___y_3118_, v___y_3117_);
v___x_3142_ = l_Array_append___redArg(v___y_3114_, v___x_3141_);
lean_dec_ref(v___x_3141_);
v___x_3143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3143_, 0, v___y_3101_);
lean_ctor_set(v___x_3143_, 1, v___y_3108_);
lean_ctor_set(v___x_3143_, 2, v___x_3142_);
v___x_3144_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_3145_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___y_3101_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
v___x_3146_ = lean_unsigned_to_nat(10u);
v___x_3147_ = lean_mk_empty_array_with_capacity(v___x_3146_);
v___x_3148_ = lean_array_push(v___x_3147_, v___y_3109_);
v___x_3149_ = lean_array_push(v___x_3148_, v___y_3122_);
v___x_3150_ = lean_array_push(v___x_3149_, v___y_3107_);
v___x_3151_ = lean_array_push(v___x_3150_, v___y_3111_);
v___x_3152_ = lean_array_push(v___x_3151_, v___y_3112_);
v___x_3153_ = lean_array_push(v___x_3152_, v___x_3125_);
v___x_3154_ = lean_array_push(v___x_3153_, v___x_3139_);
v___x_3155_ = lean_array_push(v___x_3154_, v___x_3143_);
v___x_3156_ = lean_array_push(v___x_3155_, v___x_3145_);
lean_inc(v___y_3105_);
v___x_3157_ = lean_array_push(v___x_3156_, v___y_3105_);
lean_inc(v___y_3116_);
v___x_3158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3158_, 0, v___y_3101_);
lean_ctor_set(v___x_3158_, 1, v___y_3116_);
lean_ctor_set(v___x_3158_, 2, v___x_3157_);
v___x_3159_ = l_Lean_Elab_Command_elabSyntax(v___x_3158_, v___y_3106_, v___y_3110_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v___x_3161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3134_);
lean_ctor_set(v___x_3161_, 1, v_a_3160_);
lean_ctor_set(v___x_3161_, 2, v___y_3120_);
v___x_3162_ = l_Lean_Elab_Command_getRef___redArg(v___y_3106_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v___x_3164_ = l_Lean_SourceInfo_fromRef(v_a_3163_, v___y_3104_);
lean_dec(v_a_3163_);
v___x_3165_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3106_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_quotContext_x3f_3166_; 
lean_dec_ref_known(v___x_3165_, 1);
v_quotContext_x3f_3166_ = lean_ctor_get(v___y_3106_, 5);
if (lean_obj_tag(v_quotContext_x3f_3166_) == 0)
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3110_);
lean_dec_ref(v___x_3167_);
v___y_3081_ = v___y_3103_;
v___y_3082_ = v___y_3105_;
v___y_3083_ = v___y_3106_;
v___y_3084_ = v___y_3108_;
v___y_3085_ = v___x_3161_;
v___y_3086_ = v___y_3110_;
v___y_3087_ = v___y_3113_;
v___y_3088_ = v___y_3114_;
v___y_3089_ = v___y_3115_;
v___y_3090_ = v___x_3136_;
v___y_3091_ = v___x_3164_;
v___y_3092_ = v___x_3144_;
v___y_3093_ = v___y_3119_;
v___y_3094_ = v___y_3121_;
goto v___jp_3080_;
}
else
{
v___y_3081_ = v___y_3103_;
v___y_3082_ = v___y_3105_;
v___y_3083_ = v___y_3106_;
v___y_3084_ = v___y_3108_;
v___y_3085_ = v___x_3161_;
v___y_3086_ = v___y_3110_;
v___y_3087_ = v___y_3113_;
v___y_3088_ = v___y_3114_;
v___y_3089_ = v___y_3115_;
v___y_3090_ = v___x_3136_;
v___y_3091_ = v___x_3164_;
v___y_3092_ = v___x_3144_;
v___y_3093_ = v___y_3119_;
v___y_3094_ = v___y_3121_;
goto v___jp_3080_;
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec(v___x_3164_);
lean_dec_ref_known(v___x_3161_, 3);
lean_dec(v___y_3121_);
lean_dec(v___y_3115_);
lean_dec(v___y_3113_);
lean_dec(v___y_3105_);
v_a_3168_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3165_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3165_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec_ref_known(v___x_3161_, 3);
lean_dec(v___y_3121_);
lean_dec(v___y_3115_);
lean_dec(v___y_3113_);
lean_dec(v___y_3105_);
v_a_3176_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3162_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3162_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3115_);
lean_dec(v___y_3113_);
lean_dec(v___y_3105_);
v_a_3184_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3159_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3159_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
v___jp_3192_:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_inc_ref(v___y_3206_);
v___x_3216_ = l_Array_append___redArg(v___y_3206_, v___y_3215_);
lean_dec_ref(v___y_3215_);
lean_inc(v___y_3201_);
lean_inc(v___y_3193_);
v___x_3217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3217_, 0, v___y_3193_);
lean_ctor_set(v___x_3217_, 1, v___y_3201_);
lean_ctor_set(v___x_3217_, 2, v___x_3216_);
if (lean_obj_tag(v___y_3196_) == 1)
{
lean_object* v_val_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v_val_3218_ = lean_ctor_get(v___y_3196_, 0);
lean_inc(v_val_3218_);
lean_dec_ref_known(v___y_3196_, 1);
v___x_3219_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
v___x_3220_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___y_3193_, 5);
v___x_3221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___y_3193_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__9));
v___x_3223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___y_3193_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___x_3224_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_3225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___y_3193_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
v___x_3226_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___y_3193_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
v___x_3228_ = l_Lean_Syntax_node5(v___y_3193_, v___x_3219_, v___x_3221_, v___x_3223_, v___x_3225_, v_val_3218_, v___x_3227_);
v___x_3229_ = l_Array_mkArray1___redArg(v___x_3228_);
v___y_3101_ = v___y_3193_;
v___y_3102_ = v___y_3194_;
v___y_3103_ = v___y_3195_;
v___y_3104_ = v___y_3197_;
v___y_3105_ = v___y_3198_;
v___y_3106_ = v___y_3199_;
v___y_3107_ = v___y_3200_;
v___y_3108_ = v___y_3201_;
v___y_3109_ = v___y_3202_;
v___y_3110_ = v___y_3203_;
v___y_3111_ = v___y_3204_;
v___y_3112_ = v___x_3217_;
v___y_3113_ = v___y_3205_;
v___y_3114_ = v___y_3206_;
v___y_3115_ = v___y_3207_;
v___y_3116_ = v___y_3208_;
v___y_3117_ = v___y_3209_;
v___y_3118_ = v___y_3210_;
v___y_3119_ = v___y_3211_;
v___y_3120_ = v___y_3212_;
v___y_3121_ = v___y_3214_;
v___y_3122_ = v___y_3213_;
v___y_3123_ = v___x_3229_;
goto v___jp_3100_;
}
else
{
lean_object* v___x_3230_; 
lean_dec(v___y_3196_);
v___x_3230_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3101_ = v___y_3193_;
v___y_3102_ = v___y_3194_;
v___y_3103_ = v___y_3195_;
v___y_3104_ = v___y_3197_;
v___y_3105_ = v___y_3198_;
v___y_3106_ = v___y_3199_;
v___y_3107_ = v___y_3200_;
v___y_3108_ = v___y_3201_;
v___y_3109_ = v___y_3202_;
v___y_3110_ = v___y_3203_;
v___y_3111_ = v___y_3204_;
v___y_3112_ = v___x_3217_;
v___y_3113_ = v___y_3205_;
v___y_3114_ = v___y_3206_;
v___y_3115_ = v___y_3207_;
v___y_3116_ = v___y_3208_;
v___y_3117_ = v___y_3209_;
v___y_3118_ = v___y_3210_;
v___y_3119_ = v___y_3211_;
v___y_3120_ = v___y_3212_;
v___y_3121_ = v___y_3214_;
v___y_3122_ = v___y_3213_;
v___y_3123_ = v___x_3230_;
goto v___jp_3100_;
}
}
v___jp_3231_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_inc_ref(v___y_3244_);
v___x_3256_ = l_Array_append___redArg(v___y_3244_, v___y_3255_);
lean_dec_ref(v___y_3255_);
lean_inc(v___y_3240_);
lean_inc(v___y_3232_);
v___x_3257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3257_, 0, v___y_3232_);
lean_ctor_set(v___x_3257_, 1, v___y_3240_);
lean_ctor_set(v___x_3257_, 2, v___x_3256_);
v___x_3258_ = l_Lean_SourceInfo_fromRef(v___y_3247_, v___x_3048_);
lean_dec(v___y_3247_);
lean_inc_ref(v___y_3251_);
v___x_3259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
lean_ctor_set(v___x_3259_, 1, v___y_3251_);
if (lean_obj_tag(v___y_3248_) == 1)
{
lean_object* v_val_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v_val_3260_ = lean_ctor_get(v___y_3248_, 0);
lean_inc(v_val_3260_);
lean_dec_ref_known(v___y_3248_, 1);
v___x_3261_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
v___x_3262_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc_n(v___y_3232_, 2);
v___x_3263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___y_3232_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = l_Lean_Syntax_node2(v___y_3232_, v___x_3261_, v___x_3263_, v_val_3260_);
v___x_3265_ = l_Array_mkArray1___redArg(v___x_3264_);
v___y_3193_ = v___y_3232_;
v___y_3194_ = v___y_3233_;
v___y_3195_ = v___y_3234_;
v___y_3196_ = v___y_3235_;
v___y_3197_ = v___y_3236_;
v___y_3198_ = v___y_3237_;
v___y_3199_ = v___y_3238_;
v___y_3200_ = v___y_3239_;
v___y_3201_ = v___y_3240_;
v___y_3202_ = v___y_3241_;
v___y_3203_ = v___y_3242_;
v___y_3204_ = v___x_3259_;
v___y_3205_ = v___y_3243_;
v___y_3206_ = v___y_3244_;
v___y_3207_ = v___y_3245_;
v___y_3208_ = v___y_3246_;
v___y_3209_ = v___y_3249_;
v___y_3210_ = v___y_3250_;
v___y_3211_ = v___y_3252_;
v___y_3212_ = v___y_3253_;
v___y_3213_ = v___x_3257_;
v___y_3214_ = v___y_3254_;
v___y_3215_ = v___x_3265_;
goto v___jp_3192_;
}
else
{
lean_object* v___x_3266_; 
lean_dec(v___y_3248_);
v___x_3266_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3193_ = v___y_3232_;
v___y_3194_ = v___y_3233_;
v___y_3195_ = v___y_3234_;
v___y_3196_ = v___y_3235_;
v___y_3197_ = v___y_3236_;
v___y_3198_ = v___y_3237_;
v___y_3199_ = v___y_3238_;
v___y_3200_ = v___y_3239_;
v___y_3201_ = v___y_3240_;
v___y_3202_ = v___y_3241_;
v___y_3203_ = v___y_3242_;
v___y_3204_ = v___x_3259_;
v___y_3205_ = v___y_3243_;
v___y_3206_ = v___y_3244_;
v___y_3207_ = v___y_3245_;
v___y_3208_ = v___y_3246_;
v___y_3209_ = v___y_3249_;
v___y_3210_ = v___y_3250_;
v___y_3211_ = v___y_3252_;
v___y_3212_ = v___y_3253_;
v___y_3213_ = v___x_3257_;
v___y_3214_ = v___y_3254_;
v___y_3215_ = v___x_3266_;
goto v___jp_3192_;
}
}
v___jp_3267_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_inc_ref(v___y_3278_);
v___x_3292_ = l_Array_append___redArg(v___y_3278_, v___y_3291_);
lean_dec_ref(v___y_3291_);
lean_inc(v___y_3276_);
lean_inc(v___y_3268_);
v___x_3293_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3293_, 0, v___y_3268_);
lean_ctor_set(v___x_3293_, 1, v___y_3276_);
lean_ctor_set(v___x_3293_, 2, v___x_3292_);
if (lean_obj_tag(v___y_3284_) == 1)
{
lean_object* v_val_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_val_3294_ = lean_ctor_get(v___y_3284_, 0);
lean_inc(v_val_3294_);
lean_dec_ref_known(v___y_3284_, 1);
v___x_3295_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_3270_);
v___x_3296_ = l_Lean_Name_mkStr4(v___x_3005_, v___x_3006_, v___y_3270_, v___x_3295_);
v___x_3297_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___y_3268_, 4);
v___x_3298_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___y_3268_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
lean_inc_ref(v___y_3278_);
v___x_3299_ = l_Array_append___redArg(v___y_3278_, v_val_3294_);
lean_dec(v_val_3294_);
lean_inc(v___y_3276_);
v___x_3300_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3300_, 0, v___y_3268_);
lean_ctor_set(v___x_3300_, 1, v___y_3276_);
lean_ctor_set(v___x_3300_, 2, v___x_3299_);
v___x_3301_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_3302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___y_3268_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = l_Lean_Syntax_node3(v___y_3268_, v___x_3296_, v___x_3298_, v___x_3300_, v___x_3302_);
v___x_3304_ = l_Array_mkArray1___redArg(v___x_3303_);
v___y_3232_ = v___y_3268_;
v___y_3233_ = v___y_3269_;
v___y_3234_ = v___y_3270_;
v___y_3235_ = v___y_3271_;
v___y_3236_ = v___y_3272_;
v___y_3237_ = v___y_3273_;
v___y_3238_ = v___y_3274_;
v___y_3239_ = v___y_3275_;
v___y_3240_ = v___y_3276_;
v___y_3241_ = v___x_3293_;
v___y_3242_ = v___y_3277_;
v___y_3243_ = v___y_3279_;
v___y_3244_ = v___y_3278_;
v___y_3245_ = v___y_3280_;
v___y_3246_ = v___y_3282_;
v___y_3247_ = v___y_3281_;
v___y_3248_ = v___y_3283_;
v___y_3249_ = v___y_3285_;
v___y_3250_ = v___y_3287_;
v___y_3251_ = v___y_3286_;
v___y_3252_ = v___y_3288_;
v___y_3253_ = v___y_3289_;
v___y_3254_ = v___y_3290_;
v___y_3255_ = v___x_3304_;
goto v___jp_3231_;
}
else
{
lean_object* v___x_3305_; 
lean_dec(v___y_3284_);
v___x_3305_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3232_ = v___y_3268_;
v___y_3233_ = v___y_3269_;
v___y_3234_ = v___y_3270_;
v___y_3235_ = v___y_3271_;
v___y_3236_ = v___y_3272_;
v___y_3237_ = v___y_3273_;
v___y_3238_ = v___y_3274_;
v___y_3239_ = v___y_3275_;
v___y_3240_ = v___y_3276_;
v___y_3241_ = v___x_3293_;
v___y_3242_ = v___y_3277_;
v___y_3243_ = v___y_3279_;
v___y_3244_ = v___y_3278_;
v___y_3245_ = v___y_3280_;
v___y_3246_ = v___y_3282_;
v___y_3247_ = v___y_3281_;
v___y_3248_ = v___y_3283_;
v___y_3249_ = v___y_3285_;
v___y_3250_ = v___y_3287_;
v___y_3251_ = v___y_3286_;
v___y_3252_ = v___y_3288_;
v___y_3253_ = v___y_3289_;
v___y_3254_ = v___y_3290_;
v___y_3255_ = v___x_3305_;
goto v___jp_3231_;
}
}
v___jp_3306_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3326_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__12));
v___x_3327_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__13));
v___x_3328_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_3329_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v___y_3325_) == 1)
{
lean_object* v_val_3330_; lean_object* v___x_3331_; 
v_val_3330_ = lean_ctor_get(v___y_3325_, 0);
lean_inc(v_val_3330_);
v___x_3331_ = l_Array_mkArray1___redArg(v_val_3330_);
v___y_3268_ = v___y_3307_;
v___y_3269_ = v___y_3308_;
v___y_3270_ = v___y_3309_;
v___y_3271_ = v___y_3310_;
v___y_3272_ = v___y_3311_;
v___y_3273_ = v___y_3312_;
v___y_3274_ = v___y_3313_;
v___y_3275_ = v___y_3314_;
v___y_3276_ = v___x_3328_;
v___y_3277_ = v___y_3315_;
v___y_3278_ = v___x_3329_;
v___y_3279_ = v___y_3316_;
v___y_3280_ = v___y_3317_;
v___y_3281_ = v___y_3318_;
v___y_3282_ = v___x_3327_;
v___y_3283_ = v___y_3319_;
v___y_3284_ = v___y_3321_;
v___y_3285_ = v___y_3320_;
v___y_3286_ = v___x_3326_;
v___y_3287_ = v___y_3322_;
v___y_3288_ = v___y_3323_;
v___y_3289_ = v___y_3324_;
v___y_3290_ = v___y_3325_;
v___y_3291_ = v___x_3331_;
goto v___jp_3267_;
}
else
{
lean_object* v___x_3332_; 
v___x_3332_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3268_ = v___y_3307_;
v___y_3269_ = v___y_3308_;
v___y_3270_ = v___y_3309_;
v___y_3271_ = v___y_3310_;
v___y_3272_ = v___y_3311_;
v___y_3273_ = v___y_3312_;
v___y_3274_ = v___y_3313_;
v___y_3275_ = v___y_3314_;
v___y_3276_ = v___x_3328_;
v___y_3277_ = v___y_3315_;
v___y_3278_ = v___x_3329_;
v___y_3279_ = v___y_3316_;
v___y_3280_ = v___y_3317_;
v___y_3281_ = v___y_3318_;
v___y_3282_ = v___x_3327_;
v___y_3283_ = v___y_3319_;
v___y_3284_ = v___y_3321_;
v___y_3285_ = v___y_3320_;
v___y_3286_ = v___x_3326_;
v___y_3287_ = v___y_3322_;
v___y_3288_ = v___y_3323_;
v___y_3289_ = v___y_3324_;
v___y_3290_ = v___y_3325_;
v___y_3291_ = v___x_3332_;
goto v___jp_3267_;
}
}
v___jp_3333_:
{
lean_object* v___x_3350_; lean_object* v_args_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3350_ = l_Lean_Syntax_getArg(v___y_3334_, v___y_3338_);
lean_dec(v___y_3334_);
v_args_3351_ = l_Lean_Syntax_getArgs(v___y_3340_);
lean_dec(v___y_3340_);
v___x_3352_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_3352_, 0, v___y_3345_);
v___x_3353_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v___x_3352_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; size_t v_sz_3355_; size_t v___x_3356_; lean_object* v___x_3357_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v___x_3353_, 1);
v_sz_3355_ = lean_array_size(v_args_3351_);
v___x_3356_ = ((size_t)0ULL);
v___x_3357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_3355_, v___x_3356_, v_args_3351_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3359_; lean_object* v_fst_3360_; lean_object* v_snd_3361_; lean_object* v___x_3362_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3357_, 1);
v___x_3359_ = l_Array_unzip___redArg(v_a_3358_);
lean_dec(v_a_3358_);
v_fst_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_fst_3360_);
v_snd_3361_ = lean_ctor_get(v___x_3359_, 1);
lean_inc(v_snd_3361_);
lean_dec_ref(v___x_3359_);
v___x_3362_ = l_Lean_Elab_Command_getRef___redArg(v___y_3348_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; uint8_t v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v___x_3364_ = 0;
v___x_3365_ = l_Lean_SourceInfo_fromRef(v_a_3363_, v___x_3364_);
lean_dec(v_a_3363_);
v___x_3366_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3348_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_quotContext_x3f_3367_; 
lean_dec_ref_known(v___x_3366_, 1);
v_quotContext_x3f_3367_ = lean_ctor_get(v___y_3348_, 5);
if (lean_obj_tag(v_quotContext_x3f_3367_) == 0)
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3349_);
lean_dec_ref(v___x_3368_);
v___y_3307_ = v___x_3365_;
v___y_3308_ = v_a_3354_;
v___y_3309_ = v___y_3335_;
v___y_3310_ = v___y_3336_;
v___y_3311_ = v___x_3364_;
v___y_3312_ = v___y_3337_;
v___y_3313_ = v___y_3348_;
v___y_3314_ = v___y_3339_;
v___y_3315_ = v___y_3349_;
v___y_3316_ = v_expectedType_x3f_3347_;
v___y_3317_ = v___x_3350_;
v___y_3318_ = v___y_3341_;
v___y_3319_ = v___y_3342_;
v___y_3320_ = v_fst_3360_;
v___y_3321_ = v___y_3343_;
v___y_3322_ = v___x_3356_;
v___y_3323_ = v___y_3344_;
v___y_3324_ = v_snd_3361_;
v___y_3325_ = v___y_3346_;
goto v___jp_3306_;
}
else
{
v___y_3307_ = v___x_3365_;
v___y_3308_ = v_a_3354_;
v___y_3309_ = v___y_3335_;
v___y_3310_ = v___y_3336_;
v___y_3311_ = v___x_3364_;
v___y_3312_ = v___y_3337_;
v___y_3313_ = v___y_3348_;
v___y_3314_ = v___y_3339_;
v___y_3315_ = v___y_3349_;
v___y_3316_ = v_expectedType_x3f_3347_;
v___y_3317_ = v___x_3350_;
v___y_3318_ = v___y_3341_;
v___y_3319_ = v___y_3342_;
v___y_3320_ = v_fst_3360_;
v___y_3321_ = v___y_3343_;
v___y_3322_ = v___x_3356_;
v___y_3323_ = v___y_3344_;
v___y_3324_ = v_snd_3361_;
v___y_3325_ = v___y_3346_;
goto v___jp_3306_;
}
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec(v___x_3365_);
lean_dec(v_snd_3361_);
lean_dec(v_fst_3360_);
lean_dec(v_a_3354_);
lean_dec(v___x_3350_);
lean_dec(v_expectedType_x3f_3347_);
lean_dec(v___y_3346_);
lean_dec(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec(v___y_3339_);
lean_dec(v___y_3337_);
lean_dec(v___y_3336_);
v_a_3369_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3366_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3366_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec(v_snd_3361_);
lean_dec(v_fst_3360_);
lean_dec(v_a_3354_);
lean_dec(v___x_3350_);
lean_dec(v_expectedType_x3f_3347_);
lean_dec(v___y_3346_);
lean_dec(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec(v___y_3339_);
lean_dec(v___y_3337_);
lean_dec(v___y_3336_);
v_a_3377_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3362_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3362_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec(v_a_3354_);
lean_dec(v___x_3350_);
lean_dec(v_expectedType_x3f_3347_);
lean_dec(v___y_3346_);
lean_dec(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec(v___y_3339_);
lean_dec(v___y_3337_);
lean_dec(v___y_3336_);
v_a_3385_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3357_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3357_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec_ref(v_args_3351_);
lean_dec(v___x_3350_);
lean_dec(v_expectedType_x3f_3347_);
lean_dec(v___y_3346_);
lean_dec(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec(v___y_3339_);
lean_dec(v___y_3337_);
lean_dec(v___y_3336_);
v_a_3393_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3353_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3353_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
v___jp_3401_:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; 
v___x_3416_ = lean_unsigned_to_nat(8u);
v___x_3417_ = l_Lean_Syntax_getArg(v_x_3001_, v___x_3416_);
v___x_3418_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__15));
lean_inc(v___x_3417_);
v___x_3419_ = l_Lean_Syntax_isOfKind(v___x_3417_, v___x_3418_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; 
lean_dec(v___x_3417_);
lean_dec(v_prio_x3f_3413_);
lean_dec(v___y_3412_);
lean_dec(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec(v___y_3406_);
lean_dec(v___y_3404_);
lean_dec(v___y_3402_);
lean_dec(v_x_3001_);
v___x_3420_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3420_;
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3421_ = lean_unsigned_to_nat(7u);
v___x_3422_ = l_Lean_Syntax_getArg(v_x_3001_, v___x_3421_);
lean_dec(v_x_3001_);
v___x_3423_ = l_Lean_Syntax_getArg(v___x_3417_, v___y_3408_);
v___x_3424_ = l_Lean_Syntax_getArg(v___x_3417_, v___y_3405_);
v___x_3425_ = l_Lean_Syntax_isNone(v___x_3424_);
if (v___x_3425_ == 0)
{
uint8_t v___x_3426_; 
lean_inc(v___x_3424_);
v___x_3426_ = l_Lean_Syntax_matchesNull(v___x_3424_, v___y_3405_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
lean_dec(v___x_3424_);
lean_dec(v___x_3423_);
lean_dec(v___x_3422_);
lean_dec(v___x_3417_);
lean_dec(v_prio_x3f_3413_);
lean_dec(v___y_3412_);
lean_dec(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec(v___y_3406_);
lean_dec(v___y_3404_);
lean_dec(v___y_3402_);
v___x_3427_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3427_;
}
else
{
lean_object* v_expectedType_x3f_3428_; lean_object* v___x_3429_; 
v_expectedType_x3f_3428_ = l_Lean_Syntax_getArg(v___x_3424_, v___y_3408_);
lean_dec(v___x_3424_);
v___x_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3429_, 0, v_expectedType_x3f_3428_);
v___y_3334_ = v___x_3417_;
v___y_3335_ = v___y_3403_;
v___y_3336_ = v___y_3404_;
v___y_3337_ = v___x_3423_;
v___y_3338_ = v___y_3407_;
v___y_3339_ = v___y_3406_;
v___y_3340_ = v___x_3422_;
v___y_3341_ = v___y_3402_;
v___y_3342_ = v___y_3409_;
v___y_3343_ = v___y_3410_;
v___y_3344_ = v___y_3411_;
v___y_3345_ = v_prio_x3f_3413_;
v___y_3346_ = v___y_3412_;
v_expectedType_x3f_3347_ = v___x_3429_;
v___y_3348_ = v___y_3414_;
v___y_3349_ = v___y_3415_;
goto v___jp_3333_;
}
}
else
{
lean_object* v___x_3430_; 
lean_dec(v___x_3424_);
v___x_3430_ = lean_box(0);
v___y_3334_ = v___x_3417_;
v___y_3335_ = v___y_3403_;
v___y_3336_ = v___y_3404_;
v___y_3337_ = v___x_3423_;
v___y_3338_ = v___y_3407_;
v___y_3339_ = v___y_3406_;
v___y_3340_ = v___x_3422_;
v___y_3341_ = v___y_3402_;
v___y_3342_ = v___y_3409_;
v___y_3343_ = v___y_3410_;
v___y_3344_ = v___y_3411_;
v___y_3345_ = v_prio_x3f_3413_;
v___y_3346_ = v___y_3412_;
v_expectedType_x3f_3347_ = v___x_3430_;
v___y_3348_ = v___y_3414_;
v___y_3349_ = v___y_3415_;
goto v___jp_3333_;
}
}
}
v___jp_3431_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; 
v___x_3446_ = lean_unsigned_to_nat(6u);
v___x_3447_ = l_Lean_Syntax_getArg(v_x_3001_, v___x_3446_);
v___x_3448_ = l_Lean_Syntax_isNone(v___x_3447_);
if (v___x_3448_ == 0)
{
uint8_t v___x_3449_; 
lean_inc(v___x_3447_);
v___x_3449_ = l_Lean_Syntax_matchesNull(v___x_3447_, v___y_3434_);
if (v___x_3449_ == 0)
{
lean_object* v___x_3450_; 
lean_dec(v___x_3447_);
lean_dec(v_name_x3f_3443_);
lean_dec(v___y_3442_);
lean_dec(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec(v___y_3436_);
lean_dec(v___y_3432_);
lean_dec(v_x_3001_);
v___x_3450_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3450_;
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
v___x_3451_ = l_Lean_Syntax_getArg(v___x_3447_, v___x_3050_);
lean_dec(v___x_3447_);
v___x_3452_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
lean_inc(v___x_3451_);
v___x_3453_ = l_Lean_Syntax_isOfKind(v___x_3451_, v___x_3452_);
if (v___x_3453_ == 0)
{
lean_object* v___x_3454_; 
lean_dec(v___x_3451_);
lean_dec(v_name_x3f_3443_);
lean_dec(v___y_3442_);
lean_dec(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec(v___y_3436_);
lean_dec(v___y_3432_);
lean_dec(v_x_3001_);
v___x_3454_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3454_;
}
else
{
lean_object* v_prio_x3f_3455_; lean_object* v___x_3456_; 
v_prio_x3f_3455_ = l_Lean_Syntax_getArg(v___x_3451_, v___y_3440_);
lean_dec(v___x_3451_);
v___x_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3456_, 0, v_prio_x3f_3455_);
v___y_3402_ = v___y_3432_;
v___y_3403_ = v___y_3433_;
v___y_3404_ = v_name_x3f_3443_;
v___y_3405_ = v___y_3437_;
v___y_3406_ = v___y_3436_;
v___y_3407_ = v___y_3435_;
v___y_3408_ = v___y_3434_;
v___y_3409_ = v___y_3438_;
v___y_3410_ = v___y_3439_;
v___y_3411_ = v___y_3441_;
v___y_3412_ = v___y_3442_;
v_prio_x3f_3413_ = v___x_3456_;
v___y_3414_ = v___y_3444_;
v___y_3415_ = v___y_3445_;
goto v___jp_3401_;
}
}
}
else
{
lean_object* v___x_3457_; 
lean_dec(v___x_3447_);
v___x_3457_ = lean_box(0);
v___y_3402_ = v___y_3432_;
v___y_3403_ = v___y_3433_;
v___y_3404_ = v_name_x3f_3443_;
v___y_3405_ = v___y_3437_;
v___y_3406_ = v___y_3436_;
v___y_3407_ = v___y_3435_;
v___y_3408_ = v___y_3434_;
v___y_3409_ = v___y_3438_;
v___y_3410_ = v___y_3439_;
v___y_3411_ = v___y_3441_;
v___y_3412_ = v___y_3442_;
v_prio_x3f_3413_ = v___x_3457_;
v___y_3414_ = v___y_3444_;
v___y_3415_ = v___y_3445_;
goto v___jp_3401_;
}
}
v___jp_3458_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v___x_3472_ = lean_unsigned_to_nat(5u);
v___x_3473_ = l_Lean_Syntax_getArg(v_x_3001_, v___x_3472_);
v___x_3474_ = l_Lean_Syntax_isNone(v___x_3473_);
if (v___x_3474_ == 0)
{
uint8_t v___x_3475_; 
lean_inc(v___x_3473_);
v___x_3475_ = l_Lean_Syntax_matchesNull(v___x_3473_, v___y_3464_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; 
lean_dec(v___x_3473_);
lean_dec(v_prec_x3f_3469_);
lean_dec(v___y_3468_);
lean_dec(v___y_3465_);
lean_dec(v___y_3462_);
lean_dec(v___y_3459_);
lean_dec(v_x_3001_);
v___x_3476_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3476_;
}
else
{
lean_object* v___x_3477_; lean_object* v___x_3478_; uint8_t v___x_3479_; 
v___x_3477_ = l_Lean_Syntax_getArg(v___x_3473_, v___x_3050_);
lean_dec(v___x_3473_);
v___x_3478_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
lean_inc(v___x_3477_);
v___x_3479_ = l_Lean_Syntax_isOfKind(v___x_3477_, v___x_3478_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; 
lean_dec(v___x_3477_);
lean_dec(v_prec_x3f_3469_);
lean_dec(v___y_3468_);
lean_dec(v___y_3465_);
lean_dec(v___y_3462_);
lean_dec(v___y_3459_);
lean_dec(v_x_3001_);
v___x_3480_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3480_;
}
else
{
lean_object* v_name_x3f_3481_; lean_object* v___x_3482_; 
v_name_x3f_3481_ = l_Lean_Syntax_getArg(v___x_3477_, v___y_3467_);
lean_dec(v___x_3477_);
v___x_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3482_, 0, v_name_x3f_3481_);
v___y_3432_ = v___y_3459_;
v___y_3433_ = v___y_3460_;
v___y_3434_ = v___y_3464_;
v___y_3435_ = v___y_3463_;
v___y_3436_ = v___y_3462_;
v___y_3437_ = v___y_3461_;
v___y_3438_ = v_prec_x3f_3469_;
v___y_3439_ = v___y_3465_;
v___y_3440_ = v___y_3467_;
v___y_3441_ = v___y_3466_;
v___y_3442_ = v___y_3468_;
v_name_x3f_3443_ = v___x_3482_;
v___y_3444_ = v___y_3470_;
v___y_3445_ = v___y_3471_;
goto v___jp_3431_;
}
}
}
else
{
lean_object* v___x_3483_; 
lean_dec(v___x_3473_);
v___x_3483_ = lean_box(0);
v___y_3432_ = v___y_3459_;
v___y_3433_ = v___y_3460_;
v___y_3434_ = v___y_3464_;
v___y_3435_ = v___y_3463_;
v___y_3436_ = v___y_3462_;
v___y_3437_ = v___y_3461_;
v___y_3438_ = v_prec_x3f_3469_;
v___y_3439_ = v___y_3465_;
v___y_3440_ = v___y_3467_;
v___y_3441_ = v___y_3466_;
v___y_3442_ = v___y_3468_;
v_name_x3f_3443_ = v___x_3483_;
v___y_3444_ = v___y_3470_;
v___y_3445_ = v___y_3471_;
goto v___jp_3431_;
}
}
v___jp_3484_:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
v___x_3490_ = lean_unsigned_to_nat(2u);
v___x_3491_ = l_Lean_Syntax_getArg(v_x_3001_, v___x_3490_);
v___x_3492_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_3493_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v___x_3491_);
v___x_3494_ = l_Lean_Syntax_isOfKind(v___x_3491_, v___x_3493_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; 
lean_dec(v___x_3491_);
lean_dec(v_attrs_x3f_3487_);
lean_dec(v___y_3486_);
lean_dec(v_x_3001_);
v___x_3495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3495_;
}
else
{
lean_object* v___x_3496_; lean_object* v_tk_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v___x_3496_ = lean_unsigned_to_nat(3u);
v_tk_3497_ = l_Lean_Syntax_getArg(v_x_3001_, v___x_3496_);
v___x_3498_ = lean_unsigned_to_nat(4u);
v___x_3499_ = l_Lean_Syntax_getArg(v_x_3001_, v___x_3498_);
v___x_3500_ = l_Lean_Syntax_isNone(v___x_3499_);
if (v___x_3500_ == 0)
{
uint8_t v___x_3501_; 
lean_inc(v___x_3499_);
v___x_3501_ = l_Lean_Syntax_matchesNull(v___x_3499_, v___y_3485_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3502_; 
lean_dec(v___x_3499_);
lean_dec(v_tk_3497_);
lean_dec(v___x_3491_);
lean_dec(v_attrs_x3f_3487_);
lean_dec(v___y_3486_);
lean_dec(v_x_3001_);
v___x_3502_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3502_;
}
else
{
lean_object* v___x_3503_; lean_object* v___x_3504_; uint8_t v___x_3505_; 
v___x_3503_ = l_Lean_Syntax_getArg(v___x_3499_, v___x_3050_);
lean_dec(v___x_3499_);
v___x_3504_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
lean_inc(v___x_3503_);
v___x_3505_ = l_Lean_Syntax_isOfKind(v___x_3503_, v___x_3504_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; 
lean_dec(v___x_3503_);
lean_dec(v_tk_3497_);
lean_dec(v___x_3491_);
lean_dec(v_attrs_x3f_3487_);
lean_dec(v___y_3486_);
lean_dec(v_x_3001_);
v___x_3506_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3506_;
}
else
{
lean_object* v_prec_x3f_3507_; lean_object* v___x_3508_; 
v_prec_x3f_3507_ = l_Lean_Syntax_getArg(v___x_3503_, v___y_3485_);
lean_dec(v___x_3503_);
v___x_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3508_, 0, v_prec_x3f_3507_);
v___y_3459_ = v_tk_3497_;
v___y_3460_ = v___x_3492_;
v___y_3461_ = v___x_3490_;
v___y_3462_ = v___x_3491_;
v___y_3463_ = v___x_3498_;
v___y_3464_ = v___y_3485_;
v___y_3465_ = v_attrs_x3f_3487_;
v___y_3466_ = v___x_3493_;
v___y_3467_ = v___x_3496_;
v___y_3468_ = v___y_3486_;
v_prec_x3f_3469_ = v___x_3508_;
v___y_3470_ = v___y_3488_;
v___y_3471_ = v___y_3489_;
goto v___jp_3458_;
}
}
}
else
{
lean_object* v___x_3509_; 
lean_dec(v___x_3499_);
v___x_3509_ = lean_box(0);
v___y_3459_ = v_tk_3497_;
v___y_3460_ = v___x_3492_;
v___y_3461_ = v___x_3490_;
v___y_3462_ = v___x_3491_;
v___y_3463_ = v___x_3498_;
v___y_3464_ = v___y_3485_;
v___y_3465_ = v_attrs_x3f_3487_;
v___y_3466_ = v___x_3493_;
v___y_3467_ = v___x_3496_;
v___y_3468_ = v___y_3486_;
v_prec_x3f_3469_ = v___x_3509_;
v___y_3470_ = v___y_3488_;
v___y_3471_ = v___y_3489_;
goto v___jp_3458_;
}
}
}
v___jp_3510_:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; 
v___x_3514_ = lean_unsigned_to_nat(1u);
v___x_3515_ = l_Lean_Syntax_getArg(v_x_3001_, v___x_3514_);
v___x_3516_ = l_Lean_Syntax_isNone(v___x_3515_);
if (v___x_3516_ == 0)
{
uint8_t v___x_3517_; 
lean_inc(v___x_3515_);
v___x_3517_ = l_Lean_Syntax_matchesNull(v___x_3515_, v___x_3514_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; 
lean_dec(v___x_3515_);
lean_dec(v_doc_x3f_3511_);
lean_dec(v_x_3001_);
v___x_3518_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3518_;
}
else
{
lean_object* v___x_3519_; lean_object* v___x_3520_; uint8_t v___x_3521_; 
v___x_3519_ = l_Lean_Syntax_getArg(v___x_3515_, v___x_3050_);
lean_dec(v___x_3515_);
v___x_3520_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(v___x_3519_);
v___x_3521_ = l_Lean_Syntax_isOfKind(v___x_3519_, v___x_3520_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3522_; 
lean_dec(v___x_3519_);
lean_dec(v_doc_x3f_3511_);
lean_dec(v_x_3001_);
v___x_3522_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3522_;
}
else
{
lean_object* v___x_3523_; lean_object* v_attrs_x3f_3524_; lean_object* v___x_3525_; 
v___x_3523_ = l_Lean_Syntax_getArg(v___x_3519_, v___x_3514_);
lean_dec(v___x_3519_);
v_attrs_x3f_3524_ = l_Lean_Syntax_getArgs(v___x_3523_);
lean_dec(v___x_3523_);
v___x_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3525_, 0, v_attrs_x3f_3524_);
v___y_3485_ = v___x_3514_;
v___y_3486_ = v_doc_x3f_3511_;
v_attrs_x3f_3487_ = v___x_3525_;
v___y_3488_ = v___y_3512_;
v___y_3489_ = v___y_3513_;
goto v___jp_3484_;
}
}
}
else
{
lean_object* v___x_3526_; 
lean_dec(v___x_3515_);
v___x_3526_ = lean_box(0);
v___y_3485_ = v___x_3514_;
v___y_3486_ = v_doc_x3f_3511_;
v_attrs_x3f_3487_ = v___x_3526_;
v___y_3488_ = v___y_3512_;
v___y_3489_ = v___y_3513_;
goto v___jp_3484_;
}
}
}
v___jp_3007_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_inc_ref(v___y_3015_);
v___x_3024_ = l_Array_append___redArg(v___y_3015_, v___y_3023_);
lean_dec_ref(v___y_3023_);
lean_inc_n(v___y_3011_, 4);
lean_inc_n(v___y_3019_, 11);
v___x_3025_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3025_, 0, v___y_3019_);
lean_ctor_set(v___x_3025_, 1, v___y_3011_);
lean_ctor_set(v___x_3025_, 2, v___x_3024_);
v___x_3026_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc_ref_n(v___y_3008_, 3);
v___x_3027_ = l_Lean_Name_mkStr4(v___x_3005_, v___x_3006_, v___y_3008_, v___x_3026_);
v___x_3028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_3029_ = l_Lean_Name_mkStr4(v___x_3005_, v___x_3006_, v___y_3008_, v___x_3028_);
v___x_3030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_3031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___y_3019_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__0));
v___x_3033_ = l_Lean_Name_mkStr4(v___x_3005_, v___x_3006_, v___y_3008_, v___x_3032_);
v___x_3034_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__1));
v___x_3035_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___y_3019_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
lean_inc_ref(v___y_3018_);
v___x_3036_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___y_3019_);
lean_ctor_set(v___x_3036_, 1, v___y_3018_);
v___x_3037_ = l_Lean_Syntax_node3(v___y_3019_, v___x_3033_, v___x_3035_, v___y_3013_, v___x_3036_);
v___x_3038_ = l_Lean_Syntax_node1(v___y_3019_, v___y_3011_, v___x_3037_);
v___x_3039_ = l_Lean_Syntax_node1(v___y_3019_, v___y_3011_, v___x_3038_);
v___x_3040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_3041_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___y_3019_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v___x_3042_ = l_Lean_Syntax_node4(v___y_3019_, v___x_3029_, v___x_3031_, v___x_3039_, v___x_3041_, v___y_3016_);
v___x_3043_ = l_Lean_Syntax_node1(v___y_3019_, v___y_3011_, v___x_3042_);
v___x_3044_ = l_Lean_Syntax_node1(v___y_3019_, v___x_3027_, v___x_3043_);
lean_inc(v___y_3012_);
lean_inc(v___y_3020_);
v___x_3045_ = l_Lean_Syntax_node8(v___y_3019_, v___y_3020_, v___y_3021_, v___y_3012_, v___y_3022_, v___y_3017_, v___y_3012_, v___y_3009_, v___x_3025_, v___x_3044_);
v___x_3046_ = l_Lean_Elab_Command_elabCommand(v___x_3045_, v___y_3010_, v___y_3014_);
return v___x_3046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object* v_x_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Lean_Elab_Command_elabElab(v_x_3539_, v_a_3540_, v_a_3541_);
lean_dec(v_a_3541_);
lean_dec_ref(v_a_3540_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object* v_00_u03b1_3544_, lean_object* v_x_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_3545_, v___y_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3549_, lean_object* v_x_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(v_00_u03b1_3549_, v_x_3550_, v___y_3551_, v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec_ref(v_x_3550_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object* v_00_u03b1_3554_, lean_object* v_ref_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_3555_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object* v_00_u03b1_3560_, lean_object* v_ref_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(v_00_u03b1_3560_, v_ref_3561_, v___y_3562_, v___y_3563_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object* v_00_u03b1_3566_, lean_object* v_x_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_3567_, v___y_3568_, v___y_3569_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object* v_00_u03b1_3572_, lean_object* v_x_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(v_00_u03b1_3572_, v_x_3573_, v___y_3574_, v___y_3575_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object* v_as_3578_, lean_object* v_as_x27_3579_, lean_object* v_b_3580_, lean_object* v_a_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_3579_, v_b_3580_, v___y_3582_, v___y_3583_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object* v_as_3586_, lean_object* v_as_x27_3587_, lean_object* v_b_3588_, lean_object* v_a_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(v_as_3586_, v_as_x27_3587_, v_b_3588_, v_a_3589_, v___y_3590_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v_as_x27_3587_);
lean_dec(v_as_3586_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3594_, lean_object* v_m_3595_, lean_object* v_a_3596_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_3595_, v_a_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3598_, lean_object* v_m_3599_, lean_object* v_a_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(v_00_u03b2_3598_, v_m_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec_ref(v_m_3599_);
return v_res_3601_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_3602_, lean_object* v_x_3603_, lean_object* v_x_3604_){
_start:
{
uint8_t v___x_3605_; 
v___x_3605_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_3603_, v_x_3604_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3606_, lean_object* v_x_3607_, lean_object* v_x_3608_){
_start:
{
uint8_t v_res_3609_; lean_object* v_r_3610_; 
v_res_3609_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(v_00_u03b2_3606_, v_x_3607_, v_x_3608_);
lean_dec_ref(v_x_3608_);
lean_dec_ref(v_x_3607_);
v_r_3610_ = lean_box(v_res_3609_);
return v_r_3610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_3611_, lean_object* v_a_3612_, lean_object* v_x_3613_){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_3612_, v_x_3613_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_3615_, lean_object* v_a_3616_, lean_object* v_x_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(v_00_u03b2_3615_, v_a_3616_, v_x_3617_);
lean_dec(v_x_3617_);
lean_dec(v_a_3616_);
return v_res_3618_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(lean_object* v_00_u03b2_3619_, lean_object* v_x_3620_, size_t v_x_3621_, lean_object* v_x_3622_){
_start:
{
uint8_t v___x_3623_; 
v___x_3623_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_3620_, v_x_3621_, v_x_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3624_, lean_object* v_x_3625_, lean_object* v_x_3626_, lean_object* v_x_3627_){
_start:
{
size_t v_x_18902__boxed_3628_; uint8_t v_res_3629_; lean_object* v_r_3630_; 
v_x_18902__boxed_3628_ = lean_unbox_usize(v_x_3626_);
lean_dec(v_x_3626_);
v_res_3629_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(v_00_u03b2_3624_, v_x_3625_, v_x_18902__boxed_3628_, v_x_3627_);
lean_dec_ref(v_x_3627_);
lean_dec_ref(v_x_3625_);
v_r_3630_ = lean_box(v_res_3629_);
return v_r_3630_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3631_, lean_object* v_keys_3632_, lean_object* v_vals_3633_, lean_object* v_heq_3634_, lean_object* v_i_3635_, lean_object* v_k_3636_){
_start:
{
uint8_t v___x_3637_; 
v___x_3637_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_3632_, v_i_3635_, v_k_3636_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b2_3638_, lean_object* v_keys_3639_, lean_object* v_vals_3640_, lean_object* v_heq_3641_, lean_object* v_i_3642_, lean_object* v_k_3643_){
_start:
{
uint8_t v_res_3644_; lean_object* v_r_3645_; 
v_res_3644_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(v_00_u03b2_3638_, v_keys_3639_, v_vals_3640_, v_heq_3641_, v_i_3642_, v_k_3643_);
lean_dec_ref(v_k_3643_);
lean_dec_ref(v_vals_3640_);
lean_dec_ref(v_keys_3639_);
v_r_3645_ = lean_box(v_res_3644_);
return v_r_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1(){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3653_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3654_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
v___x_3655_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3656_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElab___boxed), 4, 0);
v___x_3657_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3653_, v___x_3654_, v___x_3655_, v___x_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object* v_a_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3(){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3686_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3687_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6));
v___x_3688_ = l_Lean_addBuiltinDeclarationRanges(v___x_3686_, v___x_3687_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object* v_a_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
return v_res_3690_;
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
