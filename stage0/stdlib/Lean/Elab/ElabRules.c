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
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
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
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
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
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_evalOptPrio___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Array_mkArray5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Parser_Command_visibility_ofAttrKind(lean_object*);
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
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Term.TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__9;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "stx"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__15;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__14_value),LEAN_SCALAR_PTR_LITERAL(89, 124, 230, 186, 154, 11, 21, 78)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__16 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__16_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__17 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__17_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__18 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__18_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__19 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__19_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__20 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__21 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__21_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__22 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__22_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noErrorIfUnused"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__23 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__23_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "no_error_if_unused%"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__24 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__24_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "throwUnsupportedSyntax"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__25 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__25_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__26;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__25_value),LEAN_SCALAR_PTR_LITERAL(225, 251, 194, 35, 13, 152, 147, 184)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__27 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__27_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__28 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__29 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__30 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__31 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value;
static const lean_array_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__32 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Elab.Command.CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__33 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__34;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__35 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__35_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Elab.Do.DoElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__36 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__36_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__37;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__38 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__38_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DoElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__39 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__39_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cont"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__40 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__40_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__41;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__40_value),LEAN_SCALAR_PTR_LITERAL(53, 231, 177, 147, 174, 255, 200, 174)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__42 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__42_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Tactic.Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__43 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__43_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__44;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__45 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__45_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expectedType\?"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__46 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__46_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__47;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__46_value),LEAN_SCALAR_PTR_LITERAL(47, 72, 75, 114, 68, 52, 233, 214)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__48 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__48_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__49 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__49_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Elab.Term.withExpectedType"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__50 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__50_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__51;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withExpectedType"};
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
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 70, 226, 250, 127, 121, 118, 247)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__22_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
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
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__1;
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
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__3_value;
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
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 177, 45, 203, 60, 20, 245, 118)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__12_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabTail"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
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
lean_dec_ref(v___x_105_);
v___x_107_ = l_Lean_Elab_Command_getRef___redArg(v___y_101_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_109_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_a_108_);
lean_dec_ref(v___x_107_);
v___x_109_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_101_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_136_; 
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v___x_109_, 0);
lean_dec(v_unused_137_);
v___x_111_ = v___x_109_;
v_isShared_112_ = v_isSharedCheck_136_;
goto v_resetjp_110_;
}
else
{
lean_dec(v___x_109_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_136_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_quotContext_x3f_113_; lean_object* v___x_114_; 
v_quotContext_x3f_113_ = lean_ctor_get(v___y_101_, 5);
v___x_114_ = l_Lean_SourceInfo_fromRef(v_a_108_, v___x_104_);
lean_dec(v_a_108_);
if (lean_obj_tag(v_quotContext_x3f_113_) == 0)
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_102_);
lean_dec_ref(v___x_135_);
goto v___jp_115_;
}
else
{
goto v___jp_115_;
}
v___jp_115_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_116_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4));
v___x_117_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7));
v___x_118_ = lean_mk_syntax_ident(v_kind_100_);
v___x_119_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
lean_inc_n(v___x_114_, 2);
v___x_120_ = l_Lean_Syntax_node1(v___x_114_, v___x_119_, v_a_106_);
v___x_121_ = l_Lean_Syntax_node2(v___x_114_, v___x_117_, v___x_118_, v___x_120_);
v___x_122_ = l_Lean_Syntax_node2(v___x_114_, v___x_116_, v_attrKind_98_, v___x_121_);
if (lean_obj_tag(v_attrs_x3f_99_) == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_mk_empty_array_with_capacity(v___x_123_);
v___x_125_ = lean_array_push(v___x_124_, v___x_122_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_125_);
v___x_127_ = v___x_111_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
else
{
lean_object* v_val_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v_val_129_ = lean_ctor_get(v_attrs_x3f_99_, 0);
v___x_130_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_129_);
v___x_131_ = lean_array_push(v___x_130_, v___x_122_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_131_);
v___x_133_ = v___x_111_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec(v_a_108_);
lean_dec(v_a_106_);
lean_dec(v_kind_100_);
lean_dec(v_attrKind_98_);
v_a_138_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_109_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_109_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec(v_a_106_);
lean_dec(v_kind_100_);
lean_dec(v_attrKind_98_);
v_a_146_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_107_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_107_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec(v_kind_100_);
lean_dec(v_attrKind_98_);
v_a_154_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_105_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_105_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object* v_k_162_, lean_object* v_attrKind_163_, lean_object* v_attrs_x3f_164_, lean_object* v_kind_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_162_, v_attrKind_163_, v_attrs_x3f_164_, v_kind_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v_attrs_x3f_164_);
return v_res_169_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(lean_object* v_opts_170_, lean_object* v_opt_171_){
_start:
{
lean_object* v_name_172_; lean_object* v_defValue_173_; lean_object* v_map_174_; lean_object* v___x_175_; 
v_name_172_ = lean_ctor_get(v_opt_171_, 0);
v_defValue_173_ = lean_ctor_get(v_opt_171_, 1);
v_map_174_ = lean_ctor_get(v_opts_170_, 0);
v___x_175_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_174_, v_name_172_);
if (lean_obj_tag(v___x_175_) == 0)
{
uint8_t v___x_176_; 
v___x_176_ = lean_unbox(v_defValue_173_);
return v___x_176_;
}
else
{
lean_object* v_val_177_; 
v_val_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_177_);
lean_dec_ref(v___x_175_);
if (lean_obj_tag(v_val_177_) == 1)
{
uint8_t v_v_178_; 
v_v_178_ = lean_ctor_get_uint8(v_val_177_, 0);
lean_dec_ref(v_val_177_);
return v_v_178_;
}
else
{
uint8_t v___x_179_; 
lean_dec(v_val_177_);
v___x_179_ = lean_unbox(v_defValue_173_);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8___boxed(lean_object* v_opts_180_, lean_object* v_opt_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(v_opts_180_, v_opt_181_);
lean_dec_ref(v_opt_181_);
lean_dec_ref(v_opts_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_box(1);
v___x_185_ = l_Lean_MessageData_ofFormat(v___x_184_);
return v___x_185_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2));
v___x_190_ = l_Lean_MessageData_ofFormat(v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
return v_x_191_;
}
else
{
lean_object* v_head_193_; lean_object* v_tail_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_216_; 
v_head_193_ = lean_ctor_get(v_x_192_, 0);
v_tail_194_ = lean_ctor_get(v_x_192_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_x_192_);
if (v_isSharedCheck_216_ == 0)
{
v___x_196_ = v_x_192_;
v_isShared_197_ = v_isSharedCheck_216_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_tail_194_);
lean_inc(v_head_193_);
lean_dec(v_x_192_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_216_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v_before_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_214_; 
v_before_198_ = lean_ctor_get(v_head_193_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_head_193_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; 
v_unused_215_ = lean_ctor_get(v_head_193_, 1);
lean_dec(v_unused_215_);
v___x_200_ = v_head_193_;
v_isShared_201_ = v_isSharedCheck_214_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_before_198_);
lean_dec(v_head_193_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_214_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 7);
lean_ctor_set(v___x_200_, 1, v___x_202_);
lean_ctor_set(v___x_200_, 0, v_x_191_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_x_191_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_213_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3);
if (v_isShared_197_ == 0)
{
lean_ctor_set_tag(v___x_196_, 7);
lean_ctor_set(v___x_196_, 1, v___x_205_);
lean_ctor_set(v___x_196_, 0, v___x_204_);
v___x_207_ = v___x_196_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_205_);
v___x_207_ = v_reuseFailAlloc_212_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = l_Lean_MessageData_ofSyntax(v_before_198_);
v___x_209_ = l_Lean_indentD(v___x_208_);
v___x_210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_207_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v_x_191_ = v___x_210_;
v_x_192_ = v_tail_194_;
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
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1));
v___x_221_ = l_Lean_MessageData_ofFormat(v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(lean_object* v_msgData_222_, lean_object* v_macroStack_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___x_226_; lean_object* v_scopes_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_opts_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_226_ = lean_st_ref_get(v___y_224_);
v_scopes_227_ = lean_ctor_get(v___x_226_, 2);
lean_inc(v_scopes_227_);
lean_dec(v___x_226_);
v___x_228_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_229_ = l_List_head_x21___redArg(v___x_228_, v_scopes_227_);
lean_dec(v_scopes_227_);
v_opts_230_ = lean_ctor_get(v___x_229_, 1);
lean_inc_ref(v_opts_230_);
lean_dec(v___x_229_);
v___x_231_ = l_Lean_Elab_pp_macroStack;
v___x_232_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(v_opts_230_, v___x_231_);
lean_dec_ref(v_opts_230_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
lean_dec(v_macroStack_223_);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v_msgData_222_);
return v___x_233_;
}
else
{
if (lean_obj_tag(v_macroStack_223_) == 0)
{
lean_object* v___x_234_; 
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v_msgData_222_);
return v___x_234_;
}
else
{
lean_object* v_head_235_; lean_object* v_after_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_251_; 
v_head_235_ = lean_ctor_get(v_macroStack_223_, 0);
lean_inc(v_head_235_);
v_after_236_ = lean_ctor_get(v_head_235_, 1);
v_isSharedCheck_251_ = !lean_is_exclusive(v_head_235_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v_head_235_, 0);
lean_dec(v_unused_252_);
v___x_238_ = v_head_235_;
v_isShared_239_ = v_isSharedCheck_251_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_after_236_);
lean_dec(v_head_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_251_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 7);
lean_ctor_set(v___x_238_, 1, v___x_240_);
lean_ctor_set(v___x_238_, 0, v_msgData_222_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_msgData_222_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_250_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_msgData_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_243_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2);
v___x_244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = l_Lean_MessageData_ofSyntax(v_after_236_);
v___x_246_ = l_Lean_indentD(v___x_245_);
v_msgData_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_247_, 0, v___x_244_);
lean_ctor_set(v_msgData_247_, 1, v___x_246_);
v___x_248_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(v_msgData_247_, v_macroStack_223_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___boxed(lean_object* v_msgData_253_, lean_object* v_macroStack_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_msgData_253_, v_macroStack_254_, v___y_255_);
lean_dec(v___y_255_);
return v_res_257_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_258_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
lean_ctor_set(v___x_263_, 2, v___x_262_);
lean_ctor_set(v___x_263_, 3, v___x_262_);
lean_ctor_set(v___x_263_, 4, v___x_261_);
lean_ctor_set(v___x_263_, 5, v___x_261_);
lean_ctor_set(v___x_263_, 6, v___x_261_);
lean_ctor_set(v___x_263_, 7, v___x_261_);
lean_ctor_set(v___x_263_, 8, v___x_261_);
lean_ctor_set(v___x_263_, 9, v___x_261_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_unsigned_to_nat(32u);
v___x_265_ = lean_mk_empty_array_with_capacity(v___x_264_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_267_ = ((size_t)5ULL);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_unsigned_to_nat(32u);
v___x_270_ = lean_mk_empty_array_with_capacity(v___x_269_);
v___x_271_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3);
v___x_272_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_270_);
lean_ctor_set(v___x_272_, 2, v___x_268_);
lean_ctor_set(v___x_272_, 3, v___x_268_);
lean_ctor_set_usize(v___x_272_, 4, v___x_267_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_273_ = lean_box(1);
v___x_274_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4);
v___x_275_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
v___x_276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
lean_ctor_set(v___x_276_, 2, v___x_273_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(lean_object* v_msgData_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; lean_object* v_env_281_; lean_object* v___x_282_; lean_object* v_scopes_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_opts_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_280_ = lean_st_ref_get(v___y_278_);
v_env_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc_ref(v_env_281_);
lean_dec(v___x_280_);
v___x_282_ = lean_st_ref_get(v___y_278_);
v_scopes_283_ = lean_ctor_get(v___x_282_, 2);
lean_inc(v_scopes_283_);
lean_dec(v___x_282_);
v___x_284_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_285_ = l_List_head_x21___redArg(v___x_284_, v_scopes_283_);
lean_dec(v_scopes_283_);
v_opts_286_ = lean_ctor_get(v___x_285_, 1);
lean_inc_ref(v_opts_286_);
lean_dec(v___x_285_);
v___x_287_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2);
v___x_288_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5);
v___x_289_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_289_, 0, v_env_281_);
lean_ctor_set(v___x_289_, 1, v___x_287_);
lean_ctor_set(v___x_289_, 2, v___x_288_);
lean_ctor_set(v___x_289_, 3, v_opts_286_);
v___x_290_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_msgData_277_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___boxed(lean_object* v_msgData_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_292_, v___y_293_);
lean_dec(v___y_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(lean_object* v_msg_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Elab_Command_getRef___redArg(v___y_297_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v_macroStack_302_; lean_object* v___x_303_; lean_object* v_a_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_315_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref(v___x_300_);
v_macroStack_302_ = lean_ctor_get(v___y_297_, 4);
v___x_303_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_296_, v___y_298_);
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref(v___x_303_);
v___x_305_ = l_Lean_Elab_getBetterRef(v_a_301_, v_macroStack_302_);
lean_dec(v_a_301_);
lean_inc(v_macroStack_302_);
v___x_306_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_a_304_, v_macroStack_302_, v___y_298_);
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_315_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_315_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_315_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_305_);
lean_ctor_set(v___x_311_, 1, v_a_307_);
if (v_isShared_310_ == 0)
{
lean_ctor_set_tag(v___x_309_, 1);
lean_ctor_set(v___x_309_, 0, v___x_311_);
v___x_313_ = v___x_309_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref(v_msg_296_);
v_a_316_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_300_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_300_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg___boxed(lean_object* v_msg_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object* v_ref_329_, lean_object* v_msg_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Elab_Command_getRef___redArg(v___y_331_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v_fileName_336_; lean_object* v_fileMap_337_; lean_object* v_currRecDepth_338_; lean_object* v_cmdPos_339_; lean_object* v_macroStack_340_; lean_object* v_quotContext_x3f_341_; lean_object* v_currMacroScope_342_; lean_object* v_snap_x3f_343_; lean_object* v_cancelTk_x3f_344_; uint8_t v_suppressElabErrors_345_; lean_object* v_ref_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref(v___x_334_);
v_fileName_336_ = lean_ctor_get(v___y_331_, 0);
v_fileMap_337_ = lean_ctor_get(v___y_331_, 1);
v_currRecDepth_338_ = lean_ctor_get(v___y_331_, 2);
v_cmdPos_339_ = lean_ctor_get(v___y_331_, 3);
v_macroStack_340_ = lean_ctor_get(v___y_331_, 4);
v_quotContext_x3f_341_ = lean_ctor_get(v___y_331_, 5);
v_currMacroScope_342_ = lean_ctor_get(v___y_331_, 6);
v_snap_x3f_343_ = lean_ctor_get(v___y_331_, 8);
v_cancelTk_x3f_344_ = lean_ctor_get(v___y_331_, 9);
v_suppressElabErrors_345_ = lean_ctor_get_uint8(v___y_331_, sizeof(void*)*10);
v_ref_346_ = l_Lean_replaceRef(v_ref_329_, v_a_335_);
lean_dec(v_a_335_);
lean_inc(v_cancelTk_x3f_344_);
lean_inc(v_snap_x3f_343_);
lean_inc(v_currMacroScope_342_);
lean_inc(v_quotContext_x3f_341_);
lean_inc(v_macroStack_340_);
lean_inc(v_cmdPos_339_);
lean_inc(v_currRecDepth_338_);
lean_inc_ref(v_fileMap_337_);
lean_inc_ref(v_fileName_336_);
v___x_347_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_347_, 0, v_fileName_336_);
lean_ctor_set(v___x_347_, 1, v_fileMap_337_);
lean_ctor_set(v___x_347_, 2, v_currRecDepth_338_);
lean_ctor_set(v___x_347_, 3, v_cmdPos_339_);
lean_ctor_set(v___x_347_, 4, v_macroStack_340_);
lean_ctor_set(v___x_347_, 5, v_quotContext_x3f_341_);
lean_ctor_set(v___x_347_, 6, v_currMacroScope_342_);
lean_ctor_set(v___x_347_, 7, v_ref_346_);
lean_ctor_set(v___x_347_, 8, v_snap_x3f_343_);
lean_ctor_set(v___x_347_, 9, v_cancelTk_x3f_344_);
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*10, v_suppressElabErrors_345_);
v___x_348_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_330_, v___x_347_, v___y_332_);
lean_dec_ref(v___x_347_);
return v___x_348_;
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec_ref(v_msg_330_);
v_a_349_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_334_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_334_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object* v_ref_357_, lean_object* v_msg_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_357_, v_msg_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v_ref_357_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object* v_k_366_, lean_object* v_as_367_, size_t v_sz_368_, size_t v_i_369_, lean_object* v_b_370_){
_start:
{
uint8_t v___x_371_; 
v___x_371_ = lean_usize_dec_lt(v_i_369_, v_sz_368_);
if (v___x_371_ == 0)
{
lean_dec(v_k_366_);
lean_inc_ref(v_b_370_);
return v_b_370_;
}
else
{
lean_object* v___x_372_; lean_object* v_a_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_372_ = lean_box(0);
v_a_373_ = lean_array_uget_borrowed(v_as_367_, v_i_369_);
lean_inc(v_a_373_);
v___x_374_ = l_Lean_Syntax_getKind(v_a_373_);
lean_inc(v_k_366_);
v___x_375_ = l_Lean_Elab_Command_checkRuleKind(v___x_374_, v_k_366_);
lean_dec(v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; size_t v___x_377_; size_t v___x_378_; 
v___x_376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_add(v_i_369_, v___x_377_);
v_i_369_ = v___x_378_;
v_b_370_ = v___x_376_;
goto _start;
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec(v_k_366_);
lean_inc(v_a_373_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v_a_373_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___x_372_);
return v___x_382_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object* v_k_383_, lean_object* v_as_384_, lean_object* v_sz_385_, lean_object* v_i_386_, lean_object* v_b_387_){
_start:
{
size_t v_sz_boxed_388_; size_t v_i_boxed_389_; lean_object* v_res_390_; 
v_sz_boxed_388_ = lean_unbox_usize(v_sz_385_);
lean_dec(v_sz_385_);
v_i_boxed_389_ = lean_unbox_usize(v_i_386_);
lean_dec(v_i_386_);
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_383_, v_as_384_, v_sz_boxed_388_, v_i_boxed_389_, v_b_387_);
lean_dec_ref(v_b_387_);
lean_dec_ref(v_as_384_);
return v_res_390_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0));
v___x_393_ = l_Lean_stringToMessageData(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2));
v___x_396_ = l_Lean_stringToMessageData(v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7(void){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Array_mkArray0(lean_box(0));
return v___x_404_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11));
v___x_411_ = l_Lean_stringToMessageData(v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(lean_object* v_k_412_, size_t v_sz_413_, size_t v_i_414_, lean_object* v_bs_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
uint8_t v___x_419_; 
v___x_419_ = lean_usize_dec_lt(v_i_414_, v_sz_413_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
lean_dec(v_k_412_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v_bs_415_);
return v___x_420_;
}
else
{
lean_object* v_v_421_; lean_object* v___x_422_; lean_object* v_bs_x27_423_; lean_object* v_a_425_; lean_object* v___y_431_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___x_450_; uint8_t v___x_451_; 
v_v_421_ = lean_array_uget(v_bs_415_, v_i_414_);
v___x_422_ = lean_unsigned_to_nat(0u);
v_bs_x27_423_ = lean_array_uset(v_bs_415_, v_i_414_, v___x_422_);
v___x_450_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5));
lean_inc(v_v_421_);
v___x_451_ = l_Lean_Syntax_isOfKind(v_v_421_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
lean_dec(v_v_421_);
v___x_452_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
v___y_431_ = v___x_452_;
goto v___jp_430_;
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = l_Lean_Syntax_getArg(v_v_421_, v___x_453_);
lean_inc(v___x_454_);
v___x_455_ = l_Lean_Syntax_matchesNull(v___x_454_, v___x_453_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
lean_dec(v___x_454_);
lean_dec(v_v_421_);
v___x_456_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
v___y_431_ = v___x_456_;
goto v___jp_430_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_pat_475_; lean_object* v___y_477_; lean_object* v___y_478_; uint8_t v___x_530_; 
v___x_457_ = l_Lean_Syntax_getArg(v___x_454_, v___x_422_);
lean_dec(v___x_454_);
v___x_458_ = lean_unsigned_to_nat(3u);
v___x_459_ = l_Lean_Syntax_getArg(v_v_421_, v___x_458_);
v___x_473_ = l_Lean_Syntax_getArgs(v___x_457_);
lean_dec(v___x_457_);
v___x_474_ = lean_box(0);
v_pat_475_ = lean_array_get(v___x_474_, v___x_473_, v___x_422_);
v___x_530_ = l_Lean_Syntax_isQuot(v_pat_475_);
if (v___x_530_ == 0)
{
if (v___x_455_ == 0)
{
v___y_477_ = v___y_416_;
v___y_478_ = v___y_417_;
goto v___jp_476_;
}
else
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
if (lean_obj_tag(v___x_531_) == 0)
{
lean_dec_ref(v___x_531_);
v___y_477_ = v___y_416_;
v___y_478_ = v___y_417_;
goto v___jp_476_;
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_pat_475_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_459_);
lean_dec_ref(v_bs_x27_423_);
lean_dec(v_v_421_);
lean_dec(v_k_412_);
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
else
{
v___y_477_ = v___y_416_;
v___y_478_ = v___y_417_;
goto v___jp_476_;
}
v___jp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc_n(v___y_462_, 4);
v___x_464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_464_, 0, v___y_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_466_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
v___x_467_ = l_Array_append___redArg(v___x_466_, v___y_461_);
lean_dec_ref(v___y_461_);
v___x_468_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_468_, 0, v___y_462_);
lean_ctor_set(v___x_468_, 1, v___x_465_);
lean_ctor_set(v___x_468_, 2, v___x_467_);
v___x_469_ = l_Lean_Syntax_node1(v___y_462_, v___x_465_, v___x_468_);
v___x_470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_471_, 0, v___y_462_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = l_Lean_Syntax_node4(v___y_462_, v___x_450_, v___x_464_, v___x_469_, v___x_471_, v___x_459_);
v_a_425_ = v___x_472_;
goto v___jp_424_;
}
v___jp_476_:
{
lean_object* v_quoted_479_; lean_object* v_k_x27_480_; uint8_t v___x_481_; 
lean_inc(v_pat_475_);
v_quoted_479_ = l_Lean_Syntax_getQuotContent(v_pat_475_);
lean_inc(v_quoted_479_);
v_k_x27_480_ = l_Lean_Syntax_getKind(v_quoted_479_);
lean_inc(v_k_412_);
v___x_481_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_480_, v_k_412_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10));
v___x_483_ = lean_name_eq(v_k_x27_480_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec(v_quoted_479_);
lean_dec(v_pat_475_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_459_);
v___x_484_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12);
v___x_485_ = l_Lean_MessageData_ofName(v_k_x27_480_);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_421_, v___x_488_, v___y_477_, v___y_478_);
lean_dec(v_v_421_);
v___y_431_ = v___x_489_;
goto v___jp_430_;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; size_t v_sz_492_; size_t v___x_493_; lean_object* v___x_494_; lean_object* v_fst_495_; 
lean_dec(v_k_x27_480_);
v___x_490_ = l_Lean_Syntax_getArgs(v_quoted_479_);
lean_dec(v_quoted_479_);
v___x_491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
v_sz_492_ = lean_array_size(v___x_490_);
v___x_493_ = ((size_t)0ULL);
lean_inc(v_k_412_);
v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_412_, v___x_490_, v_sz_492_, v___x_493_, v___x_491_);
lean_dec_ref(v___x_490_);
v_fst_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_fst_495_);
lean_dec_ref(v___x_494_);
if (lean_obj_tag(v_fst_495_) == 0)
{
lean_dec(v_pat_475_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_459_);
v___y_442_ = v___y_478_;
v___y_443_ = v___y_477_;
goto v___jp_441_;
}
else
{
lean_object* v_val_496_; 
v_val_496_ = lean_ctor_get(v_fst_495_, 0);
lean_inc(v_val_496_);
lean_dec_ref(v_fst_495_);
if (lean_obj_tag(v_val_496_) == 0)
{
lean_dec(v_pat_475_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_459_);
v___y_442_ = v___y_478_;
v___y_443_ = v___y_477_;
goto v___jp_441_;
}
else
{
lean_object* v_val_497_; lean_object* v___x_498_; 
lean_dec(v_v_421_);
v_val_497_ = lean_ctor_get(v_val_496_, 0);
lean_inc(v_val_497_);
lean_dec_ref(v_val_496_);
v___x_498_ = l_Lean_Elab_Command_getRef___redArg(v___y_477_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_500_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref(v___x_498_);
v___x_500_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_477_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_quotContext_x3f_501_; lean_object* v_pat_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec_ref(v___x_500_);
v_quotContext_x3f_501_ = lean_ctor_get(v___y_477_, 5);
v_pat_502_ = l_Lean_Syntax_setArg(v_pat_475_, v___x_453_, v_val_497_);
v___x_503_ = lean_array_set(v___x_473_, v___x_422_, v_pat_502_);
v___x_504_ = l_Lean_SourceInfo_fromRef(v_a_499_, v___x_481_);
lean_dec(v_a_499_);
if (lean_obj_tag(v_quotContext_x3f_501_) == 0)
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_478_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_dec_ref(v___x_505_);
v___y_461_ = v___x_503_;
v___y_462_ = v___x_504_;
goto v___jp_460_;
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec(v___x_504_);
lean_dec_ref(v___x_503_);
lean_dec(v___x_459_);
lean_dec_ref(v_bs_x27_423_);
lean_dec(v_k_412_);
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
v___y_461_ = v___x_503_;
v___y_462_ = v___x_504_;
goto v___jp_460_;
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec(v_a_499_);
lean_dec(v_val_497_);
lean_dec(v_pat_475_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_459_);
lean_dec_ref(v_bs_x27_423_);
lean_dec(v_k_412_);
v_a_514_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_500_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_500_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_val_497_);
lean_dec(v_pat_475_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_459_);
lean_dec_ref(v_bs_x27_423_);
lean_dec(v_k_412_);
v_a_522_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_498_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_498_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_x27_480_);
lean_dec(v_quoted_479_);
lean_dec(v_pat_475_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_459_);
v_a_425_ = v_v_421_;
goto v___jp_424_;
}
}
}
}
v___jp_424_:
{
size_t v___x_426_; size_t v___x_427_; lean_object* v___x_428_; 
v___x_426_ = ((size_t)1ULL);
v___x_427_ = lean_usize_add(v_i_414_, v___x_426_);
v___x_428_ = lean_array_uset(v_bs_x27_423_, v_i_414_, v_a_425_);
v_i_414_ = v___x_427_;
v_bs_415_ = v___x_428_;
goto _start;
}
v___jp_430_:
{
if (lean_obj_tag(v___y_431_) == 0)
{
lean_object* v_a_432_; 
v_a_432_ = lean_ctor_get(v___y_431_, 0);
lean_inc(v_a_432_);
lean_dec_ref(v___y_431_);
v_a_425_ = v_a_432_;
goto v___jp_424_;
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec_ref(v_bs_x27_423_);
lean_dec(v_k_412_);
v_a_433_ = lean_ctor_get(v___y_431_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___y_431_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___y_431_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___y_431_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
v___jp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_444_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1);
lean_inc(v_k_412_);
v___x_445_ = l_Lean_MessageData_ofName(v_k_412_);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_421_, v___x_448_, v___y_443_, v___y_442_);
lean_dec(v_v_421_);
v___y_431_ = v___x_449_;
goto v___jp_430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___boxed(lean_object* v_k_540_, lean_object* v_sz_541_, lean_object* v_i_542_, lean_object* v_bs_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
size_t v_sz_boxed_547_; size_t v_i_boxed_548_; lean_object* v_res_549_; 
v_sz_boxed_547_ = lean_unbox_usize(v_sz_541_);
lean_dec(v_sz_541_);
v_i_boxed_548_ = lean_unbox_usize(v_i_542_);
lean_dec(v_i_542_);
v_res_549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_540_, v_sz_boxed_547_, v_i_boxed_548_, v_bs_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_549_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__4));
v___x_556_ = l_String_toRawSubstring_x27(v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__8));
v___x_562_ = l_String_toRawSubstring_x27(v___x_561_);
return v___x_562_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_569_ = l_String_toRawSubstring_x27(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_582_ = l_String_toRawSubstring_x27(v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__34(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___x_597_ = l_String_toRawSubstring_x27(v___x_596_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__36));
v___x_601_ = l_String_toRawSubstring_x27(v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__41(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
v___x_606_ = l_String_toRawSubstring_x27(v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__44(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__43));
v___x_611_ = l_String_toRawSubstring_x27(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__47(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__46));
v___x_615_ = l_String_toRawSubstring_x27(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__50));
v___x_621_ = l_String_toRawSubstring_x27(v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__57));
v___x_631_ = l_Lean_stringToMessageData(v___x_630_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__59));
v___x_634_ = l_Lean_stringToMessageData(v___x_633_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__71));
v___x_652_ = l_Lean_stringToMessageData(v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__75));
v___x_658_ = l_Lean_stringToMessageData(v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object* v_doc_x3f_659_, lean_object* v_attrs_x3f_660_, lean_object* v_attrKind_661_, lean_object* v_k_662_, lean_object* v_cat_x3f_663_, lean_object* v_expty_x3f_664_, lean_object* v_alts_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
size_t v_sz_669_; size_t v___x_670_; lean_object* v___x_671_; 
v_sz_669_ = lean_array_size(v_alts_665_);
v___x_670_ = ((size_t)0ULL);
lean_inc(v_k_662_);
v___x_671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_662_, v_sz_669_, v___x_670_, v_alts_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_1682_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_1682_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_1682_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v_a_800_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v_a_914_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v_a_1052_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v_a_1165_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v_a_1317_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v_a_1452_; lean_object* v___y_1463_; uint8_t v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v_catName_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; 
if (lean_obj_tag(v_cat_x3f_663_) == 1)
{
lean_object* v_val_1669_; lean_object* v___x_1670_; 
v_val_1669_ = lean_ctor_get(v_cat_x3f_663_, 0);
v___x_1670_ = l_Lean_TSyntax_getId(v_val_1669_);
v_catName_1496_ = v___x_1670_;
v___y_1497_ = v_a_666_;
v___y_1498_ = v_a_667_;
goto v___jp_1495_;
}
else
{
if (lean_obj_tag(v_expty_x3f_664_) == 1)
{
lean_object* v___x_1671_; 
v___x_1671_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v_catName_1496_ = v___x_1671_;
v___y_1497_ = v_a_666_;
v___y_1498_ = v_a_667_;
goto v___jp_1495_;
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_del_object(v___x_674_);
lean_dec(v_a_672_);
lean_dec(v_expty_x3f_664_);
lean_dec(v_k_662_);
lean_dec(v_attrKind_661_);
lean_dec(v_doc_x3f_659_);
v___x_1672_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__76, &l_Lean_Elab_Command_elabElabRulesAux___closed__76_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76);
v___x_1673_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_1672_, v_a_666_, v_a_667_);
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
v___jp_676_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
lean_inc_ref_n(v___y_680_, 4);
v___x_689_ = l_Array_append___redArg(v___y_680_, v___y_688_);
lean_dec_ref(v___y_688_);
lean_inc_n(v___y_677_, 10);
lean_inc_n(v___y_686_, 35);
v___x_690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_690_, 0, v___y_686_);
lean_ctor_set(v___x_690_, 1, v___y_677_);
lean_ctor_set(v___x_690_, 2, v___x_689_);
v___x_691_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_692_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_693_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_687_, 11);
v___x_694_ = l_Lean_Name_mkStr4(v___y_687_, v___x_691_, v___x_692_, v___x_693_);
v___x_695_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_696_, 0, v___y_686_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_698_ = l_Lean_Syntax_SepArray_ofElems(v___x_697_, v___y_684_);
lean_dec_ref(v___y_684_);
v___x_699_ = l_Array_append___redArg(v___y_680_, v___x_698_);
lean_dec_ref(v___x_698_);
v___x_700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_700_, 0, v___y_686_);
lean_ctor_set(v___x_700_, 1, v___y_677_);
lean_ctor_set(v___x_700_, 2, v___x_699_);
v___x_701_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_702_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_702_, 0, v___y_686_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = l_Lean_Syntax_node3(v___y_686_, v___x_694_, v___x_696_, v___x_700_, v___x_702_);
v___x_704_ = l_Lean_Syntax_node1(v___y_686_, v___y_677_, v___x_703_);
lean_inc_ref(v___y_678_);
v___x_705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_705_, 0, v___y_686_);
lean_ctor_set(v___x_705_, 1, v___y_678_);
v___x_706_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_707_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_685_, 3);
lean_inc_n(v___y_682_, 3);
v___x_708_ = l_Lean_addMacroScope(v___y_682_, v___x_707_, v___y_685_);
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_710_, 0, v___y_686_);
lean_ctor_set(v___x_710_, 1, v___x_706_);
lean_ctor_set(v___x_710_, 2, v___x_708_);
lean_ctor_set(v___x_710_, 3, v___x_709_);
v___x_711_ = lean_mk_syntax_ident(v_k_662_);
v___x_712_ = l_Lean_Syntax_node2(v___y_686_, v___y_677_, v___x_710_, v___x_711_);
v___x_713_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_714_, 0, v___y_686_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_716_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
lean_inc_ref_n(v___y_683_, 2);
v___x_717_ = l_Lean_Name_mkStr4(v___y_687_, v___y_683_, v___x_692_, v___x_716_);
lean_inc(v___x_717_);
v___x_718_ = l_Lean_addMacroScope(v___y_682_, v___x_717_, v___y_685_);
v___x_719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_709_);
v___x_720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___x_709_);
v___x_721_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_721_, 0, v___y_686_);
lean_ctor_set(v___x_721_, 1, v___x_715_);
lean_ctor_set(v___x_721_, 2, v___x_718_);
lean_ctor_set(v___x_721_, 3, v___x_720_);
v___x_722_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_723_, 0, v___y_686_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_725_ = l_Lean_Name_mkStr4(v___y_687_, v___x_691_, v___x_692_, v___x_724_);
v___x_726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_726_, 0, v___y_686_);
lean_ctor_set(v___x_726_, 1, v___x_724_);
v___x_727_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_728_ = l_Lean_Name_mkStr4(v___y_687_, v___x_691_, v___x_692_, v___x_727_);
v___x_729_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
v___x_730_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
v___x_731_ = l_Lean_addMacroScope(v___y_682_, v___x_730_, v___y_685_);
v___x_732_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_732_, 0, v___y_686_);
lean_ctor_set(v___x_732_, 1, v___x_729_);
lean_ctor_set(v___x_732_, 2, v___x_731_);
lean_ctor_set(v___x_732_, 3, v___x_709_);
v___x_733_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_734_ = l_Lean_Name_mkStr4(v___y_687_, v___x_691_, v___x_692_, v___x_733_);
v___x_735_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_736_, 0, v___y_686_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_Lean_Syntax_node1(v___y_686_, v___x_734_, v___x_736_);
lean_inc(v___x_737_);
lean_inc_ref(v___x_732_);
v___x_738_ = l_Lean_Syntax_node2(v___y_686_, v___y_677_, v___x_732_, v___x_737_);
v___x_739_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_739_, 0, v___y_686_);
lean_ctor_set(v___x_739_, 1, v___y_677_);
lean_ctor_set(v___x_739_, 2, v___y_680_);
v___x_740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_741_, 0, v___y_686_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_743_ = l_Lean_Name_mkStr4(v___y_687_, v___x_691_, v___x_692_, v___x_742_);
v___x_744_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_744_, 0, v___y_686_);
lean_ctor_set(v___x_744_, 1, v___x_742_);
v___x_745_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_746_ = l_Lean_Name_mkStr4(v___y_687_, v___x_691_, v___x_692_, v___x_745_);
lean_inc_ref_n(v___x_739_, 3);
v___x_747_ = l_Lean_Syntax_node2(v___y_686_, v___x_746_, v___x_739_, v___x_732_);
v___x_748_ = l_Lean_Syntax_node1(v___y_686_, v___y_677_, v___x_747_);
v___x_749_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_750_, 0, v___y_686_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_752_ = l_Lean_Name_mkStr4(v___y_687_, v___x_691_, v___x_692_, v___x_751_);
v___x_753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_754_ = l_Lean_Name_mkStr4(v___y_687_, v___x_691_, v___x_692_, v___x_753_);
v___x_755_ = l_Array_append___redArg(v___y_680_, v_a_672_);
lean_dec(v_a_672_);
v___x_756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_757_, 0, v___y_686_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l_Lean_Syntax_node1(v___y_686_, v___y_677_, v___x_737_);
v___x_759_ = l_Lean_Syntax_node1(v___y_686_, v___y_677_, v___x_758_);
v___x_760_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_761_ = l_Lean_Name_mkStr4(v___y_687_, v___x_691_, v___x_692_, v___x_760_);
v___x_762_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_763_, 0, v___y_686_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_765_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_766_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_767_ = l_Lean_addMacroScope(v___y_682_, v___x_766_, v___y_685_);
v___x_768_ = l_Lean_Name_mkStr3(v___y_687_, v___y_683_, v___x_764_);
v___x_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v___x_709_);
v___x_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_709_);
v___x_771_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_771_, 0, v___y_686_);
lean_ctor_set(v___x_771_, 1, v___x_765_);
lean_ctor_set(v___x_771_, 2, v___x_767_);
lean_ctor_set(v___x_771_, 3, v___x_770_);
v___x_772_ = l_Lean_Syntax_node2(v___y_686_, v___x_761_, v___x_763_, v___x_771_);
lean_inc_ref(v___x_741_);
v___x_773_ = l_Lean_Syntax_node4(v___y_686_, v___x_754_, v___x_757_, v___x_759_, v___x_741_, v___x_772_);
v___x_774_ = lean_array_push(v___x_755_, v___x_773_);
v___x_775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_775_, 0, v___y_686_);
lean_ctor_set(v___x_775_, 1, v___y_677_);
lean_ctor_set(v___x_775_, 2, v___x_774_);
v___x_776_ = l_Lean_Syntax_node1(v___y_686_, v___x_752_, v___x_775_);
v___x_777_ = l_Lean_Syntax_node6(v___y_686_, v___x_743_, v___x_744_, v___x_739_, v___x_739_, v___x_748_, v___x_750_, v___x_776_);
v___x_778_ = l_Lean_Syntax_node4(v___y_686_, v___x_728_, v___x_738_, v___x_739_, v___x_741_, v___x_777_);
v___x_779_ = l_Lean_Syntax_node2(v___y_686_, v___x_725_, v___x_726_, v___x_778_);
v___x_780_ = lean_unsigned_to_nat(9u);
v___x_781_ = lean_mk_empty_array_with_capacity(v___x_780_);
v___x_782_ = lean_array_push(v___x_781_, v___x_690_);
v___x_783_ = lean_array_push(v___x_782_, v___x_704_);
v___x_784_ = lean_array_push(v___x_783_, v___y_679_);
v___x_785_ = lean_array_push(v___x_784_, v___x_705_);
v___x_786_ = lean_array_push(v___x_785_, v___x_712_);
v___x_787_ = lean_array_push(v___x_786_, v___x_714_);
v___x_788_ = lean_array_push(v___x_787_, v___x_721_);
v___x_789_ = lean_array_push(v___x_788_, v___x_723_);
v___x_790_ = lean_array_push(v___x_789_, v___x_779_);
lean_inc(v___y_681_);
v___x_791_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_791_, 0, v___y_686_);
lean_ctor_set(v___x_791_, 1, v___y_681_);
lean_ctor_set(v___x_791_, 2, v___x_790_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_791_);
v___x_793_ = v___x_674_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
v___jp_795_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_801_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_802_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_803_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_804_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_805_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_806_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_659_) == 1)
{
lean_object* v_val_807_; lean_object* v___x_808_; 
v_val_807_ = lean_ctor_get(v_doc_x3f_659_, 0);
lean_inc(v_val_807_);
lean_dec_ref(v_doc_x3f_659_);
v___x_808_ = l_Array_mkArray1___redArg(v_val_807_);
v___y_677_ = v___x_805_;
v___y_678_ = v___x_803_;
v___y_679_ = v___y_796_;
v___y_680_ = v___x_806_;
v___y_681_ = v___x_804_;
v___y_682_ = v_a_800_;
v___y_683_ = v___x_802_;
v___y_684_ = v___y_797_;
v___y_685_ = v___y_799_;
v___y_686_ = v___y_798_;
v___y_687_ = v___x_801_;
v___y_688_ = v___x_808_;
goto v___jp_676_;
}
else
{
lean_object* v___x_809_; 
lean_dec(v_doc_x3f_659_);
v___x_809_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_677_ = v___x_805_;
v___y_678_ = v___x_803_;
v___y_679_ = v___y_796_;
v___y_680_ = v___x_806_;
v___y_681_ = v___x_804_;
v___y_682_ = v_a_800_;
v___y_683_ = v___x_802_;
v___y_684_ = v___y_797_;
v___y_685_ = v___y_799_;
v___y_686_ = v___y_798_;
v___y_687_ = v___x_801_;
v___y_688_ = v___x_809_;
goto v___jp_676_;
}
}
v___jp_810_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_inc_ref_n(v___y_816_, 3);
v___x_824_ = l_Array_append___redArg(v___y_816_, v___y_823_);
lean_dec_ref(v___y_823_);
lean_inc_n(v___y_820_, 7);
lean_inc_n(v___y_811_, 26);
v___x_825_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_825_, 0, v___y_811_);
lean_ctor_set(v___x_825_, 1, v___y_820_);
lean_ctor_set(v___x_825_, 2, v___x_824_);
v___x_826_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_827_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_828_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_819_, 8);
v___x_829_ = l_Lean_Name_mkStr4(v___y_819_, v___x_826_, v___x_827_, v___x_828_);
v___x_830_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_831_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_831_, 0, v___y_811_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_833_ = l_Lean_Syntax_SepArray_ofElems(v___x_832_, v___y_822_);
lean_dec_ref(v___y_822_);
v___x_834_ = l_Array_append___redArg(v___y_816_, v___x_833_);
lean_dec_ref(v___x_833_);
v___x_835_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_835_, 0, v___y_811_);
lean_ctor_set(v___x_835_, 1, v___y_820_);
lean_ctor_set(v___x_835_, 2, v___x_834_);
v___x_836_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_837_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_837_, 0, v___y_811_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_Syntax_node3(v___y_811_, v___x_829_, v___x_831_, v___x_835_, v___x_837_);
v___x_839_ = l_Lean_Syntax_node1(v___y_811_, v___y_820_, v___x_838_);
lean_inc_ref(v___y_815_);
v___x_840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_840_, 0, v___y_811_);
lean_ctor_set(v___x_840_, 1, v___y_815_);
v___x_841_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_842_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_821_, 2);
lean_inc_n(v___y_814_, 2);
v___x_843_ = l_Lean_addMacroScope(v___y_814_, v___x_842_, v___y_821_);
v___x_844_ = lean_box(0);
v___x_845_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_845_, 0, v___y_811_);
lean_ctor_set(v___x_845_, 1, v___x_841_);
lean_ctor_set(v___x_845_, 2, v___x_843_);
lean_ctor_set(v___x_845_, 3, v___x_844_);
v___x_846_ = lean_mk_syntax_ident(v_k_662_);
v___x_847_ = l_Lean_Syntax_node2(v___y_811_, v___y_820_, v___x_845_, v___x_846_);
v___x_848_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_849_, 0, v___y_811_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__34, &l_Lean_Elab_Command_elabElabRulesAux___closed__34_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__34);
v___x_851_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
lean_inc_ref(v___y_812_);
lean_inc_ref_n(v___y_817_, 2);
v___x_852_ = l_Lean_Name_mkStr4(v___y_819_, v___y_817_, v___y_812_, v___x_851_);
lean_inc(v___x_852_);
v___x_853_ = l_Lean_addMacroScope(v___y_814_, v___x_852_, v___y_821_);
v___x_854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_852_);
lean_ctor_set(v___x_854_, 1, v___x_844_);
v___x_855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v___x_844_);
v___x_856_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_856_, 0, v___y_811_);
lean_ctor_set(v___x_856_, 1, v___x_850_);
lean_ctor_set(v___x_856_, 2, v___x_853_);
lean_ctor_set(v___x_856_, 3, v___x_855_);
v___x_857_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_858_, 0, v___y_811_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_860_ = l_Lean_Name_mkStr4(v___y_819_, v___x_826_, v___x_827_, v___x_859_);
v___x_861_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_861_, 0, v___y_811_);
lean_ctor_set(v___x_861_, 1, v___x_859_);
v___x_862_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_863_ = l_Lean_Name_mkStr4(v___y_819_, v___x_826_, v___x_827_, v___x_862_);
v___x_864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_865_ = l_Lean_Name_mkStr4(v___y_819_, v___x_826_, v___x_827_, v___x_864_);
v___x_866_ = l_Array_append___redArg(v___y_816_, v_a_672_);
lean_dec(v_a_672_);
v___x_867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_868_, 0, v___y_811_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_870_ = l_Lean_Name_mkStr4(v___y_819_, v___x_826_, v___x_827_, v___x_869_);
v___x_871_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_872_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_872_, 0, v___y_811_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = l_Lean_Syntax_node1(v___y_811_, v___x_870_, v___x_872_);
v___x_874_ = l_Lean_Syntax_node1(v___y_811_, v___y_820_, v___x_873_);
v___x_875_ = l_Lean_Syntax_node1(v___y_811_, v___y_820_, v___x_874_);
v___x_876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_877_, 0, v___y_811_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_879_ = l_Lean_Name_mkStr4(v___y_819_, v___x_826_, v___x_827_, v___x_878_);
v___x_880_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_881_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_881_, 0, v___y_811_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_883_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_884_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_885_ = l_Lean_addMacroScope(v___y_814_, v___x_884_, v___y_821_);
v___x_886_ = l_Lean_Name_mkStr3(v___y_819_, v___y_817_, v___x_882_);
v___x_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v___x_844_);
v___x_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___x_844_);
v___x_889_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_889_, 0, v___y_811_);
lean_ctor_set(v___x_889_, 1, v___x_883_);
lean_ctor_set(v___x_889_, 2, v___x_885_);
lean_ctor_set(v___x_889_, 3, v___x_888_);
v___x_890_ = l_Lean_Syntax_node2(v___y_811_, v___x_879_, v___x_881_, v___x_889_);
v___x_891_ = l_Lean_Syntax_node4(v___y_811_, v___x_865_, v___x_868_, v___x_875_, v___x_877_, v___x_890_);
v___x_892_ = lean_array_push(v___x_866_, v___x_891_);
v___x_893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_893_, 0, v___y_811_);
lean_ctor_set(v___x_893_, 1, v___y_820_);
lean_ctor_set(v___x_893_, 2, v___x_892_);
v___x_894_ = l_Lean_Syntax_node1(v___y_811_, v___x_863_, v___x_893_);
v___x_895_ = l_Lean_Syntax_node2(v___y_811_, v___x_860_, v___x_861_, v___x_894_);
v___x_896_ = lean_unsigned_to_nat(9u);
v___x_897_ = lean_mk_empty_array_with_capacity(v___x_896_);
v___x_898_ = lean_array_push(v___x_897_, v___x_825_);
v___x_899_ = lean_array_push(v___x_898_, v___x_839_);
v___x_900_ = lean_array_push(v___x_899_, v___y_813_);
v___x_901_ = lean_array_push(v___x_900_, v___x_840_);
v___x_902_ = lean_array_push(v___x_901_, v___x_847_);
v___x_903_ = lean_array_push(v___x_902_, v___x_849_);
v___x_904_ = lean_array_push(v___x_903_, v___x_856_);
v___x_905_ = lean_array_push(v___x_904_, v___x_858_);
v___x_906_ = lean_array_push(v___x_905_, v___x_895_);
lean_inc(v___y_818_);
v___x_907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_907_, 0, v___y_811_);
lean_ctor_set(v___x_907_, 1, v___y_818_);
lean_ctor_set(v___x_907_, 2, v___x_906_);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
return v___x_908_;
}
v___jp_909_:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_915_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_916_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_917_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_918_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_919_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_920_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_921_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_659_) == 1)
{
lean_object* v_val_922_; lean_object* v___x_923_; 
v_val_922_ = lean_ctor_get(v_doc_x3f_659_, 0);
lean_inc(v_val_922_);
lean_dec_ref(v_doc_x3f_659_);
v___x_923_ = l_Array_mkArray1___redArg(v_val_922_);
v___y_811_ = v___y_910_;
v___y_812_ = v___x_917_;
v___y_813_ = v___y_911_;
v___y_814_ = v_a_914_;
v___y_815_ = v___x_918_;
v___y_816_ = v___x_921_;
v___y_817_ = v___x_916_;
v___y_818_ = v___x_919_;
v___y_819_ = v___x_915_;
v___y_820_ = v___x_920_;
v___y_821_ = v___y_912_;
v___y_822_ = v___y_913_;
v___y_823_ = v___x_923_;
goto v___jp_810_;
}
else
{
lean_object* v___x_924_; 
lean_dec(v_doc_x3f_659_);
v___x_924_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_811_ = v___y_910_;
v___y_812_ = v___x_917_;
v___y_813_ = v___y_911_;
v___y_814_ = v_a_914_;
v___y_815_ = v___x_918_;
v___y_816_ = v___x_921_;
v___y_817_ = v___x_916_;
v___y_818_ = v___x_919_;
v___y_819_ = v___x_915_;
v___y_820_ = v___x_920_;
v___y_821_ = v___y_912_;
v___y_822_ = v___y_913_;
v___y_823_ = v___x_924_;
goto v___jp_810_;
}
}
v___jp_925_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_inc_ref_n(v___y_934_, 4);
v___x_938_ = l_Array_append___redArg(v___y_934_, v___y_937_);
lean_dec_ref(v___y_937_);
lean_inc_n(v___y_929_, 10);
lean_inc_n(v___y_930_, 36);
v___x_939_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_939_, 0, v___y_930_);
lean_ctor_set(v___x_939_, 1, v___y_929_);
lean_ctor_set(v___x_939_, 2, v___x_938_);
v___x_940_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_941_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_942_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_936_, 11);
v___x_943_ = l_Lean_Name_mkStr4(v___y_936_, v___x_940_, v___x_941_, v___x_942_);
v___x_944_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_945_, 0, v___y_930_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_947_ = l_Lean_Syntax_SepArray_ofElems(v___x_946_, v___y_926_);
lean_dec_ref(v___y_926_);
v___x_948_ = l_Array_append___redArg(v___y_934_, v___x_947_);
lean_dec_ref(v___x_947_);
v___x_949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_949_, 0, v___y_930_);
lean_ctor_set(v___x_949_, 1, v___y_929_);
lean_ctor_set(v___x_949_, 2, v___x_948_);
v___x_950_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_951_, 0, v___y_930_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = l_Lean_Syntax_node3(v___y_930_, v___x_943_, v___x_945_, v___x_949_, v___x_951_);
v___x_953_ = l_Lean_Syntax_node1(v___y_930_, v___y_929_, v___x_952_);
lean_inc_ref(v___y_933_);
v___x_954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_954_, 0, v___y_930_);
lean_ctor_set(v___x_954_, 1, v___y_933_);
v___x_955_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_956_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_927_, 4);
lean_inc_n(v___y_928_, 4);
v___x_957_ = l_Lean_addMacroScope(v___y_928_, v___x_956_, v___y_927_);
v___x_958_ = lean_box(0);
v___x_959_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_959_, 0, v___y_930_);
lean_ctor_set(v___x_959_, 1, v___x_955_);
lean_ctor_set(v___x_959_, 2, v___x_957_);
lean_ctor_set(v___x_959_, 3, v___x_958_);
v___x_960_ = lean_mk_syntax_ident(v_k_662_);
v___x_961_ = l_Lean_Syntax_node2(v___y_930_, v___y_929_, v___x_959_, v___x_960_);
v___x_962_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_963_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_963_, 0, v___y_930_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__37, &l_Lean_Elab_Command_elabElabRulesAux___closed__37_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37);
v___x_965_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__38));
v___x_966_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__39));
lean_inc_ref_n(v___y_935_, 2);
v___x_967_ = l_Lean_Name_mkStr4(v___y_936_, v___y_935_, v___x_965_, v___x_966_);
lean_inc(v___x_967_);
v___x_968_ = l_Lean_addMacroScope(v___y_928_, v___x_967_, v___y_927_);
v___x_969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_958_);
v___x_970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v___x_958_);
v___x_971_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_971_, 0, v___y_930_);
lean_ctor_set(v___x_971_, 1, v___x_964_);
lean_ctor_set(v___x_971_, 2, v___x_968_);
lean_ctor_set(v___x_971_, 3, v___x_970_);
v___x_972_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_973_, 0, v___y_930_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_975_ = l_Lean_Name_mkStr4(v___y_936_, v___x_940_, v___x_941_, v___x_974_);
v___x_976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_976_, 0, v___y_930_);
lean_ctor_set(v___x_976_, 1, v___x_974_);
v___x_977_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_978_ = l_Lean_Name_mkStr4(v___y_936_, v___x_940_, v___x_941_, v___x_977_);
v___x_979_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
v___x_980_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
v___x_981_ = l_Lean_addMacroScope(v___y_928_, v___x_980_, v___y_927_);
v___x_982_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_982_, 0, v___y_930_);
lean_ctor_set(v___x_982_, 1, v___x_979_);
lean_ctor_set(v___x_982_, 2, v___x_981_);
lean_ctor_set(v___x_982_, 3, v___x_958_);
v___x_983_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__41, &l_Lean_Elab_Command_elabElabRulesAux___closed__41_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__41);
v___x_984_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__42));
v___x_985_ = l_Lean_addMacroScope(v___y_928_, v___x_984_, v___y_927_);
v___x_986_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_986_, 0, v___y_930_);
lean_ctor_set(v___x_986_, 1, v___x_983_);
lean_ctor_set(v___x_986_, 2, v___x_985_);
lean_ctor_set(v___x_986_, 3, v___x_958_);
lean_inc_ref(v___x_982_);
v___x_987_ = l_Lean_Syntax_node2(v___y_930_, v___y_929_, v___x_982_, v___x_986_);
v___x_988_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_988_, 0, v___y_930_);
lean_ctor_set(v___x_988_, 1, v___y_929_);
lean_ctor_set(v___x_988_, 2, v___y_934_);
v___x_989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_990_, 0, v___y_930_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_992_ = l_Lean_Name_mkStr4(v___y_936_, v___x_940_, v___x_941_, v___x_991_);
v___x_993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_993_, 0, v___y_930_);
lean_ctor_set(v___x_993_, 1, v___x_991_);
v___x_994_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_995_ = l_Lean_Name_mkStr4(v___y_936_, v___x_940_, v___x_941_, v___x_994_);
lean_inc_ref_n(v___x_988_, 3);
v___x_996_ = l_Lean_Syntax_node2(v___y_930_, v___x_995_, v___x_988_, v___x_982_);
v___x_997_ = l_Lean_Syntax_node1(v___y_930_, v___y_929_, v___x_996_);
v___x_998_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_999_, 0, v___y_930_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1001_ = l_Lean_Name_mkStr4(v___y_936_, v___x_940_, v___x_941_, v___x_1000_);
v___x_1002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1003_ = l_Lean_Name_mkStr4(v___y_936_, v___x_940_, v___x_941_, v___x_1002_);
v___x_1004_ = l_Array_append___redArg(v___y_934_, v_a_672_);
lean_dec(v_a_672_);
v___x_1005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___y_930_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1008_ = l_Lean_Name_mkStr4(v___y_936_, v___x_940_, v___x_941_, v___x_1007_);
v___x_1009_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___y_930_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l_Lean_Syntax_node1(v___y_930_, v___x_1008_, v___x_1010_);
v___x_1012_ = l_Lean_Syntax_node1(v___y_930_, v___y_929_, v___x_1011_);
v___x_1013_ = l_Lean_Syntax_node1(v___y_930_, v___y_929_, v___x_1012_);
v___x_1014_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1015_ = l_Lean_Name_mkStr4(v___y_936_, v___x_940_, v___x_941_, v___x_1014_);
v___x_1016_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___y_930_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1019_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_1020_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1021_ = l_Lean_addMacroScope(v___y_928_, v___x_1020_, v___y_927_);
v___x_1022_ = l_Lean_Name_mkStr3(v___y_936_, v___y_935_, v___x_1018_);
v___x_1023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___x_958_);
v___x_1024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_958_);
v___x_1025_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1025_, 0, v___y_930_);
lean_ctor_set(v___x_1025_, 1, v___x_1019_);
lean_ctor_set(v___x_1025_, 2, v___x_1021_);
lean_ctor_set(v___x_1025_, 3, v___x_1024_);
v___x_1026_ = l_Lean_Syntax_node2(v___y_930_, v___x_1015_, v___x_1017_, v___x_1025_);
lean_inc_ref(v___x_990_);
v___x_1027_ = l_Lean_Syntax_node4(v___y_930_, v___x_1003_, v___x_1006_, v___x_1013_, v___x_990_, v___x_1026_);
v___x_1028_ = lean_array_push(v___x_1004_, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1029_, 0, v___y_930_);
lean_ctor_set(v___x_1029_, 1, v___y_929_);
lean_ctor_set(v___x_1029_, 2, v___x_1028_);
v___x_1030_ = l_Lean_Syntax_node1(v___y_930_, v___x_1001_, v___x_1029_);
v___x_1031_ = l_Lean_Syntax_node6(v___y_930_, v___x_992_, v___x_993_, v___x_988_, v___x_988_, v___x_997_, v___x_999_, v___x_1030_);
v___x_1032_ = l_Lean_Syntax_node4(v___y_930_, v___x_978_, v___x_987_, v___x_988_, v___x_990_, v___x_1031_);
v___x_1033_ = l_Lean_Syntax_node2(v___y_930_, v___x_975_, v___x_976_, v___x_1032_);
v___x_1034_ = lean_unsigned_to_nat(9u);
v___x_1035_ = lean_mk_empty_array_with_capacity(v___x_1034_);
v___x_1036_ = lean_array_push(v___x_1035_, v___x_939_);
v___x_1037_ = lean_array_push(v___x_1036_, v___x_953_);
v___x_1038_ = lean_array_push(v___x_1037_, v___y_932_);
v___x_1039_ = lean_array_push(v___x_1038_, v___x_954_);
v___x_1040_ = lean_array_push(v___x_1039_, v___x_961_);
v___x_1041_ = lean_array_push(v___x_1040_, v___x_963_);
v___x_1042_ = lean_array_push(v___x_1041_, v___x_971_);
v___x_1043_ = lean_array_push(v___x_1042_, v___x_973_);
v___x_1044_ = lean_array_push(v___x_1043_, v___x_1033_);
lean_inc(v___y_931_);
v___x_1045_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1045_, 0, v___y_930_);
lean_ctor_set(v___x_1045_, 1, v___y_931_);
lean_ctor_set(v___x_1045_, 2, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
v___jp_1047_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1053_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1054_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1055_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1056_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1057_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1058_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_659_) == 1)
{
lean_object* v_val_1059_; lean_object* v___x_1060_; 
v_val_1059_ = lean_ctor_get(v_doc_x3f_659_, 0);
lean_inc(v_val_1059_);
lean_dec_ref(v_doc_x3f_659_);
v___x_1060_ = l_Array_mkArray1___redArg(v_val_1059_);
v___y_926_ = v___y_1048_;
v___y_927_ = v___y_1049_;
v___y_928_ = v_a_1052_;
v___y_929_ = v___x_1057_;
v___y_930_ = v___y_1050_;
v___y_931_ = v___x_1056_;
v___y_932_ = v___y_1051_;
v___y_933_ = v___x_1055_;
v___y_934_ = v___x_1058_;
v___y_935_ = v___x_1054_;
v___y_936_ = v___x_1053_;
v___y_937_ = v___x_1060_;
goto v___jp_925_;
}
else
{
lean_object* v___x_1061_; 
lean_dec(v_doc_x3f_659_);
v___x_1061_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_926_ = v___y_1048_;
v___y_927_ = v___y_1049_;
v___y_928_ = v_a_1052_;
v___y_929_ = v___x_1057_;
v___y_930_ = v___y_1050_;
v___y_931_ = v___x_1056_;
v___y_932_ = v___y_1051_;
v___y_933_ = v___x_1055_;
v___y_934_ = v___x_1058_;
v___y_935_ = v___x_1054_;
v___y_936_ = v___x_1053_;
v___y_937_ = v___x_1061_;
goto v___jp_925_;
}
}
v___jp_1062_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_inc_ref_n(v___y_1063_, 3);
v___x_1075_ = l_Array_append___redArg(v___y_1063_, v___y_1074_);
lean_dec_ref(v___y_1074_);
lean_inc_n(v___y_1066_, 7);
lean_inc_n(v___y_1070_, 26);
v___x_1076_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1076_, 0, v___y_1070_);
lean_ctor_set(v___x_1076_, 1, v___y_1066_);
lean_ctor_set(v___x_1076_, 2, v___x_1075_);
v___x_1077_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1078_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1079_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1069_, 8);
v___x_1080_ = l_Lean_Name_mkStr4(v___y_1069_, v___x_1077_, v___x_1078_, v___x_1079_);
v___x_1081_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___y_1070_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1084_ = l_Lean_Syntax_SepArray_ofElems(v___x_1083_, v___y_1071_);
lean_dec_ref(v___y_1071_);
v___x_1085_ = l_Array_append___redArg(v___y_1063_, v___x_1084_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1086_, 0, v___y_1070_);
lean_ctor_set(v___x_1086_, 1, v___y_1066_);
lean_ctor_set(v___x_1086_, 2, v___x_1085_);
v___x_1087_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___y_1070_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = l_Lean_Syntax_node3(v___y_1070_, v___x_1080_, v___x_1082_, v___x_1086_, v___x_1088_);
v___x_1090_ = l_Lean_Syntax_node1(v___y_1070_, v___y_1066_, v___x_1089_);
lean_inc_ref(v___y_1073_);
v___x_1091_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___y_1070_);
lean_ctor_set(v___x_1091_, 1, v___y_1073_);
v___x_1092_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1093_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1064_, 2);
lean_inc_n(v___y_1065_, 2);
v___x_1094_ = l_Lean_addMacroScope(v___y_1065_, v___x_1093_, v___y_1064_);
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1096_, 0, v___y_1070_);
lean_ctor_set(v___x_1096_, 1, v___x_1092_);
lean_ctor_set(v___x_1096_, 2, v___x_1094_);
lean_ctor_set(v___x_1096_, 3, v___x_1095_);
v___x_1097_ = lean_mk_syntax_ident(v_k_662_);
v___x_1098_ = l_Lean_Syntax_node2(v___y_1070_, v___y_1066_, v___x_1096_, v___x_1097_);
v___x_1099_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1100_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___y_1070_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__44, &l_Lean_Elab_Command_elabElabRulesAux___closed__44_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__44);
v___x_1102_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__45));
lean_inc_ref_n(v___y_1072_, 2);
v___x_1103_ = l_Lean_Name_mkStr4(v___y_1069_, v___y_1072_, v___x_1102_, v___x_1102_);
lean_inc(v___x_1103_);
v___x_1104_ = l_Lean_addMacroScope(v___y_1065_, v___x_1103_, v___y_1064_);
v___x_1105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1095_);
v___x_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v___x_1095_);
v___x_1107_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1107_, 0, v___y_1070_);
lean_ctor_set(v___x_1107_, 1, v___x_1101_);
lean_ctor_set(v___x_1107_, 2, v___x_1104_);
lean_ctor_set(v___x_1107_, 3, v___x_1106_);
v___x_1108_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_1109_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___y_1070_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1111_ = l_Lean_Name_mkStr4(v___y_1069_, v___x_1077_, v___x_1078_, v___x_1110_);
v___x_1112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___y_1070_);
lean_ctor_set(v___x_1112_, 1, v___x_1110_);
v___x_1113_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1114_ = l_Lean_Name_mkStr4(v___y_1069_, v___x_1077_, v___x_1078_, v___x_1113_);
v___x_1115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1116_ = l_Lean_Name_mkStr4(v___y_1069_, v___x_1077_, v___x_1078_, v___x_1115_);
v___x_1117_ = l_Array_append___redArg(v___y_1063_, v_a_672_);
lean_dec(v_a_672_);
v___x_1118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___y_1070_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1121_ = l_Lean_Name_mkStr4(v___y_1069_, v___x_1077_, v___x_1078_, v___x_1120_);
v___x_1122_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___y_1070_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = l_Lean_Syntax_node1(v___y_1070_, v___x_1121_, v___x_1123_);
v___x_1125_ = l_Lean_Syntax_node1(v___y_1070_, v___y_1066_, v___x_1124_);
v___x_1126_ = l_Lean_Syntax_node1(v___y_1070_, v___y_1066_, v___x_1125_);
v___x_1127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___y_1070_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1130_ = l_Lean_Name_mkStr4(v___y_1069_, v___x_1077_, v___x_1078_, v___x_1129_);
v___x_1131_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___y_1070_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1134_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1136_ = l_Lean_addMacroScope(v___y_1065_, v___x_1135_, v___y_1064_);
v___x_1137_ = l_Lean_Name_mkStr3(v___y_1069_, v___y_1072_, v___x_1133_);
v___x_1138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v___x_1095_);
v___x_1139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set(v___x_1139_, 1, v___x_1095_);
v___x_1140_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1140_, 0, v___y_1070_);
lean_ctor_set(v___x_1140_, 1, v___x_1134_);
lean_ctor_set(v___x_1140_, 2, v___x_1136_);
lean_ctor_set(v___x_1140_, 3, v___x_1139_);
v___x_1141_ = l_Lean_Syntax_node2(v___y_1070_, v___x_1130_, v___x_1132_, v___x_1140_);
v___x_1142_ = l_Lean_Syntax_node4(v___y_1070_, v___x_1116_, v___x_1119_, v___x_1126_, v___x_1128_, v___x_1141_);
v___x_1143_ = lean_array_push(v___x_1117_, v___x_1142_);
v___x_1144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1144_, 0, v___y_1070_);
lean_ctor_set(v___x_1144_, 1, v___y_1066_);
lean_ctor_set(v___x_1144_, 2, v___x_1143_);
v___x_1145_ = l_Lean_Syntax_node1(v___y_1070_, v___x_1114_, v___x_1144_);
v___x_1146_ = l_Lean_Syntax_node2(v___y_1070_, v___x_1111_, v___x_1112_, v___x_1145_);
v___x_1147_ = lean_unsigned_to_nat(9u);
v___x_1148_ = lean_mk_empty_array_with_capacity(v___x_1147_);
v___x_1149_ = lean_array_push(v___x_1148_, v___x_1076_);
v___x_1150_ = lean_array_push(v___x_1149_, v___x_1090_);
v___x_1151_ = lean_array_push(v___x_1150_, v___y_1068_);
v___x_1152_ = lean_array_push(v___x_1151_, v___x_1091_);
v___x_1153_ = lean_array_push(v___x_1152_, v___x_1098_);
v___x_1154_ = lean_array_push(v___x_1153_, v___x_1100_);
v___x_1155_ = lean_array_push(v___x_1154_, v___x_1107_);
v___x_1156_ = lean_array_push(v___x_1155_, v___x_1109_);
v___x_1157_ = lean_array_push(v___x_1156_, v___x_1146_);
lean_inc(v___y_1067_);
v___x_1158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1158_, 0, v___y_1070_);
lean_ctor_set(v___x_1158_, 1, v___y_1067_);
lean_ctor_set(v___x_1158_, 2, v___x_1157_);
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
return v___x_1159_;
}
v___jp_1160_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1167_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1169_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1170_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1171_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_659_) == 1)
{
lean_object* v_val_1172_; lean_object* v___x_1173_; 
v_val_1172_ = lean_ctor_get(v_doc_x3f_659_, 0);
lean_inc(v_val_1172_);
lean_dec_ref(v_doc_x3f_659_);
v___x_1173_ = l_Array_mkArray1___redArg(v_val_1172_);
v___y_1063_ = v___x_1171_;
v___y_1064_ = v___y_1161_;
v___y_1065_ = v_a_1165_;
v___y_1066_ = v___x_1170_;
v___y_1067_ = v___x_1169_;
v___y_1068_ = v___y_1162_;
v___y_1069_ = v___x_1166_;
v___y_1070_ = v___y_1163_;
v___y_1071_ = v___y_1164_;
v___y_1072_ = v___x_1167_;
v___y_1073_ = v___x_1168_;
v___y_1074_ = v___x_1173_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_1174_; 
lean_dec(v_doc_x3f_659_);
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_1063_ = v___x_1171_;
v___y_1064_ = v___y_1161_;
v___y_1065_ = v_a_1165_;
v___y_1066_ = v___x_1170_;
v___y_1067_ = v___x_1169_;
v___y_1068_ = v___y_1162_;
v___y_1069_ = v___x_1166_;
v___y_1070_ = v___y_1163_;
v___y_1071_ = v___y_1164_;
v___y_1072_ = v___x_1167_;
v___y_1073_ = v___x_1168_;
v___y_1074_ = v___x_1174_;
goto v___jp_1062_;
}
}
v___jp_1175_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_inc_ref_n(v___y_1186_, 4);
v___x_1189_ = l_Array_append___redArg(v___y_1186_, v___y_1188_);
lean_dec_ref(v___y_1188_);
lean_inc_n(v___y_1180_, 12);
lean_inc_n(v___y_1178_, 42);
v___x_1190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1190_, 0, v___y_1178_);
lean_ctor_set(v___x_1190_, 1, v___y_1180_);
lean_ctor_set(v___x_1190_, 2, v___x_1189_);
v___x_1191_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1192_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1193_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1185_, 13);
v___x_1194_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1191_, v___x_1192_, v___x_1193_);
v___x_1195_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___y_1178_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1198_ = l_Lean_Syntax_SepArray_ofElems(v___x_1197_, v___y_1184_);
lean_dec_ref(v___y_1184_);
v___x_1199_ = l_Array_append___redArg(v___y_1186_, v___x_1198_);
lean_dec_ref(v___x_1198_);
v___x_1200_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1200_, 0, v___y_1178_);
lean_ctor_set(v___x_1200_, 1, v___y_1180_);
lean_ctor_set(v___x_1200_, 2, v___x_1199_);
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___y_1178_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = l_Lean_Syntax_node3(v___y_1178_, v___x_1194_, v___x_1196_, v___x_1200_, v___x_1202_);
v___x_1204_ = l_Lean_Syntax_node1(v___y_1178_, v___y_1180_, v___x_1203_);
lean_inc_ref(v___y_1181_);
v___x_1205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___y_1178_);
lean_ctor_set(v___x_1205_, 1, v___y_1181_);
v___x_1206_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1207_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1182_, 5);
lean_inc_n(v___y_1179_, 5);
v___x_1208_ = l_Lean_addMacroScope(v___y_1179_, v___x_1207_, v___y_1182_);
v___x_1209_ = lean_box(0);
v___x_1210_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1210_, 0, v___y_1178_);
lean_ctor_set(v___x_1210_, 1, v___x_1206_);
lean_ctor_set(v___x_1210_, 2, v___x_1208_);
lean_ctor_set(v___x_1210_, 3, v___x_1209_);
v___x_1211_ = lean_mk_syntax_ident(v_k_662_);
v___x_1212_ = l_Lean_Syntax_node2(v___y_1178_, v___y_1180_, v___x_1210_, v___x_1211_);
v___x_1213_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___y_1178_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_1216_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
lean_inc_ref_n(v___y_1176_, 3);
v___x_1217_ = l_Lean_Name_mkStr4(v___y_1185_, v___y_1176_, v___x_1192_, v___x_1216_);
lean_inc(v___x_1217_);
v___x_1218_ = l_Lean_addMacroScope(v___y_1179_, v___x_1217_, v___y_1182_);
v___x_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1209_);
v___x_1220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set(v___x_1220_, 1, v___x_1209_);
v___x_1221_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1221_, 0, v___y_1178_);
lean_ctor_set(v___x_1221_, 1, v___x_1215_);
lean_ctor_set(v___x_1221_, 2, v___x_1218_);
lean_ctor_set(v___x_1221_, 3, v___x_1220_);
v___x_1222_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_1223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___y_1178_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1225_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1191_, v___x_1192_, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___y_1178_);
lean_ctor_set(v___x_1226_, 1, v___x_1224_);
v___x_1227_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1228_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1191_, v___x_1192_, v___x_1227_);
v___x_1229_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
v___x_1230_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
v___x_1231_ = l_Lean_addMacroScope(v___y_1179_, v___x_1230_, v___y_1182_);
v___x_1232_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1232_, 0, v___y_1178_);
lean_ctor_set(v___x_1232_, 1, v___x_1229_);
lean_ctor_set(v___x_1232_, 2, v___x_1231_);
lean_ctor_set(v___x_1232_, 3, v___x_1209_);
v___x_1233_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__47, &l_Lean_Elab_Command_elabElabRulesAux___closed__47_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__47);
v___x_1234_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__48));
v___x_1235_ = l_Lean_addMacroScope(v___y_1179_, v___x_1234_, v___y_1182_);
v___x_1236_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1236_, 0, v___y_1178_);
lean_ctor_set(v___x_1236_, 1, v___x_1233_);
lean_ctor_set(v___x_1236_, 2, v___x_1235_);
lean_ctor_set(v___x_1236_, 3, v___x_1209_);
lean_inc_ref(v___x_1236_);
lean_inc_ref(v___x_1232_);
v___x_1237_ = l_Lean_Syntax_node2(v___y_1178_, v___y_1180_, v___x_1232_, v___x_1236_);
v___x_1238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1238_, 0, v___y_1178_);
lean_ctor_set(v___x_1238_, 1, v___y_1180_);
lean_ctor_set(v___x_1238_, 2, v___y_1186_);
v___x_1239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___y_1178_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__49));
v___x_1242_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1191_, v___x_1192_, v___x_1241_);
v___x_1243_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__51, &l_Lean_Elab_Command_elabElabRulesAux___closed__51_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51);
v___x_1244_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__52));
v___x_1245_ = l_Lean_Name_mkStr4(v___y_1185_, v___y_1176_, v___x_1192_, v___x_1244_);
lean_inc(v___x_1245_);
v___x_1246_ = l_Lean_addMacroScope(v___y_1179_, v___x_1245_, v___y_1182_);
v___x_1247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1209_);
v___x_1248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
lean_ctor_set(v___x_1248_, 1, v___x_1209_);
v___x_1249_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1249_, 0, v___y_1178_);
lean_ctor_set(v___x_1249_, 1, v___x_1243_);
lean_ctor_set(v___x_1249_, 2, v___x_1246_);
lean_ctor_set(v___x_1249_, 3, v___x_1248_);
v___x_1250_ = l_Lean_Syntax_node1(v___y_1178_, v___y_1180_, v___y_1183_);
v___x_1251_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1252_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1191_, v___x_1192_, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___y_1178_);
lean_ctor_set(v___x_1253_, 1, v___x_1251_);
v___x_1254_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1255_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1191_, v___x_1192_, v___x_1254_);
lean_inc_ref_n(v___x_1238_, 4);
v___x_1256_ = l_Lean_Syntax_node2(v___y_1178_, v___x_1255_, v___x_1238_, v___x_1232_);
v___x_1257_ = l_Lean_Syntax_node1(v___y_1178_, v___y_1180_, v___x_1256_);
v___x_1258_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___y_1178_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1261_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1191_, v___x_1192_, v___x_1260_);
v___x_1262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1263_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1191_, v___x_1192_, v___x_1262_);
v___x_1264_ = l_Array_append___redArg(v___y_1186_, v_a_672_);
lean_dec(v_a_672_);
v___x_1265_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___y_1178_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1268_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1191_, v___x_1192_, v___x_1267_);
v___x_1269_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___y_1178_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = l_Lean_Syntax_node1(v___y_1178_, v___x_1268_, v___x_1270_);
v___x_1272_ = l_Lean_Syntax_node1(v___y_1178_, v___y_1180_, v___x_1271_);
v___x_1273_ = l_Lean_Syntax_node1(v___y_1178_, v___y_1180_, v___x_1272_);
v___x_1274_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1275_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1191_, v___x_1192_, v___x_1274_);
v___x_1276_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___y_1178_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1279_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_1280_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1281_ = l_Lean_addMacroScope(v___y_1179_, v___x_1280_, v___y_1182_);
v___x_1282_ = l_Lean_Name_mkStr3(v___y_1185_, v___y_1176_, v___x_1278_);
v___x_1283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
lean_ctor_set(v___x_1283_, 1, v___x_1209_);
v___x_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
lean_ctor_set(v___x_1284_, 1, v___x_1209_);
v___x_1285_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1285_, 0, v___y_1178_);
lean_ctor_set(v___x_1285_, 1, v___x_1279_);
lean_ctor_set(v___x_1285_, 2, v___x_1281_);
lean_ctor_set(v___x_1285_, 3, v___x_1284_);
v___x_1286_ = l_Lean_Syntax_node2(v___y_1178_, v___x_1275_, v___x_1277_, v___x_1285_);
lean_inc_ref_n(v___x_1240_, 2);
v___x_1287_ = l_Lean_Syntax_node4(v___y_1178_, v___x_1263_, v___x_1266_, v___x_1273_, v___x_1240_, v___x_1286_);
v___x_1288_ = lean_array_push(v___x_1264_, v___x_1287_);
v___x_1289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1289_, 0, v___y_1178_);
lean_ctor_set(v___x_1289_, 1, v___y_1180_);
lean_ctor_set(v___x_1289_, 2, v___x_1288_);
v___x_1290_ = l_Lean_Syntax_node1(v___y_1178_, v___x_1261_, v___x_1289_);
v___x_1291_ = l_Lean_Syntax_node6(v___y_1178_, v___x_1252_, v___x_1253_, v___x_1238_, v___x_1238_, v___x_1257_, v___x_1259_, v___x_1290_);
lean_inc(v___x_1228_);
v___x_1292_ = l_Lean_Syntax_node4(v___y_1178_, v___x_1228_, v___x_1250_, v___x_1238_, v___x_1240_, v___x_1291_);
lean_inc_ref(v___x_1226_);
lean_inc(v___x_1225_);
v___x_1293_ = l_Lean_Syntax_node2(v___y_1178_, v___x_1225_, v___x_1226_, v___x_1292_);
v___x_1294_ = l_Lean_Syntax_node2(v___y_1178_, v___y_1180_, v___x_1236_, v___x_1293_);
v___x_1295_ = l_Lean_Syntax_node2(v___y_1178_, v___x_1242_, v___x_1249_, v___x_1294_);
v___x_1296_ = l_Lean_Syntax_node4(v___y_1178_, v___x_1228_, v___x_1237_, v___x_1238_, v___x_1240_, v___x_1295_);
v___x_1297_ = l_Lean_Syntax_node2(v___y_1178_, v___x_1225_, v___x_1226_, v___x_1296_);
v___x_1298_ = lean_unsigned_to_nat(9u);
v___x_1299_ = lean_mk_empty_array_with_capacity(v___x_1298_);
v___x_1300_ = lean_array_push(v___x_1299_, v___x_1190_);
v___x_1301_ = lean_array_push(v___x_1300_, v___x_1204_);
v___x_1302_ = lean_array_push(v___x_1301_, v___y_1177_);
v___x_1303_ = lean_array_push(v___x_1302_, v___x_1205_);
v___x_1304_ = lean_array_push(v___x_1303_, v___x_1212_);
v___x_1305_ = lean_array_push(v___x_1304_, v___x_1214_);
v___x_1306_ = lean_array_push(v___x_1305_, v___x_1221_);
v___x_1307_ = lean_array_push(v___x_1306_, v___x_1223_);
v___x_1308_ = lean_array_push(v___x_1307_, v___x_1297_);
lean_inc(v___y_1187_);
v___x_1309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1309_, 0, v___y_1178_);
lean_ctor_set(v___x_1309_, 1, v___y_1187_);
lean_ctor_set(v___x_1309_, 2, v___x_1308_);
v___x_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
v___jp_1311_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1318_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1319_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1320_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1321_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1322_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1323_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_659_) == 1)
{
lean_object* v_val_1324_; lean_object* v___x_1325_; 
v_val_1324_ = lean_ctor_get(v_doc_x3f_659_, 0);
lean_inc(v_val_1324_);
lean_dec_ref(v_doc_x3f_659_);
v___x_1325_ = l_Array_mkArray1___redArg(v_val_1324_);
v___y_1176_ = v___x_1319_;
v___y_1177_ = v___y_1314_;
v___y_1178_ = v___y_1316_;
v___y_1179_ = v_a_1317_;
v___y_1180_ = v___x_1322_;
v___y_1181_ = v___x_1320_;
v___y_1182_ = v___y_1312_;
v___y_1183_ = v___y_1313_;
v___y_1184_ = v___y_1315_;
v___y_1185_ = v___x_1318_;
v___y_1186_ = v___x_1323_;
v___y_1187_ = v___x_1321_;
v___y_1188_ = v___x_1325_;
goto v___jp_1175_;
}
else
{
lean_object* v___x_1326_; 
lean_dec(v_doc_x3f_659_);
v___x_1326_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_1176_ = v___x_1319_;
v___y_1177_ = v___y_1314_;
v___y_1178_ = v___y_1316_;
v___y_1179_ = v_a_1317_;
v___y_1180_ = v___x_1322_;
v___y_1181_ = v___x_1320_;
v___y_1182_ = v___y_1312_;
v___y_1183_ = v___y_1313_;
v___y_1184_ = v___y_1315_;
v___y_1185_ = v___x_1318_;
v___y_1186_ = v___x_1323_;
v___y_1187_ = v___x_1321_;
v___y_1188_ = v___x_1326_;
goto v___jp_1175_;
}
}
v___jp_1327_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_inc_ref_n(v___y_1338_, 4);
v___x_1341_ = l_Array_append___redArg(v___y_1338_, v___y_1340_);
lean_dec_ref(v___y_1340_);
lean_inc_n(v___y_1334_, 10);
lean_inc_n(v___y_1331_, 35);
v___x_1342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1342_, 0, v___y_1331_);
lean_ctor_set(v___x_1342_, 1, v___y_1334_);
lean_ctor_set(v___x_1342_, 2, v___x_1341_);
v___x_1343_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1344_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1345_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1335_, 11);
v___x_1346_ = l_Lean_Name_mkStr4(v___y_1335_, v___x_1343_, v___x_1344_, v___x_1345_);
v___x_1347_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___y_1331_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1350_ = l_Lean_Syntax_SepArray_ofElems(v___x_1349_, v___y_1332_);
lean_dec_ref(v___y_1332_);
v___x_1351_ = l_Array_append___redArg(v___y_1338_, v___x_1350_);
lean_dec_ref(v___x_1350_);
v___x_1352_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1352_, 0, v___y_1331_);
lean_ctor_set(v___x_1352_, 1, v___y_1334_);
lean_ctor_set(v___x_1352_, 2, v___x_1351_);
v___x_1353_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___y_1331_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = l_Lean_Syntax_node3(v___y_1331_, v___x_1346_, v___x_1348_, v___x_1352_, v___x_1354_);
v___x_1356_ = l_Lean_Syntax_node1(v___y_1331_, v___y_1334_, v___x_1355_);
lean_inc_ref(v___y_1328_);
v___x_1357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___y_1331_);
lean_ctor_set(v___x_1357_, 1, v___y_1328_);
v___x_1358_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1359_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1330_, 3);
lean_inc_n(v___y_1339_, 3);
v___x_1360_ = l_Lean_addMacroScope(v___y_1339_, v___x_1359_, v___y_1330_);
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1362_, 0, v___y_1331_);
lean_ctor_set(v___x_1362_, 1, v___x_1358_);
lean_ctor_set(v___x_1362_, 2, v___x_1360_);
lean_ctor_set(v___x_1362_, 3, v___x_1361_);
v___x_1363_ = lean_mk_syntax_ident(v_k_662_);
v___x_1364_ = l_Lean_Syntax_node2(v___y_1331_, v___y_1334_, v___x_1362_, v___x_1363_);
v___x_1365_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___y_1331_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__37, &l_Lean_Elab_Command_elabElabRulesAux___closed__37_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37);
v___x_1368_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__38));
v___x_1369_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__39));
lean_inc_ref_n(v___y_1336_, 2);
v___x_1370_ = l_Lean_Name_mkStr4(v___y_1335_, v___y_1336_, v___x_1368_, v___x_1369_);
lean_inc(v___x_1370_);
v___x_1371_ = l_Lean_addMacroScope(v___y_1339_, v___x_1370_, v___y_1330_);
v___x_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1370_);
lean_ctor_set(v___x_1372_, 1, v___x_1361_);
v___x_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
lean_ctor_set(v___x_1373_, 1, v___x_1361_);
v___x_1374_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1374_, 0, v___y_1331_);
lean_ctor_set(v___x_1374_, 1, v___x_1367_);
lean_ctor_set(v___x_1374_, 2, v___x_1371_);
lean_ctor_set(v___x_1374_, 3, v___x_1373_);
v___x_1375_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_1376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___y_1331_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1378_ = l_Lean_Name_mkStr4(v___y_1335_, v___x_1343_, v___x_1344_, v___x_1377_);
v___x_1379_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___y_1331_);
lean_ctor_set(v___x_1379_, 1, v___x_1377_);
v___x_1380_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1381_ = l_Lean_Name_mkStr4(v___y_1335_, v___x_1343_, v___x_1344_, v___x_1380_);
v___x_1382_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
v___x_1383_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
v___x_1384_ = l_Lean_addMacroScope(v___y_1339_, v___x_1383_, v___y_1330_);
v___x_1385_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1385_, 0, v___y_1331_);
lean_ctor_set(v___x_1385_, 1, v___x_1382_);
lean_ctor_set(v___x_1385_, 2, v___x_1384_);
lean_ctor_set(v___x_1385_, 3, v___x_1361_);
lean_inc_ref(v___x_1385_);
v___x_1386_ = l_Lean_Syntax_node2(v___y_1331_, v___y_1334_, v___x_1385_, v___y_1337_);
v___x_1387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1387_, 0, v___y_1331_);
lean_ctor_set(v___x_1387_, 1, v___y_1334_);
lean_ctor_set(v___x_1387_, 2, v___y_1338_);
v___x_1388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___y_1331_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1391_ = l_Lean_Name_mkStr4(v___y_1335_, v___x_1343_, v___x_1344_, v___x_1390_);
v___x_1392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___y_1331_);
lean_ctor_set(v___x_1392_, 1, v___x_1390_);
v___x_1393_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1394_ = l_Lean_Name_mkStr4(v___y_1335_, v___x_1343_, v___x_1344_, v___x_1393_);
lean_inc_ref_n(v___x_1387_, 3);
v___x_1395_ = l_Lean_Syntax_node2(v___y_1331_, v___x_1394_, v___x_1387_, v___x_1385_);
v___x_1396_ = l_Lean_Syntax_node1(v___y_1331_, v___y_1334_, v___x_1395_);
v___x_1397_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___y_1331_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1400_ = l_Lean_Name_mkStr4(v___y_1335_, v___x_1343_, v___x_1344_, v___x_1399_);
v___x_1401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1402_ = l_Lean_Name_mkStr4(v___y_1335_, v___x_1343_, v___x_1344_, v___x_1401_);
v___x_1403_ = l_Array_append___redArg(v___y_1338_, v_a_672_);
lean_dec(v_a_672_);
v___x_1404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___y_1331_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
v___x_1406_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1407_ = l_Lean_Name_mkStr4(v___y_1335_, v___x_1343_, v___x_1344_, v___x_1406_);
v___x_1408_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___y_1331_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = l_Lean_Syntax_node1(v___y_1331_, v___x_1407_, v___x_1409_);
v___x_1411_ = l_Lean_Syntax_node1(v___y_1331_, v___y_1334_, v___x_1410_);
v___x_1412_ = l_Lean_Syntax_node1(v___y_1331_, v___y_1334_, v___x_1411_);
v___x_1413_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1414_ = l_Lean_Name_mkStr4(v___y_1335_, v___x_1343_, v___x_1344_, v___x_1413_);
v___x_1415_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___y_1331_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1418_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_1419_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1420_ = l_Lean_addMacroScope(v___y_1339_, v___x_1419_, v___y_1330_);
v___x_1421_ = l_Lean_Name_mkStr3(v___y_1335_, v___y_1336_, v___x_1417_);
v___x_1422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
lean_ctor_set(v___x_1422_, 1, v___x_1361_);
v___x_1423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
lean_ctor_set(v___x_1423_, 1, v___x_1361_);
v___x_1424_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1424_, 0, v___y_1331_);
lean_ctor_set(v___x_1424_, 1, v___x_1418_);
lean_ctor_set(v___x_1424_, 2, v___x_1420_);
lean_ctor_set(v___x_1424_, 3, v___x_1423_);
v___x_1425_ = l_Lean_Syntax_node2(v___y_1331_, v___x_1414_, v___x_1416_, v___x_1424_);
lean_inc_ref(v___x_1389_);
v___x_1426_ = l_Lean_Syntax_node4(v___y_1331_, v___x_1402_, v___x_1405_, v___x_1412_, v___x_1389_, v___x_1425_);
v___x_1427_ = lean_array_push(v___x_1403_, v___x_1426_);
v___x_1428_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1428_, 0, v___y_1331_);
lean_ctor_set(v___x_1428_, 1, v___y_1334_);
lean_ctor_set(v___x_1428_, 2, v___x_1427_);
v___x_1429_ = l_Lean_Syntax_node1(v___y_1331_, v___x_1400_, v___x_1428_);
v___x_1430_ = l_Lean_Syntax_node6(v___y_1331_, v___x_1391_, v___x_1392_, v___x_1387_, v___x_1387_, v___x_1396_, v___x_1398_, v___x_1429_);
v___x_1431_ = l_Lean_Syntax_node4(v___y_1331_, v___x_1381_, v___x_1386_, v___x_1387_, v___x_1389_, v___x_1430_);
v___x_1432_ = l_Lean_Syntax_node2(v___y_1331_, v___x_1378_, v___x_1379_, v___x_1431_);
v___x_1433_ = lean_unsigned_to_nat(9u);
v___x_1434_ = lean_mk_empty_array_with_capacity(v___x_1433_);
v___x_1435_ = lean_array_push(v___x_1434_, v___x_1342_);
v___x_1436_ = lean_array_push(v___x_1435_, v___x_1356_);
v___x_1437_ = lean_array_push(v___x_1436_, v___y_1329_);
v___x_1438_ = lean_array_push(v___x_1437_, v___x_1357_);
v___x_1439_ = lean_array_push(v___x_1438_, v___x_1364_);
v___x_1440_ = lean_array_push(v___x_1439_, v___x_1366_);
v___x_1441_ = lean_array_push(v___x_1440_, v___x_1374_);
v___x_1442_ = lean_array_push(v___x_1441_, v___x_1376_);
v___x_1443_ = lean_array_push(v___x_1442_, v___x_1432_);
lean_inc(v___y_1333_);
v___x_1444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1444_, 0, v___y_1331_);
lean_ctor_set(v___x_1444_, 1, v___y_1333_);
lean_ctor_set(v___x_1444_, 2, v___x_1443_);
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
return v___x_1445_;
}
v___jp_1446_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1453_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1454_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1455_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1456_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1457_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1458_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_659_) == 1)
{
lean_object* v_val_1459_; lean_object* v___x_1460_; 
v_val_1459_ = lean_ctor_get(v_doc_x3f_659_, 0);
lean_inc(v_val_1459_);
lean_dec_ref(v_doc_x3f_659_);
v___x_1460_ = l_Array_mkArray1___redArg(v_val_1459_);
v___y_1328_ = v___x_1455_;
v___y_1329_ = v___y_1448_;
v___y_1330_ = v___y_1449_;
v___y_1331_ = v___y_1451_;
v___y_1332_ = v___y_1450_;
v___y_1333_ = v___x_1456_;
v___y_1334_ = v___x_1457_;
v___y_1335_ = v___x_1453_;
v___y_1336_ = v___x_1454_;
v___y_1337_ = v___y_1447_;
v___y_1338_ = v___x_1458_;
v___y_1339_ = v_a_1452_;
v___y_1340_ = v___x_1460_;
goto v___jp_1327_;
}
else
{
lean_object* v___x_1461_; 
lean_dec(v_doc_x3f_659_);
v___x_1461_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_1328_ = v___x_1455_;
v___y_1329_ = v___y_1448_;
v___y_1330_ = v___y_1449_;
v___y_1331_ = v___y_1451_;
v___y_1332_ = v___y_1450_;
v___y_1333_ = v___x_1456_;
v___y_1334_ = v___x_1457_;
v___y_1335_ = v___x_1453_;
v___y_1336_ = v___x_1454_;
v___y_1337_ = v___y_1447_;
v___y_1338_ = v___x_1458_;
v___y_1339_ = v_a_1452_;
v___y_1340_ = v___x_1461_;
goto v___jp_1327_;
}
}
v___jp_1462_:
{
lean_object* v___x_1468_; 
lean_inc(v___y_1463_);
lean_inc(v_k_662_);
v___x_1468_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_662_, v_attrKind_661_, v_attrs_x3f_660_, v___y_1463_, v___y_1467_, v___y_1466_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref(v___x_1468_);
v___x_1470_ = l_Lean_Elab_Command_getRef___redArg(v___y_1467_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref(v___x_1470_);
v___x_1472_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1467_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v_quotContext_x3f_1474_; lean_object* v___x_1475_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref(v___x_1472_);
v_quotContext_x3f_1474_ = lean_ctor_get(v___y_1467_, 5);
v___x_1475_ = l_Lean_SourceInfo_fromRef(v_a_1471_, v___y_1464_);
lean_dec(v_a_1471_);
if (lean_obj_tag(v_quotContext_x3f_1474_) == 0)
{
lean_object* v___x_1476_; lean_object* v_a_1477_; 
v___x_1476_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1466_);
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref(v___x_1476_);
v___y_1161_ = v_a_1473_;
v___y_1162_ = v___y_1465_;
v___y_1163_ = v___x_1475_;
v___y_1164_ = v_a_1469_;
v_a_1165_ = v_a_1477_;
goto v___jp_1160_;
}
else
{
lean_object* v_val_1478_; 
v_val_1478_ = lean_ctor_get(v_quotContext_x3f_1474_, 0);
lean_inc(v_val_1478_);
v___y_1161_ = v_a_1473_;
v___y_1162_ = v___y_1465_;
v___y_1163_ = v___x_1475_;
v___y_1164_ = v_a_1469_;
v_a_1165_ = v_val_1478_;
goto v___jp_1160_;
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_a_1471_);
lean_dec(v_a_1469_);
lean_dec(v___y_1465_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
v_a_1479_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1472_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1472_);
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
else
{
lean_dec(v_a_1469_);
lean_dec(v___y_1465_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
return v___x_1470_;
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v___y_1465_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
v_a_1487_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1468_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1468_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
v___jp_1495_:
{
lean_object* v___x_1499_; 
lean_inc(v_attrKind_661_);
v___x_1499_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_661_);
if (lean_obj_tag(v_expty_x3f_664_) == 1)
{
lean_object* v_val_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; 
lean_del_object(v___x_674_);
v_val_1500_ = lean_ctor_get(v_expty_x3f_664_, 0);
lean_inc(v_val_1500_);
lean_dec_ref(v_expty_x3f_664_);
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
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_attrKind_661_);
lean_dec(v_doc_x3f_659_);
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
lean_inc(v_k_662_);
v___x_1512_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_662_, v_attrKind_661_, v_attrs_x3f_660_, v___x_1511_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref(v___x_1512_);
v___x_1514_ = l_Lean_Elab_Command_getRef___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref(v___x_1514_);
v___x_1516_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v_quotContext_x3f_1518_; lean_object* v___x_1519_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v___x_1516_);
v_quotContext_x3f_1518_ = lean_ctor_get(v___y_1497_, 5);
v___x_1519_ = l_Lean_SourceInfo_fromRef(v_a_1515_, v___x_1502_);
lean_dec(v_a_1515_);
if (lean_obj_tag(v_quotContext_x3f_1518_) == 0)
{
lean_object* v___x_1520_; lean_object* v_a_1521_; 
v___x_1520_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1498_);
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref(v___x_1520_);
v___y_1447_ = v_val_1500_;
v___y_1448_ = v___x_1499_;
v___y_1449_ = v_a_1517_;
v___y_1450_ = v_a_1513_;
v___y_1451_ = v___x_1519_;
v_a_1452_ = v_a_1521_;
goto v___jp_1446_;
}
else
{
lean_object* v_val_1522_; 
v_val_1522_ = lean_ctor_get(v_quotContext_x3f_1518_, 0);
lean_inc(v_val_1522_);
v___y_1447_ = v_val_1500_;
v___y_1448_ = v___x_1499_;
v___y_1449_ = v_a_1517_;
v___y_1450_ = v_a_1513_;
v___y_1451_ = v___x_1519_;
v_a_1452_ = v_val_1522_;
goto v___jp_1446_;
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec(v_a_1515_);
lean_dec(v_a_1513_);
lean_dec(v_val_1500_);
lean_dec(v___x_1499_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
v_a_1523_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1516_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1516_);
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
else
{
lean_dec(v_a_1513_);
lean_dec(v_val_1500_);
lean_dec(v___x_1499_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
return v___x_1514_;
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_val_1500_);
lean_dec(v___x_1499_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
v_a_1531_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1512_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1512_);
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
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_dec(v_catName_1496_);
v___x_1539_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(v_k_662_);
v___x_1540_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_662_, v_attrKind_661_, v_attrs_x3f_660_, v___x_1539_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1542_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref(v___x_1540_);
v___x_1542_ = l_Lean_Elab_Command_getRef___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1542_);
v___x_1544_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v_quotContext_x3f_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref(v___x_1544_);
v_quotContext_x3f_1546_ = lean_ctor_get(v___y_1497_, 5);
v___x_1547_ = 0;
v___x_1548_ = l_Lean_SourceInfo_fromRef(v_a_1543_, v___x_1547_);
lean_dec(v_a_1543_);
if (lean_obj_tag(v_quotContext_x3f_1546_) == 0)
{
lean_object* v___x_1549_; lean_object* v_a_1550_; 
v___x_1549_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1498_);
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
v___y_1312_ = v_a_1545_;
v___y_1313_ = v_val_1500_;
v___y_1314_ = v___x_1499_;
v___y_1315_ = v_a_1541_;
v___y_1316_ = v___x_1548_;
v_a_1317_ = v_a_1550_;
goto v___jp_1311_;
}
else
{
lean_object* v_val_1551_; 
v_val_1551_ = lean_ctor_get(v_quotContext_x3f_1546_, 0);
lean_inc(v_val_1551_);
v___y_1312_ = v_a_1545_;
v___y_1313_ = v_val_1500_;
v___y_1314_ = v___x_1499_;
v___y_1315_ = v_a_1541_;
v___y_1316_ = v___x_1548_;
v_a_1317_ = v_val_1551_;
goto v___jp_1311_;
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec(v_a_1543_);
lean_dec(v_a_1541_);
lean_dec(v_val_1500_);
lean_dec(v___x_1499_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
v_a_1552_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1544_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1544_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
else
{
lean_dec(v_a_1541_);
lean_dec(v_val_1500_);
lean_dec(v___x_1499_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
return v___x_1542_;
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec(v_val_1500_);
lean_dec(v___x_1499_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
v_a_1560_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1540_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1540_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
else
{
lean_object* v___x_1568_; uint8_t v___x_1569_; 
lean_dec(v_expty_x3f_664_);
v___x_1568_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_1569_ = lean_name_eq(v_catName_1496_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
lean_del_object(v___x_674_);
v___x_1570_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__66));
v___x_1571_ = lean_name_eq(v_catName_1496_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__68));
v___x_1573_ = lean_name_eq(v_catName_1496_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__70));
v___x_1575_ = lean_name_eq(v_catName_1496_, v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
v___x_1577_ = lean_name_eq(v_catName_1496_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec(v___x_1499_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_attrKind_661_);
lean_dec(v_doc_x3f_659_);
v___x_1578_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__72, &l_Lean_Elab_Command_elabElabRulesAux___closed__72_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72);
v___x_1579_ = l_Lean_MessageData_ofName(v_catName_1496_);
v___x_1580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_1582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_1582_, v___y_1497_, v___y_1498_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec(v_catName_1496_);
v___x_1584_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(v_k_662_);
v___x_1585_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_662_, v_attrKind_661_, v_attrs_x3f_660_, v___x_1584_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1587_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref(v___x_1585_);
v___x_1587_ = l_Lean_Elab_Command_getRef___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref(v___x_1587_);
v___x_1589_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v_quotContext_x3f_1591_; lean_object* v___x_1592_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref(v___x_1589_);
v_quotContext_x3f_1591_ = lean_ctor_get(v___y_1497_, 5);
v___x_1592_ = l_Lean_SourceInfo_fromRef(v_a_1588_, v___x_1575_);
lean_dec(v_a_1588_);
if (lean_obj_tag(v_quotContext_x3f_1591_) == 0)
{
lean_object* v___x_1593_; lean_object* v_a_1594_; 
v___x_1593_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1498_);
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref(v___x_1593_);
v___y_1048_ = v_a_1586_;
v___y_1049_ = v_a_1590_;
v___y_1050_ = v___x_1592_;
v___y_1051_ = v___x_1499_;
v_a_1052_ = v_a_1594_;
goto v___jp_1047_;
}
else
{
lean_object* v_val_1595_; 
v_val_1595_ = lean_ctor_get(v_quotContext_x3f_1591_, 0);
lean_inc(v_val_1595_);
v___y_1048_ = v_a_1586_;
v___y_1049_ = v_a_1590_;
v___y_1050_ = v___x_1592_;
v___y_1051_ = v___x_1499_;
v_a_1052_ = v_val_1595_;
goto v___jp_1047_;
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_a_1588_);
lean_dec(v_a_1586_);
lean_dec(v___x_1499_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
v_a_1596_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1589_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1589_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_dec(v_a_1586_);
lean_dec(v___x_1499_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
return v___x_1587_;
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v___x_1499_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
v_a_1604_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1585_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1585_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
else
{
lean_dec(v_catName_1496_);
v___y_1463_ = v___x_1572_;
v___y_1464_ = v___x_1571_;
v___y_1465_ = v___x_1499_;
v___y_1466_ = v___y_1498_;
v___y_1467_ = v___y_1497_;
goto v___jp_1462_;
}
}
else
{
lean_dec(v_catName_1496_);
v___y_1463_ = v___x_1572_;
v___y_1464_ = v___x_1571_;
v___y_1465_ = v___x_1499_;
v___y_1466_ = v___y_1498_;
v___y_1467_ = v___y_1497_;
goto v___jp_1462_;
}
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec(v_catName_1496_);
v___x_1612_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__74));
lean_inc(v_k_662_);
v___x_1613_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_662_, v_attrKind_661_, v_attrs_x3f_660_, v___x_1612_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1615_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref(v___x_1613_);
v___x_1615_ = l_Lean_Elab_Command_getRef___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1617_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref(v___x_1615_);
v___x_1617_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v_quotContext_x3f_1619_; lean_object* v___x_1620_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref(v___x_1617_);
v_quotContext_x3f_1619_ = lean_ctor_get(v___y_1497_, 5);
v___x_1620_ = l_Lean_SourceInfo_fromRef(v_a_1616_, v___x_1569_);
lean_dec(v_a_1616_);
if (lean_obj_tag(v_quotContext_x3f_1619_) == 0)
{
lean_object* v___x_1621_; lean_object* v_a_1622_; 
v___x_1621_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1498_);
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref(v___x_1621_);
v___y_910_ = v___x_1620_;
v___y_911_ = v___x_1499_;
v___y_912_ = v_a_1618_;
v___y_913_ = v_a_1614_;
v_a_914_ = v_a_1622_;
goto v___jp_909_;
}
else
{
lean_object* v_val_1623_; 
v_val_1623_ = lean_ctor_get(v_quotContext_x3f_1619_, 0);
lean_inc(v_val_1623_);
v___y_910_ = v___x_1620_;
v___y_911_ = v___x_1499_;
v___y_912_ = v_a_1618_;
v___y_913_ = v_a_1614_;
v_a_914_ = v_val_1623_;
goto v___jp_909_;
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v_a_1616_);
lean_dec(v_a_1614_);
lean_dec(v___x_1499_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
v_a_1624_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1617_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1617_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_dec(v_a_1614_);
lean_dec(v___x_1499_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
return v___x_1615_;
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec(v___x_1499_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
v_a_1632_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1613_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1613_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec(v_catName_1496_);
v___x_1640_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(v_k_662_);
v___x_1641_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_662_, v_attrKind_661_, v_attrs_x3f_660_, v___x_1640_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1643_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref(v___x_1641_);
v___x_1643_ = l_Lean_Elab_Command_getRef___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1645_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref(v___x_1643_);
v___x_1645_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1497_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v_quotContext_x3f_1647_; uint8_t v___x_1648_; lean_object* v___x_1649_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1645_);
v_quotContext_x3f_1647_ = lean_ctor_get(v___y_1497_, 5);
v___x_1648_ = 0;
v___x_1649_ = l_Lean_SourceInfo_fromRef(v_a_1644_, v___x_1648_);
lean_dec(v_a_1644_);
if (lean_obj_tag(v_quotContext_x3f_1647_) == 0)
{
lean_object* v___x_1650_; lean_object* v_a_1651_; 
v___x_1650_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1498_);
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref(v___x_1650_);
v___y_796_ = v___x_1499_;
v___y_797_ = v_a_1642_;
v___y_798_ = v___x_1649_;
v___y_799_ = v_a_1646_;
v_a_800_ = v_a_1651_;
goto v___jp_795_;
}
else
{
lean_object* v_val_1652_; 
v_val_1652_ = lean_ctor_get(v_quotContext_x3f_1647_, 0);
lean_inc(v_val_1652_);
v___y_796_ = v___x_1499_;
v___y_797_ = v_a_1642_;
v___y_798_ = v___x_1649_;
v___y_799_ = v_a_1646_;
v_a_800_ = v_val_1652_;
goto v___jp_795_;
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_a_1644_);
lean_dec(v_a_1642_);
lean_dec(v___x_1499_);
lean_del_object(v___x_674_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
v_a_1653_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1645_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1645_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_dec(v_a_1642_);
lean_dec(v___x_1499_);
lean_del_object(v___x_674_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
return v___x_1643_;
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v___x_1499_);
lean_del_object(v___x_674_);
lean_dec(v_a_672_);
lean_dec(v_k_662_);
lean_dec(v_doc_x3f_659_);
v_a_1661_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1641_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1641_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
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
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec(v_expty_x3f_664_);
lean_dec(v_k_662_);
lean_dec(v_attrKind_661_);
lean_dec(v_doc_x3f_659_);
v_a_1683_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_671_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_671_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object* v_doc_x3f_1691_, lean_object* v_attrs_x3f_1692_, lean_object* v_attrKind_1693_, lean_object* v_k_1694_, lean_object* v_cat_x3f_1695_, lean_object* v_expty_x3f_1696_, lean_object* v_alts_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Elab_Command_elabElabRulesAux(v_doc_x3f_1691_, v_attrs_x3f_1692_, v_attrKind_1693_, v_k_1694_, v_cat_x3f_1695_, v_expty_x3f_1696_, v_alts_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_cat_x3f_1695_);
lean_dec(v_attrs_x3f_1692_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object* v_00_u03b1_1702_, lean_object* v_ref_1703_, lean_object* v_msg_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_1703_, v_msg_1704_, v___y_1705_, v___y_1706_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object* v_00_u03b1_1709_, lean_object* v_ref_1710_, lean_object* v_msg_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(v_00_u03b1_1709_, v_ref_1710_, v_msg_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v_ref_1710_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(lean_object* v_msgData_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_1716_, v___y_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___boxed(lean_object* v_msgData_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(v_msgData_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(lean_object* v_00_u03b1_1726_, lean_object* v_msg_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_1727_, v___y_1728_, v___y_1729_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___boxed(lean_object* v_00_u03b1_1732_, lean_object* v_msg_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(v_00_u03b1_1732_, v_msg_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(lean_object* v_msgData_1738_, lean_object* v_macroStack_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_msgData_1738_, v_macroStack_1739_, v___y_1741_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___boxed(lean_object* v_msgData_1744_, lean_object* v_macroStack_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(v_msgData_1744_, v_macroStack_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object* v_x_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object* v_x_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_Elab_Command_elabElabRules___lam__0(v_x_1752_);
lean_dec(v_x_1752_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object* v___x_1758_, lean_object* v___x_1759_, lean_object* v_attrKind_1760_, lean_object* v_expty_x3f_1761_, lean_object* v___f_1762_, lean_object* v_cat_x3f_1763_, lean_object* v___x_1764_, lean_object* v___x_1765_, lean_object* v_attrs_x3f_1766_, lean_object* v___x_1767_, lean_object* v___x_1768_, lean_object* v___x_1769_, lean_object* v_doc_x3f_1770_, lean_object* v_kind_x3f_1771_, lean_object* v_alts_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_Elab_Command_getRef___redArg(v___y_1773_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1778_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref(v___x_1776_);
v___x_1778_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1773_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1877_; 
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1877_ == 0)
{
lean_object* v_unused_1878_; 
v_unused_1878_ = lean_ctor_get(v___x_1778_, 0);
lean_dec(v_unused_1878_);
v___x_1780_ = v___x_1778_;
v_isShared_1781_ = v_isSharedCheck_1877_;
goto v_resetjp_1779_;
}
else
{
lean_dec(v___x_1778_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1877_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_quotContext_x3f_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; 
v_quotContext_x3f_1782_ = lean_ctor_get(v___y_1773_, 5);
v___x_1783_ = 0;
v___x_1784_ = l_Lean_SourceInfo_fromRef(v_a_1777_, v___x_1783_);
lean_dec(v_a_1777_);
if (lean_obj_tag(v_quotContext_x3f_1782_) == 0)
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1774_);
lean_dec_ref(v___x_1876_);
goto v___jp_1870_;
}
else
{
goto v___jp_1870_;
}
v___jp_1785_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1801_; 
lean_inc_ref_n(v___y_1788_, 2);
v___x_1794_ = l_Array_append___redArg(v___y_1788_, v___y_1793_);
lean_dec_ref(v___y_1793_);
lean_inc_n(v___y_1787_, 2);
lean_inc_n(v___x_1784_, 3);
v___x_1795_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1784_);
lean_ctor_set(v___x_1795_, 1, v___y_1787_);
lean_ctor_set(v___x_1795_, 2, v___x_1794_);
v___x_1796_ = l_Array_append___redArg(v___y_1788_, v_alts_1772_);
v___x_1797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1784_);
lean_ctor_set(v___x_1797_, 1, v___y_1787_);
lean_ctor_set(v___x_1797_, 2, v___x_1796_);
v___x_1798_ = l_Lean_Syntax_node1(v___x_1784_, v___x_1758_, v___x_1797_);
v___x_1799_ = l_Lean_Syntax_node8(v___x_1784_, v___x_1759_, v___y_1792_, v___y_1791_, v_attrKind_1760_, v___y_1786_, v___y_1790_, v___y_1789_, v___x_1795_, v___x_1798_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1799_);
v___x_1801_ = v___x_1780_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
v___jp_1803_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
lean_inc_ref(v___y_1806_);
v___x_1811_ = l_Array_append___redArg(v___y_1806_, v___y_1810_);
lean_dec_ref(v___y_1810_);
lean_inc(v___y_1805_);
lean_inc(v___x_1784_);
v___x_1812_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1784_);
lean_ctor_set(v___x_1812_, 1, v___y_1805_);
lean_ctor_set(v___x_1812_, 2, v___x_1811_);
if (lean_obj_tag(v_expty_x3f_1761_) == 1)
{
lean_object* v_val_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
lean_dec_ref(v___f_1762_);
v_val_1813_ = lean_ctor_get(v_expty_x3f_1761_, 0);
lean_inc(v_val_1813_);
lean_dec_ref(v_expty_x3f_1761_);
v___x_1814_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___x_1784_);
v___x_1815_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1784_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = l_Array_mkArray2___redArg(v___x_1815_, v_val_1813_);
v___y_1786_ = v___y_1804_;
v___y_1787_ = v___y_1805_;
v___y_1788_ = v___y_1806_;
v___y_1789_ = v___x_1812_;
v___y_1790_ = v___y_1807_;
v___y_1791_ = v___y_1808_;
v___y_1792_ = v___y_1809_;
v___y_1793_ = v___x_1816_;
goto v___jp_1785_;
}
else
{
lean_object* v___x_1817_; 
v___x_1817_ = lean_apply_1(v___f_1762_, v_expty_x3f_1761_);
v___y_1786_ = v___y_1804_;
v___y_1787_ = v___y_1805_;
v___y_1788_ = v___y_1806_;
v___y_1789_ = v___x_1812_;
v___y_1790_ = v___y_1807_;
v___y_1791_ = v___y_1808_;
v___y_1792_ = v___y_1809_;
v___y_1793_ = v___x_1817_;
goto v___jp_1785_;
}
}
v___jp_1818_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_inc_ref(v___y_1821_);
v___x_1825_ = l_Array_append___redArg(v___y_1821_, v___y_1824_);
lean_dec_ref(v___y_1824_);
lean_inc(v___y_1820_);
lean_inc(v___x_1784_);
v___x_1826_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1784_);
lean_ctor_set(v___x_1826_, 1, v___y_1820_);
lean_ctor_set(v___x_1826_, 2, v___x_1825_);
if (lean_obj_tag(v_cat_x3f_1763_) == 1)
{
lean_object* v_val_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v_val_1827_ = lean_ctor_get(v_cat_x3f_1763_, 0);
lean_inc(v_val_1827_);
lean_dec_ref(v_cat_x3f_1763_);
v___x_1828_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___x_1784_);
v___x_1829_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1784_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = l_Array_mkArray2___redArg(v___x_1829_, v_val_1827_);
v___y_1804_ = v___y_1819_;
v___y_1805_ = v___y_1820_;
v___y_1806_ = v___y_1821_;
v___y_1807_ = v___x_1826_;
v___y_1808_ = v___y_1822_;
v___y_1809_ = v___y_1823_;
v___y_1810_ = v___x_1830_;
goto v___jp_1803_;
}
else
{
lean_object* v___x_1831_; 
lean_inc_ref(v___f_1762_);
v___x_1831_ = lean_apply_1(v___f_1762_, v_cat_x3f_1763_);
v___y_1804_ = v___y_1819_;
v___y_1805_ = v___y_1820_;
v___y_1806_ = v___y_1821_;
v___y_1807_ = v___x_1826_;
v___y_1808_ = v___y_1822_;
v___y_1809_ = v___y_1823_;
v___y_1810_ = v___x_1831_;
goto v___jp_1803_;
}
}
v___jp_1832_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_inc_ref(v___y_1834_);
v___x_1837_ = l_Array_append___redArg(v___y_1834_, v___y_1836_);
lean_dec_ref(v___y_1836_);
lean_inc(v___y_1833_);
lean_inc_n(v___x_1784_, 2);
v___x_1838_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1784_);
lean_ctor_set(v___x_1838_, 1, v___y_1833_);
lean_ctor_set(v___x_1838_, 2, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1784_);
lean_ctor_set(v___x_1839_, 1, v___x_1764_);
if (lean_obj_tag(v_kind_x3f_1771_) == 0)
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_mk_empty_array_with_capacity(v___x_1765_);
v___y_1819_ = v___x_1839_;
v___y_1820_ = v___y_1833_;
v___y_1821_ = v___y_1834_;
v___y_1822_ = v___x_1838_;
v___y_1823_ = v___y_1835_;
v___y_1824_ = v___x_1840_;
goto v___jp_1818_;
}
else
{
lean_object* v_val_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_val_1841_ = lean_ctor_get(v_kind_x3f_1771_, 0);
lean_inc(v_val_1841_);
lean_dec_ref(v_kind_x3f_1771_);
v___x_1842_ = lean_mk_syntax_ident(v_val_1841_);
v___x_1843_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___x_1784_, 4);
v___x_1844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1784_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__2));
v___x_1846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1784_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_1848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1784_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_1850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1784_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = l_Array_mkArray5___redArg(v___x_1844_, v___x_1846_, v___x_1848_, v___x_1842_, v___x_1850_);
v___y_1819_ = v___x_1839_;
v___y_1820_ = v___y_1833_;
v___y_1821_ = v___y_1834_;
v___y_1822_ = v___x_1838_;
v___y_1823_ = v___y_1835_;
v___y_1824_ = v___x_1851_;
goto v___jp_1818_;
}
}
v___jp_1852_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_inc_ref(v___y_1854_);
v___x_1856_ = l_Array_append___redArg(v___y_1854_, v___y_1855_);
lean_dec_ref(v___y_1855_);
lean_inc(v___y_1853_);
lean_inc(v___x_1784_);
v___x_1857_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1784_);
lean_ctor_set(v___x_1857_, 1, v___y_1853_);
lean_ctor_set(v___x_1857_, 2, v___x_1856_);
if (lean_obj_tag(v_attrs_x3f_1766_) == 1)
{
lean_object* v_val_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v_val_1858_ = lean_ctor_get(v_attrs_x3f_1766_, 0);
v___x_1859_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
v___x_1860_ = l_Lean_Name_mkStr4(v___x_1767_, v___x_1768_, v___x_1769_, v___x_1859_);
v___x_1861_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___x_1784_, 4);
v___x_1862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1784_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
lean_inc_ref(v___y_1854_);
v___x_1863_ = l_Array_append___redArg(v___y_1854_, v_val_1858_);
lean_inc(v___y_1853_);
v___x_1864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1784_);
lean_ctor_set(v___x_1864_, 1, v___y_1853_);
lean_ctor_set(v___x_1864_, 2, v___x_1863_);
v___x_1865_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1784_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = l_Lean_Syntax_node3(v___x_1784_, v___x_1860_, v___x_1862_, v___x_1864_, v___x_1866_);
v___x_1868_ = l_Array_mkArray1___redArg(v___x_1867_);
v___y_1833_ = v___y_1853_;
v___y_1834_ = v___y_1854_;
v___y_1835_ = v___x_1857_;
v___y_1836_ = v___x_1868_;
goto v___jp_1832_;
}
else
{
lean_object* v___x_1869_; 
lean_dec_ref(v___x_1769_);
lean_dec_ref(v___x_1768_);
lean_dec_ref(v___x_1767_);
v___x_1869_ = lean_mk_empty_array_with_capacity(v___x_1765_);
v___y_1833_ = v___y_1853_;
v___y_1834_ = v___y_1854_;
v___y_1835_ = v___x_1857_;
v___y_1836_ = v___x_1869_;
goto v___jp_1832_;
}
}
v___jp_1870_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1872_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_1770_) == 1)
{
lean_object* v_val_1873_; lean_object* v___x_1874_; 
v_val_1873_ = lean_ctor_get(v_doc_x3f_1770_, 0);
lean_inc(v_val_1873_);
lean_dec_ref(v_doc_x3f_1770_);
v___x_1874_ = l_Array_mkArray1___redArg(v_val_1873_);
v___y_1853_ = v___x_1871_;
v___y_1854_ = v___x_1872_;
v___y_1855_ = v___x_1874_;
goto v___jp_1852_;
}
else
{
lean_object* v___x_1875_; 
lean_dec(v_doc_x3f_1770_);
v___x_1875_ = lean_mk_empty_array_with_capacity(v___x_1765_);
v___y_1853_ = v___x_1871_;
v___y_1854_ = v___x_1872_;
v___y_1855_ = v___x_1875_;
goto v___jp_1852_;
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v_a_1777_);
lean_dec(v_kind_x3f_1771_);
lean_dec(v_doc_x3f_1770_);
lean_dec_ref(v___x_1769_);
lean_dec_ref(v___x_1768_);
lean_dec_ref(v___x_1767_);
lean_dec_ref(v___x_1764_);
lean_dec(v_cat_x3f_1763_);
lean_dec_ref(v___f_1762_);
lean_dec(v_expty_x3f_1761_);
lean_dec(v_attrKind_1760_);
lean_dec(v___x_1759_);
lean_dec(v___x_1758_);
v_a_1879_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1778_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1778_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec(v_kind_x3f_1771_);
lean_dec(v_doc_x3f_1770_);
lean_dec_ref(v___x_1769_);
lean_dec_ref(v___x_1768_);
lean_dec_ref(v___x_1767_);
lean_dec_ref(v___x_1764_);
lean_dec(v_cat_x3f_1763_);
lean_dec_ref(v___f_1762_);
lean_dec(v_expty_x3f_1761_);
lean_dec(v_attrKind_1760_);
lean_dec(v___x_1759_);
lean_dec(v___x_1758_);
v_a_1887_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1776_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1776_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object** _args){
lean_object* v___x_1895_ = _args[0];
lean_object* v___x_1896_ = _args[1];
lean_object* v_attrKind_1897_ = _args[2];
lean_object* v_expty_x3f_1898_ = _args[3];
lean_object* v___f_1899_ = _args[4];
lean_object* v_cat_x3f_1900_ = _args[5];
lean_object* v___x_1901_ = _args[6];
lean_object* v___x_1902_ = _args[7];
lean_object* v_attrs_x3f_1903_ = _args[8];
lean_object* v___x_1904_ = _args[9];
lean_object* v___x_1905_ = _args[10];
lean_object* v___x_1906_ = _args[11];
lean_object* v_doc_x3f_1907_ = _args[12];
lean_object* v_kind_x3f_1908_ = _args[13];
lean_object* v_alts_1909_ = _args[14];
lean_object* v___y_1910_ = _args[15];
lean_object* v___y_1911_ = _args[16];
lean_object* v___y_1912_ = _args[17];
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_Elab_Command_elabElabRules___lam__1(v___x_1895_, v___x_1896_, v_attrKind_1897_, v_expty_x3f_1898_, v___f_1899_, v_cat_x3f_1900_, v___x_1901_, v___x_1902_, v_attrs_x3f_1903_, v___x_1904_, v___x_1905_, v___x_1906_, v_doc_x3f_1907_, v_kind_x3f_1908_, v_alts_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v_alts_1909_);
lean_dec(v_attrs_x3f_1903_);
lean_dec(v___x_1902_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object* v___f_1942_, lean_object* v_stx_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1947_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1948_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1949_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_1950_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
lean_inc(v_stx_1943_);
v___x_1951_ = l_Lean_Syntax_isOfKind(v_stx_1943_, v___x_1950_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; 
lean_dec(v_stx_1943_);
lean_dec_ref(v___f_1942_);
v___x_1952_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_1952_;
}
else
{
lean_object* v___x_1953_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v_expty_x3f_1961_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v_cat_x3f_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v_expty_x3f_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v_cat_x3f_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v_attrs_x3f_2059_; lean_object* v_doc_x3f_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_1953_ = lean_unsigned_to_nat(0u);
v___x_2106_ = l_Lean_Syntax_getArg(v_stx_1943_, v___x_1953_);
v___x_2107_ = l_Lean_Syntax_isNone(v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2108_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2106_);
v___x_2109_ = l_Lean_Syntax_matchesNull(v___x_2106_, v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
lean_dec(v___x_2106_);
lean_dec(v_stx_1943_);
lean_dec_ref(v___f_1942_);
v___x_2110_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2110_;
}
else
{
lean_object* v_doc_x3f_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v_doc_x3f_2111_ = l_Lean_Syntax_getArg(v___x_2106_, v___x_1953_);
lean_dec(v___x_2106_);
v___x_2112_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(v_doc_x3f_2111_);
v___x_2113_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_dec(v_doc_x3f_2111_);
lean_dec(v_stx_1943_);
lean_dec_ref(v___f_1942_);
v___x_2114_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; 
v___x_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2115_, 0, v_doc_x3f_2111_);
v_doc_x3f_2090_ = v___x_2115_;
v___y_2091_ = v___y_1944_;
v___y_2092_ = v___y_1945_;
goto v___jp_2089_;
}
}
}
else
{
lean_object* v___x_2116_; 
lean_dec(v___x_2106_);
v___x_2116_ = lean_box(0);
v_doc_x3f_2090_ = v___x_2116_;
v___y_2091_ = v___y_1944_;
v___y_2092_ = v___y_1945_;
goto v___jp_2089_;
}
v___jp_1954_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1962_ = lean_unsigned_to_nat(7u);
v___x_1963_ = l_Lean_Syntax_getArg(v_stx_1943_, v___x_1962_);
lean_dec(v_stx_1943_);
v___x_1964_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1965_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__2));
lean_inc(v___x_1963_);
v___x_1966_ = l_Lean_Syntax_isOfKind(v___x_1963_, v___x_1965_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; 
lean_dec(v___x_1963_);
lean_dec(v_expty_x3f_1961_);
lean_dec(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___f_1942_);
v___x_1967_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_1967_;
}
else
{
lean_object* v___f_1968_; lean_object* v___x_1969_; lean_object* v_alts_1970_; lean_object* v___x_1971_; 
v___f_1968_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lam__1___boxed), 18, 13);
lean_closure_set(v___f_1968_, 0, v___x_1965_);
lean_closure_set(v___f_1968_, 1, v___x_1950_);
lean_closure_set(v___f_1968_, 2, v___y_1957_);
lean_closure_set(v___f_1968_, 3, v_expty_x3f_1961_);
lean_closure_set(v___f_1968_, 4, v___f_1942_);
lean_closure_set(v___f_1968_, 5, v___y_1956_);
lean_closure_set(v___f_1968_, 6, v___x_1949_);
lean_closure_set(v___f_1968_, 7, v___x_1953_);
lean_closure_set(v___f_1968_, 8, v___y_1959_);
lean_closure_set(v___f_1968_, 9, v___x_1947_);
lean_closure_set(v___f_1968_, 10, v___x_1948_);
lean_closure_set(v___f_1968_, 11, v___x_1964_);
lean_closure_set(v___f_1968_, 12, v___y_1960_);
v___x_1969_ = l_Lean_Syntax_getArg(v___x_1963_, v___x_1953_);
lean_dec(v___x_1963_);
v_alts_1970_ = l_Lean_Syntax_getArgs(v___x_1969_);
lean_dec(v___x_1969_);
v___x_1971_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_1970_, v___x_1949_, v___f_1968_, v___y_1958_, v___y_1955_);
lean_dec_ref(v_alts_1970_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
v_a_1980_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1971_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1971_);
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
lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1997_ = lean_unsigned_to_nat(6u);
v___x_1998_ = l_Lean_Syntax_getArg(v_stx_1943_, v___x_1997_);
v___x_1999_ = l_Lean_Syntax_isNone(v___x_1998_);
if (v___x_1999_ == 0)
{
uint8_t v___x_2000_; 
lean_inc(v___x_1998_);
v___x_2000_ = l_Lean_Syntax_matchesNull(v___x_1998_, v___y_1993_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; 
lean_dec(v___x_1998_);
lean_dec(v_cat_x3f_1994_);
lean_dec(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec(v_stx_1943_);
lean_dec_ref(v___f_1942_);
v___x_2001_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2001_;
}
else
{
lean_object* v_expty_x3f_2002_; lean_object* v___x_2003_; 
v_expty_x3f_2002_ = l_Lean_Syntax_getArg(v___x_1998_, v___y_1992_);
lean_dec(v___x_1998_);
v___x_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_expty_x3f_2002_);
v___y_1955_ = v___y_1996_;
v___y_1956_ = v_cat_x3f_1994_;
v___y_1957_ = v___y_1989_;
v___y_1958_ = v___y_1995_;
v___y_1959_ = v___y_1990_;
v___y_1960_ = v___y_1991_;
v_expty_x3f_1961_ = v___x_2003_;
goto v___jp_1954_;
}
}
else
{
lean_object* v___x_2004_; 
lean_dec(v___x_1998_);
v___x_2004_ = lean_box(0);
v___y_1955_ = v___y_1996_;
v___y_1956_ = v_cat_x3f_1994_;
v___y_1957_ = v___y_1989_;
v___y_1958_ = v___y_1995_;
v___y_1959_ = v___y_1990_;
v___y_1960_ = v___y_1991_;
v_expty_x3f_1961_ = v___x_2004_;
goto v___jp_1954_;
}
}
v___jp_2005_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2015_ = lean_unsigned_to_nat(7u);
v___x_2016_ = l_Lean_Syntax_getArg(v_stx_1943_, v___x_2015_);
lean_dec(v_stx_1943_);
v___x_2017_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(v___y_2008_);
v___x_2018_ = l_Lean_Name_mkStr4(v___x_1947_, v___x_1948_, v___y_2008_, v___x_2017_);
lean_inc(v___x_2016_);
v___x_2019_ = l_Lean_Syntax_isOfKind(v___x_2016_, v___x_2018_);
lean_dec(v___x_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; 
lean_dec(v___x_2016_);
lean_dec(v_expty_x3f_2012_);
lean_dec(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec(v___y_2007_);
lean_dec(v___y_2006_);
v___x_2020_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2020_;
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = l_Lean_TSyntax_getId(v___y_2011_);
lean_dec(v___y_2011_);
v___x_2022_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_2021_, v___y_2013_, v___y_2014_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2024_; lean_object* v_alts_2025_; lean_object* v___x_2026_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref(v___x_2022_);
v___x_2024_ = l_Lean_Syntax_getArg(v___x_2016_, v___x_1953_);
lean_dec(v___x_2016_);
v_alts_2025_ = l_Lean_Syntax_getArgs(v___x_2024_);
lean_dec(v___x_2024_);
v___x_2026_ = l_Lean_Elab_Command_elabElabRulesAux(v___y_2009_, v___y_2006_, v___y_2007_, v_a_2023_, v___y_2010_, v_expty_x3f_2012_, v_alts_2025_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2010_);
lean_dec(v___y_2006_);
return v___x_2026_;
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v___x_2016_);
lean_dec(v_expty_x3f_2012_);
lean_dec(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec(v___y_2007_);
lean_dec(v___y_2006_);
v_a_2027_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2022_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2022_);
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
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
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
}
}
v___jp_2035_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2046_ = lean_unsigned_to_nat(6u);
v___x_2047_ = l_Lean_Syntax_getArg(v_stx_1943_, v___x_2046_);
v___x_2048_ = l_Lean_Syntax_isNone(v___x_2047_);
if (v___x_2048_ == 0)
{
uint8_t v___x_2049_; 
lean_inc(v___x_2047_);
v___x_2049_ = l_Lean_Syntax_matchesNull(v___x_2047_, v___y_2040_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
lean_dec(v___x_2047_);
lean_dec(v_cat_x3f_2043_);
lean_dec(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec(v_stx_1943_);
v___x_2050_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2050_;
}
else
{
lean_object* v_expty_x3f_2051_; lean_object* v___x_2052_; 
v_expty_x3f_2051_ = l_Lean_Syntax_getArg(v___x_2047_, v___y_2036_);
lean_dec(v___x_2047_);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_expty_x3f_2051_);
v___y_2006_ = v___y_2037_;
v___y_2007_ = v___y_2038_;
v___y_2008_ = v___y_2039_;
v___y_2009_ = v___y_2041_;
v___y_2010_ = v_cat_x3f_2043_;
v___y_2011_ = v___y_2042_;
v_expty_x3f_2012_ = v___x_2052_;
v___y_2013_ = v___y_2044_;
v___y_2014_ = v___y_2045_;
goto v___jp_2005_;
}
}
else
{
lean_object* v___x_2053_; 
lean_dec(v___x_2047_);
v___x_2053_ = lean_box(0);
v___y_2006_ = v___y_2037_;
v___y_2007_ = v___y_2038_;
v___y_2008_ = v___y_2039_;
v___y_2009_ = v___y_2041_;
v___y_2010_ = v_cat_x3f_2043_;
v___y_2011_ = v___y_2042_;
v_expty_x3f_2012_ = v___x_2053_;
v___y_2013_ = v___y_2044_;
v___y_2014_ = v___y_2045_;
goto v___jp_2005_;
}
}
v___jp_2054_:
{
lean_object* v___x_2060_; lean_object* v_attrKind_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2060_ = lean_unsigned_to_nat(2u);
v_attrKind_2061_ = l_Lean_Syntax_getArg(v_stx_1943_, v___x_2060_);
v___x_2062_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_2063_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v_attrKind_2061_);
v___x_2064_ = l_Lean_Syntax_isOfKind(v_attrKind_2061_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; 
lean_dec(v_attrKind_2061_);
lean_dec(v_attrs_x3f_2059_);
lean_dec(v___y_2057_);
lean_dec(v_stx_1943_);
lean_dec_ref(v___f_1942_);
v___x_2065_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2065_;
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2066_ = lean_unsigned_to_nat(4u);
v___x_2067_ = l_Lean_Syntax_getArg(v_stx_1943_, v___x_2066_);
lean_inc(v___x_2067_);
v___x_2068_ = l_Lean_Syntax_matchesNull(v___x_2067_, v___x_1953_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; uint8_t v___x_2070_; 
lean_dec_ref(v___f_1942_);
v___x_2069_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2067_);
v___x_2070_ = l_Lean_Syntax_matchesNull(v___x_2067_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; 
lean_dec(v___x_2067_);
lean_dec(v_attrKind_2061_);
lean_dec(v_attrs_x3f_2059_);
lean_dec(v___y_2057_);
lean_dec(v_stx_1943_);
v___x_2071_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2071_;
}
else
{
lean_object* v___x_2072_; lean_object* v_kind_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2072_ = lean_unsigned_to_nat(3u);
v_kind_2073_ = l_Lean_Syntax_getArg(v___x_2067_, v___x_2072_);
lean_dec(v___x_2067_);
v___x_2074_ = l_Lean_Syntax_getArg(v_stx_1943_, v___x_2069_);
v___x_2075_ = l_Lean_Syntax_isNone(v___x_2074_);
if (v___x_2075_ == 0)
{
uint8_t v___x_2076_; 
lean_inc(v___x_2074_);
v___x_2076_ = l_Lean_Syntax_matchesNull(v___x_2074_, v___x_2060_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
lean_dec(v___x_2074_);
lean_dec(v_kind_2073_);
lean_dec(v_attrKind_2061_);
lean_dec(v_attrs_x3f_2059_);
lean_dec(v___y_2057_);
lean_dec(v_stx_1943_);
v___x_2077_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2077_;
}
else
{
lean_object* v_cat_x3f_2078_; lean_object* v___x_2079_; 
v_cat_x3f_2078_ = l_Lean_Syntax_getArg(v___x_2074_, v___y_2058_);
lean_dec(v___x_2074_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v_cat_x3f_2078_);
v___y_2036_ = v___y_2058_;
v___y_2037_ = v_attrs_x3f_2059_;
v___y_2038_ = v_attrKind_2061_;
v___y_2039_ = v___x_2062_;
v___y_2040_ = v___x_2060_;
v___y_2041_ = v___y_2057_;
v___y_2042_ = v_kind_2073_;
v_cat_x3f_2043_ = v___x_2079_;
v___y_2044_ = v___y_2056_;
v___y_2045_ = v___y_2055_;
goto v___jp_2035_;
}
}
else
{
lean_object* v___x_2080_; 
lean_dec(v___x_2074_);
v___x_2080_ = lean_box(0);
v___y_2036_ = v___y_2058_;
v___y_2037_ = v_attrs_x3f_2059_;
v___y_2038_ = v_attrKind_2061_;
v___y_2039_ = v___x_2062_;
v___y_2040_ = v___x_2060_;
v___y_2041_ = v___y_2057_;
v___y_2042_ = v_kind_2073_;
v_cat_x3f_2043_ = v___x_2080_;
v___y_2044_ = v___y_2056_;
v___y_2045_ = v___y_2055_;
goto v___jp_2035_;
}
}
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
lean_dec(v___x_2067_);
v___x_2081_ = lean_unsigned_to_nat(5u);
v___x_2082_ = l_Lean_Syntax_getArg(v_stx_1943_, v___x_2081_);
v___x_2083_ = l_Lean_Syntax_isNone(v___x_2082_);
if (v___x_2083_ == 0)
{
uint8_t v___x_2084_; 
lean_inc(v___x_2082_);
v___x_2084_ = l_Lean_Syntax_matchesNull(v___x_2082_, v___x_2060_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
lean_dec(v___x_2082_);
lean_dec(v_attrKind_2061_);
lean_dec(v_attrs_x3f_2059_);
lean_dec(v___y_2057_);
lean_dec(v_stx_1943_);
lean_dec_ref(v___f_1942_);
v___x_2085_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2085_;
}
else
{
lean_object* v_cat_x3f_2086_; lean_object* v___x_2087_; 
v_cat_x3f_2086_ = l_Lean_Syntax_getArg(v___x_2082_, v___y_2058_);
lean_dec(v___x_2082_);
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v_cat_x3f_2086_);
v___y_1989_ = v_attrKind_2061_;
v___y_1990_ = v_attrs_x3f_2059_;
v___y_1991_ = v___y_2057_;
v___y_1992_ = v___y_2058_;
v___y_1993_ = v___x_2060_;
v_cat_x3f_1994_ = v___x_2087_;
v___y_1995_ = v___y_2056_;
v___y_1996_ = v___y_2055_;
goto v___jp_1988_;
}
}
else
{
lean_object* v___x_2088_; 
lean_dec(v___x_2082_);
v___x_2088_ = lean_box(0);
v___y_1989_ = v_attrKind_2061_;
v___y_1990_ = v_attrs_x3f_2059_;
v___y_1991_ = v___y_2057_;
v___y_1992_ = v___y_2058_;
v___y_1993_ = v___x_2060_;
v_cat_x3f_1994_ = v___x_2088_;
v___y_1995_ = v___y_2056_;
v___y_1996_ = v___y_2055_;
goto v___jp_1988_;
}
}
}
}
v___jp_2089_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2093_ = lean_unsigned_to_nat(1u);
v___x_2094_ = l_Lean_Syntax_getArg(v_stx_1943_, v___x_2093_);
v___x_2095_ = l_Lean_Syntax_isNone(v___x_2094_);
if (v___x_2095_ == 0)
{
uint8_t v___x_2096_; 
lean_inc(v___x_2094_);
v___x_2096_ = l_Lean_Syntax_matchesNull(v___x_2094_, v___x_2093_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
lean_dec(v___x_2094_);
lean_dec(v_doc_x3f_2090_);
lean_dec(v_stx_1943_);
lean_dec_ref(v___f_1942_);
v___x_2097_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2097_;
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
v___x_2098_ = l_Lean_Syntax_getArg(v___x_2094_, v___x_1953_);
lean_dec(v___x_2094_);
v___x_2099_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(v___x_2098_);
v___x_2100_ = l_Lean_Syntax_isOfKind(v___x_2098_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; 
lean_dec(v___x_2098_);
lean_dec(v_doc_x3f_2090_);
lean_dec(v_stx_1943_);
lean_dec_ref(v___f_1942_);
v___x_2101_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2101_;
}
else
{
lean_object* v___x_2102_; lean_object* v_attrs_x3f_2103_; lean_object* v___x_2104_; 
v___x_2102_ = l_Lean_Syntax_getArg(v___x_2098_, v___x_2093_);
lean_dec(v___x_2098_);
v_attrs_x3f_2103_ = l_Lean_Syntax_getArgs(v___x_2102_);
lean_dec(v___x_2102_);
v___x_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2104_, 0, v_attrs_x3f_2103_);
v___y_2055_ = v___y_2092_;
v___y_2056_ = v___y_2091_;
v___y_2057_ = v_doc_x3f_2090_;
v___y_2058_ = v___x_2093_;
v_attrs_x3f_2059_ = v___x_2104_;
goto v___jp_2054_;
}
}
}
else
{
lean_object* v___x_2105_; 
lean_dec(v___x_2094_);
v___x_2105_ = lean_box(0);
v___y_2055_ = v___y_2092_;
v___y_2056_ = v___y_2091_;
v___y_2057_ = v_doc_x3f_2090_;
v___y_2058_ = v___x_2093_;
v_attrs_x3f_2059_ = v___x_2105_;
goto v___jp_2054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object* v___f_2117_, lean_object* v_stx_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_Elab_Command_elabElabRules___lam__2(v___f_2117_, v_stx_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v___f_2130_; lean_object* v___x_2131_; 
v___f_2130_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___closed__1));
v___x_2131_ = l_Lean_Elab_Command_adaptExpander(v___f_2130_, v_a_2126_, v_a_2127_, v_a_2128_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_Elab_Command_elabElabRules(v_a_2132_, v_a_2133_, v_a_2134_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1(){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2144_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2145_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
v___x_2146_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2147_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___boxed), 4, 0);
v___x_2148_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2144_, v___x_2145_, v___x_2146_, v___x_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object* v_a_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3(){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2178_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6));
v___x_2179_ = l_Lean_addBuiltinDeclarationRanges(v___x_2177_, v___x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object* v_a_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t v_sz_2182_, size_t v_i_2183_, lean_object* v_bs_2184_){
_start:
{
uint8_t v___x_2185_; 
v___x_2185_ = lean_usize_dec_lt(v_i_2183_, v_sz_2182_);
if (v___x_2185_ == 0)
{
return v_bs_2184_;
}
else
{
lean_object* v_v_2186_; lean_object* v___x_2187_; lean_object* v_bs_x27_2188_; size_t v___x_2189_; size_t v___x_2190_; lean_object* v___x_2191_; 
v_v_2186_ = lean_array_uget(v_bs_2184_, v_i_2183_);
v___x_2187_ = lean_unsigned_to_nat(0u);
v_bs_x27_2188_ = lean_array_uset(v_bs_2184_, v_i_2183_, v___x_2187_);
v___x_2189_ = ((size_t)1ULL);
v___x_2190_ = lean_usize_add(v_i_2183_, v___x_2189_);
v___x_2191_ = lean_array_uset(v_bs_x27_2188_, v_i_2183_, v_v_2186_);
v_i_2183_ = v___x_2190_;
v_bs_2184_ = v___x_2191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object* v_sz_2193_, lean_object* v_i_2194_, lean_object* v_bs_2195_){
_start:
{
size_t v_sz_boxed_2196_; size_t v_i_boxed_2197_; lean_object* v_res_2198_; 
v_sz_boxed_2196_ = lean_unbox_usize(v_sz_2193_);
lean_dec(v_sz_2193_);
v_i_boxed_2197_ = lean_unbox_usize(v_i_2194_);
lean_dec(v_i_2194_);
v_res_2198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_boxed_2196_, v_i_boxed_2197_, v_bs_2195_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t v_sz_2199_, size_t v_i_2200_, lean_object* v_bs_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
uint8_t v___x_2205_; 
v___x_2205_ = lean_usize_dec_lt(v_i_2200_, v_sz_2199_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v_bs_2201_);
return v___x_2206_;
}
else
{
lean_object* v_v_2207_; lean_object* v___x_2208_; 
v_v_2207_ = lean_array_uget_borrowed(v_bs_2201_, v_i_2200_);
lean_inc(v_v_2207_);
v___x_2208_ = l_Lean_Elab_Command_expandMacroArg(v_v_2207_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2210_; lean_object* v_bs_x27_2211_; size_t v___x_2212_; size_t v___x_2213_; lean_object* v___x_2214_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref(v___x_2208_);
v___x_2210_ = lean_unsigned_to_nat(0u);
v_bs_x27_2211_ = lean_array_uset(v_bs_2201_, v_i_2200_, v___x_2210_);
v___x_2212_ = ((size_t)1ULL);
v___x_2213_ = lean_usize_add(v_i_2200_, v___x_2212_);
v___x_2214_ = lean_array_uset(v_bs_x27_2211_, v_i_2200_, v_a_2209_);
v_i_2200_ = v___x_2213_;
v_bs_2201_ = v___x_2214_;
goto _start;
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec_ref(v_bs_2201_);
v_a_2216_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2208_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2208_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object* v_sz_2224_, lean_object* v_i_2225_, lean_object* v_bs_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
size_t v_sz_boxed_2230_; size_t v_i_boxed_2231_; lean_object* v_res_2232_; 
v_sz_boxed_2230_ = lean_unbox_usize(v_sz_2224_);
lean_dec(v_sz_2224_);
v_i_boxed_2231_ = lean_unbox_usize(v_i_2225_);
lean_dec(v_i_2225_);
v_res_2232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_boxed_2230_, v_i_boxed_2231_, v_bs_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
return v_res_2232_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(lean_object* v_keys_2233_, lean_object* v_i_2234_, lean_object* v_k_2235_){
_start:
{
lean_object* v___x_2236_; uint8_t v___x_2237_; 
v___x_2236_ = lean_array_get_size(v_keys_2233_);
v___x_2237_ = lean_nat_dec_lt(v_i_2234_, v___x_2236_);
if (v___x_2237_ == 0)
{
lean_dec(v_i_2234_);
return v___x_2237_;
}
else
{
lean_object* v_k_x27_2238_; uint8_t v___x_2239_; 
v_k_x27_2238_ = lean_array_fget_borrowed(v_keys_2233_, v_i_2234_);
v___x_2239_ = l_Lean_instBEqExtraModUse_beq(v_k_2235_, v_k_x27_2238_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = lean_unsigned_to_nat(1u);
v___x_2241_ = lean_nat_add(v_i_2234_, v___x_2240_);
lean_dec(v_i_2234_);
v_i_2234_ = v___x_2241_;
goto _start;
}
else
{
lean_dec(v_i_2234_);
return v___x_2239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_keys_2243_, lean_object* v_i_2244_, lean_object* v_k_2245_){
_start:
{
uint8_t v_res_2246_; lean_object* v_r_2247_; 
v_res_2246_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_2243_, v_i_2244_, v_k_2245_);
lean_dec_ref(v_k_2245_);
lean_dec_ref(v_keys_2243_);
v_r_2247_ = lean_box(v_res_2246_);
return v_r_2247_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__0(void){
_start:
{
size_t v___x_2248_; size_t v___x_2249_; size_t v___x_2250_; 
v___x_2248_ = ((size_t)5ULL);
v___x_2249_ = ((size_t)1ULL);
v___x_2250_ = lean_usize_shift_left(v___x_2249_, v___x_2248_);
return v___x_2250_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__1(void){
_start:
{
size_t v___x_2251_; size_t v___x_2252_; size_t v___x_2253_; 
v___x_2251_ = ((size_t)1ULL);
v___x_2252_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__0);
v___x_2253_ = lean_usize_sub(v___x_2252_, v___x_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(lean_object* v_x_2254_, size_t v_x_2255_, lean_object* v_x_2256_){
_start:
{
if (lean_obj_tag(v_x_2254_) == 0)
{
lean_object* v_es_2257_; lean_object* v___x_2258_; size_t v___x_2259_; size_t v___x_2260_; size_t v___x_2261_; lean_object* v_j_2262_; lean_object* v___x_2263_; 
v_es_2257_ = lean_ctor_get(v_x_2254_, 0);
v___x_2258_ = lean_box(2);
v___x_2259_ = ((size_t)5ULL);
v___x_2260_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__1);
v___x_2261_ = lean_usize_land(v_x_2255_, v___x_2260_);
v_j_2262_ = lean_usize_to_nat(v___x_2261_);
v___x_2263_ = lean_array_get_borrowed(v___x_2258_, v_es_2257_, v_j_2262_);
lean_dec(v_j_2262_);
switch(lean_obj_tag(v___x_2263_))
{
case 0:
{
lean_object* v_key_2264_; uint8_t v___x_2265_; 
v_key_2264_ = lean_ctor_get(v___x_2263_, 0);
v___x_2265_ = l_Lean_instBEqExtraModUse_beq(v_x_2256_, v_key_2264_);
return v___x_2265_;
}
case 1:
{
lean_object* v_node_2266_; size_t v___x_2267_; 
v_node_2266_ = lean_ctor_get(v___x_2263_, 0);
v___x_2267_ = lean_usize_shift_right(v_x_2255_, v___x_2259_);
v_x_2254_ = v_node_2266_;
v_x_2255_ = v___x_2267_;
goto _start;
}
default: 
{
uint8_t v___x_2269_; 
v___x_2269_ = 0;
return v___x_2269_;
}
}
}
else
{
lean_object* v_ks_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v_ks_2270_ = lean_ctor_get(v_x_2254_, 0);
v___x_2271_ = lean_unsigned_to_nat(0u);
v___x_2272_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_ks_2270_, v___x_2271_, v_x_2256_);
return v___x_2272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_x_2273_, lean_object* v_x_2274_, lean_object* v_x_2275_){
_start:
{
size_t v_x_19498__boxed_2276_; uint8_t v_res_2277_; lean_object* v_r_2278_; 
v_x_19498__boxed_2276_ = lean_unbox_usize(v_x_2274_);
lean_dec(v_x_2274_);
v_res_2277_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2273_, v_x_19498__boxed_2276_, v_x_2275_);
lean_dec_ref(v_x_2275_);
lean_dec_ref(v_x_2273_);
v_r_2278_ = lean_box(v_res_2277_);
return v_r_2278_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(lean_object* v_x_2279_, lean_object* v_x_2280_){
_start:
{
uint64_t v___x_2281_; size_t v___x_2282_; uint8_t v___x_2283_; 
v___x_2281_ = l_Lean_instHashableExtraModUse_hash(v_x_2280_);
v___x_2282_ = lean_uint64_to_usize(v___x_2281_);
v___x_2283_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2279_, v___x_2282_, v_x_2280_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_x_2284_, lean_object* v_x_2285_){
_start:
{
uint8_t v_res_2286_; lean_object* v_r_2287_; 
v_res_2286_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_2284_, v_x_2285_);
lean_dec_ref(v_x_2285_);
lean_dec_ref(v_x_2284_);
v_r_2287_ = lean_box(v_res_2286_);
return v_r_2287_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2288_; double v___x_2289_; 
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = lean_float_of_nat(v___x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object* v_cls_2293_, lean_object* v_msg_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_Elab_Command_getRef___redArg(v___y_2295_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2300_; lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2348_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref(v___x_2298_);
v___x_2300_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_2294_, v___y_2296_);
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2348_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2348_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; lean_object* v_traceState_2306_; lean_object* v_env_2307_; lean_object* v_messages_2308_; lean_object* v_scopes_2309_; lean_object* v_usedQuotCtxts_2310_; lean_object* v_nextMacroScope_2311_; lean_object* v_maxRecDepth_2312_; lean_object* v_ngen_2313_; lean_object* v_auxDeclNGen_2314_; lean_object* v_infoState_2315_; lean_object* v_snapshotTasks_2316_; lean_object* v_newDecls_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2347_; 
v___x_2305_ = lean_st_ref_take(v___y_2296_);
v_traceState_2306_ = lean_ctor_get(v___x_2305_, 9);
v_env_2307_ = lean_ctor_get(v___x_2305_, 0);
v_messages_2308_ = lean_ctor_get(v___x_2305_, 1);
v_scopes_2309_ = lean_ctor_get(v___x_2305_, 2);
v_usedQuotCtxts_2310_ = lean_ctor_get(v___x_2305_, 3);
v_nextMacroScope_2311_ = lean_ctor_get(v___x_2305_, 4);
v_maxRecDepth_2312_ = lean_ctor_get(v___x_2305_, 5);
v_ngen_2313_ = lean_ctor_get(v___x_2305_, 6);
v_auxDeclNGen_2314_ = lean_ctor_get(v___x_2305_, 7);
v_infoState_2315_ = lean_ctor_get(v___x_2305_, 8);
v_snapshotTasks_2316_ = lean_ctor_get(v___x_2305_, 10);
v_newDecls_2317_ = lean_ctor_get(v___x_2305_, 11);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2319_ = v___x_2305_;
v_isShared_2320_ = v_isSharedCheck_2347_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_newDecls_2317_);
lean_inc(v_snapshotTasks_2316_);
lean_inc(v_traceState_2306_);
lean_inc(v_infoState_2315_);
lean_inc(v_auxDeclNGen_2314_);
lean_inc(v_ngen_2313_);
lean_inc(v_maxRecDepth_2312_);
lean_inc(v_nextMacroScope_2311_);
lean_inc(v_usedQuotCtxts_2310_);
lean_inc(v_scopes_2309_);
lean_inc(v_messages_2308_);
lean_inc(v_env_2307_);
lean_dec(v___x_2305_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2347_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
uint64_t v_tid_2321_; lean_object* v_traces_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2346_; 
v_tid_2321_ = lean_ctor_get_uint64(v_traceState_2306_, sizeof(void*)*1);
v_traces_2322_ = lean_ctor_get(v_traceState_2306_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_traceState_2306_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2324_ = v_traceState_2306_;
v_isShared_2325_ = v_isSharedCheck_2346_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_traces_2322_);
lean_dec(v_traceState_2306_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2346_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; double v___x_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2326_ = lean_box(0);
v___x_2327_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0);
v___x_2328_ = 0;
v___x_2329_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2330_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2330_, 0, v_cls_2293_);
lean_ctor_set(v___x_2330_, 1, v___x_2326_);
lean_ctor_set(v___x_2330_, 2, v___x_2329_);
lean_ctor_set_float(v___x_2330_, sizeof(void*)*3, v___x_2327_);
lean_ctor_set_float(v___x_2330_, sizeof(void*)*3 + 8, v___x_2327_);
lean_ctor_set_uint8(v___x_2330_, sizeof(void*)*3 + 16, v___x_2328_);
v___x_2331_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2));
v___x_2332_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v_a_2301_);
lean_ctor_set(v___x_2332_, 2, v___x_2331_);
v___x_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2333_, 0, v_a_2299_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = l_Lean_PersistentArray_push___redArg(v_traces_2322_, v___x_2333_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2334_);
v___x_2336_ = v___x_2324_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2334_);
lean_ctor_set_uint64(v_reuseFailAlloc_2345_, sizeof(void*)*1, v_tid_2321_);
v___x_2336_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2338_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 9, v___x_2336_);
v___x_2338_ = v___x_2319_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_env_2307_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_messages_2308_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_scopes_2309_);
lean_ctor_set(v_reuseFailAlloc_2344_, 3, v_usedQuotCtxts_2310_);
lean_ctor_set(v_reuseFailAlloc_2344_, 4, v_nextMacroScope_2311_);
lean_ctor_set(v_reuseFailAlloc_2344_, 5, v_maxRecDepth_2312_);
lean_ctor_set(v_reuseFailAlloc_2344_, 6, v_ngen_2313_);
lean_ctor_set(v_reuseFailAlloc_2344_, 7, v_auxDeclNGen_2314_);
lean_ctor_set(v_reuseFailAlloc_2344_, 8, v_infoState_2315_);
lean_ctor_set(v_reuseFailAlloc_2344_, 9, v___x_2336_);
lean_ctor_set(v_reuseFailAlloc_2344_, 10, v_snapshotTasks_2316_);
lean_ctor_set(v_reuseFailAlloc_2344_, 11, v_newDecls_2317_);
v___x_2338_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2339_ = lean_st_ref_set(v___y_2296_, v___x_2338_);
v___x_2340_ = lean_box(0);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2340_);
v___x_2342_ = v___x_2303_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2340_);
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
lean_dec_ref(v_msg_2294_);
lean_dec(v_cls_2293_);
v_a_2349_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2298_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2298_);
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
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1));
v___x_2366_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0));
v___x_2367_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2366_, v___x_2365_);
return v___x_2367_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5));
v___x_2373_ = l_Lean_stringToMessageData(v___x_2372_);
return v___x_2373_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7));
v___x_2376_ = l_Lean_stringToMessageData(v___x_2375_);
return v___x_2376_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2378_ = l_Lean_stringToMessageData(v___x_2377_);
return v___x_2378_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v_cls_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_cls_2382_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4));
v___x_2383_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11));
v___x_2384_ = l_Lean_Name_append(v___x_2383_, v_cls_2382_);
return v___x_2384_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13));
v___x_2387_ = l_Lean_stringToMessageData(v___x_2386_);
return v___x_2387_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15));
v___x_2390_ = l_Lean_stringToMessageData(v___x_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(lean_object* v_mod_2395_, uint8_t v_isMeta_2396_, lean_object* v_hint_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v___x_2401_; lean_object* v_env_2402_; uint8_t v_isExporting_2403_; lean_object* v___x_2404_; lean_object* v_env_2405_; lean_object* v___x_2406_; lean_object* v_entry_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___y_2412_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2401_ = lean_st_ref_get(v___y_2399_);
v_env_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc_ref(v_env_2402_);
lean_dec(v___x_2401_);
v_isExporting_2403_ = lean_ctor_get_uint8(v_env_2402_, sizeof(void*)*8);
lean_dec_ref(v_env_2402_);
v___x_2404_ = lean_st_ref_get(v___y_2399_);
v_env_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc_ref(v_env_2405_);
lean_dec(v___x_2404_);
v___x_2406_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2);
lean_inc(v_mod_2395_);
v_entry_2407_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2407_, 0, v_mod_2395_);
lean_ctor_set_uint8(v_entry_2407_, sizeof(void*)*1, v_isExporting_2403_);
lean_ctor_set_uint8(v_entry_2407_, sizeof(void*)*1 + 1, v_isMeta_2396_);
v___x_2408_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2409_ = lean_box(1);
v___x_2410_ = lean_box(0);
v___x_2439_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2406_, v___x_2408_, v_env_2405_, v___x_2409_, v___x_2410_);
v___x_2440_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v___x_2439_, v_entry_2407_);
lean_dec(v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_scopes_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_opts_2447_; uint8_t v_hasTrace_2448_; 
v___x_2441_ = l_Lean_inheritedTraceOptions;
v___x_2442_ = lean_st_ref_get(v___x_2441_);
v___x_2443_ = lean_st_ref_get(v___y_2399_);
v_scopes_2444_ = lean_ctor_get(v___x_2443_, 2);
lean_inc(v_scopes_2444_);
lean_dec(v___x_2443_);
v___x_2445_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2446_ = l_List_head_x21___redArg(v___x_2445_, v_scopes_2444_);
lean_dec(v_scopes_2444_);
v_opts_2447_ = lean_ctor_get(v___x_2446_, 1);
lean_inc_ref(v_opts_2447_);
lean_dec(v___x_2446_);
v_hasTrace_2448_ = lean_ctor_get_uint8(v_opts_2447_, sizeof(void*)*1);
if (v_hasTrace_2448_ == 0)
{
lean_dec_ref(v_opts_2447_);
lean_dec(v___x_2442_);
lean_dec(v_hint_2397_);
lean_dec(v_mod_2395_);
v___y_2412_ = v___y_2399_;
goto v___jp_2411_;
}
else
{
lean_object* v_cls_2449_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v_cls_2449_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4));
v___x_2469_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12);
v___x_2470_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2442_, v_opts_2447_, v___x_2469_);
lean_dec_ref(v_opts_2447_);
lean_dec(v___x_2442_);
if (v___x_2470_ == 0)
{
lean_dec(v_hint_2397_);
lean_dec(v_mod_2395_);
v___y_2412_ = v___y_2399_;
goto v___jp_2411_;
}
else
{
lean_object* v___x_2471_; lean_object* v___y_2473_; 
v___x_2471_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14);
if (v_isExporting_2403_ == 0)
{
lean_object* v___x_2480_; 
v___x_2480_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__19));
v___y_2473_ = v___x_2480_;
goto v___jp_2472_;
}
else
{
lean_object* v___x_2481_; 
v___x_2481_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__20));
v___y_2473_ = v___x_2481_;
goto v___jp_2472_;
}
v___jp_2472_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_inc_ref(v___y_2473_);
v___x_2474_ = l_Lean_stringToMessageData(v___y_2473_);
v___x_2475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2471_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16);
v___x_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2475_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
if (v_isMeta_2396_ == 0)
{
lean_object* v___x_2478_; 
v___x_2478_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17));
v___y_2456_ = v___x_2477_;
v___y_2457_ = v___x_2478_;
goto v___jp_2455_;
}
else
{
lean_object* v___x_2479_; 
v___x_2479_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18));
v___y_2456_ = v___x_2477_;
v___y_2457_ = v___x_2479_;
goto v___jp_2455_;
}
}
}
v___jp_2450_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___y_2451_);
lean_ctor_set(v___x_2453_, 1, v___y_2452_);
v___x_2454_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2449_, v___x_2453_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_dec_ref(v___x_2454_);
v___y_2412_ = v___y_2399_;
goto v___jp_2411_;
}
else
{
lean_dec_ref(v_entry_2407_);
return v___x_2454_;
}
}
v___jp_2455_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
lean_inc_ref(v___y_2457_);
v___x_2458_ = l_Lean_stringToMessageData(v___y_2457_);
v___x_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___y_2456_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6);
v___x_2461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = l_Lean_MessageData_ofName(v_mod_2395_);
v___x_2463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = l_Lean_Name_isAnonymous(v_hint_2397_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8);
v___x_2466_ = l_Lean_MessageData_ofName(v_hint_2397_);
v___x_2467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2465_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___y_2451_ = v___x_2463_;
v___y_2452_ = v___x_2467_;
goto v___jp_2450_;
}
else
{
lean_object* v___x_2468_; 
lean_dec(v_hint_2397_);
v___x_2468_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9);
v___y_2451_ = v___x_2463_;
v___y_2452_ = v___x_2468_;
goto v___jp_2450_;
}
}
}
}
else
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec_ref(v_entry_2407_);
lean_dec(v_hint_2397_);
lean_dec(v_mod_2395_);
v___x_2482_ = lean_box(0);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
return v___x_2483_;
}
v___jp_2411_:
{
lean_object* v___x_2413_; lean_object* v_toEnvExtension_2414_; lean_object* v_env_2415_; lean_object* v_messages_2416_; lean_object* v_scopes_2417_; lean_object* v_usedQuotCtxts_2418_; lean_object* v_nextMacroScope_2419_; lean_object* v_maxRecDepth_2420_; lean_object* v_ngen_2421_; lean_object* v_auxDeclNGen_2422_; lean_object* v_infoState_2423_; lean_object* v_traceState_2424_; lean_object* v_snapshotTasks_2425_; lean_object* v_newDecls_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2438_; 
v___x_2413_ = lean_st_ref_take(v___y_2412_);
v_toEnvExtension_2414_ = lean_ctor_get(v___x_2408_, 0);
v_env_2415_ = lean_ctor_get(v___x_2413_, 0);
v_messages_2416_ = lean_ctor_get(v___x_2413_, 1);
v_scopes_2417_ = lean_ctor_get(v___x_2413_, 2);
v_usedQuotCtxts_2418_ = lean_ctor_get(v___x_2413_, 3);
v_nextMacroScope_2419_ = lean_ctor_get(v___x_2413_, 4);
v_maxRecDepth_2420_ = lean_ctor_get(v___x_2413_, 5);
v_ngen_2421_ = lean_ctor_get(v___x_2413_, 6);
v_auxDeclNGen_2422_ = lean_ctor_get(v___x_2413_, 7);
v_infoState_2423_ = lean_ctor_get(v___x_2413_, 8);
v_traceState_2424_ = lean_ctor_get(v___x_2413_, 9);
v_snapshotTasks_2425_ = lean_ctor_get(v___x_2413_, 10);
v_newDecls_2426_ = lean_ctor_get(v___x_2413_, 11);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2428_ = v___x_2413_;
v_isShared_2429_ = v_isSharedCheck_2438_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_newDecls_2426_);
lean_inc(v_snapshotTasks_2425_);
lean_inc(v_traceState_2424_);
lean_inc(v_infoState_2423_);
lean_inc(v_auxDeclNGen_2422_);
lean_inc(v_ngen_2421_);
lean_inc(v_maxRecDepth_2420_);
lean_inc(v_nextMacroScope_2419_);
lean_inc(v_usedQuotCtxts_2418_);
lean_inc(v_scopes_2417_);
lean_inc(v_messages_2416_);
lean_inc(v_env_2415_);
lean_dec(v___x_2413_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2438_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v_asyncMode_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v_asyncMode_2430_ = lean_ctor_get(v_toEnvExtension_2414_, 2);
v___x_2431_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2408_, v_env_2415_, v_entry_2407_, v_asyncMode_2430_, v___x_2410_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2431_);
v___x_2433_ = v___x_2428_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_messages_2416_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v_scopes_2417_);
lean_ctor_set(v_reuseFailAlloc_2437_, 3, v_usedQuotCtxts_2418_);
lean_ctor_set(v_reuseFailAlloc_2437_, 4, v_nextMacroScope_2419_);
lean_ctor_set(v_reuseFailAlloc_2437_, 5, v_maxRecDepth_2420_);
lean_ctor_set(v_reuseFailAlloc_2437_, 6, v_ngen_2421_);
lean_ctor_set(v_reuseFailAlloc_2437_, 7, v_auxDeclNGen_2422_);
lean_ctor_set(v_reuseFailAlloc_2437_, 8, v_infoState_2423_);
lean_ctor_set(v_reuseFailAlloc_2437_, 9, v_traceState_2424_);
lean_ctor_set(v_reuseFailAlloc_2437_, 10, v_snapshotTasks_2425_);
lean_ctor_set(v_reuseFailAlloc_2437_, 11, v_newDecls_2426_);
v___x_2433_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = lean_st_ref_set(v___y_2412_, v___x_2433_);
v___x_2435_ = lean_box(0);
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
return v___x_2436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___boxed(lean_object* v_mod_2484_, lean_object* v_isMeta_2485_, lean_object* v_hint_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
uint8_t v_isMeta_boxed_2490_; lean_object* v_res_2491_; 
v_isMeta_boxed_2490_ = lean_unbox(v_isMeta_2485_);
v_res_2491_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_mod_2484_, v_isMeta_boxed_2490_, v_hint_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(lean_object* v___x_2492_, lean_object* v_declName_2493_, lean_object* v_as_2494_, size_t v_sz_2495_, size_t v_i_2496_, lean_object* v_b_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
uint8_t v___x_2501_; 
v___x_2501_ = lean_usize_dec_lt(v_i_2496_, v_sz_2495_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; 
lean_dec(v_declName_2493_);
v___x_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2502_, 0, v_b_2497_);
return v___x_2502_;
}
else
{
lean_object* v___x_2503_; lean_object* v_modules_2504_; lean_object* v___x_2505_; lean_object* v_a_2506_; lean_object* v___x_2507_; lean_object* v_toImport_2508_; lean_object* v_module_2509_; uint8_t v___x_2510_; lean_object* v___x_2511_; 
v___x_2503_ = l_Lean_Environment_header(v___x_2492_);
v_modules_2504_ = lean_ctor_get(v___x_2503_, 3);
lean_inc_ref(v_modules_2504_);
lean_dec_ref(v___x_2503_);
v___x_2505_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2506_ = lean_array_uget_borrowed(v_as_2494_, v_i_2496_);
v___x_2507_ = lean_array_get(v___x_2505_, v_modules_2504_, v_a_2506_);
lean_dec_ref(v_modules_2504_);
v_toImport_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc_ref(v_toImport_2508_);
lean_dec(v___x_2507_);
v_module_2509_ = lean_ctor_get(v_toImport_2508_, 0);
lean_inc(v_module_2509_);
lean_dec_ref(v_toImport_2508_);
v___x_2510_ = 0;
lean_inc(v_declName_2493_);
v___x_2511_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2509_, v___x_2510_, v_declName_2493_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v___x_2512_; size_t v___x_2513_; size_t v___x_2514_; 
lean_dec_ref(v___x_2511_);
v___x_2512_ = lean_box(0);
v___x_2513_ = ((size_t)1ULL);
v___x_2514_ = lean_usize_add(v_i_2496_, v___x_2513_);
v_i_2496_ = v___x_2514_;
v_b_2497_ = v___x_2512_;
goto _start;
}
else
{
lean_dec(v_declName_2493_);
return v___x_2511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4___boxed(lean_object* v___x_2516_, lean_object* v_declName_2517_, lean_object* v_as_2518_, lean_object* v_sz_2519_, lean_object* v_i_2520_, lean_object* v_b_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
size_t v_sz_boxed_2525_; size_t v_i_boxed_2526_; lean_object* v_res_2527_; 
v_sz_boxed_2525_ = lean_unbox_usize(v_sz_2519_);
lean_dec(v_sz_2519_);
v_i_boxed_2526_ = lean_unbox_usize(v_i_2520_);
lean_dec(v_i_2520_);
v_res_2527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v___x_2516_, v_declName_2517_, v_as_2518_, v_sz_boxed_2525_, v_i_boxed_2526_, v_b_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec_ref(v_as_2518_);
lean_dec_ref(v___x_2516_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(lean_object* v_a_2528_, lean_object* v_x_2529_){
_start:
{
if (lean_obj_tag(v_x_2529_) == 0)
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_box(0);
return v___x_2530_;
}
else
{
lean_object* v_key_2531_; lean_object* v_value_2532_; lean_object* v_tail_2533_; uint8_t v___x_2534_; 
v_key_2531_ = lean_ctor_get(v_x_2529_, 0);
v_value_2532_ = lean_ctor_get(v_x_2529_, 1);
v_tail_2533_ = lean_ctor_get(v_x_2529_, 2);
v___x_2534_ = lean_name_eq(v_key_2531_, v_a_2528_);
if (v___x_2534_ == 0)
{
v_x_2529_ = v_tail_2533_;
goto _start;
}
else
{
lean_object* v___x_2536_; 
lean_inc(v_value_2532_);
v___x_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2536_, 0, v_value_2532_);
return v___x_2536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_a_2537_, lean_object* v_x_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2537_, v_x_2538_);
lean_dec(v_x_2538_);
lean_dec(v_a_2537_);
return v_res_2539_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2540_; uint64_t v___x_2541_; 
v___x_2540_ = lean_unsigned_to_nat(1723u);
v___x_2541_ = lean_uint64_of_nat(v___x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(lean_object* v_m_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v_buckets_2544_; lean_object* v___x_2545_; uint64_t v___y_2547_; 
v_buckets_2544_ = lean_ctor_get(v_m_2542_, 1);
v___x_2545_ = lean_array_get_size(v_buckets_2544_);
if (lean_obj_tag(v_a_2543_) == 0)
{
uint64_t v___x_2561_; 
v___x_2561_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0);
v___y_2547_ = v___x_2561_;
goto v___jp_2546_;
}
else
{
uint64_t v_hash_2562_; 
v_hash_2562_ = lean_ctor_get_uint64(v_a_2543_, sizeof(void*)*2);
v___y_2547_ = v_hash_2562_;
goto v___jp_2546_;
}
v___jp_2546_:
{
uint64_t v___x_2548_; uint64_t v___x_2549_; uint64_t v_fold_2550_; uint64_t v___x_2551_; uint64_t v___x_2552_; uint64_t v___x_2553_; size_t v___x_2554_; size_t v___x_2555_; size_t v___x_2556_; size_t v___x_2557_; size_t v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2548_ = 32ULL;
v___x_2549_ = lean_uint64_shift_right(v___y_2547_, v___x_2548_);
v_fold_2550_ = lean_uint64_xor(v___y_2547_, v___x_2549_);
v___x_2551_ = 16ULL;
v___x_2552_ = lean_uint64_shift_right(v_fold_2550_, v___x_2551_);
v___x_2553_ = lean_uint64_xor(v_fold_2550_, v___x_2552_);
v___x_2554_ = lean_uint64_to_usize(v___x_2553_);
v___x_2555_ = lean_usize_of_nat(v___x_2545_);
v___x_2556_ = ((size_t)1ULL);
v___x_2557_ = lean_usize_sub(v___x_2555_, v___x_2556_);
v___x_2558_ = lean_usize_land(v___x_2554_, v___x_2557_);
v___x_2559_ = lean_array_uget_borrowed(v_buckets_2544_, v___x_2558_);
v___x_2560_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2543_, v___x_2559_);
return v___x_2560_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_2563_, v_a_2564_);
lean_dec(v_a_2564_);
lean_dec_ref(v_m_2563_);
return v_res_2565_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2568_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1));
v___x_2569_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0));
v___x_2570_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2569_, v___x_2568_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object* v_declName_2573_, uint8_t v_isMeta_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v___x_2578_; lean_object* v_env_2582_; lean_object* v___y_2584_; lean_object* v___x_2597_; 
v___x_2578_ = lean_st_ref_get(v___y_2576_);
v_env_2582_ = lean_ctor_get(v___x_2578_, 0);
lean_inc_ref(v_env_2582_);
lean_dec(v___x_2578_);
v___x_2597_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2582_, v_declName_2573_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_dec_ref(v_env_2582_);
lean_dec(v_declName_2573_);
goto v___jp_2579_;
}
else
{
lean_object* v_val_2598_; lean_object* v___x_2599_; lean_object* v_modules_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v_val_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_val_2598_);
lean_dec_ref(v___x_2597_);
v___x_2599_ = l_Lean_Environment_header(v_env_2582_);
v_modules_2600_ = lean_ctor_get(v___x_2599_, 3);
lean_inc_ref(v_modules_2600_);
lean_dec_ref(v___x_2599_);
v___x_2601_ = lean_array_get_size(v_modules_2600_);
v___x_2602_ = lean_nat_dec_lt(v_val_2598_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_dec_ref(v_modules_2600_);
lean_dec(v_val_2598_);
lean_dec_ref(v_env_2582_);
lean_dec(v_declName_2573_);
goto v___jp_2579_;
}
else
{
lean_object* v___x_2603_; lean_object* v_env_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; uint8_t v___y_2608_; 
v___x_2603_ = lean_st_ref_get(v___y_2576_);
v_env_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc_ref(v_env_2604_);
lean_dec(v___x_2603_);
v___x_2605_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2);
v___x_2606_ = lean_array_fget(v_modules_2600_, v_val_2598_);
lean_dec(v_val_2598_);
lean_dec_ref(v_modules_2600_);
if (v_isMeta_2574_ == 0)
{
lean_dec_ref(v_env_2604_);
v___y_2608_ = v_isMeta_2574_;
goto v___jp_2607_;
}
else
{
uint8_t v___x_2619_; 
lean_inc(v_declName_2573_);
v___x_2619_ = l_Lean_isMarkedMeta(v_env_2604_, v_declName_2573_);
if (v___x_2619_ == 0)
{
v___y_2608_ = v_isMeta_2574_;
goto v___jp_2607_;
}
else
{
uint8_t v___x_2620_; 
v___x_2620_ = 0;
v___y_2608_ = v___x_2620_;
goto v___jp_2607_;
}
}
v___jp_2607_:
{
lean_object* v_toImport_2609_; lean_object* v_module_2610_; lean_object* v___x_2611_; 
v_toImport_2609_ = lean_ctor_get(v___x_2606_, 0);
lean_inc_ref(v_toImport_2609_);
lean_dec(v___x_2606_);
v_module_2610_ = lean_ctor_get(v_toImport_2609_, 0);
lean_inc(v_module_2610_);
lean_dec_ref(v_toImport_2609_);
lean_inc(v_declName_2573_);
v___x_2611_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2610_, v___y_2608_, v_declName_2573_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
lean_dec_ref(v___x_2611_);
v___x_2612_ = l_Lean_indirectModUseExt;
v___x_2613_ = lean_box(1);
v___x_2614_ = lean_box(0);
lean_inc_ref(v_env_2582_);
v___x_2615_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2605_, v___x_2612_, v_env_2582_, v___x_2613_, v___x_2614_);
v___x_2616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v___x_2615_, v_declName_2573_);
lean_dec(v___x_2615_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v___x_2617_; 
v___x_2617_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__3));
v___y_2584_ = v___x_2617_;
goto v___jp_2583_;
}
else
{
lean_object* v_val_2618_; 
v_val_2618_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_val_2618_);
lean_dec_ref(v___x_2616_);
v___y_2584_ = v_val_2618_;
goto v___jp_2583_;
}
}
else
{
lean_dec_ref(v_env_2582_);
lean_dec(v_declName_2573_);
return v___x_2611_;
}
}
}
}
v___jp_2579_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = lean_box(0);
v___x_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
return v___x_2581_;
}
v___jp_2583_:
{
lean_object* v___x_2585_; size_t v_sz_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
v___x_2585_ = lean_box(0);
v_sz_2586_ = lean_array_size(v___y_2584_);
v___x_2587_ = ((size_t)0ULL);
v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v_env_2582_, v_declName_2573_, v___y_2584_, v_sz_2586_, v___x_2587_, v___x_2585_, v___y_2575_, v___y_2576_);
lean_dec_ref(v___y_2584_);
lean_dec_ref(v_env_2582_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2595_ == 0)
{
lean_object* v_unused_2596_; 
v_unused_2596_ = lean_ctor_get(v___x_2588_, 0);
lean_dec(v_unused_2596_);
v___x_2590_ = v___x_2588_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_dec(v___x_2588_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2585_);
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2585_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
else
{
return v___x_2588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object* v_declName_2621_, lean_object* v_isMeta_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
uint8_t v_isMeta_boxed_2626_; lean_object* v_res_2627_; 
v_isMeta_boxed_2626_ = lean_unbox(v_isMeta_2622_);
v_res_2627_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_declName_2621_, v_isMeta_boxed_2626_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(lean_object* v_as_x27_2628_, lean_object* v_b_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
if (lean_obj_tag(v_as_x27_2628_) == 0)
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v_b_2629_);
return v___x_2633_;
}
else
{
lean_object* v_head_2634_; lean_object* v_tail_2635_; uint8_t v___x_2636_; lean_object* v___x_2637_; 
v_head_2634_ = lean_ctor_get(v_as_x27_2628_, 0);
v_tail_2635_ = lean_ctor_get(v_as_x27_2628_, 1);
v___x_2636_ = 1;
lean_inc(v_head_2634_);
v___x_2637_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_head_2634_, v___x_2636_, v___y_2630_, v___y_2631_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v___x_2638_; 
lean_dec_ref(v___x_2637_);
v___x_2638_ = lean_box(0);
v_as_x27_2628_ = v_tail_2635_;
v_b_2629_ = v___x_2638_;
goto _start;
}
else
{
return v___x_2637_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_2640_, lean_object* v_b_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_2640_, v_b_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v_as_x27_2640_);
return v_res_2645_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = l_Lean_maxRecDepthErrorMessage;
v___x_2652_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
return v___x_2652_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3);
v___x_2654_ = l_Lean_MessageData_ofFormat(v___x_2653_);
return v___x_2654_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2655_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4);
v___x_2656_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2));
v___x_2657_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
lean_ctor_set(v___x_2657_, 1, v___x_2655_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(lean_object* v_ref_2658_){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5);
v___x_2661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2661_, 0, v_ref_2658_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___boxed(lean_object* v_ref_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_2663_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object* v_currNamespace_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v_currNamespace_2666_);
lean_ctor_set(v___x_2669_, 1, v___y_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(v_currNamespace_2670_, v___y_2671_, v___y_2672_);
lean_dec_ref(v___y_2671_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object* v_env_2674_, lean_object* v_declName_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
uint8_t v___x_2678_; lean_object* v_env_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; uint8_t v___x_2682_; 
v___x_2678_ = 0;
v_env_2679_ = l_Lean_Environment_setExporting(v_env_2674_, v___x_2678_);
lean_inc(v_declName_2675_);
v___x_2680_ = l_Lean_mkPrivateName(v_env_2679_, v_declName_2675_);
v___x_2681_ = 1;
lean_inc_ref(v_env_2679_);
v___x_2682_ = l_Lean_Environment_contains(v_env_2679_, v___x_2680_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; uint8_t v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2683_ = l_Lean_privateToUserName(v_declName_2675_);
v___x_2684_ = l_Lean_Environment_contains(v_env_2679_, v___x_2683_, v___x_2681_);
v___x_2685_ = lean_box(v___x_2684_);
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
lean_ctor_set(v___x_2686_, 1, v___y_2677_);
return v___x_2686_;
}
else
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
lean_dec_ref(v_env_2679_);
lean_dec(v_declName_2675_);
v___x_2687_ = lean_box(v___x_2682_);
v___x_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
lean_ctor_set(v___x_2688_, 1, v___y_2677_);
return v___x_2688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object* v_env_2689_, lean_object* v_declName_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(v_env_2689_, v_declName_2690_, v___y_2691_, v___y_2692_);
lean_dec_ref(v___y_2691_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(lean_object* v_x_2694_, lean_object* v___y_2695_){
_start:
{
if (lean_obj_tag(v_x_2694_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2697_; 
v_a_2696_ = lean_ctor_get(v_x_2694_, 0);
lean_inc(v_a_2696_);
v___x_2697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2697_, 0, v_a_2696_);
lean_ctor_set(v___x_2697_, 1, v___y_2695_);
return v___x_2697_;
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2699_; 
v_a_2698_ = lean_ctor_get(v_x_2694_, 0);
lean_inc(v_a_2698_);
v___x_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2699_, 0, v_a_2698_);
lean_ctor_set(v___x_2699_, 1, v___y_2695_);
return v___x_2699_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_2700_, v___y_2701_);
lean_dec_ref(v_x_2700_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object* v_env_2703_, lean_object* v_stx_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2703_, v_stx_2704_, v___y_2705_, v___y_2706_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
if (lean_obj_tag(v_a_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2717_; 
v_a_2709_ = lean_ctor_get(v___x_2707_, 1);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2717_ == 0)
{
lean_object* v_unused_2718_; 
v_unused_2718_ = lean_ctor_get(v___x_2707_, 0);
lean_dec(v_unused_2718_);
v___x_2711_ = v___x_2707_;
v_isShared_2712_ = v_isSharedCheck_2717_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2707_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2717_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2713_ = lean_box(0);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2713_);
v___x_2715_ = v___x_2711_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2713_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v_a_2709_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
else
{
lean_object* v_val_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2747_; 
v_val_2719_ = lean_ctor_get(v_a_2708_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v_a_2708_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2721_ = v_a_2708_;
v_isShared_2722_ = v_isSharedCheck_2747_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_val_2719_);
lean_dec(v_a_2708_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2747_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v_snd_2723_; 
v_snd_2723_ = lean_ctor_get(v_val_2719_, 1);
lean_inc(v_snd_2723_);
lean_dec(v_val_2719_);
if (lean_obj_tag(v_snd_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2733_; 
lean_del_object(v___x_2721_);
v_a_2724_ = lean_ctor_get(v___x_2707_, 1);
lean_inc(v_a_2724_);
lean_dec_ref(v___x_2707_);
v_a_2725_ = lean_ctor_get(v_snd_2723_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_snd_2723_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2727_ = v_snd_2723_;
v_isShared_2728_ = v_isSharedCheck_2733_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v_snd_2723_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2733_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2730_, v_a_2724_);
lean_dec_ref(v___x_2730_);
return v___x_2731_;
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2746_; 
v_a_2734_ = lean_ctor_get(v___x_2707_, 1);
lean_inc(v_a_2734_);
lean_dec_ref(v___x_2707_);
v_a_2735_ = lean_ctor_get(v_snd_2723_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v_snd_2723_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2737_ = v_snd_2723_;
v_isShared_2738_ = v_isSharedCheck_2746_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v_snd_2723_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2746_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 0, v_a_2735_);
v___x_2740_ = v___x_2721_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2742_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2740_);
v___x_2742_ = v___x_2737_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2742_, v_a_2734_);
lean_dec_ref(v___x_2742_);
return v___x_2743_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
v_a_2748_ = lean_ctor_get(v___x_2707_, 0);
v_a_2749_ = lean_ctor_get(v___x_2707_, 1);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2707_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_inc(v_a_2748_);
lean_dec(v___x_2707_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2748_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object* v_env_2757_, lean_object* v_stx_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(v_env_2757_, v_stx_2758_, v___y_2759_, v___y_2760_);
lean_dec_ref(v___y_2759_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object* v_env_2762_, lean_object* v_currNamespace_2763_, lean_object* v_openDecls_2764_, lean_object* v_n_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = l_Lean_ResolveName_resolveNamespace(v_env_2762_, v_currNamespace_2763_, v_openDecls_2764_, v_n_2765_);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
lean_ctor_set(v___x_2769_, 1, v___y_2767_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object* v_env_2770_, lean_object* v_currNamespace_2771_, lean_object* v_openDecls_2772_, lean_object* v_n_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(v_env_2770_, v_currNamespace_2771_, v_openDecls_2772_, v_n_2773_, v___y_2774_, v___y_2775_);
lean_dec_ref(v___y_2774_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object* v_as_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
if (lean_obj_tag(v_as_2777_) == 0)
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_box(0);
v___x_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
return v___x_2782_;
}
else
{
lean_object* v_head_2783_; lean_object* v_tail_2784_; lean_object* v_fst_2785_; lean_object* v_snd_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v_scopes_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v_opts_2793_; uint8_t v_hasTrace_2794_; 
v_head_2783_ = lean_ctor_get(v_as_2777_, 0);
lean_inc(v_head_2783_);
v_tail_2784_ = lean_ctor_get(v_as_2777_, 1);
lean_inc(v_tail_2784_);
lean_dec_ref(v_as_2777_);
v_fst_2785_ = lean_ctor_get(v_head_2783_, 0);
lean_inc(v_fst_2785_);
v_snd_2786_ = lean_ctor_get(v_head_2783_, 1);
lean_inc(v_snd_2786_);
lean_dec(v_head_2783_);
v___x_2787_ = l_Lean_inheritedTraceOptions;
v___x_2788_ = lean_st_ref_get(v___x_2787_);
v___x_2789_ = lean_st_ref_get(v___y_2779_);
v_scopes_2790_ = lean_ctor_get(v___x_2789_, 2);
lean_inc(v_scopes_2790_);
lean_dec(v___x_2789_);
v___x_2791_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2792_ = l_List_head_x21___redArg(v___x_2791_, v_scopes_2790_);
lean_dec(v_scopes_2790_);
v_opts_2793_ = lean_ctor_get(v___x_2792_, 1);
lean_inc_ref(v_opts_2793_);
lean_dec(v___x_2792_);
v_hasTrace_2794_ = lean_ctor_get_uint8(v_opts_2793_, sizeof(void*)*1);
if (v_hasTrace_2794_ == 0)
{
lean_dec_ref(v_opts_2793_);
lean_dec(v___x_2788_);
lean_dec(v_snd_2786_);
lean_dec(v_fst_2785_);
v_as_2777_ = v_tail_2784_;
goto _start;
}
else
{
lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2796_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11));
lean_inc(v_fst_2785_);
v___x_2797_ = l_Lean_Name_append(v___x_2796_, v_fst_2785_);
v___x_2798_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2788_, v_opts_2793_, v___x_2797_);
lean_dec(v___x_2797_);
lean_dec_ref(v_opts_2793_);
lean_dec(v___x_2788_);
if (v___x_2798_ == 0)
{
lean_dec(v_snd_2786_);
lean_dec(v_fst_2785_);
v_as_2777_ = v_tail_2784_;
goto _start;
}
else
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2800_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2800_, 0, v_snd_2786_);
v___x_2801_ = l_Lean_MessageData_ofFormat(v___x_2800_);
v___x_2802_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_fst_2785_, v___x_2801_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_dec_ref(v___x_2802_);
v_as_2777_ = v_tail_2784_;
goto _start;
}
else
{
lean_dec(v_tail_2784_);
return v___x_2802_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object* v_as_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v_as_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object* v_env_2809_, lean_object* v_opts_2810_, lean_object* v_currNamespace_2811_, lean_object* v_openDecls_2812_, lean_object* v_n_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = l_Lean_ResolveName_resolveGlobalName(v_env_2809_, v_opts_2810_, v_currNamespace_2811_, v_openDecls_2812_, v_n_2813_);
v___x_2817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2816_);
lean_ctor_set(v___x_2817_, 1, v___y_2815_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object* v_env_2818_, lean_object* v_opts_2819_, lean_object* v_currNamespace_2820_, lean_object* v_openDecls_2821_, lean_object* v_n_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(v_env_2818_, v_opts_2819_, v_currNamespace_2820_, v_openDecls_2821_, v_n_2822_, v___y_2823_, v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec_ref(v_opts_2819_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object* v_x_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___x_2831_; lean_object* v_env_2832_; lean_object* v___x_2833_; lean_object* v_scopes_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v_opts_2837_; lean_object* v___x_2838_; 
v___x_2831_ = lean_st_ref_get(v___y_2829_);
v_env_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc_ref(v_env_2832_);
lean_dec(v___x_2831_);
v___x_2833_ = lean_st_ref_get(v___y_2829_);
v_scopes_2834_ = lean_ctor_get(v___x_2833_, 2);
lean_inc(v_scopes_2834_);
lean_dec(v___x_2833_);
v___x_2835_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2836_ = l_List_head_x21___redArg(v___x_2835_, v_scopes_2834_);
lean_dec(v_scopes_2834_);
v_opts_2837_ = lean_ctor_get(v___x_2836_, 1);
lean_inc_ref(v_opts_2837_);
lean_dec(v___x_2836_);
v___x_2838_ = l_Lean_Elab_Command_getScope___redArg(v___y_2829_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v_currNamespace_2840_; lean_object* v___x_2841_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref(v___x_2838_);
v_currNamespace_2840_ = lean_ctor_get(v_a_2839_, 2);
lean_inc(v_currNamespace_2840_);
lean_dec(v_a_2839_);
v___x_2841_ = l_Lean_Elab_Command_getScope___redArg(v___y_2829_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v_openDecls_2843_; lean_object* v___x_2844_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref(v___x_2841_);
v_openDecls_2843_ = lean_ctor_get(v_a_2842_, 3);
lean_inc(v_openDecls_2843_);
lean_dec(v_a_2842_);
v___x_2844_ = l_Lean_Elab_Command_getRef___redArg(v___y_2828_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref(v___x_2844_);
v___x_2846_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2828_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v_currRecDepth_2848_; lean_object* v_quotContext_x3f_2849_; lean_object* v___f_2850_; lean_object* v___f_2851_; lean_object* v___f_2852_; lean_object* v___f_2853_; lean_object* v___f_2854_; lean_object* v_methods_2855_; lean_object* v_a_2857_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref(v___x_2846_);
v_currRecDepth_2848_ = lean_ctor_get(v___y_2828_, 2);
v_quotContext_x3f_2849_ = lean_ctor_get(v___y_2828_, 5);
lean_inc_ref_n(v_env_2832_, 3);
v___f_2850_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2850_, 0, v_env_2832_);
v___f_2851_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2851_, 0, v_env_2832_);
lean_inc_n(v_currNamespace_2840_, 2);
v___f_2852_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2852_, 0, v_currNamespace_2840_);
lean_inc(v_openDecls_2843_);
v___f_2853_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2853_, 0, v_env_2832_);
lean_closure_set(v___f_2853_, 1, v_currNamespace_2840_);
lean_closure_set(v___f_2853_, 2, v_openDecls_2843_);
v___f_2854_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2854_, 0, v_env_2832_);
lean_closure_set(v___f_2854_, 1, v_opts_2837_);
lean_closure_set(v___f_2854_, 2, v_currNamespace_2840_);
lean_closure_set(v___f_2854_, 3, v_openDecls_2843_);
v_methods_2855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2855_, 0, v___f_2851_);
lean_ctor_set(v_methods_2855_, 1, v___f_2852_);
lean_ctor_set(v_methods_2855_, 2, v___f_2850_);
lean_ctor_set(v_methods_2855_, 3, v___f_2853_);
lean_ctor_set(v_methods_2855_, 4, v___f_2854_);
if (lean_obj_tag(v_quotContext_x3f_2849_) == 0)
{
lean_object* v___x_2930_; lean_object* v_a_2931_; 
v___x_2930_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_2829_);
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref(v___x_2930_);
v_a_2857_ = v_a_2931_;
goto v___jp_2856_;
}
else
{
lean_object* v_val_2932_; 
v_val_2932_ = lean_ctor_get(v_quotContext_x3f_2849_, 0);
lean_inc(v_val_2932_);
v_a_2857_ = v_val_2932_;
goto v___jp_2856_;
}
v___jp_2856_:
{
lean_object* v___x_2858_; lean_object* v_maxRecDepth_2859_; lean_object* v___x_2860_; lean_object* v_nextMacroScope_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2858_ = lean_st_ref_get(v___y_2829_);
v_maxRecDepth_2859_ = lean_ctor_get(v___x_2858_, 5);
lean_inc(v_maxRecDepth_2859_);
lean_dec(v___x_2858_);
v___x_2860_ = lean_st_ref_get(v___y_2829_);
v_nextMacroScope_2861_ = lean_ctor_get(v___x_2860_, 4);
lean_inc(v_nextMacroScope_2861_);
lean_dec(v___x_2860_);
lean_inc(v_currRecDepth_2848_);
v___x_2862_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2862_, 0, v_methods_2855_);
lean_ctor_set(v___x_2862_, 1, v_a_2857_);
lean_ctor_set(v___x_2862_, 2, v_a_2847_);
lean_ctor_set(v___x_2862_, 3, v_currRecDepth_2848_);
lean_ctor_set(v___x_2862_, 4, v_maxRecDepth_2859_);
lean_ctor_set(v___x_2862_, 5, v_a_2845_);
v___x_2863_ = lean_box(0);
v___x_2864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2864_, 0, v_nextMacroScope_2861_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
lean_ctor_set(v___x_2864_, 2, v___x_2863_);
v___x_2865_ = lean_apply_2(v_x_2827_, v___x_2862_, v___x_2864_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v_a_2867_; lean_object* v_macroScope_2868_; lean_object* v_traceMsgs_2869_; lean_object* v_expandedMacroDecls_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 1);
lean_inc(v_a_2866_);
v_a_2867_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2867_);
lean_dec_ref(v___x_2865_);
v_macroScope_2868_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_macroScope_2868_);
v_traceMsgs_2869_ = lean_ctor_get(v_a_2866_, 1);
lean_inc(v_traceMsgs_2869_);
v_expandedMacroDecls_2870_ = lean_ctor_get(v_a_2866_, 2);
lean_inc(v_expandedMacroDecls_2870_);
lean_dec(v_a_2866_);
v___x_2871_ = lean_box(0);
v___x_2872_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_expandedMacroDecls_2870_, v___x_2871_, v___y_2828_, v___y_2829_);
lean_dec(v_expandedMacroDecls_2870_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v___x_2873_; lean_object* v_env_2874_; lean_object* v_messages_2875_; lean_object* v_scopes_2876_; lean_object* v_usedQuotCtxts_2877_; lean_object* v_maxRecDepth_2878_; lean_object* v_ngen_2879_; lean_object* v_auxDeclNGen_2880_; lean_object* v_infoState_2881_; lean_object* v_traceState_2882_; lean_object* v_snapshotTasks_2883_; lean_object* v_newDecls_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2910_; 
lean_dec_ref(v___x_2872_);
v___x_2873_ = lean_st_ref_take(v___y_2829_);
v_env_2874_ = lean_ctor_get(v___x_2873_, 0);
v_messages_2875_ = lean_ctor_get(v___x_2873_, 1);
v_scopes_2876_ = lean_ctor_get(v___x_2873_, 2);
v_usedQuotCtxts_2877_ = lean_ctor_get(v___x_2873_, 3);
v_maxRecDepth_2878_ = lean_ctor_get(v___x_2873_, 5);
v_ngen_2879_ = lean_ctor_get(v___x_2873_, 6);
v_auxDeclNGen_2880_ = lean_ctor_get(v___x_2873_, 7);
v_infoState_2881_ = lean_ctor_get(v___x_2873_, 8);
v_traceState_2882_ = lean_ctor_get(v___x_2873_, 9);
v_snapshotTasks_2883_ = lean_ctor_get(v___x_2873_, 10);
v_newDecls_2884_ = lean_ctor_get(v___x_2873_, 11);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2910_ == 0)
{
lean_object* v_unused_2911_; 
v_unused_2911_ = lean_ctor_get(v___x_2873_, 4);
lean_dec(v_unused_2911_);
v___x_2886_ = v___x_2873_;
v_isShared_2887_ = v_isSharedCheck_2910_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_newDecls_2884_);
lean_inc(v_snapshotTasks_2883_);
lean_inc(v_traceState_2882_);
lean_inc(v_infoState_2881_);
lean_inc(v_auxDeclNGen_2880_);
lean_inc(v_ngen_2879_);
lean_inc(v_maxRecDepth_2878_);
lean_inc(v_usedQuotCtxts_2877_);
lean_inc(v_scopes_2876_);
lean_inc(v_messages_2875_);
lean_inc(v_env_2874_);
lean_dec(v___x_2873_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2910_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 4, v_macroScope_2868_);
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_env_2874_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_messages_2875_);
lean_ctor_set(v_reuseFailAlloc_2909_, 2, v_scopes_2876_);
lean_ctor_set(v_reuseFailAlloc_2909_, 3, v_usedQuotCtxts_2877_);
lean_ctor_set(v_reuseFailAlloc_2909_, 4, v_macroScope_2868_);
lean_ctor_set(v_reuseFailAlloc_2909_, 5, v_maxRecDepth_2878_);
lean_ctor_set(v_reuseFailAlloc_2909_, 6, v_ngen_2879_);
lean_ctor_set(v_reuseFailAlloc_2909_, 7, v_auxDeclNGen_2880_);
lean_ctor_set(v_reuseFailAlloc_2909_, 8, v_infoState_2881_);
lean_ctor_set(v_reuseFailAlloc_2909_, 9, v_traceState_2882_);
lean_ctor_set(v_reuseFailAlloc_2909_, 10, v_snapshotTasks_2883_);
lean_ctor_set(v_reuseFailAlloc_2909_, 11, v_newDecls_2884_);
v___x_2889_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2890_ = lean_st_ref_set(v___y_2829_, v___x_2889_);
v___x_2891_ = l_List_reverse___redArg(v_traceMsgs_2869_);
v___x_2892_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v___x_2891_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2899_ == 0)
{
lean_object* v_unused_2900_; 
v_unused_2900_ = lean_ctor_get(v___x_2892_, 0);
lean_dec(v_unused_2900_);
v___x_2894_ = v___x_2892_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_dec(v___x_2892_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v_a_2867_);
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2867_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec(v_a_2867_);
v_a_2901_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2892_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2892_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec(v_traceMsgs_2869_);
lean_dec(v_macroScope_2868_);
lean_dec(v_a_2867_);
v_a_2912_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2872_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2872_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
else
{
lean_object* v_a_2920_; 
v_a_2920_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2920_);
lean_dec_ref(v___x_2865_);
if (lean_obj_tag(v_a_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v_a_2922_; lean_object* v___x_2923_; uint8_t v___x_2924_; 
v_a_2921_ = lean_ctor_get(v_a_2920_, 0);
lean_inc(v_a_2921_);
v_a_2922_ = lean_ctor_get(v_a_2920_, 1);
lean_inc_ref(v_a_2922_);
lean_dec_ref(v_a_2920_);
v___x_2923_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0));
v___x_2924_ = lean_string_dec_eq(v_a_2922_, v___x_2923_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2925_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2925_, 0, v_a_2922_);
v___x_2926_ = l_Lean_MessageData_ofFormat(v___x_2925_);
v___x_2927_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_a_2921_, v___x_2926_, v___y_2828_, v___y_2829_);
lean_dec(v_a_2921_);
return v___x_2927_;
}
else
{
lean_object* v___x_2928_; 
lean_dec_ref(v_a_2922_);
v___x_2928_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_a_2921_);
return v___x_2928_;
}
}
else
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2929_;
}
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec(v_a_2845_);
lean_dec(v_openDecls_2843_);
lean_dec(v_currNamespace_2840_);
lean_dec_ref(v_opts_2837_);
lean_dec_ref(v_env_2832_);
lean_dec_ref(v_x_2827_);
v_a_2933_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2846_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2846_);
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
lean_dec(v_openDecls_2843_);
lean_dec(v_currNamespace_2840_);
lean_dec_ref(v_opts_2837_);
lean_dec_ref(v_env_2832_);
lean_dec_ref(v_x_2827_);
v_a_2941_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2844_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2844_);
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
lean_dec(v_currNamespace_2840_);
lean_dec_ref(v_opts_2837_);
lean_dec_ref(v_env_2832_);
lean_dec_ref(v_x_2827_);
v_a_2949_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2841_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2841_);
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
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec_ref(v_opts_2837_);
lean_dec_ref(v_env_2832_);
lean_dec_ref(v_x_2827_);
v_a_2957_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2838_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2838_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object* v_x_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object* v_x_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___x_3055_; uint8_t v___x_3056_; 
v___x_3013_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_3014_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_3055_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
lean_inc(v_x_3009_);
v___x_3056_ = l_Lean_Syntax_isOfKind(v_x_3009_, v___x_3055_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; 
lean_dec(v_x_3009_);
v___x_3057_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3057_;
}
else
{
lean_object* v___x_3058_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; uint8_t v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; size_t v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; uint8_t v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; size_t v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3240_; uint8_t v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; size_t v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3276_; uint8_t v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; size_t v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3315_; uint8_t v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; size_t v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v_expectedType_x3f_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v_prio_x3f_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v_name_x3f_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v_prec_x3f_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v_attrs_x3f_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v_doc_x3f_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___x_3535_; uint8_t v___x_3536_; 
v___x_3058_ = lean_unsigned_to_nat(0u);
v___x_3535_ = l_Lean_Syntax_getArg(v_x_3009_, v___x_3058_);
v___x_3536_ = l_Lean_Syntax_isNone(v___x_3535_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; uint8_t v___x_3538_; 
v___x_3537_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3535_);
v___x_3538_ = l_Lean_Syntax_matchesNull(v___x_3535_, v___x_3537_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; 
lean_dec(v___x_3535_);
lean_dec(v_x_3009_);
v___x_3539_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3539_;
}
else
{
lean_object* v_doc_x3f_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v_doc_x3f_3540_ = l_Lean_Syntax_getArg(v___x_3535_, v___x_3058_);
lean_dec(v___x_3535_);
v___x_3541_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(v_doc_x3f_3540_);
v___x_3542_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3540_, v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; 
lean_dec(v_doc_x3f_3540_);
lean_dec(v_x_3009_);
v___x_3543_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3543_;
}
else
{
lean_object* v___x_3544_; 
v___x_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3544_, 0, v_doc_x3f_3540_);
v_doc_x3f_3519_ = v___x_3544_;
v___y_3520_ = v_a_3010_;
v___y_3521_ = v_a_3011_;
goto v___jp_3518_;
}
}
}
else
{
lean_object* v___x_3545_; 
lean_dec(v___x_3535_);
v___x_3545_ = lean_box(0);
v_doc_x3f_3519_ = v___x_3545_;
v___y_3520_ = v_a_3010_;
v___y_3521_ = v_a_3011_;
goto v___jp_3518_;
}
v___jp_3059_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
lean_inc_ref_n(v___y_3063_, 2);
v___x_3076_ = l_Array_append___redArg(v___y_3063_, v___y_3075_);
lean_dec_ref(v___y_3075_);
lean_inc_n(v___y_3072_, 3);
lean_inc_n(v___y_3061_, 6);
v___x_3077_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3077_, 0, v___y_3061_);
lean_ctor_set(v___x_3077_, 1, v___y_3072_);
lean_ctor_set(v___x_3077_, 2, v___x_3076_);
v___x_3078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3078_, 0, v___y_3061_);
lean_ctor_set(v___x_3078_, 1, v___y_3072_);
lean_ctor_set(v___x_3078_, 2, v___y_3063_);
lean_inc_ref(v___x_3078_);
lean_inc(v___y_3060_);
v___x_3079_ = l_Lean_Syntax_node1(v___y_3061_, v___y_3060_, v___x_3078_);
lean_inc_ref(v___y_3074_);
v___x_3080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___y_3061_);
lean_ctor_set(v___x_3080_, 1, v___y_3074_);
lean_inc_ref(v___y_3073_);
v___x_3081_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___y_3061_);
lean_ctor_set(v___x_3081_, 1, v___y_3073_);
v___x_3082_ = l_Lean_Syntax_node2(v___y_3061_, v___y_3072_, v___x_3081_, v___y_3066_);
if (lean_obj_tag(v___y_3071_) == 1)
{
lean_object* v_val_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v_val_3083_ = lean_ctor_get(v___y_3071_, 0);
lean_inc(v_val_3083_);
lean_dec_ref(v___y_3071_);
v___x_3084_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___y_3061_);
v___x_3085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___y_3061_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
v___x_3086_ = l_Array_mkArray2___redArg(v___x_3085_, v_val_3083_);
v___y_3016_ = v___x_3079_;
v___y_3017_ = v___x_3082_;
v___y_3018_ = v___x_3077_;
v___y_3019_ = v___y_3061_;
v___y_3020_ = v___y_3062_;
v___y_3021_ = v___y_3063_;
v___y_3022_ = v___y_3064_;
v___y_3023_ = v___y_3065_;
v___y_3024_ = v___x_3078_;
v___y_3025_ = v___y_3067_;
v___y_3026_ = v___y_3068_;
v___y_3027_ = v___y_3070_;
v___y_3028_ = v___y_3069_;
v___y_3029_ = v___y_3072_;
v___y_3030_ = v___x_3080_;
v___y_3031_ = v___x_3086_;
goto v___jp_3015_;
}
else
{
lean_object* v___x_3087_; 
lean_dec(v___y_3071_);
v___x_3087_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3016_ = v___x_3079_;
v___y_3017_ = v___x_3082_;
v___y_3018_ = v___x_3077_;
v___y_3019_ = v___y_3061_;
v___y_3020_ = v___y_3062_;
v___y_3021_ = v___y_3063_;
v___y_3022_ = v___y_3064_;
v___y_3023_ = v___y_3065_;
v___y_3024_ = v___x_3078_;
v___y_3025_ = v___y_3067_;
v___y_3026_ = v___y_3068_;
v___y_3027_ = v___y_3070_;
v___y_3028_ = v___y_3069_;
v___y_3029_ = v___y_3072_;
v___y_3030_ = v___x_3080_;
v___y_3031_ = v___x_3087_;
goto v___jp_3015_;
}
}
v___jp_3088_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_3104_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
if (lean_obj_tag(v___y_3102_) == 1)
{
lean_object* v_val_3105_; lean_object* v___x_3106_; 
v_val_3105_ = lean_ctor_get(v___y_3102_, 0);
lean_inc(v_val_3105_);
lean_dec_ref(v___y_3102_);
v___x_3106_ = l_Array_mkArray1___redArg(v_val_3105_);
v___y_3060_ = v___y_3089_;
v___y_3061_ = v___y_3090_;
v___y_3062_ = v___y_3091_;
v___y_3063_ = v___y_3092_;
v___y_3064_ = v___y_3093_;
v___y_3065_ = v___y_3094_;
v___y_3066_ = v___y_3095_;
v___y_3067_ = v___x_3104_;
v___y_3068_ = v___y_3096_;
v___y_3069_ = v___y_3097_;
v___y_3070_ = v___y_3098_;
v___y_3071_ = v___y_3099_;
v___y_3072_ = v___y_3100_;
v___y_3073_ = v___y_3101_;
v___y_3074_ = v___x_3103_;
v___y_3075_ = v___x_3106_;
goto v___jp_3059_;
}
else
{
lean_object* v___x_3107_; 
lean_dec(v___y_3102_);
v___x_3107_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3060_ = v___y_3089_;
v___y_3061_ = v___y_3090_;
v___y_3062_ = v___y_3091_;
v___y_3063_ = v___y_3092_;
v___y_3064_ = v___y_3093_;
v___y_3065_ = v___y_3094_;
v___y_3066_ = v___y_3095_;
v___y_3067_ = v___x_3104_;
v___y_3068_ = v___y_3096_;
v___y_3069_ = v___y_3097_;
v___y_3070_ = v___y_3098_;
v___y_3071_ = v___y_3099_;
v___y_3072_ = v___y_3100_;
v___y_3073_ = v___y_3101_;
v___y_3074_ = v___x_3103_;
v___y_3075_ = v___x_3107_;
goto v___jp_3059_;
}
}
v___jp_3108_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; size_t v_sz_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_inc_ref_n(v___y_3112_, 2);
v___x_3132_ = l_Array_append___redArg(v___y_3112_, v___y_3131_);
lean_dec_ref(v___y_3131_);
lean_inc_n(v___y_3121_, 3);
lean_inc_n(v___y_3124_, 9);
v___x_3133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3133_, 0, v___y_3124_);
lean_ctor_set(v___x_3133_, 1, v___y_3121_);
lean_ctor_set(v___x_3133_, 2, v___x_3132_);
v___x_3134_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
v___x_3135_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
v___x_3136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___y_3124_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__6));
v___x_3138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___y_3124_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_3140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___y_3124_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = l_Nat_reprFast(v___y_3120_);
v___x_3142_ = lean_box(2);
v___x_3143_ = l_Lean_Syntax_mkNumLit(v___x_3141_, v___x_3142_);
v___x_3144_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3145_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___y_3124_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
v___x_3146_ = l_Lean_Syntax_node5(v___y_3124_, v___x_3134_, v___x_3136_, v___x_3138_, v___x_3140_, v___x_3143_, v___x_3145_);
v___x_3147_ = l_Lean_Syntax_node1(v___y_3124_, v___y_3121_, v___x_3146_);
v_sz_3148_ = lean_array_size(v___y_3125_);
v___x_3149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_3148_, v___y_3127_, v___y_3125_);
v___x_3150_ = l_Array_append___redArg(v___y_3112_, v___x_3149_);
lean_dec_ref(v___x_3149_);
v___x_3151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3151_, 0, v___y_3124_);
lean_ctor_set(v___x_3151_, 1, v___y_3121_);
lean_ctor_set(v___x_3151_, 2, v___x_3150_);
v___x_3152_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_3153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___y_3124_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v___x_3154_ = lean_unsigned_to_nat(10u);
v___x_3155_ = lean_mk_empty_array_with_capacity(v___x_3154_);
v___x_3156_ = lean_array_push(v___x_3155_, v___y_3126_);
v___x_3157_ = lean_array_push(v___x_3156_, v___y_3111_);
v___x_3158_ = lean_array_push(v___x_3157_, v___y_3130_);
v___x_3159_ = lean_array_push(v___x_3158_, v___y_3122_);
v___x_3160_ = lean_array_push(v___x_3159_, v___y_3117_);
v___x_3161_ = lean_array_push(v___x_3160_, v___x_3133_);
v___x_3162_ = lean_array_push(v___x_3161_, v___x_3147_);
v___x_3163_ = lean_array_push(v___x_3162_, v___x_3151_);
v___x_3164_ = lean_array_push(v___x_3163_, v___x_3153_);
lean_inc(v___y_3115_);
v___x_3165_ = lean_array_push(v___x_3164_, v___y_3115_);
lean_inc(v___y_3128_);
v___x_3166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3166_, 0, v___y_3124_);
lean_ctor_set(v___x_3166_, 1, v___y_3128_);
lean_ctor_set(v___x_3166_, 2, v___x_3165_);
v___x_3167_ = l_Lean_Elab_Command_elabSyntax(v___x_3166_, v___y_3118_, v___y_3116_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3169_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3168_);
lean_dec_ref(v___x_3167_);
v___x_3169_ = l_Lean_Elab_Command_getRef___redArg(v___y_3118_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3171_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref(v___x_3169_);
v___x_3171_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3118_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_quotContext_x3f_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_dec_ref(v___x_3171_);
v_quotContext_x3f_3172_ = lean_ctor_get(v___y_3118_, 5);
v___x_3173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3142_);
lean_ctor_set(v___x_3173_, 1, v_a_3168_);
lean_ctor_set(v___x_3173_, 2, v___y_3129_);
v___x_3174_ = l_Lean_SourceInfo_fromRef(v_a_3170_, v___y_3109_);
lean_dec(v_a_3170_);
if (lean_obj_tag(v_quotContext_x3f_3172_) == 0)
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3116_);
lean_dec_ref(v___x_3175_);
v___y_3089_ = v___y_3110_;
v___y_3090_ = v___x_3174_;
v___y_3091_ = v___x_3144_;
v___y_3092_ = v___y_3112_;
v___y_3093_ = v___y_3114_;
v___y_3094_ = v___y_3113_;
v___y_3095_ = v___y_3115_;
v___y_3096_ = v___y_3116_;
v___y_3097_ = v___x_3173_;
v___y_3098_ = v___y_3118_;
v___y_3099_ = v___y_3119_;
v___y_3100_ = v___y_3121_;
v___y_3101_ = v___x_3152_;
v___y_3102_ = v___y_3123_;
goto v___jp_3088_;
}
else
{
v___y_3089_ = v___y_3110_;
v___y_3090_ = v___x_3174_;
v___y_3091_ = v___x_3144_;
v___y_3092_ = v___y_3112_;
v___y_3093_ = v___y_3114_;
v___y_3094_ = v___y_3113_;
v___y_3095_ = v___y_3115_;
v___y_3096_ = v___y_3116_;
v___y_3097_ = v___x_3173_;
v___y_3098_ = v___y_3118_;
v___y_3099_ = v___y_3119_;
v___y_3100_ = v___y_3121_;
v___y_3101_ = v___x_3152_;
v___y_3102_ = v___y_3123_;
goto v___jp_3088_;
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec(v_a_3170_);
lean_dec(v_a_3168_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3123_);
lean_dec(v___y_3119_);
lean_dec(v___y_3115_);
lean_dec(v___y_3113_);
v_a_3176_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3171_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3171_);
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
lean_dec(v_a_3168_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3123_);
lean_dec(v___y_3119_);
lean_dec(v___y_3115_);
lean_dec(v___y_3113_);
v_a_3184_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3169_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3169_);
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
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3123_);
lean_dec(v___y_3119_);
lean_dec(v___y_3115_);
lean_dec(v___y_3113_);
v_a_3192_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3167_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3167_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
v___jp_3200_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_inc_ref(v___y_3204_);
v___x_3224_ = l_Array_append___redArg(v___y_3204_, v___y_3223_);
lean_dec_ref(v___y_3223_);
lean_inc(v___y_3213_);
lean_inc(v___y_3218_);
v___x_3225_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3225_, 0, v___y_3218_);
lean_ctor_set(v___x_3225_, 1, v___y_3213_);
lean_ctor_set(v___x_3225_, 2, v___x_3224_);
if (lean_obj_tag(v___y_3209_) == 1)
{
lean_object* v_val_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v_val_3226_ = lean_ctor_get(v___y_3209_, 0);
lean_inc(v_val_3226_);
lean_dec_ref(v___y_3209_);
v___x_3227_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
v___x_3228_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___y_3218_, 5);
v___x_3229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___y_3218_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__9));
v___x_3231_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___y_3218_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
v___x_3232_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_3233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___y_3218_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___x_3234_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___y_3218_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = l_Lean_Syntax_node5(v___y_3218_, v___x_3227_, v___x_3229_, v___x_3231_, v___x_3233_, v_val_3226_, v___x_3235_);
v___x_3237_ = l_Array_mkArray1___redArg(v___x_3236_);
v___y_3109_ = v___y_3201_;
v___y_3110_ = v___y_3202_;
v___y_3111_ = v___y_3203_;
v___y_3112_ = v___y_3204_;
v___y_3113_ = v___y_3205_;
v___y_3114_ = v___y_3206_;
v___y_3115_ = v___y_3207_;
v___y_3116_ = v___y_3208_;
v___y_3117_ = v___x_3225_;
v___y_3118_ = v___y_3210_;
v___y_3119_ = v___y_3211_;
v___y_3120_ = v___y_3212_;
v___y_3121_ = v___y_3213_;
v___y_3122_ = v___y_3214_;
v___y_3123_ = v___y_3217_;
v___y_3124_ = v___y_3218_;
v___y_3125_ = v___y_3216_;
v___y_3126_ = v___y_3215_;
v___y_3127_ = v___y_3219_;
v___y_3128_ = v___y_3220_;
v___y_3129_ = v___y_3222_;
v___y_3130_ = v___y_3221_;
v___y_3131_ = v___x_3237_;
goto v___jp_3108_;
}
else
{
lean_object* v___x_3238_; 
lean_dec(v___y_3209_);
v___x_3238_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3109_ = v___y_3201_;
v___y_3110_ = v___y_3202_;
v___y_3111_ = v___y_3203_;
v___y_3112_ = v___y_3204_;
v___y_3113_ = v___y_3205_;
v___y_3114_ = v___y_3206_;
v___y_3115_ = v___y_3207_;
v___y_3116_ = v___y_3208_;
v___y_3117_ = v___x_3225_;
v___y_3118_ = v___y_3210_;
v___y_3119_ = v___y_3211_;
v___y_3120_ = v___y_3212_;
v___y_3121_ = v___y_3213_;
v___y_3122_ = v___y_3214_;
v___y_3123_ = v___y_3217_;
v___y_3124_ = v___y_3218_;
v___y_3125_ = v___y_3216_;
v___y_3126_ = v___y_3215_;
v___y_3127_ = v___y_3219_;
v___y_3128_ = v___y_3220_;
v___y_3129_ = v___y_3222_;
v___y_3130_ = v___y_3221_;
v___y_3131_ = v___x_3238_;
goto v___jp_3108_;
}
}
v___jp_3239_:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
lean_inc_ref(v___y_3243_);
v___x_3264_ = l_Array_append___redArg(v___y_3243_, v___y_3263_);
lean_dec_ref(v___y_3263_);
lean_inc(v___y_3253_);
lean_inc(v___y_3258_);
v___x_3265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3265_, 0, v___y_3258_);
lean_ctor_set(v___x_3265_, 1, v___y_3253_);
lean_ctor_set(v___x_3265_, 2, v___x_3264_);
v___x_3266_ = l_Lean_SourceInfo_fromRef(v___y_3240_, v___x_3056_);
lean_dec(v___y_3240_);
lean_inc_ref(v___y_3254_);
v___x_3267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
lean_ctor_set(v___x_3267_, 1, v___y_3254_);
if (lean_obj_tag(v___y_3251_) == 1)
{
lean_object* v_val_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v_val_3268_ = lean_ctor_get(v___y_3251_, 0);
lean_inc(v_val_3268_);
lean_dec_ref(v___y_3251_);
v___x_3269_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
v___x_3270_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc_n(v___y_3258_, 2);
v___x_3271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___y_3258_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3272_ = l_Lean_Syntax_node2(v___y_3258_, v___x_3269_, v___x_3271_, v_val_3268_);
v___x_3273_ = l_Array_mkArray1___redArg(v___x_3272_);
v___y_3201_ = v___y_3241_;
v___y_3202_ = v___y_3242_;
v___y_3203_ = v___x_3265_;
v___y_3204_ = v___y_3243_;
v___y_3205_ = v___y_3244_;
v___y_3206_ = v___y_3245_;
v___y_3207_ = v___y_3246_;
v___y_3208_ = v___y_3247_;
v___y_3209_ = v___y_3248_;
v___y_3210_ = v___y_3249_;
v___y_3211_ = v___y_3250_;
v___y_3212_ = v___y_3252_;
v___y_3213_ = v___y_3253_;
v___y_3214_ = v___x_3267_;
v___y_3215_ = v___y_3257_;
v___y_3216_ = v___y_3256_;
v___y_3217_ = v___y_3255_;
v___y_3218_ = v___y_3258_;
v___y_3219_ = v___y_3259_;
v___y_3220_ = v___y_3260_;
v___y_3221_ = v___y_3262_;
v___y_3222_ = v___y_3261_;
v___y_3223_ = v___x_3273_;
goto v___jp_3200_;
}
else
{
lean_object* v___x_3274_; 
lean_dec(v___y_3251_);
v___x_3274_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3201_ = v___y_3241_;
v___y_3202_ = v___y_3242_;
v___y_3203_ = v___x_3265_;
v___y_3204_ = v___y_3243_;
v___y_3205_ = v___y_3244_;
v___y_3206_ = v___y_3245_;
v___y_3207_ = v___y_3246_;
v___y_3208_ = v___y_3247_;
v___y_3209_ = v___y_3248_;
v___y_3210_ = v___y_3249_;
v___y_3211_ = v___y_3250_;
v___y_3212_ = v___y_3252_;
v___y_3213_ = v___y_3253_;
v___y_3214_ = v___x_3267_;
v___y_3215_ = v___y_3257_;
v___y_3216_ = v___y_3256_;
v___y_3217_ = v___y_3255_;
v___y_3218_ = v___y_3258_;
v___y_3219_ = v___y_3259_;
v___y_3220_ = v___y_3260_;
v___y_3221_ = v___y_3262_;
v___y_3222_ = v___y_3261_;
v___y_3223_ = v___x_3274_;
goto v___jp_3200_;
}
}
v___jp_3275_:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
lean_inc_ref(v___y_3279_);
v___x_3300_ = l_Array_append___redArg(v___y_3279_, v___y_3299_);
lean_dec_ref(v___y_3299_);
lean_inc(v___y_3289_);
lean_inc(v___y_3293_);
v___x_3301_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3301_, 0, v___y_3293_);
lean_ctor_set(v___x_3301_, 1, v___y_3289_);
lean_ctor_set(v___x_3301_, 2, v___x_3300_);
if (lean_obj_tag(v___y_3294_) == 1)
{
lean_object* v_val_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_val_3302_ = lean_ctor_get(v___y_3294_, 0);
lean_inc(v_val_3302_);
lean_dec_ref(v___y_3294_);
v___x_3303_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_3281_);
v___x_3304_ = l_Lean_Name_mkStr4(v___x_3013_, v___x_3014_, v___y_3281_, v___x_3303_);
v___x_3305_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___y_3293_, 4);
v___x_3306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___y_3293_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
lean_inc_ref(v___y_3279_);
v___x_3307_ = l_Array_append___redArg(v___y_3279_, v_val_3302_);
lean_dec(v_val_3302_);
lean_inc(v___y_3289_);
v___x_3308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3308_, 0, v___y_3293_);
lean_ctor_set(v___x_3308_, 1, v___y_3289_);
lean_ctor_set(v___x_3308_, 2, v___x_3307_);
v___x_3309_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_3310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___y_3293_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = l_Lean_Syntax_node3(v___y_3293_, v___x_3304_, v___x_3306_, v___x_3308_, v___x_3310_);
v___x_3312_ = l_Array_mkArray1___redArg(v___x_3311_);
v___y_3240_ = v___y_3276_;
v___y_3241_ = v___y_3277_;
v___y_3242_ = v___y_3278_;
v___y_3243_ = v___y_3279_;
v___y_3244_ = v___y_3280_;
v___y_3245_ = v___y_3281_;
v___y_3246_ = v___y_3282_;
v___y_3247_ = v___y_3283_;
v___y_3248_ = v___y_3284_;
v___y_3249_ = v___y_3285_;
v___y_3250_ = v___y_3286_;
v___y_3251_ = v___y_3287_;
v___y_3252_ = v___y_3288_;
v___y_3253_ = v___y_3289_;
v___y_3254_ = v___y_3290_;
v___y_3255_ = v___y_3292_;
v___y_3256_ = v___y_3291_;
v___y_3257_ = v___x_3301_;
v___y_3258_ = v___y_3293_;
v___y_3259_ = v___y_3295_;
v___y_3260_ = v___y_3296_;
v___y_3261_ = v___y_3298_;
v___y_3262_ = v___y_3297_;
v___y_3263_ = v___x_3312_;
goto v___jp_3239_;
}
else
{
lean_object* v___x_3313_; 
lean_dec(v___y_3294_);
v___x_3313_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3240_ = v___y_3276_;
v___y_3241_ = v___y_3277_;
v___y_3242_ = v___y_3278_;
v___y_3243_ = v___y_3279_;
v___y_3244_ = v___y_3280_;
v___y_3245_ = v___y_3281_;
v___y_3246_ = v___y_3282_;
v___y_3247_ = v___y_3283_;
v___y_3248_ = v___y_3284_;
v___y_3249_ = v___y_3285_;
v___y_3250_ = v___y_3286_;
v___y_3251_ = v___y_3287_;
v___y_3252_ = v___y_3288_;
v___y_3253_ = v___y_3289_;
v___y_3254_ = v___y_3290_;
v___y_3255_ = v___y_3292_;
v___y_3256_ = v___y_3291_;
v___y_3257_ = v___x_3301_;
v___y_3258_ = v___y_3293_;
v___y_3259_ = v___y_3295_;
v___y_3260_ = v___y_3296_;
v___y_3261_ = v___y_3298_;
v___y_3262_ = v___y_3297_;
v___y_3263_ = v___x_3313_;
goto v___jp_3239_;
}
}
v___jp_3314_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3334_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__12));
v___x_3335_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__13));
v___x_3336_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_3337_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v___y_3328_) == 1)
{
lean_object* v_val_3338_; lean_object* v___x_3339_; 
v_val_3338_ = lean_ctor_get(v___y_3328_, 0);
lean_inc(v_val_3338_);
v___x_3339_ = l_Array_mkArray1___redArg(v_val_3338_);
v___y_3276_ = v___y_3315_;
v___y_3277_ = v___y_3316_;
v___y_3278_ = v___y_3317_;
v___y_3279_ = v___x_3337_;
v___y_3280_ = v___y_3318_;
v___y_3281_ = v___y_3319_;
v___y_3282_ = v___y_3320_;
v___y_3283_ = v___y_3321_;
v___y_3284_ = v___y_3322_;
v___y_3285_ = v___y_3323_;
v___y_3286_ = v___y_3324_;
v___y_3287_ = v___y_3325_;
v___y_3288_ = v___y_3326_;
v___y_3289_ = v___x_3336_;
v___y_3290_ = v___x_3334_;
v___y_3291_ = v___y_3329_;
v___y_3292_ = v___y_3328_;
v___y_3293_ = v___y_3327_;
v___y_3294_ = v___y_3331_;
v___y_3295_ = v___y_3330_;
v___y_3296_ = v___x_3335_;
v___y_3297_ = v___y_3333_;
v___y_3298_ = v___y_3332_;
v___y_3299_ = v___x_3339_;
goto v___jp_3275_;
}
else
{
lean_object* v___x_3340_; 
v___x_3340_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3276_ = v___y_3315_;
v___y_3277_ = v___y_3316_;
v___y_3278_ = v___y_3317_;
v___y_3279_ = v___x_3337_;
v___y_3280_ = v___y_3318_;
v___y_3281_ = v___y_3319_;
v___y_3282_ = v___y_3320_;
v___y_3283_ = v___y_3321_;
v___y_3284_ = v___y_3322_;
v___y_3285_ = v___y_3323_;
v___y_3286_ = v___y_3324_;
v___y_3287_ = v___y_3325_;
v___y_3288_ = v___y_3326_;
v___y_3289_ = v___x_3336_;
v___y_3290_ = v___x_3334_;
v___y_3291_ = v___y_3329_;
v___y_3292_ = v___y_3328_;
v___y_3293_ = v___y_3327_;
v___y_3294_ = v___y_3331_;
v___y_3295_ = v___y_3330_;
v___y_3296_ = v___x_3335_;
v___y_3297_ = v___y_3333_;
v___y_3298_ = v___y_3332_;
v___y_3299_ = v___x_3340_;
goto v___jp_3275_;
}
}
v___jp_3341_:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_3358_, 0, v___y_3347_);
v___x_3359_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v___x_3358_, v___y_3356_, v___y_3357_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v_args_3361_; size_t v_sz_3362_; size_t v___x_3363_; lean_object* v___x_3364_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref(v___x_3359_);
v_args_3361_ = l_Lean_Syntax_getArgs(v___y_3343_);
lean_dec(v___y_3343_);
v_sz_3362_ = lean_array_size(v_args_3361_);
v___x_3363_ = ((size_t)0ULL);
v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_3362_, v___x_3363_, v_args_3361_, v___y_3356_, v___y_3357_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3366_; lean_object* v_fst_3367_; lean_object* v_snd_3368_; lean_object* v___x_3369_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref(v___x_3364_);
v___x_3366_ = l_Array_unzip___redArg(v_a_3365_);
lean_dec(v_a_3365_);
v_fst_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_fst_3367_);
v_snd_3368_ = lean_ctor_get(v___x_3366_, 1);
lean_inc(v_snd_3368_);
lean_dec_ref(v___x_3366_);
v___x_3369_ = l_Lean_Elab_Command_getRef___redArg(v___y_3356_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v___x_3371_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_a_3370_);
lean_dec_ref(v___x_3369_);
v___x_3371_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3356_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_quotContext_x3f_3372_; lean_object* v___x_3373_; uint8_t v___x_3374_; lean_object* v___x_3375_; 
lean_dec_ref(v___x_3371_);
v_quotContext_x3f_3372_ = lean_ctor_get(v___y_3356_, 5);
v___x_3373_ = l_Lean_Syntax_getArg(v___y_3349_, v___y_3344_);
lean_dec(v___y_3349_);
v___x_3374_ = 0;
v___x_3375_ = l_Lean_SourceInfo_fromRef(v_a_3370_, v___x_3374_);
lean_dec(v_a_3370_);
if (lean_obj_tag(v_quotContext_x3f_3372_) == 0)
{
lean_object* v___x_3376_; 
v___x_3376_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3357_);
lean_dec_ref(v___x_3376_);
v___y_3315_ = v___y_3342_;
v___y_3316_ = v___x_3374_;
v___y_3317_ = v___y_3345_;
v___y_3318_ = v___x_3373_;
v___y_3319_ = v___y_3346_;
v___y_3320_ = v___y_3348_;
v___y_3321_ = v___y_3357_;
v___y_3322_ = v___y_3350_;
v___y_3323_ = v___y_3356_;
v___y_3324_ = v_expectedType_x3f_3355_;
v___y_3325_ = v___y_3351_;
v___y_3326_ = v_a_3360_;
v___y_3327_ = v___x_3375_;
v___y_3328_ = v___y_3352_;
v___y_3329_ = v_fst_3367_;
v___y_3330_ = v___x_3363_;
v___y_3331_ = v___y_3353_;
v___y_3332_ = v_snd_3368_;
v___y_3333_ = v___y_3354_;
goto v___jp_3314_;
}
else
{
v___y_3315_ = v___y_3342_;
v___y_3316_ = v___x_3374_;
v___y_3317_ = v___y_3345_;
v___y_3318_ = v___x_3373_;
v___y_3319_ = v___y_3346_;
v___y_3320_ = v___y_3348_;
v___y_3321_ = v___y_3357_;
v___y_3322_ = v___y_3350_;
v___y_3323_ = v___y_3356_;
v___y_3324_ = v_expectedType_x3f_3355_;
v___y_3325_ = v___y_3351_;
v___y_3326_ = v_a_3360_;
v___y_3327_ = v___x_3375_;
v___y_3328_ = v___y_3352_;
v___y_3329_ = v_fst_3367_;
v___y_3330_ = v___x_3363_;
v___y_3331_ = v___y_3353_;
v___y_3332_ = v_snd_3368_;
v___y_3333_ = v___y_3354_;
goto v___jp_3314_;
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec(v_a_3370_);
lean_dec(v_snd_3368_);
lean_dec(v_fst_3367_);
lean_dec(v_a_3360_);
lean_dec(v_expectedType_x3f_3355_);
lean_dec(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec(v___y_3342_);
v_a_3377_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3371_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3371_);
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
lean_dec(v_snd_3368_);
lean_dec(v_fst_3367_);
lean_dec(v_a_3360_);
lean_dec(v_expectedType_x3f_3355_);
lean_dec(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec(v___y_3342_);
v_a_3385_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3369_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3369_);
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
lean_dec(v_a_3360_);
lean_dec(v_expectedType_x3f_3355_);
lean_dec(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec(v___y_3342_);
v_a_3393_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3364_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3364_);
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
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec(v_expectedType_x3f_3355_);
lean_dec(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec(v___y_3343_);
lean_dec(v___y_3342_);
v_a_3401_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3359_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3359_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
v___jp_3409_:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
v___x_3424_ = lean_unsigned_to_nat(8u);
v___x_3425_ = l_Lean_Syntax_getArg(v_x_3009_, v___x_3424_);
v___x_3426_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__15));
lean_inc(v___x_3425_);
v___x_3427_ = l_Lean_Syntax_isOfKind(v___x_3425_, v___x_3426_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; 
lean_dec(v___x_3425_);
lean_dec(v_prio_x3f_3421_);
lean_dec(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec(v___y_3413_);
lean_dec(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec(v_x_3009_);
v___x_3428_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3428_;
}
else
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; 
v___x_3429_ = lean_unsigned_to_nat(7u);
v___x_3430_ = l_Lean_Syntax_getArg(v_x_3009_, v___x_3429_);
lean_dec(v_x_3009_);
v___x_3431_ = l_Lean_Syntax_getArg(v___x_3425_, v___y_3420_);
v___x_3432_ = l_Lean_Syntax_getArg(v___x_3425_, v___y_3412_);
v___x_3433_ = l_Lean_Syntax_isNone(v___x_3432_);
if (v___x_3433_ == 0)
{
uint8_t v___x_3434_; 
lean_inc(v___x_3432_);
v___x_3434_ = l_Lean_Syntax_matchesNull(v___x_3432_, v___y_3412_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; 
lean_dec(v___x_3432_);
lean_dec(v___x_3431_);
lean_dec(v___x_3430_);
lean_dec(v___x_3425_);
lean_dec(v_prio_x3f_3421_);
lean_dec(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec(v___y_3413_);
lean_dec(v___y_3411_);
lean_dec(v___y_3410_);
v___x_3435_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3435_;
}
else
{
lean_object* v_expectedType_x3f_3436_; lean_object* v___x_3437_; 
v_expectedType_x3f_3436_ = l_Lean_Syntax_getArg(v___x_3432_, v___y_3420_);
lean_dec(v___x_3432_);
v___x_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3437_, 0, v_expectedType_x3f_3436_);
v___y_3342_ = v___y_3410_;
v___y_3343_ = v___x_3430_;
v___y_3344_ = v___y_3414_;
v___y_3345_ = v___y_3415_;
v___y_3346_ = v___y_3419_;
v___y_3347_ = v_prio_x3f_3421_;
v___y_3348_ = v___x_3431_;
v___y_3349_ = v___x_3425_;
v___y_3350_ = v___y_3411_;
v___y_3351_ = v___y_3413_;
v___y_3352_ = v___y_3416_;
v___y_3353_ = v___y_3417_;
v___y_3354_ = v___y_3418_;
v_expectedType_x3f_3355_ = v___x_3437_;
v___y_3356_ = v___y_3422_;
v___y_3357_ = v___y_3423_;
goto v___jp_3341_;
}
}
else
{
lean_object* v___x_3438_; 
lean_dec(v___x_3432_);
v___x_3438_ = lean_box(0);
v___y_3342_ = v___y_3410_;
v___y_3343_ = v___x_3430_;
v___y_3344_ = v___y_3414_;
v___y_3345_ = v___y_3415_;
v___y_3346_ = v___y_3419_;
v___y_3347_ = v_prio_x3f_3421_;
v___y_3348_ = v___x_3431_;
v___y_3349_ = v___x_3425_;
v___y_3350_ = v___y_3411_;
v___y_3351_ = v___y_3413_;
v___y_3352_ = v___y_3416_;
v___y_3353_ = v___y_3417_;
v___y_3354_ = v___y_3418_;
v_expectedType_x3f_3355_ = v___x_3438_;
v___y_3356_ = v___y_3422_;
v___y_3357_ = v___y_3423_;
goto v___jp_3341_;
}
}
}
v___jp_3439_:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; 
v___x_3454_ = lean_unsigned_to_nat(6u);
v___x_3455_ = l_Lean_Syntax_getArg(v_x_3009_, v___x_3454_);
v___x_3456_ = l_Lean_Syntax_isNone(v___x_3455_);
if (v___x_3456_ == 0)
{
uint8_t v___x_3457_; 
lean_inc(v___x_3455_);
v___x_3457_ = l_Lean_Syntax_matchesNull(v___x_3455_, v___y_3448_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; 
lean_dec(v___x_3455_);
lean_dec(v_name_x3f_3451_);
lean_dec(v___y_3450_);
lean_dec(v___y_3447_);
lean_dec(v___y_3445_);
lean_dec(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec(v_x_3009_);
v___x_3458_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3458_;
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; uint8_t v___x_3461_; 
v___x_3459_ = l_Lean_Syntax_getArg(v___x_3455_, v___x_3058_);
lean_dec(v___x_3455_);
v___x_3460_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
lean_inc(v___x_3459_);
v___x_3461_ = l_Lean_Syntax_isOfKind(v___x_3459_, v___x_3460_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; 
lean_dec(v___x_3459_);
lean_dec(v_name_x3f_3451_);
lean_dec(v___y_3450_);
lean_dec(v___y_3447_);
lean_dec(v___y_3445_);
lean_dec(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec(v_x_3009_);
v___x_3462_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3462_;
}
else
{
lean_object* v_prio_x3f_3463_; lean_object* v___x_3464_; 
v_prio_x3f_3463_ = l_Lean_Syntax_getArg(v___x_3459_, v___y_3446_);
lean_dec(v___x_3459_);
v___x_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3464_, 0, v_prio_x3f_3463_);
v___y_3410_ = v___y_3440_;
v___y_3411_ = v_name_x3f_3451_;
v___y_3412_ = v___y_3442_;
v___y_3413_ = v___y_3441_;
v___y_3414_ = v___y_3443_;
v___y_3415_ = v___y_3444_;
v___y_3416_ = v___y_3445_;
v___y_3417_ = v___y_3447_;
v___y_3418_ = v___y_3450_;
v___y_3419_ = v___y_3449_;
v___y_3420_ = v___y_3448_;
v_prio_x3f_3421_ = v___x_3464_;
v___y_3422_ = v___y_3452_;
v___y_3423_ = v___y_3453_;
goto v___jp_3409_;
}
}
}
else
{
lean_object* v___x_3465_; 
lean_dec(v___x_3455_);
v___x_3465_ = lean_box(0);
v___y_3410_ = v___y_3440_;
v___y_3411_ = v_name_x3f_3451_;
v___y_3412_ = v___y_3442_;
v___y_3413_ = v___y_3441_;
v___y_3414_ = v___y_3443_;
v___y_3415_ = v___y_3444_;
v___y_3416_ = v___y_3445_;
v___y_3417_ = v___y_3447_;
v___y_3418_ = v___y_3450_;
v___y_3419_ = v___y_3449_;
v___y_3420_ = v___y_3448_;
v_prio_x3f_3421_ = v___x_3465_;
v___y_3422_ = v___y_3452_;
v___y_3423_ = v___y_3453_;
goto v___jp_3409_;
}
}
v___jp_3466_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; uint8_t v___x_3482_; 
v___x_3480_ = lean_unsigned_to_nat(5u);
v___x_3481_ = l_Lean_Syntax_getArg(v_x_3009_, v___x_3480_);
v___x_3482_ = l_Lean_Syntax_isNone(v___x_3481_);
if (v___x_3482_ == 0)
{
uint8_t v___x_3483_; 
lean_inc(v___x_3481_);
v___x_3483_ = l_Lean_Syntax_matchesNull(v___x_3481_, v___y_3476_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3484_; 
lean_dec(v___x_3481_);
lean_dec(v_prec_x3f_3477_);
lean_dec(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec(v___y_3471_);
lean_dec(v___y_3467_);
lean_dec(v_x_3009_);
v___x_3484_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3484_;
}
else
{
lean_object* v___x_3485_; lean_object* v___x_3486_; uint8_t v___x_3487_; 
v___x_3485_ = l_Lean_Syntax_getArg(v___x_3481_, v___x_3058_);
lean_dec(v___x_3481_);
v___x_3486_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
lean_inc(v___x_3485_);
v___x_3487_ = l_Lean_Syntax_isOfKind(v___x_3485_, v___x_3486_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
lean_dec(v___x_3485_);
lean_dec(v_prec_x3f_3477_);
lean_dec(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec(v___y_3471_);
lean_dec(v___y_3467_);
lean_dec(v_x_3009_);
v___x_3488_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3488_;
}
else
{
lean_object* v_name_x3f_3489_; lean_object* v___x_3490_; 
v_name_x3f_3489_ = l_Lean_Syntax_getArg(v___x_3485_, v___y_3472_);
lean_dec(v___x_3485_);
v___x_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3490_, 0, v_name_x3f_3489_);
v___y_3440_ = v___y_3467_;
v___y_3441_ = v_prec_x3f_3477_;
v___y_3442_ = v___y_3468_;
v___y_3443_ = v___y_3469_;
v___y_3444_ = v___y_3470_;
v___y_3445_ = v___y_3471_;
v___y_3446_ = v___y_3472_;
v___y_3447_ = v___y_3473_;
v___y_3448_ = v___y_3476_;
v___y_3449_ = v___y_3475_;
v___y_3450_ = v___y_3474_;
v_name_x3f_3451_ = v___x_3490_;
v___y_3452_ = v___y_3478_;
v___y_3453_ = v___y_3479_;
goto v___jp_3439_;
}
}
}
else
{
lean_object* v___x_3491_; 
lean_dec(v___x_3481_);
v___x_3491_ = lean_box(0);
v___y_3440_ = v___y_3467_;
v___y_3441_ = v_prec_x3f_3477_;
v___y_3442_ = v___y_3468_;
v___y_3443_ = v___y_3469_;
v___y_3444_ = v___y_3470_;
v___y_3445_ = v___y_3471_;
v___y_3446_ = v___y_3472_;
v___y_3447_ = v___y_3473_;
v___y_3448_ = v___y_3476_;
v___y_3449_ = v___y_3475_;
v___y_3450_ = v___y_3474_;
v_name_x3f_3451_ = v___x_3491_;
v___y_3452_ = v___y_3478_;
v___y_3453_ = v___y_3479_;
goto v___jp_3439_;
}
}
v___jp_3492_:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; 
v___x_3498_ = lean_unsigned_to_nat(2u);
v___x_3499_ = l_Lean_Syntax_getArg(v_x_3009_, v___x_3498_);
v___x_3500_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_3501_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v___x_3499_);
v___x_3502_ = l_Lean_Syntax_isOfKind(v___x_3499_, v___x_3501_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; 
lean_dec(v___x_3499_);
lean_dec(v_attrs_x3f_3495_);
lean_dec(v___y_3493_);
lean_dec(v_x_3009_);
v___x_3503_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3503_;
}
else
{
lean_object* v___x_3504_; lean_object* v_tk_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; uint8_t v___x_3508_; 
v___x_3504_ = lean_unsigned_to_nat(3u);
v_tk_3505_ = l_Lean_Syntax_getArg(v_x_3009_, v___x_3504_);
v___x_3506_ = lean_unsigned_to_nat(4u);
v___x_3507_ = l_Lean_Syntax_getArg(v_x_3009_, v___x_3506_);
v___x_3508_ = l_Lean_Syntax_isNone(v___x_3507_);
if (v___x_3508_ == 0)
{
uint8_t v___x_3509_; 
lean_inc(v___x_3507_);
v___x_3509_ = l_Lean_Syntax_matchesNull(v___x_3507_, v___y_3494_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; 
lean_dec(v___x_3507_);
lean_dec(v_tk_3505_);
lean_dec(v___x_3499_);
lean_dec(v_attrs_x3f_3495_);
lean_dec(v___y_3493_);
lean_dec(v_x_3009_);
v___x_3510_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3510_;
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; uint8_t v___x_3513_; 
v___x_3511_ = l_Lean_Syntax_getArg(v___x_3507_, v___x_3058_);
lean_dec(v___x_3507_);
v___x_3512_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
lean_inc(v___x_3511_);
v___x_3513_ = l_Lean_Syntax_isOfKind(v___x_3511_, v___x_3512_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; 
lean_dec(v___x_3511_);
lean_dec(v_tk_3505_);
lean_dec(v___x_3499_);
lean_dec(v_attrs_x3f_3495_);
lean_dec(v___y_3493_);
lean_dec(v_x_3009_);
v___x_3514_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3514_;
}
else
{
lean_object* v_prec_x3f_3515_; lean_object* v___x_3516_; 
v_prec_x3f_3515_ = l_Lean_Syntax_getArg(v___x_3511_, v___y_3494_);
lean_dec(v___x_3511_);
v___x_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3516_, 0, v_prec_x3f_3515_);
v___y_3467_ = v_tk_3505_;
v___y_3468_ = v___x_3498_;
v___y_3469_ = v___x_3506_;
v___y_3470_ = v___x_3501_;
v___y_3471_ = v___y_3493_;
v___y_3472_ = v___x_3504_;
v___y_3473_ = v_attrs_x3f_3495_;
v___y_3474_ = v___x_3499_;
v___y_3475_ = v___x_3500_;
v___y_3476_ = v___y_3494_;
v_prec_x3f_3477_ = v___x_3516_;
v___y_3478_ = v___y_3496_;
v___y_3479_ = v___y_3497_;
goto v___jp_3466_;
}
}
}
else
{
lean_object* v___x_3517_; 
lean_dec(v___x_3507_);
v___x_3517_ = lean_box(0);
v___y_3467_ = v_tk_3505_;
v___y_3468_ = v___x_3498_;
v___y_3469_ = v___x_3506_;
v___y_3470_ = v___x_3501_;
v___y_3471_ = v___y_3493_;
v___y_3472_ = v___x_3504_;
v___y_3473_ = v_attrs_x3f_3495_;
v___y_3474_ = v___x_3499_;
v___y_3475_ = v___x_3500_;
v___y_3476_ = v___y_3494_;
v_prec_x3f_3477_ = v___x_3517_;
v___y_3478_ = v___y_3496_;
v___y_3479_ = v___y_3497_;
goto v___jp_3466_;
}
}
}
v___jp_3518_:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; 
v___x_3522_ = lean_unsigned_to_nat(1u);
v___x_3523_ = l_Lean_Syntax_getArg(v_x_3009_, v___x_3522_);
v___x_3524_ = l_Lean_Syntax_isNone(v___x_3523_);
if (v___x_3524_ == 0)
{
uint8_t v___x_3525_; 
lean_inc(v___x_3523_);
v___x_3525_ = l_Lean_Syntax_matchesNull(v___x_3523_, v___x_3522_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; 
lean_dec(v___x_3523_);
lean_dec(v_doc_x3f_3519_);
lean_dec(v_x_3009_);
v___x_3526_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3526_;
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; 
v___x_3527_ = l_Lean_Syntax_getArg(v___x_3523_, v___x_3058_);
lean_dec(v___x_3523_);
v___x_3528_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(v___x_3527_);
v___x_3529_ = l_Lean_Syntax_isOfKind(v___x_3527_, v___x_3528_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; 
lean_dec(v___x_3527_);
lean_dec(v_doc_x3f_3519_);
lean_dec(v_x_3009_);
v___x_3530_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3530_;
}
else
{
lean_object* v___x_3531_; lean_object* v_attrs_x3f_3532_; lean_object* v___x_3533_; 
v___x_3531_ = l_Lean_Syntax_getArg(v___x_3527_, v___x_3522_);
lean_dec(v___x_3527_);
v_attrs_x3f_3532_ = l_Lean_Syntax_getArgs(v___x_3531_);
lean_dec(v___x_3531_);
v___x_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3533_, 0, v_attrs_x3f_3532_);
v___y_3493_ = v_doc_x3f_3519_;
v___y_3494_ = v___x_3522_;
v_attrs_x3f_3495_ = v___x_3533_;
v___y_3496_ = v___y_3520_;
v___y_3497_ = v___y_3521_;
goto v___jp_3492_;
}
}
}
else
{
lean_object* v___x_3534_; 
lean_dec(v___x_3523_);
v___x_3534_ = lean_box(0);
v___y_3493_ = v_doc_x3f_3519_;
v___y_3494_ = v___x_3522_;
v_attrs_x3f_3495_ = v___x_3534_;
v___y_3496_ = v___y_3520_;
v___y_3497_ = v___y_3521_;
goto v___jp_3492_;
}
}
}
v___jp_3015_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
lean_inc_ref(v___y_3021_);
v___x_3032_ = l_Array_append___redArg(v___y_3021_, v___y_3031_);
lean_dec_ref(v___y_3031_);
lean_inc_n(v___y_3029_, 4);
lean_inc_n(v___y_3019_, 11);
v___x_3033_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3033_, 0, v___y_3019_);
lean_ctor_set(v___x_3033_, 1, v___y_3029_);
lean_ctor_set(v___x_3033_, 2, v___x_3032_);
v___x_3034_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref_n(v___y_3022_, 3);
v___x_3035_ = l_Lean_Name_mkStr4(v___x_3013_, v___x_3014_, v___y_3022_, v___x_3034_);
v___x_3036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_3037_ = l_Lean_Name_mkStr4(v___x_3013_, v___x_3014_, v___y_3022_, v___x_3036_);
v___x_3038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_3039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___y_3019_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
v___x_3040_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__0));
v___x_3041_ = l_Lean_Name_mkStr4(v___x_3013_, v___x_3014_, v___y_3022_, v___x_3040_);
v___x_3042_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__1));
v___x_3043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___y_3019_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
lean_inc_ref(v___y_3020_);
v___x_3044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___y_3019_);
lean_ctor_set(v___x_3044_, 1, v___y_3020_);
v___x_3045_ = l_Lean_Syntax_node3(v___y_3019_, v___x_3041_, v___x_3043_, v___y_3028_, v___x_3044_);
v___x_3046_ = l_Lean_Syntax_node1(v___y_3019_, v___y_3029_, v___x_3045_);
v___x_3047_ = l_Lean_Syntax_node1(v___y_3019_, v___y_3029_, v___x_3046_);
v___x_3048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_3049_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___y_3019_);
lean_ctor_set(v___x_3049_, 1, v___x_3048_);
v___x_3050_ = l_Lean_Syntax_node4(v___y_3019_, v___x_3037_, v___x_3039_, v___x_3047_, v___x_3049_, v___y_3023_);
v___x_3051_ = l_Lean_Syntax_node1(v___y_3019_, v___y_3029_, v___x_3050_);
v___x_3052_ = l_Lean_Syntax_node1(v___y_3019_, v___x_3035_, v___x_3051_);
lean_inc(v___y_3024_);
lean_inc(v___y_3025_);
v___x_3053_ = l_Lean_Syntax_node8(v___y_3019_, v___y_3025_, v___y_3018_, v___y_3024_, v___y_3016_, v___y_3030_, v___y_3024_, v___y_3017_, v___x_3033_, v___x_3052_);
v___x_3054_ = l_Lean_Elab_Command_elabCommand(v___x_3053_, v___y_3027_, v___y_3026_);
return v___x_3054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object* v_x_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Lean_Elab_Command_elabElab(v_x_3546_, v_a_3547_, v_a_3548_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_3547_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object* v_00_u03b1_3551_, lean_object* v_x_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_3552_, v___y_3554_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3556_, lean_object* v_x_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(v_00_u03b1_3556_, v_x_3557_, v___y_3558_, v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v_x_3557_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object* v_00_u03b1_3561_, lean_object* v_ref_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_3562_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object* v_00_u03b1_3567_, lean_object* v_ref_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(v_00_u03b1_3567_, v_ref_3568_, v___y_3569_, v___y_3570_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object* v_00_u03b1_3573_, lean_object* v_x_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_3574_, v___y_3575_, v___y_3576_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object* v_00_u03b1_3579_, lean_object* v_x_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(v_00_u03b1_3579_, v_x_3580_, v___y_3581_, v___y_3582_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object* v_as_3585_, lean_object* v_as_x27_3586_, lean_object* v_b_3587_, lean_object* v_a_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_3586_, v_b_3587_, v___y_3589_, v___y_3590_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object* v_as_3593_, lean_object* v_as_x27_3594_, lean_object* v_b_3595_, lean_object* v_a_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(v_as_3593_, v_as_x27_3594_, v_b_3595_, v_a_3596_, v___y_3597_, v___y_3598_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v_as_x27_3594_);
lean_dec(v_as_3593_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3601_, lean_object* v_m_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_3602_, v_a_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3605_, lean_object* v_m_3606_, lean_object* v_a_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(v_00_u03b2_3605_, v_m_3606_, v_a_3607_);
lean_dec(v_a_3607_);
lean_dec_ref(v_m_3606_);
return v_res_3608_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_3609_, lean_object* v_x_3610_, lean_object* v_x_3611_){
_start:
{
uint8_t v___x_3612_; 
v___x_3612_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_3610_, v_x_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3613_, lean_object* v_x_3614_, lean_object* v_x_3615_){
_start:
{
uint8_t v_res_3616_; lean_object* v_r_3617_; 
v_res_3616_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(v_00_u03b2_3613_, v_x_3614_, v_x_3615_);
lean_dec_ref(v_x_3615_);
lean_dec_ref(v_x_3614_);
v_r_3617_ = lean_box(v_res_3616_);
return v_r_3617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_3618_, lean_object* v_a_3619_, lean_object* v_x_3620_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_3619_, v_x_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_3622_, lean_object* v_a_3623_, lean_object* v_x_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(v_00_u03b2_3622_, v_a_3623_, v_x_3624_);
lean_dec(v_x_3624_);
lean_dec(v_a_3623_);
return v_res_3625_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(lean_object* v_00_u03b2_3626_, lean_object* v_x_3627_, size_t v_x_3628_, lean_object* v_x_3629_){
_start:
{
uint8_t v___x_3630_; 
v___x_3630_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_3627_, v_x_3628_, v_x_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3631_, lean_object* v_x_3632_, lean_object* v_x_3633_, lean_object* v_x_3634_){
_start:
{
size_t v_x_21939__boxed_3635_; uint8_t v_res_3636_; lean_object* v_r_3637_; 
v_x_21939__boxed_3635_ = lean_unbox_usize(v_x_3633_);
lean_dec(v_x_3633_);
v_res_3636_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(v_00_u03b2_3631_, v_x_3632_, v_x_21939__boxed_3635_, v_x_3634_);
lean_dec_ref(v_x_3634_);
lean_dec_ref(v_x_3632_);
v_r_3637_ = lean_box(v_res_3636_);
return v_r_3637_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3638_, lean_object* v_keys_3639_, lean_object* v_vals_3640_, lean_object* v_heq_3641_, lean_object* v_i_3642_, lean_object* v_k_3643_){
_start:
{
uint8_t v___x_3644_; 
v___x_3644_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_3639_, v_i_3642_, v_k_3643_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b2_3645_, lean_object* v_keys_3646_, lean_object* v_vals_3647_, lean_object* v_heq_3648_, lean_object* v_i_3649_, lean_object* v_k_3650_){
_start:
{
uint8_t v_res_3651_; lean_object* v_r_3652_; 
v_res_3651_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(v_00_u03b2_3645_, v_keys_3646_, v_vals_3647_, v_heq_3648_, v_i_3649_, v_k_3650_);
lean_dec_ref(v_k_3650_);
lean_dec_ref(v_vals_3647_);
lean_dec_ref(v_keys_3646_);
v_r_3652_ = lean_box(v_res_3651_);
return v_r_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1(){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3660_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3661_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
v___x_3662_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3663_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElab___boxed), 4, 0);
v___x_3664_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3660_, v___x_3661_, v___x_3662_, v___x_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object* v_a_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3(){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3693_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3694_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6));
v___x_3695_ = l_Lean_addBuiltinDeclarationRanges(v___x_3693_, v___x_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object* v_a_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
return v_res_3697_;
}
}
lean_object* runtime_initialize_Lean_Elab_MacroArgUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ElabRules(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
