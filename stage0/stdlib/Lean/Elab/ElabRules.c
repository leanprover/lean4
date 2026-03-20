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
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
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
lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
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
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Parser_Command_visibility_ofAttrKind(lean_object*);
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabElabRules"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 97, 52, 186, 206, 196, 221, 235)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(81) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value),((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value),((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabElab"};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 235, 135, 254, 44, 234, 233, 9)}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object*);
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
lean_inc(v___x_114_);
v___x_120_ = l_Lean_Syntax_node1(v___x_114_, v___x_119_, v_a_106_);
lean_inc(v___x_114_);
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
v___x_263_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
lean_ctor_set(v___x_263_, 2, v___x_262_);
lean_ctor_set(v___x_263_, 3, v___x_261_);
lean_ctor_set(v___x_263_, 4, v___x_261_);
lean_ctor_set(v___x_263_, 5, v___x_261_);
lean_ctor_set(v___x_263_, 6, v___x_261_);
lean_ctor_set(v___x_263_, 7, v___x_261_);
lean_ctor_set(v___x_263_, 8, v___x_261_);
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
lean_inc(v_macroStack_302_);
lean_dec_ref(v___y_297_);
v___x_303_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_296_, v___y_298_);
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref(v___x_303_);
lean_inc(v_macroStack_302_);
v___x_305_ = l_Lean_Elab_getBetterRef(v_a_301_, v_macroStack_302_);
lean_dec(v_a_301_);
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
lean_dec_ref(v___y_297_);
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
lean_object* v_a_335_; lean_object* v_fileName_336_; lean_object* v_fileMap_337_; lean_object* v_currRecDepth_338_; lean_object* v_cmdPos_339_; lean_object* v_macroStack_340_; lean_object* v_quotContext_x3f_341_; lean_object* v_currMacroScope_342_; lean_object* v_snap_x3f_343_; lean_object* v_cancelTk_x3f_344_; uint8_t v_suppressElabErrors_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_354_; 
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
v_isSharedCheck_354_ = !lean_is_exclusive(v___y_331_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v___y_331_, 7);
lean_dec(v_unused_355_);
v___x_347_ = v___y_331_;
v_isShared_348_ = v_isSharedCheck_354_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_cancelTk_x3f_344_);
lean_inc(v_snap_x3f_343_);
lean_inc(v_currMacroScope_342_);
lean_inc(v_quotContext_x3f_341_);
lean_inc(v_macroStack_340_);
lean_inc(v_cmdPos_339_);
lean_inc(v_currRecDepth_338_);
lean_inc(v_fileMap_337_);
lean_inc(v_fileName_336_);
lean_dec(v___y_331_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_354_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v_ref_349_; lean_object* v___x_351_; 
v_ref_349_ = l_Lean_replaceRef(v_ref_329_, v_a_335_);
lean_dec(v_a_335_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 7, v_ref_349_);
v___x_351_ = v___x_347_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_fileName_336_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_fileMap_337_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_currRecDepth_338_);
lean_ctor_set(v_reuseFailAlloc_353_, 3, v_cmdPos_339_);
lean_ctor_set(v_reuseFailAlloc_353_, 4, v_macroStack_340_);
lean_ctor_set(v_reuseFailAlloc_353_, 5, v_quotContext_x3f_341_);
lean_ctor_set(v_reuseFailAlloc_353_, 6, v_currMacroScope_342_);
lean_ctor_set(v_reuseFailAlloc_353_, 7, v_ref_349_);
lean_ctor_set(v_reuseFailAlloc_353_, 8, v_snap_x3f_343_);
lean_ctor_set(v_reuseFailAlloc_353_, 9, v_cancelTk_x3f_344_);
lean_ctor_set_uint8(v_reuseFailAlloc_353_, sizeof(void*)*10, v_suppressElabErrors_345_);
v___x_351_ = v_reuseFailAlloc_353_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_330_, v___x_351_, v___y_332_);
return v___x_352_;
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec_ref(v___y_331_);
lean_dec_ref(v_msg_330_);
v_a_356_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_334_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_334_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object* v_ref_364_, lean_object* v_msg_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_364_, v_msg_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec(v_ref_364_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object* v_k_373_, lean_object* v_as_374_, size_t v_sz_375_, size_t v_i_376_, lean_object* v_b_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = lean_usize_dec_lt(v_i_376_, v_sz_375_);
if (v___x_378_ == 0)
{
lean_dec(v_k_373_);
return v_b_377_;
}
else
{
lean_object* v___x_379_; lean_object* v_a_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
lean_dec_ref(v_b_377_);
v___x_379_ = lean_box(0);
v_a_380_ = lean_array_uget_borrowed(v_as_374_, v_i_376_);
lean_inc(v_a_380_);
v___x_381_ = l_Lean_Syntax_getKind(v_a_380_);
lean_inc(v_k_373_);
v___x_382_ = l_Lean_Elab_Command_checkRuleKind(v___x_381_, v_k_373_);
lean_dec(v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; size_t v___x_384_; size_t v___x_385_; 
v___x_383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_add(v_i_376_, v___x_384_);
v_i_376_ = v___x_385_;
v_b_377_ = v___x_383_;
goto _start;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec(v_k_373_);
lean_inc(v_a_380_);
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v_a_380_);
v___x_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_379_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object* v_k_390_, lean_object* v_as_391_, lean_object* v_sz_392_, lean_object* v_i_393_, lean_object* v_b_394_){
_start:
{
size_t v_sz_boxed_395_; size_t v_i_boxed_396_; lean_object* v_res_397_; 
v_sz_boxed_395_ = lean_unbox_usize(v_sz_392_);
lean_dec(v_sz_392_);
v_i_boxed_396_ = lean_unbox_usize(v_i_393_);
lean_dec(v_i_393_);
v_res_397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_390_, v_as_391_, v_sz_boxed_395_, v_i_boxed_396_, v_b_394_);
lean_dec_ref(v_as_391_);
return v_res_397_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0));
v___x_400_ = l_Lean_stringToMessageData(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2));
v___x_403_ = l_Lean_stringToMessageData(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7(void){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Array_mkArray0(lean_box(0));
return v___x_411_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11));
v___x_418_ = l_Lean_stringToMessageData(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(lean_object* v_k_419_, size_t v_sz_420_, size_t v_i_421_, lean_object* v_bs_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
uint8_t v___x_426_; 
v___x_426_ = lean_usize_dec_lt(v_i_421_, v_sz_420_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
lean_dec_ref(v___y_423_);
lean_dec(v_k_419_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v_bs_422_);
return v___x_427_;
}
else
{
lean_object* v_v_428_; lean_object* v___x_429_; lean_object* v_bs_x27_430_; lean_object* v_a_432_; lean_object* v___y_438_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_v_428_ = lean_array_uget(v_bs_422_, v_i_421_);
v___x_429_ = lean_unsigned_to_nat(0u);
v_bs_x27_430_ = lean_array_uset(v_bs_422_, v_i_421_, v___x_429_);
v___x_457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5));
lean_inc(v_v_428_);
v___x_458_ = l_Lean_Syntax_isOfKind(v_v_428_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec(v_v_428_);
v___x_459_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
v___y_438_ = v___x_459_;
goto v___jp_437_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = l_Lean_Syntax_getArg(v_v_428_, v___x_460_);
lean_inc(v___x_461_);
v___x_462_ = l_Lean_Syntax_matchesNull(v___x_461_, v___x_460_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_dec(v___x_461_);
lean_dec(v_v_428_);
v___x_463_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
v___y_438_ = v___x_463_;
goto v___jp_437_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v_pat_482_; lean_object* v___y_484_; lean_object* v___y_485_; uint8_t v___x_537_; 
v___x_464_ = l_Lean_Syntax_getArg(v___x_461_, v___x_429_);
lean_dec(v___x_461_);
v___x_465_ = lean_unsigned_to_nat(3u);
v___x_466_ = l_Lean_Syntax_getArg(v_v_428_, v___x_465_);
v___x_480_ = l_Lean_Syntax_getArgs(v___x_464_);
lean_dec(v___x_464_);
v___x_481_ = lean_box(0);
v_pat_482_ = lean_array_get(v___x_481_, v___x_480_, v___x_429_);
v___x_537_ = l_Lean_Syntax_isQuot(v_pat_482_);
if (v___x_537_ == 0)
{
if (v___x_462_ == 0)
{
lean_inc_ref(v___y_423_);
v___y_484_ = v___y_423_;
v___y_485_ = v___y_424_;
goto v___jp_483_;
}
else
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
if (lean_obj_tag(v___x_538_) == 0)
{
lean_dec_ref(v___x_538_);
lean_inc_ref(v___y_423_);
v___y_484_ = v___y_423_;
v___y_485_ = v___y_424_;
goto v___jp_483_;
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_pat_482_);
lean_dec_ref(v___x_480_);
lean_dec(v___x_466_);
lean_dec_ref(v_bs_x27_430_);
lean_dec(v_v_428_);
lean_dec_ref(v___y_423_);
lean_dec(v_k_419_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
else
{
lean_inc_ref(v___y_423_);
v___y_484_ = v___y_423_;
v___y_485_ = v___y_424_;
goto v___jp_483_;
}
v___jp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(v___y_468_);
v___x_471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_471_, 0, v___y_468_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_473_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
v___x_474_ = l_Array_append___redArg(v___x_473_, v___y_469_);
lean_dec_ref(v___y_469_);
lean_inc(v___y_468_);
v___x_475_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_475_, 0, v___y_468_);
lean_ctor_set(v___x_475_, 1, v___x_472_);
lean_ctor_set(v___x_475_, 2, v___x_474_);
lean_inc(v___y_468_);
v___x_476_ = l_Lean_Syntax_node1(v___y_468_, v___x_472_, v___x_475_);
v___x_477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(v___y_468_);
v___x_478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_478_, 0, v___y_468_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = l_Lean_Syntax_node4(v___y_468_, v___x_457_, v___x_471_, v___x_476_, v___x_478_, v___x_466_);
v_a_432_ = v___x_479_;
goto v___jp_431_;
}
v___jp_483_:
{
lean_object* v_quoted_486_; lean_object* v_k_x27_487_; uint8_t v___x_488_; 
lean_inc(v_pat_482_);
v_quoted_486_ = l_Lean_Syntax_getQuotContent(v_pat_482_);
lean_inc(v_quoted_486_);
v_k_x27_487_ = l_Lean_Syntax_getKind(v_quoted_486_);
lean_inc(v_k_419_);
v___x_488_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_487_, v_k_419_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10));
v___x_490_ = lean_name_eq(v_k_x27_487_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
lean_dec(v_quoted_486_);
lean_dec(v_pat_482_);
lean_dec_ref(v___x_480_);
lean_dec(v___x_466_);
v___x_491_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12);
v___x_492_ = l_Lean_MessageData_ofName(v_k_x27_487_);
v___x_493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_428_, v___x_495_, v___y_484_, v___y_485_);
lean_dec(v_v_428_);
v___y_438_ = v___x_496_;
goto v___jp_437_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; size_t v_sz_499_; size_t v___x_500_; lean_object* v___x_501_; lean_object* v_fst_502_; 
lean_dec(v_k_x27_487_);
v___x_497_ = l_Lean_Syntax_getArgs(v_quoted_486_);
lean_dec(v_quoted_486_);
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
v_sz_499_ = lean_array_size(v___x_497_);
v___x_500_ = ((size_t)0ULL);
lean_inc(v_k_419_);
v___x_501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_419_, v___x_497_, v_sz_499_, v___x_500_, v___x_498_);
lean_dec_ref(v___x_497_);
v_fst_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_fst_502_);
lean_dec_ref(v___x_501_);
if (lean_obj_tag(v_fst_502_) == 0)
{
lean_dec(v_pat_482_);
lean_dec_ref(v___x_480_);
lean_dec(v___x_466_);
v___y_449_ = v___y_485_;
v___y_450_ = v___y_484_;
goto v___jp_448_;
}
else
{
lean_object* v_val_503_; 
v_val_503_ = lean_ctor_get(v_fst_502_, 0);
lean_inc(v_val_503_);
lean_dec_ref(v_fst_502_);
if (lean_obj_tag(v_val_503_) == 0)
{
lean_dec(v_pat_482_);
lean_dec_ref(v___x_480_);
lean_dec(v___x_466_);
v___y_449_ = v___y_485_;
v___y_450_ = v___y_484_;
goto v___jp_448_;
}
else
{
lean_object* v_val_504_; lean_object* v___x_505_; 
lean_dec(v_v_428_);
v_val_504_ = lean_ctor_get(v_val_503_, 0);
lean_inc(v_val_504_);
lean_dec_ref(v_val_503_);
v___x_505_ = l_Lean_Elab_Command_getRef___redArg(v___y_484_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___x_505_);
v___x_507_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_484_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_quotContext_x3f_508_; lean_object* v_pat_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec_ref(v___x_507_);
v_quotContext_x3f_508_ = lean_ctor_get(v___y_484_, 5);
lean_inc(v_quotContext_x3f_508_);
lean_dec_ref(v___y_484_);
v_pat_509_ = l_Lean_Syntax_setArg(v_pat_482_, v___x_460_, v_val_504_);
v___x_510_ = lean_array_set(v___x_480_, v___x_429_, v_pat_509_);
v___x_511_ = l_Lean_SourceInfo_fromRef(v_a_506_, v___x_488_);
lean_dec(v_a_506_);
if (lean_obj_tag(v_quotContext_x3f_508_) == 0)
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_485_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_dec_ref(v___x_512_);
v___y_468_ = v___x_511_;
v___y_469_ = v___x_510_;
goto v___jp_467_;
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v___x_511_);
lean_dec_ref(v___x_510_);
lean_dec(v___x_466_);
lean_dec_ref(v_bs_x27_430_);
lean_dec_ref(v___y_423_);
lean_dec(v_k_419_);
v_a_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_512_);
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
lean_dec_ref(v_quotContext_x3f_508_);
v___y_468_ = v___x_511_;
v___y_469_ = v___x_510_;
goto v___jp_467_;
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec(v_a_506_);
lean_dec(v_val_504_);
lean_dec_ref(v___y_484_);
lean_dec(v_pat_482_);
lean_dec_ref(v___x_480_);
lean_dec(v___x_466_);
lean_dec_ref(v_bs_x27_430_);
lean_dec_ref(v___y_423_);
lean_dec(v_k_419_);
v_a_521_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_507_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_507_);
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
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec(v_val_504_);
lean_dec_ref(v___y_484_);
lean_dec(v_pat_482_);
lean_dec_ref(v___x_480_);
lean_dec(v___x_466_);
lean_dec_ref(v_bs_x27_430_);
lean_dec_ref(v___y_423_);
lean_dec(v_k_419_);
v_a_529_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_505_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_505_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_x27_487_);
lean_dec(v_quoted_486_);
lean_dec_ref(v___y_484_);
lean_dec(v_pat_482_);
lean_dec_ref(v___x_480_);
lean_dec(v___x_466_);
v_a_432_ = v_v_428_;
goto v___jp_431_;
}
}
}
}
v___jp_431_:
{
size_t v___x_433_; size_t v___x_434_; lean_object* v___x_435_; 
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_add(v_i_421_, v___x_433_);
v___x_435_ = lean_array_uset(v_bs_x27_430_, v_i_421_, v_a_432_);
v_i_421_ = v___x_434_;
v_bs_422_ = v___x_435_;
goto _start;
}
v___jp_437_:
{
if (lean_obj_tag(v___y_438_) == 0)
{
lean_object* v_a_439_; 
v_a_439_ = lean_ctor_get(v___y_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref(v___y_438_);
v_a_432_ = v_a_439_;
goto v___jp_431_;
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec_ref(v_bs_x27_430_);
lean_dec_ref(v___y_423_);
lean_dec(v_k_419_);
v_a_440_ = lean_ctor_get(v___y_438_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___y_438_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___y_438_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___y_438_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
v___jp_448_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_451_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1);
lean_inc(v_k_419_);
v___x_452_ = l_Lean_MessageData_ofName(v_k_419_);
v___x_453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_428_, v___x_455_, v___y_450_, v___y_449_);
lean_dec(v_v_428_);
v___y_438_ = v___x_456_;
goto v___jp_437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___boxed(lean_object* v_k_547_, lean_object* v_sz_548_, lean_object* v_i_549_, lean_object* v_bs_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
size_t v_sz_boxed_554_; size_t v_i_boxed_555_; lean_object* v_res_556_; 
v_sz_boxed_554_ = lean_unbox_usize(v_sz_548_);
lean_dec(v_sz_548_);
v_i_boxed_555_ = lean_unbox_usize(v_i_549_);
lean_dec(v_i_549_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_547_, v_sz_boxed_554_, v_i_boxed_555_, v_bs_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
return v_res_556_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__4));
v___x_563_ = l_String_toRawSubstring_x27(v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__8));
v___x_569_ = l_String_toRawSubstring_x27(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_576_ = l_String_toRawSubstring_x27(v___x_575_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_589_ = l_String_toRawSubstring_x27(v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__34(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___x_604_ = l_String_toRawSubstring_x27(v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__36));
v___x_608_ = l_String_toRawSubstring_x27(v___x_607_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__41(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
v___x_613_ = l_String_toRawSubstring_x27(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__44(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__43));
v___x_618_ = l_String_toRawSubstring_x27(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__47(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__46));
v___x_622_ = l_String_toRawSubstring_x27(v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__50));
v___x_628_ = l_String_toRawSubstring_x27(v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__57));
v___x_638_ = l_Lean_stringToMessageData(v___x_637_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__59));
v___x_641_ = l_Lean_stringToMessageData(v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__71));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__75));
v___x_665_ = l_Lean_stringToMessageData(v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object* v_doc_x3f_666_, lean_object* v_attrs_x3f_667_, lean_object* v_attrKind_668_, lean_object* v_k_669_, lean_object* v_cat_x3f_670_, lean_object* v_expty_x3f_671_, lean_object* v_alts_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
size_t v_sz_676_; size_t v___x_677_; lean_object* v___x_678_; 
v_sz_676_ = lean_array_size(v_alts_672_);
v___x_677_ = ((size_t)0ULL);
lean_inc_ref(v_a_673_);
lean_inc(v_k_669_);
v___x_678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_669_, v_sz_676_, v___x_677_, v_alts_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_1689_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_1689_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_1689_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v_a_807_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v_a_921_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v_a_1059_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v_a_1172_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v_a_1324_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v_a_1459_; uint8_t v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v_catName_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; 
if (lean_obj_tag(v_cat_x3f_670_) == 1)
{
lean_object* v_val_1676_; lean_object* v___x_1677_; 
v_val_1676_ = lean_ctor_get(v_cat_x3f_670_, 0);
v___x_1677_ = l_Lean_TSyntax_getId(v_val_1676_);
v_catName_1503_ = v___x_1677_;
v___y_1504_ = v_a_673_;
v___y_1505_ = v_a_674_;
goto v___jp_1502_;
}
else
{
if (lean_obj_tag(v_expty_x3f_671_) == 1)
{
lean_object* v___x_1678_; 
v___x_1678_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v_catName_1503_ = v___x_1678_;
v___y_1504_ = v_a_673_;
v___y_1505_ = v_a_674_;
goto v___jp_1502_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_del_object(v___x_681_);
lean_dec(v_a_679_);
lean_dec(v_expty_x3f_671_);
lean_dec(v_k_669_);
lean_dec(v_attrKind_668_);
lean_dec(v_doc_x3f_666_);
v___x_1679_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__76, &l_Lean_Elab_Command_elabElabRulesAux___closed__76_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76);
v___x_1680_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_1679_, v_a_673_, v_a_674_);
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
v___jp_683_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
lean_inc_ref(v___y_687_);
v___x_696_ = l_Array_append___redArg(v___y_687_, v___y_695_);
lean_dec_ref(v___y_695_);
lean_inc(v___y_686_);
lean_inc(v___y_692_);
v___x_697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_697_, 0, v___y_692_);
lean_ctor_set(v___x_697_, 1, v___y_686_);
lean_ctor_set(v___x_697_, 2, v___x_696_);
v___x_698_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_699_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_700_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_690_);
v___x_701_ = l_Lean_Name_mkStr4(v___y_690_, v___x_698_, v___x_699_, v___x_700_);
v___x_702_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(v___y_692_);
v___x_703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_703_, 0, v___y_692_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_705_ = l_Lean_Syntax_SepArray_ofElems(v___x_704_, v___y_694_);
lean_dec_ref(v___y_694_);
lean_inc_ref(v___y_687_);
v___x_706_ = l_Array_append___redArg(v___y_687_, v___x_705_);
lean_dec_ref(v___x_705_);
lean_inc(v___y_686_);
lean_inc(v___y_692_);
v___x_707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_707_, 0, v___y_692_);
lean_ctor_set(v___x_707_, 1, v___y_686_);
lean_ctor_set(v___x_707_, 2, v___x_706_);
v___x_708_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(v___y_692_);
v___x_709_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_709_, 0, v___y_692_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
lean_inc(v___y_692_);
v___x_710_ = l_Lean_Syntax_node3(v___y_692_, v___x_701_, v___x_703_, v___x_707_, v___x_709_);
lean_inc(v___y_686_);
lean_inc(v___y_692_);
v___x_711_ = l_Lean_Syntax_node1(v___y_692_, v___y_686_, v___x_710_);
lean_inc(v___y_692_);
v___x_712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_712_, 0, v___y_692_);
lean_ctor_set(v___x_712_, 1, v___y_685_);
v___x_713_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_714_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(v___y_689_);
lean_inc(v___y_684_);
v___x_715_ = l_Lean_addMacroScope(v___y_684_, v___x_714_, v___y_689_);
v___x_716_ = lean_box(0);
lean_inc(v___y_692_);
v___x_717_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_717_, 0, v___y_692_);
lean_ctor_set(v___x_717_, 1, v___x_713_);
lean_ctor_set(v___x_717_, 2, v___x_715_);
lean_ctor_set(v___x_717_, 3, v___x_716_);
v___x_718_ = lean_mk_syntax_ident(v_k_669_);
lean_inc(v___y_686_);
lean_inc(v___y_692_);
v___x_719_ = l_Lean_Syntax_node2(v___y_692_, v___y_686_, v___x_717_, v___x_718_);
v___x_720_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___y_692_);
v___x_721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_721_, 0, v___y_692_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_723_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
lean_inc_ref(v___y_693_);
lean_inc_ref(v___y_690_);
v___x_724_ = l_Lean_Name_mkStr4(v___y_690_, v___y_693_, v___x_699_, v___x_723_);
lean_inc(v___y_689_);
lean_inc(v___x_724_);
lean_inc(v___y_684_);
v___x_725_ = l_Lean_addMacroScope(v___y_684_, v___x_724_, v___y_689_);
v___x_726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_716_);
v___x_727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_716_);
lean_inc(v___y_692_);
v___x_728_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_728_, 0, v___y_692_);
lean_ctor_set(v___x_728_, 1, v___x_722_);
lean_ctor_set(v___x_728_, 2, v___x_725_);
lean_ctor_set(v___x_728_, 3, v___x_727_);
v___x_729_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(v___y_692_);
v___x_730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_730_, 0, v___y_692_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(v___y_690_);
v___x_732_ = l_Lean_Name_mkStr4(v___y_690_, v___x_698_, v___x_699_, v___x_731_);
lean_inc(v___y_692_);
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v___y_692_);
lean_ctor_set(v___x_733_, 1, v___x_731_);
v___x_734_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
lean_inc_ref(v___y_690_);
v___x_735_ = l_Lean_Name_mkStr4(v___y_690_, v___x_698_, v___x_699_, v___x_734_);
v___x_736_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
v___x_737_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
lean_inc(v___y_689_);
lean_inc(v___y_684_);
v___x_738_ = l_Lean_addMacroScope(v___y_684_, v___x_737_, v___y_689_);
lean_inc(v___y_692_);
v___x_739_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_739_, 0, v___y_692_);
lean_ctor_set(v___x_739_, 1, v___x_736_);
lean_ctor_set(v___x_739_, 2, v___x_738_);
lean_ctor_set(v___x_739_, 3, v___x_716_);
v___x_740_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(v___y_690_);
v___x_741_ = l_Lean_Name_mkStr4(v___y_690_, v___x_698_, v___x_699_, v___x_740_);
v___x_742_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(v___y_692_);
v___x_743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_743_, 0, v___y_692_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
lean_inc(v___y_692_);
v___x_744_ = l_Lean_Syntax_node1(v___y_692_, v___x_741_, v___x_743_);
lean_inc(v___x_744_);
lean_inc_ref(v___x_739_);
lean_inc(v___y_686_);
lean_inc(v___y_692_);
v___x_745_ = l_Lean_Syntax_node2(v___y_692_, v___y_686_, v___x_739_, v___x_744_);
lean_inc_ref(v___y_687_);
lean_inc(v___y_686_);
lean_inc(v___y_692_);
v___x_746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_746_, 0, v___y_692_);
lean_ctor_set(v___x_746_, 1, v___y_686_);
lean_ctor_set(v___x_746_, 2, v___y_687_);
v___x_747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(v___y_692_);
v___x_748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_748_, 0, v___y_692_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
lean_inc_ref(v___y_690_);
v___x_750_ = l_Lean_Name_mkStr4(v___y_690_, v___x_698_, v___x_699_, v___x_749_);
lean_inc(v___y_692_);
v___x_751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_751_, 0, v___y_692_);
lean_ctor_set(v___x_751_, 1, v___x_749_);
v___x_752_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
lean_inc_ref(v___y_690_);
v___x_753_ = l_Lean_Name_mkStr4(v___y_690_, v___x_698_, v___x_699_, v___x_752_);
lean_inc_ref(v___x_746_);
lean_inc(v___y_692_);
v___x_754_ = l_Lean_Syntax_node2(v___y_692_, v___x_753_, v___x_746_, v___x_739_);
lean_inc(v___y_686_);
lean_inc(v___y_692_);
v___x_755_ = l_Lean_Syntax_node1(v___y_692_, v___y_686_, v___x_754_);
v___x_756_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc(v___y_692_);
v___x_757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_757_, 0, v___y_692_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(v___y_690_);
v___x_759_ = l_Lean_Name_mkStr4(v___y_690_, v___x_698_, v___x_699_, v___x_758_);
v___x_760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(v___y_690_);
v___x_761_ = l_Lean_Name_mkStr4(v___y_690_, v___x_698_, v___x_699_, v___x_760_);
v___x_762_ = l_Array_append___redArg(v___y_687_, v_a_679_);
lean_dec(v_a_679_);
v___x_763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(v___y_692_);
v___x_764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_764_, 0, v___y_692_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
lean_inc(v___y_686_);
lean_inc(v___y_692_);
v___x_765_ = l_Lean_Syntax_node1(v___y_692_, v___y_686_, v___x_744_);
lean_inc(v___y_686_);
lean_inc(v___y_692_);
v___x_766_ = l_Lean_Syntax_node1(v___y_692_, v___y_686_, v___x_765_);
v___x_767_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(v___y_690_);
v___x_768_ = l_Lean_Name_mkStr4(v___y_690_, v___x_698_, v___x_699_, v___x_767_);
v___x_769_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(v___y_692_);
v___x_770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_770_, 0, v___y_692_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_772_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_773_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_774_ = l_Lean_addMacroScope(v___y_684_, v___x_773_, v___y_689_);
v___x_775_ = l_Lean_Name_mkStr3(v___y_690_, v___y_693_, v___x_771_);
v___x_776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___x_716_);
v___x_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v___x_716_);
lean_inc(v___y_692_);
v___x_778_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_778_, 0, v___y_692_);
lean_ctor_set(v___x_778_, 1, v___x_772_);
lean_ctor_set(v___x_778_, 2, v___x_774_);
lean_ctor_set(v___x_778_, 3, v___x_777_);
lean_inc(v___y_692_);
v___x_779_ = l_Lean_Syntax_node2(v___y_692_, v___x_768_, v___x_770_, v___x_778_);
lean_inc_ref(v___x_748_);
lean_inc(v___y_692_);
v___x_780_ = l_Lean_Syntax_node4(v___y_692_, v___x_761_, v___x_764_, v___x_766_, v___x_748_, v___x_779_);
v___x_781_ = lean_array_push(v___x_762_, v___x_780_);
lean_inc(v___y_692_);
v___x_782_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_782_, 0, v___y_692_);
lean_ctor_set(v___x_782_, 1, v___y_686_);
lean_ctor_set(v___x_782_, 2, v___x_781_);
lean_inc(v___y_692_);
v___x_783_ = l_Lean_Syntax_node1(v___y_692_, v___x_759_, v___x_782_);
lean_inc_ref_n(v___x_746_, 2);
lean_inc(v___y_692_);
v___x_784_ = l_Lean_Syntax_node6(v___y_692_, v___x_750_, v___x_751_, v___x_746_, v___x_746_, v___x_755_, v___x_757_, v___x_783_);
lean_inc(v___y_692_);
v___x_785_ = l_Lean_Syntax_node4(v___y_692_, v___x_735_, v___x_745_, v___x_746_, v___x_748_, v___x_784_);
lean_inc(v___y_692_);
v___x_786_ = l_Lean_Syntax_node2(v___y_692_, v___x_732_, v___x_733_, v___x_785_);
v___x_787_ = lean_unsigned_to_nat(9u);
v___x_788_ = lean_mk_empty_array_with_capacity(v___x_787_);
v___x_789_ = lean_array_push(v___x_788_, v___x_697_);
v___x_790_ = lean_array_push(v___x_789_, v___x_711_);
v___x_791_ = lean_array_push(v___x_790_, v___y_688_);
v___x_792_ = lean_array_push(v___x_791_, v___x_712_);
v___x_793_ = lean_array_push(v___x_792_, v___x_719_);
v___x_794_ = lean_array_push(v___x_793_, v___x_721_);
v___x_795_ = lean_array_push(v___x_794_, v___x_728_);
v___x_796_ = lean_array_push(v___x_795_, v___x_730_);
v___x_797_ = lean_array_push(v___x_796_, v___x_786_);
v___x_798_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_798_, 0, v___y_692_);
lean_ctor_set(v___x_798_, 1, v___y_691_);
lean_ctor_set(v___x_798_, 2, v___x_797_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_798_);
v___x_800_ = v___x_681_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
v___jp_802_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_808_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_809_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_810_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_811_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_812_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_813_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_666_) == 1)
{
lean_object* v_val_814_; lean_object* v___x_815_; 
v_val_814_ = lean_ctor_get(v_doc_x3f_666_, 0);
lean_inc(v_val_814_);
lean_dec_ref(v_doc_x3f_666_);
v___x_815_ = l_Array_mkArray1___redArg(v_val_814_);
v___y_684_ = v_a_807_;
v___y_685_ = v___x_810_;
v___y_686_ = v___x_812_;
v___y_687_ = v___x_813_;
v___y_688_ = v___y_803_;
v___y_689_ = v___y_804_;
v___y_690_ = v___x_808_;
v___y_691_ = v___x_811_;
v___y_692_ = v___y_805_;
v___y_693_ = v___x_809_;
v___y_694_ = v___y_806_;
v___y_695_ = v___x_815_;
goto v___jp_683_;
}
else
{
lean_object* v___x_816_; 
lean_dec(v_doc_x3f_666_);
v___x_816_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_684_ = v_a_807_;
v___y_685_ = v___x_810_;
v___y_686_ = v___x_812_;
v___y_687_ = v___x_813_;
v___y_688_ = v___y_803_;
v___y_689_ = v___y_804_;
v___y_690_ = v___x_808_;
v___y_691_ = v___x_811_;
v___y_692_ = v___y_805_;
v___y_693_ = v___x_809_;
v___y_694_ = v___y_806_;
v___y_695_ = v___x_816_;
goto v___jp_683_;
}
}
v___jp_817_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_inc_ref(v___y_827_);
v___x_831_ = l_Array_append___redArg(v___y_827_, v___y_830_);
lean_dec_ref(v___y_830_);
lean_inc(v___y_829_);
lean_inc(v___y_823_);
v___x_832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_832_, 0, v___y_823_);
lean_ctor_set(v___x_832_, 1, v___y_829_);
lean_ctor_set(v___x_832_, 2, v___x_831_);
v___x_833_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_834_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_835_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_822_);
v___x_836_ = l_Lean_Name_mkStr4(v___y_822_, v___x_833_, v___x_834_, v___x_835_);
v___x_837_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(v___y_823_);
v___x_838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_838_, 0, v___y_823_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_840_ = l_Lean_Syntax_SepArray_ofElems(v___x_839_, v___y_820_);
lean_dec_ref(v___y_820_);
lean_inc_ref(v___y_827_);
v___x_841_ = l_Array_append___redArg(v___y_827_, v___x_840_);
lean_dec_ref(v___x_840_);
lean_inc(v___y_829_);
lean_inc(v___y_823_);
v___x_842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_842_, 0, v___y_823_);
lean_ctor_set(v___x_842_, 1, v___y_829_);
lean_ctor_set(v___x_842_, 2, v___x_841_);
v___x_843_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(v___y_823_);
v___x_844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_844_, 0, v___y_823_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
lean_inc(v___y_823_);
v___x_845_ = l_Lean_Syntax_node3(v___y_823_, v___x_836_, v___x_838_, v___x_842_, v___x_844_);
lean_inc(v___y_829_);
lean_inc(v___y_823_);
v___x_846_ = l_Lean_Syntax_node1(v___y_823_, v___y_829_, v___x_845_);
lean_inc(v___y_823_);
v___x_847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_847_, 0, v___y_823_);
lean_ctor_set(v___x_847_, 1, v___y_819_);
v___x_848_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_849_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(v___y_818_);
lean_inc(v___y_825_);
v___x_850_ = l_Lean_addMacroScope(v___y_825_, v___x_849_, v___y_818_);
v___x_851_ = lean_box(0);
lean_inc(v___y_823_);
v___x_852_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_852_, 0, v___y_823_);
lean_ctor_set(v___x_852_, 1, v___x_848_);
lean_ctor_set(v___x_852_, 2, v___x_850_);
lean_ctor_set(v___x_852_, 3, v___x_851_);
v___x_853_ = lean_mk_syntax_ident(v_k_669_);
lean_inc(v___y_829_);
lean_inc(v___y_823_);
v___x_854_ = l_Lean_Syntax_node2(v___y_823_, v___y_829_, v___x_852_, v___x_853_);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___y_823_);
v___x_856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_856_, 0, v___y_823_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__34, &l_Lean_Elab_Command_elabElabRulesAux___closed__34_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__34);
v___x_858_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
lean_inc_ref(v___y_828_);
lean_inc_ref(v___y_822_);
v___x_859_ = l_Lean_Name_mkStr4(v___y_822_, v___y_828_, v___y_821_, v___x_858_);
lean_inc(v___y_818_);
lean_inc(v___x_859_);
lean_inc(v___y_825_);
v___x_860_ = l_Lean_addMacroScope(v___y_825_, v___x_859_, v___y_818_);
v___x_861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_851_);
v___x_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v___x_851_);
lean_inc(v___y_823_);
v___x_863_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_863_, 0, v___y_823_);
lean_ctor_set(v___x_863_, 1, v___x_857_);
lean_ctor_set(v___x_863_, 2, v___x_860_);
lean_ctor_set(v___x_863_, 3, v___x_862_);
v___x_864_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(v___y_823_);
v___x_865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_865_, 0, v___y_823_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(v___y_822_);
v___x_867_ = l_Lean_Name_mkStr4(v___y_822_, v___x_833_, v___x_834_, v___x_866_);
lean_inc(v___y_823_);
v___x_868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_868_, 0, v___y_823_);
lean_ctor_set(v___x_868_, 1, v___x_866_);
v___x_869_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(v___y_822_);
v___x_870_ = l_Lean_Name_mkStr4(v___y_822_, v___x_833_, v___x_834_, v___x_869_);
v___x_871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(v___y_822_);
v___x_872_ = l_Lean_Name_mkStr4(v___y_822_, v___x_833_, v___x_834_, v___x_871_);
v___x_873_ = l_Array_append___redArg(v___y_827_, v_a_679_);
lean_dec(v_a_679_);
v___x_874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(v___y_823_);
v___x_875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_875_, 0, v___y_823_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(v___y_822_);
v___x_877_ = l_Lean_Name_mkStr4(v___y_822_, v___x_833_, v___x_834_, v___x_876_);
v___x_878_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(v___y_823_);
v___x_879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_879_, 0, v___y_823_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
lean_inc(v___y_823_);
v___x_880_ = l_Lean_Syntax_node1(v___y_823_, v___x_877_, v___x_879_);
lean_inc(v___y_829_);
lean_inc(v___y_823_);
v___x_881_ = l_Lean_Syntax_node1(v___y_823_, v___y_829_, v___x_880_);
lean_inc(v___y_829_);
lean_inc(v___y_823_);
v___x_882_ = l_Lean_Syntax_node1(v___y_823_, v___y_829_, v___x_881_);
v___x_883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(v___y_823_);
v___x_884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_884_, 0, v___y_823_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(v___y_822_);
v___x_886_ = l_Lean_Name_mkStr4(v___y_822_, v___x_833_, v___x_834_, v___x_885_);
v___x_887_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(v___y_823_);
v___x_888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_888_, 0, v___y_823_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_890_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_891_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_892_ = l_Lean_addMacroScope(v___y_825_, v___x_891_, v___y_818_);
v___x_893_ = l_Lean_Name_mkStr3(v___y_822_, v___y_828_, v___x_889_);
v___x_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v___x_851_);
v___x_895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___x_851_);
lean_inc(v___y_823_);
v___x_896_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_896_, 0, v___y_823_);
lean_ctor_set(v___x_896_, 1, v___x_890_);
lean_ctor_set(v___x_896_, 2, v___x_892_);
lean_ctor_set(v___x_896_, 3, v___x_895_);
lean_inc(v___y_823_);
v___x_897_ = l_Lean_Syntax_node2(v___y_823_, v___x_886_, v___x_888_, v___x_896_);
lean_inc(v___y_823_);
v___x_898_ = l_Lean_Syntax_node4(v___y_823_, v___x_872_, v___x_875_, v___x_882_, v___x_884_, v___x_897_);
v___x_899_ = lean_array_push(v___x_873_, v___x_898_);
lean_inc(v___y_823_);
v___x_900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_900_, 0, v___y_823_);
lean_ctor_set(v___x_900_, 1, v___y_829_);
lean_ctor_set(v___x_900_, 2, v___x_899_);
lean_inc(v___y_823_);
v___x_901_ = l_Lean_Syntax_node1(v___y_823_, v___x_870_, v___x_900_);
lean_inc(v___y_823_);
v___x_902_ = l_Lean_Syntax_node2(v___y_823_, v___x_867_, v___x_868_, v___x_901_);
v___x_903_ = lean_unsigned_to_nat(9u);
v___x_904_ = lean_mk_empty_array_with_capacity(v___x_903_);
v___x_905_ = lean_array_push(v___x_904_, v___x_832_);
v___x_906_ = lean_array_push(v___x_905_, v___x_846_);
v___x_907_ = lean_array_push(v___x_906_, v___y_826_);
v___x_908_ = lean_array_push(v___x_907_, v___x_847_);
v___x_909_ = lean_array_push(v___x_908_, v___x_854_);
v___x_910_ = lean_array_push(v___x_909_, v___x_856_);
v___x_911_ = lean_array_push(v___x_910_, v___x_863_);
v___x_912_ = lean_array_push(v___x_911_, v___x_865_);
v___x_913_ = lean_array_push(v___x_912_, v___x_902_);
v___x_914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_914_, 0, v___y_823_);
lean_ctor_set(v___x_914_, 1, v___y_824_);
lean_ctor_set(v___x_914_, 2, v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
v___jp_916_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_922_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_923_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_924_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_925_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_926_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_927_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_928_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_666_) == 1)
{
lean_object* v_val_929_; lean_object* v___x_930_; 
v_val_929_ = lean_ctor_get(v_doc_x3f_666_, 0);
lean_inc(v_val_929_);
lean_dec_ref(v_doc_x3f_666_);
v___x_930_ = l_Array_mkArray1___redArg(v_val_929_);
v___y_818_ = v___y_917_;
v___y_819_ = v___x_925_;
v___y_820_ = v___y_919_;
v___y_821_ = v___x_924_;
v___y_822_ = v___x_922_;
v___y_823_ = v___y_920_;
v___y_824_ = v___x_926_;
v___y_825_ = v_a_921_;
v___y_826_ = v___y_918_;
v___y_827_ = v___x_928_;
v___y_828_ = v___x_923_;
v___y_829_ = v___x_927_;
v___y_830_ = v___x_930_;
goto v___jp_817_;
}
else
{
lean_object* v___x_931_; 
lean_dec(v_doc_x3f_666_);
v___x_931_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_818_ = v___y_917_;
v___y_819_ = v___x_925_;
v___y_820_ = v___y_919_;
v___y_821_ = v___x_924_;
v___y_822_ = v___x_922_;
v___y_823_ = v___y_920_;
v___y_824_ = v___x_926_;
v___y_825_ = v_a_921_;
v___y_826_ = v___y_918_;
v___y_827_ = v___x_928_;
v___y_828_ = v___x_923_;
v___y_829_ = v___x_927_;
v___y_830_ = v___x_931_;
goto v___jp_817_;
}
}
v___jp_932_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_inc_ref(v___y_943_);
v___x_945_ = l_Array_append___redArg(v___y_943_, v___y_944_);
lean_dec_ref(v___y_944_);
lean_inc(v___y_938_);
lean_inc(v___y_935_);
v___x_946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_946_, 0, v___y_935_);
lean_ctor_set(v___x_946_, 1, v___y_938_);
lean_ctor_set(v___x_946_, 2, v___x_945_);
v___x_947_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_948_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_949_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_936_);
v___x_950_ = l_Lean_Name_mkStr4(v___y_936_, v___x_947_, v___x_948_, v___x_949_);
v___x_951_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(v___y_935_);
v___x_952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_952_, 0, v___y_935_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_954_ = l_Lean_Syntax_SepArray_ofElems(v___x_953_, v___y_937_);
lean_dec_ref(v___y_937_);
lean_inc_ref(v___y_943_);
v___x_955_ = l_Array_append___redArg(v___y_943_, v___x_954_);
lean_dec_ref(v___x_954_);
lean_inc(v___y_938_);
lean_inc(v___y_935_);
v___x_956_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_956_, 0, v___y_935_);
lean_ctor_set(v___x_956_, 1, v___y_938_);
lean_ctor_set(v___x_956_, 2, v___x_955_);
v___x_957_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(v___y_935_);
v___x_958_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_958_, 0, v___y_935_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
lean_inc(v___y_935_);
v___x_959_ = l_Lean_Syntax_node3(v___y_935_, v___x_950_, v___x_952_, v___x_956_, v___x_958_);
lean_inc(v___y_938_);
lean_inc(v___y_935_);
v___x_960_ = l_Lean_Syntax_node1(v___y_935_, v___y_938_, v___x_959_);
lean_inc(v___y_935_);
v___x_961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_961_, 0, v___y_935_);
lean_ctor_set(v___x_961_, 1, v___y_942_);
v___x_962_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_963_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(v___y_934_);
lean_inc(v___y_941_);
v___x_964_ = l_Lean_addMacroScope(v___y_941_, v___x_963_, v___y_934_);
v___x_965_ = lean_box(0);
lean_inc(v___y_935_);
v___x_966_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_966_, 0, v___y_935_);
lean_ctor_set(v___x_966_, 1, v___x_962_);
lean_ctor_set(v___x_966_, 2, v___x_964_);
lean_ctor_set(v___x_966_, 3, v___x_965_);
v___x_967_ = lean_mk_syntax_ident(v_k_669_);
lean_inc(v___y_938_);
lean_inc(v___y_935_);
v___x_968_ = l_Lean_Syntax_node2(v___y_935_, v___y_938_, v___x_966_, v___x_967_);
v___x_969_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___y_935_);
v___x_970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_970_, 0, v___y_935_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__37, &l_Lean_Elab_Command_elabElabRulesAux___closed__37_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37);
v___x_972_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__38));
v___x_973_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__39));
lean_inc_ref(v___y_940_);
lean_inc_ref(v___y_936_);
v___x_974_ = l_Lean_Name_mkStr4(v___y_936_, v___y_940_, v___x_972_, v___x_973_);
lean_inc(v___y_934_);
lean_inc(v___x_974_);
lean_inc(v___y_941_);
v___x_975_ = l_Lean_addMacroScope(v___y_941_, v___x_974_, v___y_934_);
v___x_976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_965_);
v___x_977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_965_);
lean_inc(v___y_935_);
v___x_978_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_978_, 0, v___y_935_);
lean_ctor_set(v___x_978_, 1, v___x_971_);
lean_ctor_set(v___x_978_, 2, v___x_975_);
lean_ctor_set(v___x_978_, 3, v___x_977_);
v___x_979_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(v___y_935_);
v___x_980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_980_, 0, v___y_935_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(v___y_936_);
v___x_982_ = l_Lean_Name_mkStr4(v___y_936_, v___x_947_, v___x_948_, v___x_981_);
lean_inc(v___y_935_);
v___x_983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_983_, 0, v___y_935_);
lean_ctor_set(v___x_983_, 1, v___x_981_);
v___x_984_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
lean_inc_ref(v___y_936_);
v___x_985_ = l_Lean_Name_mkStr4(v___y_936_, v___x_947_, v___x_948_, v___x_984_);
v___x_986_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
v___x_987_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
lean_inc(v___y_934_);
lean_inc(v___y_941_);
v___x_988_ = l_Lean_addMacroScope(v___y_941_, v___x_987_, v___y_934_);
lean_inc(v___y_935_);
v___x_989_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_989_, 0, v___y_935_);
lean_ctor_set(v___x_989_, 1, v___x_986_);
lean_ctor_set(v___x_989_, 2, v___x_988_);
lean_ctor_set(v___x_989_, 3, v___x_965_);
v___x_990_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__41, &l_Lean_Elab_Command_elabElabRulesAux___closed__41_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__41);
v___x_991_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__42));
lean_inc(v___y_934_);
lean_inc(v___y_941_);
v___x_992_ = l_Lean_addMacroScope(v___y_941_, v___x_991_, v___y_934_);
lean_inc(v___y_935_);
v___x_993_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_993_, 0, v___y_935_);
lean_ctor_set(v___x_993_, 1, v___x_990_);
lean_ctor_set(v___x_993_, 2, v___x_992_);
lean_ctor_set(v___x_993_, 3, v___x_965_);
lean_inc_ref(v___x_989_);
lean_inc(v___y_938_);
lean_inc(v___y_935_);
v___x_994_ = l_Lean_Syntax_node2(v___y_935_, v___y_938_, v___x_989_, v___x_993_);
lean_inc_ref(v___y_943_);
lean_inc(v___y_938_);
lean_inc(v___y_935_);
v___x_995_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_995_, 0, v___y_935_);
lean_ctor_set(v___x_995_, 1, v___y_938_);
lean_ctor_set(v___x_995_, 2, v___y_943_);
v___x_996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(v___y_935_);
v___x_997_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_997_, 0, v___y_935_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
lean_inc_ref(v___y_936_);
v___x_999_ = l_Lean_Name_mkStr4(v___y_936_, v___x_947_, v___x_948_, v___x_998_);
lean_inc(v___y_935_);
v___x_1000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___y_935_);
lean_ctor_set(v___x_1000_, 1, v___x_998_);
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
lean_inc_ref(v___y_936_);
v___x_1002_ = l_Lean_Name_mkStr4(v___y_936_, v___x_947_, v___x_948_, v___x_1001_);
lean_inc_ref(v___x_995_);
lean_inc(v___y_935_);
v___x_1003_ = l_Lean_Syntax_node2(v___y_935_, v___x_1002_, v___x_995_, v___x_989_);
lean_inc(v___y_938_);
lean_inc(v___y_935_);
v___x_1004_ = l_Lean_Syntax_node1(v___y_935_, v___y_938_, v___x_1003_);
v___x_1005_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc(v___y_935_);
v___x_1006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___y_935_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(v___y_936_);
v___x_1008_ = l_Lean_Name_mkStr4(v___y_936_, v___x_947_, v___x_948_, v___x_1007_);
v___x_1009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(v___y_936_);
v___x_1010_ = l_Lean_Name_mkStr4(v___y_936_, v___x_947_, v___x_948_, v___x_1009_);
v___x_1011_ = l_Array_append___redArg(v___y_943_, v_a_679_);
lean_dec(v_a_679_);
v___x_1012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(v___y_935_);
v___x_1013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___y_935_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(v___y_936_);
v___x_1015_ = l_Lean_Name_mkStr4(v___y_936_, v___x_947_, v___x_948_, v___x_1014_);
v___x_1016_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(v___y_935_);
v___x_1017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___y_935_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
lean_inc(v___y_935_);
v___x_1018_ = l_Lean_Syntax_node1(v___y_935_, v___x_1015_, v___x_1017_);
lean_inc(v___y_938_);
lean_inc(v___y_935_);
v___x_1019_ = l_Lean_Syntax_node1(v___y_935_, v___y_938_, v___x_1018_);
lean_inc(v___y_938_);
lean_inc(v___y_935_);
v___x_1020_ = l_Lean_Syntax_node1(v___y_935_, v___y_938_, v___x_1019_);
v___x_1021_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(v___y_936_);
v___x_1022_ = l_Lean_Name_mkStr4(v___y_936_, v___x_947_, v___x_948_, v___x_1021_);
v___x_1023_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(v___y_935_);
v___x_1024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___y_935_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1026_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_1027_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1028_ = l_Lean_addMacroScope(v___y_941_, v___x_1027_, v___y_934_);
v___x_1029_ = l_Lean_Name_mkStr3(v___y_936_, v___y_940_, v___x_1025_);
v___x_1030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_965_);
v___x_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_965_);
lean_inc(v___y_935_);
v___x_1032_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1032_, 0, v___y_935_);
lean_ctor_set(v___x_1032_, 1, v___x_1026_);
lean_ctor_set(v___x_1032_, 2, v___x_1028_);
lean_ctor_set(v___x_1032_, 3, v___x_1031_);
lean_inc(v___y_935_);
v___x_1033_ = l_Lean_Syntax_node2(v___y_935_, v___x_1022_, v___x_1024_, v___x_1032_);
lean_inc_ref(v___x_997_);
lean_inc(v___y_935_);
v___x_1034_ = l_Lean_Syntax_node4(v___y_935_, v___x_1010_, v___x_1013_, v___x_1020_, v___x_997_, v___x_1033_);
v___x_1035_ = lean_array_push(v___x_1011_, v___x_1034_);
lean_inc(v___y_935_);
v___x_1036_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1036_, 0, v___y_935_);
lean_ctor_set(v___x_1036_, 1, v___y_938_);
lean_ctor_set(v___x_1036_, 2, v___x_1035_);
lean_inc(v___y_935_);
v___x_1037_ = l_Lean_Syntax_node1(v___y_935_, v___x_1008_, v___x_1036_);
lean_inc_ref_n(v___x_995_, 2);
lean_inc(v___y_935_);
v___x_1038_ = l_Lean_Syntax_node6(v___y_935_, v___x_999_, v___x_1000_, v___x_995_, v___x_995_, v___x_1004_, v___x_1006_, v___x_1037_);
lean_inc(v___y_935_);
v___x_1039_ = l_Lean_Syntax_node4(v___y_935_, v___x_985_, v___x_994_, v___x_995_, v___x_997_, v___x_1038_);
lean_inc(v___y_935_);
v___x_1040_ = l_Lean_Syntax_node2(v___y_935_, v___x_982_, v___x_983_, v___x_1039_);
v___x_1041_ = lean_unsigned_to_nat(9u);
v___x_1042_ = lean_mk_empty_array_with_capacity(v___x_1041_);
v___x_1043_ = lean_array_push(v___x_1042_, v___x_946_);
v___x_1044_ = lean_array_push(v___x_1043_, v___x_960_);
v___x_1045_ = lean_array_push(v___x_1044_, v___y_939_);
v___x_1046_ = lean_array_push(v___x_1045_, v___x_961_);
v___x_1047_ = lean_array_push(v___x_1046_, v___x_968_);
v___x_1048_ = lean_array_push(v___x_1047_, v___x_970_);
v___x_1049_ = lean_array_push(v___x_1048_, v___x_978_);
v___x_1050_ = lean_array_push(v___x_1049_, v___x_980_);
v___x_1051_ = lean_array_push(v___x_1050_, v___x_1040_);
v___x_1052_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1052_, 0, v___y_935_);
lean_ctor_set(v___x_1052_, 1, v___y_933_);
lean_ctor_set(v___x_1052_, 2, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
return v___x_1053_;
}
v___jp_1054_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1060_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1061_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1062_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1063_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1064_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1065_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_666_) == 1)
{
lean_object* v_val_1066_; lean_object* v___x_1067_; 
v_val_1066_ = lean_ctor_get(v_doc_x3f_666_, 0);
lean_inc(v_val_1066_);
lean_dec_ref(v_doc_x3f_666_);
v___x_1067_ = l_Array_mkArray1___redArg(v_val_1066_);
v___y_933_ = v___x_1063_;
v___y_934_ = v___y_1056_;
v___y_935_ = v___y_1055_;
v___y_936_ = v___x_1060_;
v___y_937_ = v___y_1057_;
v___y_938_ = v___x_1064_;
v___y_939_ = v___y_1058_;
v___y_940_ = v___x_1061_;
v___y_941_ = v_a_1059_;
v___y_942_ = v___x_1062_;
v___y_943_ = v___x_1065_;
v___y_944_ = v___x_1067_;
goto v___jp_932_;
}
else
{
lean_object* v___x_1068_; 
lean_dec(v_doc_x3f_666_);
v___x_1068_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_933_ = v___x_1063_;
v___y_934_ = v___y_1056_;
v___y_935_ = v___y_1055_;
v___y_936_ = v___x_1060_;
v___y_937_ = v___y_1057_;
v___y_938_ = v___x_1064_;
v___y_939_ = v___y_1058_;
v___y_940_ = v___x_1061_;
v___y_941_ = v_a_1059_;
v___y_942_ = v___x_1062_;
v___y_943_ = v___x_1065_;
v___y_944_ = v___x_1068_;
goto v___jp_932_;
}
}
v___jp_1069_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_inc_ref(v___y_1070_);
v___x_1082_ = l_Array_append___redArg(v___y_1070_, v___y_1081_);
lean_dec_ref(v___y_1081_);
lean_inc(v___y_1076_);
lean_inc(v___y_1077_);
v___x_1083_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1083_, 0, v___y_1077_);
lean_ctor_set(v___x_1083_, 1, v___y_1076_);
lean_ctor_set(v___x_1083_, 2, v___x_1082_);
v___x_1084_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1085_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1086_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_1079_);
v___x_1087_ = l_Lean_Name_mkStr4(v___y_1079_, v___x_1084_, v___x_1085_, v___x_1086_);
v___x_1088_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(v___y_1077_);
v___x_1089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___y_1077_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1091_ = l_Lean_Syntax_SepArray_ofElems(v___x_1090_, v___y_1071_);
lean_dec_ref(v___y_1071_);
lean_inc_ref(v___y_1070_);
v___x_1092_ = l_Array_append___redArg(v___y_1070_, v___x_1091_);
lean_dec_ref(v___x_1091_);
lean_inc(v___y_1076_);
lean_inc(v___y_1077_);
v___x_1093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1093_, 0, v___y_1077_);
lean_ctor_set(v___x_1093_, 1, v___y_1076_);
lean_ctor_set(v___x_1093_, 2, v___x_1092_);
v___x_1094_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(v___y_1077_);
v___x_1095_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___y_1077_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
lean_inc(v___y_1077_);
v___x_1096_ = l_Lean_Syntax_node3(v___y_1077_, v___x_1087_, v___x_1089_, v___x_1093_, v___x_1095_);
lean_inc(v___y_1076_);
lean_inc(v___y_1077_);
v___x_1097_ = l_Lean_Syntax_node1(v___y_1077_, v___y_1076_, v___x_1096_);
lean_inc(v___y_1077_);
v___x_1098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___y_1077_);
lean_ctor_set(v___x_1098_, 1, v___y_1080_);
v___x_1099_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1100_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(v___y_1072_);
lean_inc(v___y_1073_);
v___x_1101_ = l_Lean_addMacroScope(v___y_1073_, v___x_1100_, v___y_1072_);
v___x_1102_ = lean_box(0);
lean_inc(v___y_1077_);
v___x_1103_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1103_, 0, v___y_1077_);
lean_ctor_set(v___x_1103_, 1, v___x_1099_);
lean_ctor_set(v___x_1103_, 2, v___x_1101_);
lean_ctor_set(v___x_1103_, 3, v___x_1102_);
v___x_1104_ = lean_mk_syntax_ident(v_k_669_);
lean_inc(v___y_1076_);
lean_inc(v___y_1077_);
v___x_1105_ = l_Lean_Syntax_node2(v___y_1077_, v___y_1076_, v___x_1103_, v___x_1104_);
v___x_1106_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___y_1077_);
v___x_1107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___y_1077_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__44, &l_Lean_Elab_Command_elabElabRulesAux___closed__44_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__44);
v___x_1109_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__45));
lean_inc_ref(v___y_1075_);
lean_inc_ref(v___y_1079_);
v___x_1110_ = l_Lean_Name_mkStr4(v___y_1079_, v___y_1075_, v___x_1109_, v___x_1109_);
lean_inc(v___y_1072_);
lean_inc(v___x_1110_);
lean_inc(v___y_1073_);
v___x_1111_ = l_Lean_addMacroScope(v___y_1073_, v___x_1110_, v___y_1072_);
v___x_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1102_);
v___x_1113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v___x_1102_);
lean_inc(v___y_1077_);
v___x_1114_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1114_, 0, v___y_1077_);
lean_ctor_set(v___x_1114_, 1, v___x_1108_);
lean_ctor_set(v___x_1114_, 2, v___x_1111_);
lean_ctor_set(v___x_1114_, 3, v___x_1113_);
v___x_1115_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(v___y_1077_);
v___x_1116_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___y_1077_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(v___y_1079_);
v___x_1118_ = l_Lean_Name_mkStr4(v___y_1079_, v___x_1084_, v___x_1085_, v___x_1117_);
lean_inc(v___y_1077_);
v___x_1119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___y_1077_);
lean_ctor_set(v___x_1119_, 1, v___x_1117_);
v___x_1120_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(v___y_1079_);
v___x_1121_ = l_Lean_Name_mkStr4(v___y_1079_, v___x_1084_, v___x_1085_, v___x_1120_);
v___x_1122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(v___y_1079_);
v___x_1123_ = l_Lean_Name_mkStr4(v___y_1079_, v___x_1084_, v___x_1085_, v___x_1122_);
v___x_1124_ = l_Array_append___redArg(v___y_1070_, v_a_679_);
lean_dec(v_a_679_);
v___x_1125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(v___y_1077_);
v___x_1126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___y_1077_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(v___y_1079_);
v___x_1128_ = l_Lean_Name_mkStr4(v___y_1079_, v___x_1084_, v___x_1085_, v___x_1127_);
v___x_1129_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(v___y_1077_);
v___x_1130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___y_1077_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
lean_inc(v___y_1077_);
v___x_1131_ = l_Lean_Syntax_node1(v___y_1077_, v___x_1128_, v___x_1130_);
lean_inc(v___y_1076_);
lean_inc(v___y_1077_);
v___x_1132_ = l_Lean_Syntax_node1(v___y_1077_, v___y_1076_, v___x_1131_);
lean_inc(v___y_1076_);
lean_inc(v___y_1077_);
v___x_1133_ = l_Lean_Syntax_node1(v___y_1077_, v___y_1076_, v___x_1132_);
v___x_1134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(v___y_1077_);
v___x_1135_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___y_1077_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(v___y_1079_);
v___x_1137_ = l_Lean_Name_mkStr4(v___y_1079_, v___x_1084_, v___x_1085_, v___x_1136_);
v___x_1138_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(v___y_1077_);
v___x_1139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___y_1077_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1141_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_1142_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1143_ = l_Lean_addMacroScope(v___y_1073_, v___x_1142_, v___y_1072_);
v___x_1144_ = l_Lean_Name_mkStr3(v___y_1079_, v___y_1075_, v___x_1140_);
v___x_1145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v___x_1102_);
v___x_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
lean_ctor_set(v___x_1146_, 1, v___x_1102_);
lean_inc(v___y_1077_);
v___x_1147_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1147_, 0, v___y_1077_);
lean_ctor_set(v___x_1147_, 1, v___x_1141_);
lean_ctor_set(v___x_1147_, 2, v___x_1143_);
lean_ctor_set(v___x_1147_, 3, v___x_1146_);
lean_inc(v___y_1077_);
v___x_1148_ = l_Lean_Syntax_node2(v___y_1077_, v___x_1137_, v___x_1139_, v___x_1147_);
lean_inc(v___y_1077_);
v___x_1149_ = l_Lean_Syntax_node4(v___y_1077_, v___x_1123_, v___x_1126_, v___x_1133_, v___x_1135_, v___x_1148_);
v___x_1150_ = lean_array_push(v___x_1124_, v___x_1149_);
lean_inc(v___y_1077_);
v___x_1151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1151_, 0, v___y_1077_);
lean_ctor_set(v___x_1151_, 1, v___y_1076_);
lean_ctor_set(v___x_1151_, 2, v___x_1150_);
lean_inc(v___y_1077_);
v___x_1152_ = l_Lean_Syntax_node1(v___y_1077_, v___x_1121_, v___x_1151_);
lean_inc(v___y_1077_);
v___x_1153_ = l_Lean_Syntax_node2(v___y_1077_, v___x_1118_, v___x_1119_, v___x_1152_);
v___x_1154_ = lean_unsigned_to_nat(9u);
v___x_1155_ = lean_mk_empty_array_with_capacity(v___x_1154_);
v___x_1156_ = lean_array_push(v___x_1155_, v___x_1083_);
v___x_1157_ = lean_array_push(v___x_1156_, v___x_1097_);
v___x_1158_ = lean_array_push(v___x_1157_, v___y_1078_);
v___x_1159_ = lean_array_push(v___x_1158_, v___x_1098_);
v___x_1160_ = lean_array_push(v___x_1159_, v___x_1105_);
v___x_1161_ = lean_array_push(v___x_1160_, v___x_1107_);
v___x_1162_ = lean_array_push(v___x_1161_, v___x_1114_);
v___x_1163_ = lean_array_push(v___x_1162_, v___x_1116_);
v___x_1164_ = lean_array_push(v___x_1163_, v___x_1153_);
v___x_1165_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1165_, 0, v___y_1077_);
lean_ctor_set(v___x_1165_, 1, v___y_1074_);
lean_ctor_set(v___x_1165_, 2, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
v___jp_1167_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1173_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1175_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1176_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1178_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_666_) == 1)
{
lean_object* v_val_1179_; lean_object* v___x_1180_; 
v_val_1179_ = lean_ctor_get(v_doc_x3f_666_, 0);
lean_inc(v_val_1179_);
lean_dec_ref(v_doc_x3f_666_);
v___x_1180_ = l_Array_mkArray1___redArg(v_val_1179_);
v___y_1070_ = v___x_1178_;
v___y_1071_ = v___y_1168_;
v___y_1072_ = v___y_1169_;
v___y_1073_ = v_a_1172_;
v___y_1074_ = v___x_1176_;
v___y_1075_ = v___x_1174_;
v___y_1076_ = v___x_1177_;
v___y_1077_ = v___y_1170_;
v___y_1078_ = v___y_1171_;
v___y_1079_ = v___x_1173_;
v___y_1080_ = v___x_1175_;
v___y_1081_ = v___x_1180_;
goto v___jp_1069_;
}
else
{
lean_object* v___x_1181_; 
lean_dec(v_doc_x3f_666_);
v___x_1181_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_1070_ = v___x_1178_;
v___y_1071_ = v___y_1168_;
v___y_1072_ = v___y_1169_;
v___y_1073_ = v_a_1172_;
v___y_1074_ = v___x_1176_;
v___y_1075_ = v___x_1174_;
v___y_1076_ = v___x_1177_;
v___y_1077_ = v___y_1170_;
v___y_1078_ = v___y_1171_;
v___y_1079_ = v___x_1173_;
v___y_1080_ = v___x_1175_;
v___y_1081_ = v___x_1181_;
goto v___jp_1069_;
}
}
v___jp_1182_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_inc_ref(v___y_1187_);
v___x_1196_ = l_Array_append___redArg(v___y_1187_, v___y_1195_);
lean_dec_ref(v___y_1195_);
lean_inc(v___y_1183_);
lean_inc(v___y_1190_);
v___x_1197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1197_, 0, v___y_1190_);
lean_ctor_set(v___x_1197_, 1, v___y_1183_);
lean_ctor_set(v___x_1197_, 2, v___x_1196_);
v___x_1198_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1199_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1200_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_1186_);
v___x_1201_ = l_Lean_Name_mkStr4(v___y_1186_, v___x_1198_, v___x_1199_, v___x_1200_);
v___x_1202_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(v___y_1190_);
v___x_1203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___y_1190_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1205_ = l_Lean_Syntax_SepArray_ofElems(v___x_1204_, v___y_1185_);
lean_dec_ref(v___y_1185_);
lean_inc_ref(v___y_1187_);
v___x_1206_ = l_Array_append___redArg(v___y_1187_, v___x_1205_);
lean_dec_ref(v___x_1205_);
lean_inc(v___y_1183_);
lean_inc(v___y_1190_);
v___x_1207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1207_, 0, v___y_1190_);
lean_ctor_set(v___x_1207_, 1, v___y_1183_);
lean_ctor_set(v___x_1207_, 2, v___x_1206_);
v___x_1208_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(v___y_1190_);
v___x_1209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___y_1190_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
lean_inc(v___y_1190_);
v___x_1210_ = l_Lean_Syntax_node3(v___y_1190_, v___x_1201_, v___x_1203_, v___x_1207_, v___x_1209_);
lean_inc(v___y_1183_);
lean_inc(v___y_1190_);
v___x_1211_ = l_Lean_Syntax_node1(v___y_1190_, v___y_1183_, v___x_1210_);
lean_inc(v___y_1190_);
v___x_1212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___y_1190_);
lean_ctor_set(v___x_1212_, 1, v___y_1192_);
v___x_1213_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1214_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(v___y_1184_);
lean_inc(v___y_1194_);
v___x_1215_ = l_Lean_addMacroScope(v___y_1194_, v___x_1214_, v___y_1184_);
v___x_1216_ = lean_box(0);
lean_inc(v___y_1190_);
v___x_1217_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1217_, 0, v___y_1190_);
lean_ctor_set(v___x_1217_, 1, v___x_1213_);
lean_ctor_set(v___x_1217_, 2, v___x_1215_);
lean_ctor_set(v___x_1217_, 3, v___x_1216_);
v___x_1218_ = lean_mk_syntax_ident(v_k_669_);
lean_inc(v___y_1183_);
lean_inc(v___y_1190_);
v___x_1219_ = l_Lean_Syntax_node2(v___y_1190_, v___y_1183_, v___x_1217_, v___x_1218_);
v___x_1220_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___y_1190_);
v___x_1221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___y_1190_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_1223_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
lean_inc_ref(v___y_1188_);
lean_inc_ref(v___y_1186_);
v___x_1224_ = l_Lean_Name_mkStr4(v___y_1186_, v___y_1188_, v___x_1199_, v___x_1223_);
lean_inc(v___y_1184_);
lean_inc(v___x_1224_);
lean_inc(v___y_1194_);
v___x_1225_ = l_Lean_addMacroScope(v___y_1194_, v___x_1224_, v___y_1184_);
v___x_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1216_);
v___x_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v___x_1216_);
lean_inc(v___y_1190_);
v___x_1228_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1228_, 0, v___y_1190_);
lean_ctor_set(v___x_1228_, 1, v___x_1222_);
lean_ctor_set(v___x_1228_, 2, v___x_1225_);
lean_ctor_set(v___x_1228_, 3, v___x_1227_);
v___x_1229_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(v___y_1190_);
v___x_1230_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___y_1190_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(v___y_1186_);
v___x_1232_ = l_Lean_Name_mkStr4(v___y_1186_, v___x_1198_, v___x_1199_, v___x_1231_);
lean_inc(v___y_1190_);
v___x_1233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___y_1190_);
lean_ctor_set(v___x_1233_, 1, v___x_1231_);
v___x_1234_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
lean_inc_ref(v___y_1186_);
v___x_1235_ = l_Lean_Name_mkStr4(v___y_1186_, v___x_1198_, v___x_1199_, v___x_1234_);
v___x_1236_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
v___x_1237_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
lean_inc(v___y_1184_);
lean_inc(v___y_1194_);
v___x_1238_ = l_Lean_addMacroScope(v___y_1194_, v___x_1237_, v___y_1184_);
lean_inc(v___y_1190_);
v___x_1239_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1239_, 0, v___y_1190_);
lean_ctor_set(v___x_1239_, 1, v___x_1236_);
lean_ctor_set(v___x_1239_, 2, v___x_1238_);
lean_ctor_set(v___x_1239_, 3, v___x_1216_);
v___x_1240_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__47, &l_Lean_Elab_Command_elabElabRulesAux___closed__47_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__47);
v___x_1241_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__48));
lean_inc(v___y_1184_);
lean_inc(v___y_1194_);
v___x_1242_ = l_Lean_addMacroScope(v___y_1194_, v___x_1241_, v___y_1184_);
lean_inc(v___y_1190_);
v___x_1243_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1243_, 0, v___y_1190_);
lean_ctor_set(v___x_1243_, 1, v___x_1240_);
lean_ctor_set(v___x_1243_, 2, v___x_1242_);
lean_ctor_set(v___x_1243_, 3, v___x_1216_);
lean_inc_ref(v___x_1243_);
lean_inc_ref(v___x_1239_);
lean_inc(v___y_1183_);
lean_inc(v___y_1190_);
v___x_1244_ = l_Lean_Syntax_node2(v___y_1190_, v___y_1183_, v___x_1239_, v___x_1243_);
lean_inc_ref(v___y_1187_);
lean_inc(v___y_1183_);
lean_inc(v___y_1190_);
v___x_1245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1245_, 0, v___y_1190_);
lean_ctor_set(v___x_1245_, 1, v___y_1183_);
lean_ctor_set(v___x_1245_, 2, v___y_1187_);
v___x_1246_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(v___y_1190_);
v___x_1247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___y_1190_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__49));
lean_inc_ref(v___y_1186_);
v___x_1249_ = l_Lean_Name_mkStr4(v___y_1186_, v___x_1198_, v___x_1199_, v___x_1248_);
v___x_1250_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__51, &l_Lean_Elab_Command_elabElabRulesAux___closed__51_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51);
v___x_1251_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__52));
lean_inc_ref(v___y_1188_);
lean_inc_ref(v___y_1186_);
v___x_1252_ = l_Lean_Name_mkStr4(v___y_1186_, v___y_1188_, v___x_1199_, v___x_1251_);
lean_inc(v___y_1184_);
lean_inc(v___x_1252_);
lean_inc(v___y_1194_);
v___x_1253_ = l_Lean_addMacroScope(v___y_1194_, v___x_1252_, v___y_1184_);
v___x_1254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set(v___x_1254_, 1, v___x_1216_);
v___x_1255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v___x_1216_);
lean_inc(v___y_1190_);
v___x_1256_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1256_, 0, v___y_1190_);
lean_ctor_set(v___x_1256_, 1, v___x_1250_);
lean_ctor_set(v___x_1256_, 2, v___x_1253_);
lean_ctor_set(v___x_1256_, 3, v___x_1255_);
lean_inc(v___y_1183_);
lean_inc(v___y_1190_);
v___x_1257_ = l_Lean_Syntax_node1(v___y_1190_, v___y_1183_, v___y_1193_);
v___x_1258_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
lean_inc_ref(v___y_1186_);
v___x_1259_ = l_Lean_Name_mkStr4(v___y_1186_, v___x_1198_, v___x_1199_, v___x_1258_);
lean_inc(v___y_1190_);
v___x_1260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___y_1190_);
lean_ctor_set(v___x_1260_, 1, v___x_1258_);
v___x_1261_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
lean_inc_ref(v___y_1186_);
v___x_1262_ = l_Lean_Name_mkStr4(v___y_1186_, v___x_1198_, v___x_1199_, v___x_1261_);
lean_inc_ref(v___x_1245_);
lean_inc(v___y_1190_);
v___x_1263_ = l_Lean_Syntax_node2(v___y_1190_, v___x_1262_, v___x_1245_, v___x_1239_);
lean_inc(v___y_1183_);
lean_inc(v___y_1190_);
v___x_1264_ = l_Lean_Syntax_node1(v___y_1190_, v___y_1183_, v___x_1263_);
v___x_1265_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc(v___y_1190_);
v___x_1266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___y_1190_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(v___y_1186_);
v___x_1268_ = l_Lean_Name_mkStr4(v___y_1186_, v___x_1198_, v___x_1199_, v___x_1267_);
v___x_1269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(v___y_1186_);
v___x_1270_ = l_Lean_Name_mkStr4(v___y_1186_, v___x_1198_, v___x_1199_, v___x_1269_);
v___x_1271_ = l_Array_append___redArg(v___y_1187_, v_a_679_);
lean_dec(v_a_679_);
v___x_1272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(v___y_1190_);
v___x_1273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___y_1190_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(v___y_1186_);
v___x_1275_ = l_Lean_Name_mkStr4(v___y_1186_, v___x_1198_, v___x_1199_, v___x_1274_);
v___x_1276_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(v___y_1190_);
v___x_1277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___y_1190_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
lean_inc(v___y_1190_);
v___x_1278_ = l_Lean_Syntax_node1(v___y_1190_, v___x_1275_, v___x_1277_);
lean_inc(v___y_1183_);
lean_inc(v___y_1190_);
v___x_1279_ = l_Lean_Syntax_node1(v___y_1190_, v___y_1183_, v___x_1278_);
lean_inc(v___y_1183_);
lean_inc(v___y_1190_);
v___x_1280_ = l_Lean_Syntax_node1(v___y_1190_, v___y_1183_, v___x_1279_);
v___x_1281_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(v___y_1186_);
v___x_1282_ = l_Lean_Name_mkStr4(v___y_1186_, v___x_1198_, v___x_1199_, v___x_1281_);
v___x_1283_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(v___y_1190_);
v___x_1284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___y_1190_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1286_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_1287_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1288_ = l_Lean_addMacroScope(v___y_1194_, v___x_1287_, v___y_1184_);
v___x_1289_ = l_Lean_Name_mkStr3(v___y_1186_, v___y_1188_, v___x_1285_);
v___x_1290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v___x_1216_);
v___x_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v___x_1216_);
lean_inc(v___y_1190_);
v___x_1292_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1292_, 0, v___y_1190_);
lean_ctor_set(v___x_1292_, 1, v___x_1286_);
lean_ctor_set(v___x_1292_, 2, v___x_1288_);
lean_ctor_set(v___x_1292_, 3, v___x_1291_);
lean_inc(v___y_1190_);
v___x_1293_ = l_Lean_Syntax_node2(v___y_1190_, v___x_1282_, v___x_1284_, v___x_1292_);
lean_inc_ref(v___x_1247_);
lean_inc(v___y_1190_);
v___x_1294_ = l_Lean_Syntax_node4(v___y_1190_, v___x_1270_, v___x_1273_, v___x_1280_, v___x_1247_, v___x_1293_);
v___x_1295_ = lean_array_push(v___x_1271_, v___x_1294_);
lean_inc(v___y_1183_);
lean_inc(v___y_1190_);
v___x_1296_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1296_, 0, v___y_1190_);
lean_ctor_set(v___x_1296_, 1, v___y_1183_);
lean_ctor_set(v___x_1296_, 2, v___x_1295_);
lean_inc(v___y_1190_);
v___x_1297_ = l_Lean_Syntax_node1(v___y_1190_, v___x_1268_, v___x_1296_);
lean_inc_ref_n(v___x_1245_, 2);
lean_inc(v___y_1190_);
v___x_1298_ = l_Lean_Syntax_node6(v___y_1190_, v___x_1259_, v___x_1260_, v___x_1245_, v___x_1245_, v___x_1264_, v___x_1266_, v___x_1297_);
lean_inc_ref(v___x_1247_);
lean_inc_ref(v___x_1245_);
lean_inc(v___x_1235_);
lean_inc(v___y_1190_);
v___x_1299_ = l_Lean_Syntax_node4(v___y_1190_, v___x_1235_, v___x_1257_, v___x_1245_, v___x_1247_, v___x_1298_);
lean_inc_ref(v___x_1233_);
lean_inc(v___x_1232_);
lean_inc(v___y_1190_);
v___x_1300_ = l_Lean_Syntax_node2(v___y_1190_, v___x_1232_, v___x_1233_, v___x_1299_);
lean_inc(v___y_1190_);
v___x_1301_ = l_Lean_Syntax_node2(v___y_1190_, v___y_1183_, v___x_1243_, v___x_1300_);
lean_inc(v___y_1190_);
v___x_1302_ = l_Lean_Syntax_node2(v___y_1190_, v___x_1249_, v___x_1256_, v___x_1301_);
lean_inc(v___y_1190_);
v___x_1303_ = l_Lean_Syntax_node4(v___y_1190_, v___x_1235_, v___x_1244_, v___x_1245_, v___x_1247_, v___x_1302_);
lean_inc(v___y_1190_);
v___x_1304_ = l_Lean_Syntax_node2(v___y_1190_, v___x_1232_, v___x_1233_, v___x_1303_);
v___x_1305_ = lean_unsigned_to_nat(9u);
v___x_1306_ = lean_mk_empty_array_with_capacity(v___x_1305_);
v___x_1307_ = lean_array_push(v___x_1306_, v___x_1197_);
v___x_1308_ = lean_array_push(v___x_1307_, v___x_1211_);
v___x_1309_ = lean_array_push(v___x_1308_, v___y_1189_);
v___x_1310_ = lean_array_push(v___x_1309_, v___x_1212_);
v___x_1311_ = lean_array_push(v___x_1310_, v___x_1219_);
v___x_1312_ = lean_array_push(v___x_1311_, v___x_1221_);
v___x_1313_ = lean_array_push(v___x_1312_, v___x_1228_);
v___x_1314_ = lean_array_push(v___x_1313_, v___x_1230_);
v___x_1315_ = lean_array_push(v___x_1314_, v___x_1304_);
v___x_1316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1316_, 0, v___y_1190_);
lean_ctor_set(v___x_1316_, 1, v___y_1191_);
lean_ctor_set(v___x_1316_, 2, v___x_1315_);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
v___jp_1318_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1325_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1326_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1327_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1328_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1329_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1330_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_666_) == 1)
{
lean_object* v_val_1331_; lean_object* v___x_1332_; 
v_val_1331_ = lean_ctor_get(v_doc_x3f_666_, 0);
lean_inc(v_val_1331_);
lean_dec_ref(v_doc_x3f_666_);
v___x_1332_ = l_Array_mkArray1___redArg(v_val_1331_);
v___y_1183_ = v___x_1329_;
v___y_1184_ = v___y_1319_;
v___y_1185_ = v___y_1320_;
v___y_1186_ = v___x_1325_;
v___y_1187_ = v___x_1330_;
v___y_1188_ = v___x_1326_;
v___y_1189_ = v___y_1321_;
v___y_1190_ = v___y_1322_;
v___y_1191_ = v___x_1328_;
v___y_1192_ = v___x_1327_;
v___y_1193_ = v___y_1323_;
v___y_1194_ = v_a_1324_;
v___y_1195_ = v___x_1332_;
goto v___jp_1182_;
}
else
{
lean_object* v___x_1333_; 
lean_dec(v_doc_x3f_666_);
v___x_1333_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_1183_ = v___x_1329_;
v___y_1184_ = v___y_1319_;
v___y_1185_ = v___y_1320_;
v___y_1186_ = v___x_1325_;
v___y_1187_ = v___x_1330_;
v___y_1188_ = v___x_1326_;
v___y_1189_ = v___y_1321_;
v___y_1190_ = v___y_1322_;
v___y_1191_ = v___x_1328_;
v___y_1192_ = v___x_1327_;
v___y_1193_ = v___y_1323_;
v___y_1194_ = v_a_1324_;
v___y_1195_ = v___x_1333_;
goto v___jp_1182_;
}
}
v___jp_1334_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_inc_ref(v___y_1343_);
v___x_1348_ = l_Array_append___redArg(v___y_1343_, v___y_1347_);
lean_dec_ref(v___y_1347_);
lean_inc(v___y_1337_);
lean_inc(v___y_1345_);
v___x_1349_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1349_, 0, v___y_1345_);
lean_ctor_set(v___x_1349_, 1, v___y_1337_);
lean_ctor_set(v___x_1349_, 2, v___x_1348_);
v___x_1350_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1351_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1352_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_1338_);
v___x_1353_ = l_Lean_Name_mkStr4(v___y_1338_, v___x_1350_, v___x_1351_, v___x_1352_);
v___x_1354_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(v___y_1345_);
v___x_1355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___y_1345_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1357_ = l_Lean_Syntax_SepArray_ofElems(v___x_1356_, v___y_1340_);
lean_dec_ref(v___y_1340_);
lean_inc_ref(v___y_1343_);
v___x_1358_ = l_Array_append___redArg(v___y_1343_, v___x_1357_);
lean_dec_ref(v___x_1357_);
lean_inc(v___y_1337_);
lean_inc(v___y_1345_);
v___x_1359_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1359_, 0, v___y_1345_);
lean_ctor_set(v___x_1359_, 1, v___y_1337_);
lean_ctor_set(v___x_1359_, 2, v___x_1358_);
v___x_1360_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(v___y_1345_);
v___x_1361_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___y_1345_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
lean_inc(v___y_1345_);
v___x_1362_ = l_Lean_Syntax_node3(v___y_1345_, v___x_1353_, v___x_1355_, v___x_1359_, v___x_1361_);
lean_inc(v___y_1337_);
lean_inc(v___y_1345_);
v___x_1363_ = l_Lean_Syntax_node1(v___y_1345_, v___y_1337_, v___x_1362_);
lean_inc(v___y_1345_);
v___x_1364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___y_1345_);
lean_ctor_set(v___x_1364_, 1, v___y_1342_);
v___x_1365_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1366_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(v___y_1336_);
lean_inc(v___y_1335_);
v___x_1367_ = l_Lean_addMacroScope(v___y_1335_, v___x_1366_, v___y_1336_);
v___x_1368_ = lean_box(0);
lean_inc(v___y_1345_);
v___x_1369_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1369_, 0, v___y_1345_);
lean_ctor_set(v___x_1369_, 1, v___x_1365_);
lean_ctor_set(v___x_1369_, 2, v___x_1367_);
lean_ctor_set(v___x_1369_, 3, v___x_1368_);
v___x_1370_ = lean_mk_syntax_ident(v_k_669_);
lean_inc(v___y_1337_);
lean_inc(v___y_1345_);
v___x_1371_ = l_Lean_Syntax_node2(v___y_1345_, v___y_1337_, v___x_1369_, v___x_1370_);
v___x_1372_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___y_1345_);
v___x_1373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___y_1345_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__37, &l_Lean_Elab_Command_elabElabRulesAux___closed__37_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37);
v___x_1375_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__38));
v___x_1376_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__39));
lean_inc_ref(v___y_1346_);
lean_inc_ref(v___y_1338_);
v___x_1377_ = l_Lean_Name_mkStr4(v___y_1338_, v___y_1346_, v___x_1375_, v___x_1376_);
lean_inc(v___y_1336_);
lean_inc(v___x_1377_);
lean_inc(v___y_1335_);
v___x_1378_ = l_Lean_addMacroScope(v___y_1335_, v___x_1377_, v___y_1336_);
v___x_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1368_);
v___x_1380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set(v___x_1380_, 1, v___x_1368_);
lean_inc(v___y_1345_);
v___x_1381_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1381_, 0, v___y_1345_);
lean_ctor_set(v___x_1381_, 1, v___x_1374_);
lean_ctor_set(v___x_1381_, 2, v___x_1378_);
lean_ctor_set(v___x_1381_, 3, v___x_1380_);
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(v___y_1345_);
v___x_1383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___y_1345_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(v___y_1338_);
v___x_1385_ = l_Lean_Name_mkStr4(v___y_1338_, v___x_1350_, v___x_1351_, v___x_1384_);
lean_inc(v___y_1345_);
v___x_1386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___y_1345_);
lean_ctor_set(v___x_1386_, 1, v___x_1384_);
v___x_1387_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
lean_inc_ref(v___y_1338_);
v___x_1388_ = l_Lean_Name_mkStr4(v___y_1338_, v___x_1350_, v___x_1351_, v___x_1387_);
v___x_1389_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
v___x_1390_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
lean_inc(v___y_1336_);
lean_inc(v___y_1335_);
v___x_1391_ = l_Lean_addMacroScope(v___y_1335_, v___x_1390_, v___y_1336_);
lean_inc(v___y_1345_);
v___x_1392_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1392_, 0, v___y_1345_);
lean_ctor_set(v___x_1392_, 1, v___x_1389_);
lean_ctor_set(v___x_1392_, 2, v___x_1391_);
lean_ctor_set(v___x_1392_, 3, v___x_1368_);
lean_inc_ref(v___x_1392_);
lean_inc(v___y_1337_);
lean_inc(v___y_1345_);
v___x_1393_ = l_Lean_Syntax_node2(v___y_1345_, v___y_1337_, v___x_1392_, v___y_1344_);
lean_inc_ref(v___y_1343_);
lean_inc(v___y_1337_);
lean_inc(v___y_1345_);
v___x_1394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1394_, 0, v___y_1345_);
lean_ctor_set(v___x_1394_, 1, v___y_1337_);
lean_ctor_set(v___x_1394_, 2, v___y_1343_);
v___x_1395_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(v___y_1345_);
v___x_1396_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___y_1345_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
lean_inc_ref(v___y_1338_);
v___x_1398_ = l_Lean_Name_mkStr4(v___y_1338_, v___x_1350_, v___x_1351_, v___x_1397_);
lean_inc(v___y_1345_);
v___x_1399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___y_1345_);
lean_ctor_set(v___x_1399_, 1, v___x_1397_);
v___x_1400_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
lean_inc_ref(v___y_1338_);
v___x_1401_ = l_Lean_Name_mkStr4(v___y_1338_, v___x_1350_, v___x_1351_, v___x_1400_);
lean_inc_ref(v___x_1394_);
lean_inc(v___y_1345_);
v___x_1402_ = l_Lean_Syntax_node2(v___y_1345_, v___x_1401_, v___x_1394_, v___x_1392_);
lean_inc(v___y_1337_);
lean_inc(v___y_1345_);
v___x_1403_ = l_Lean_Syntax_node1(v___y_1345_, v___y_1337_, v___x_1402_);
v___x_1404_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc(v___y_1345_);
v___x_1405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___y_1345_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
v___x_1406_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(v___y_1338_);
v___x_1407_ = l_Lean_Name_mkStr4(v___y_1338_, v___x_1350_, v___x_1351_, v___x_1406_);
v___x_1408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(v___y_1338_);
v___x_1409_ = l_Lean_Name_mkStr4(v___y_1338_, v___x_1350_, v___x_1351_, v___x_1408_);
v___x_1410_ = l_Array_append___redArg(v___y_1343_, v_a_679_);
lean_dec(v_a_679_);
v___x_1411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(v___y_1345_);
v___x_1412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___y_1345_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(v___y_1338_);
v___x_1414_ = l_Lean_Name_mkStr4(v___y_1338_, v___x_1350_, v___x_1351_, v___x_1413_);
v___x_1415_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(v___y_1345_);
v___x_1416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___y_1345_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
lean_inc(v___y_1345_);
v___x_1417_ = l_Lean_Syntax_node1(v___y_1345_, v___x_1414_, v___x_1416_);
lean_inc(v___y_1337_);
lean_inc(v___y_1345_);
v___x_1418_ = l_Lean_Syntax_node1(v___y_1345_, v___y_1337_, v___x_1417_);
lean_inc(v___y_1337_);
lean_inc(v___y_1345_);
v___x_1419_ = l_Lean_Syntax_node1(v___y_1345_, v___y_1337_, v___x_1418_);
v___x_1420_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(v___y_1338_);
v___x_1421_ = l_Lean_Name_mkStr4(v___y_1338_, v___x_1350_, v___x_1351_, v___x_1420_);
v___x_1422_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(v___y_1345_);
v___x_1423_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___y_1345_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1425_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_1426_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1427_ = l_Lean_addMacroScope(v___y_1335_, v___x_1426_, v___y_1336_);
v___x_1428_ = l_Lean_Name_mkStr3(v___y_1338_, v___y_1346_, v___x_1424_);
v___x_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
lean_ctor_set(v___x_1429_, 1, v___x_1368_);
v___x_1430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1368_);
lean_inc(v___y_1345_);
v___x_1431_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1431_, 0, v___y_1345_);
lean_ctor_set(v___x_1431_, 1, v___x_1425_);
lean_ctor_set(v___x_1431_, 2, v___x_1427_);
lean_ctor_set(v___x_1431_, 3, v___x_1430_);
lean_inc(v___y_1345_);
v___x_1432_ = l_Lean_Syntax_node2(v___y_1345_, v___x_1421_, v___x_1423_, v___x_1431_);
lean_inc_ref(v___x_1396_);
lean_inc(v___y_1345_);
v___x_1433_ = l_Lean_Syntax_node4(v___y_1345_, v___x_1409_, v___x_1412_, v___x_1419_, v___x_1396_, v___x_1432_);
v___x_1434_ = lean_array_push(v___x_1410_, v___x_1433_);
lean_inc(v___y_1345_);
v___x_1435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1435_, 0, v___y_1345_);
lean_ctor_set(v___x_1435_, 1, v___y_1337_);
lean_ctor_set(v___x_1435_, 2, v___x_1434_);
lean_inc(v___y_1345_);
v___x_1436_ = l_Lean_Syntax_node1(v___y_1345_, v___x_1407_, v___x_1435_);
lean_inc_ref_n(v___x_1394_, 2);
lean_inc(v___y_1345_);
v___x_1437_ = l_Lean_Syntax_node6(v___y_1345_, v___x_1398_, v___x_1399_, v___x_1394_, v___x_1394_, v___x_1403_, v___x_1405_, v___x_1436_);
lean_inc(v___y_1345_);
v___x_1438_ = l_Lean_Syntax_node4(v___y_1345_, v___x_1388_, v___x_1393_, v___x_1394_, v___x_1396_, v___x_1437_);
lean_inc(v___y_1345_);
v___x_1439_ = l_Lean_Syntax_node2(v___y_1345_, v___x_1385_, v___x_1386_, v___x_1438_);
v___x_1440_ = lean_unsigned_to_nat(9u);
v___x_1441_ = lean_mk_empty_array_with_capacity(v___x_1440_);
v___x_1442_ = lean_array_push(v___x_1441_, v___x_1349_);
v___x_1443_ = lean_array_push(v___x_1442_, v___x_1363_);
v___x_1444_ = lean_array_push(v___x_1443_, v___y_1341_);
v___x_1445_ = lean_array_push(v___x_1444_, v___x_1364_);
v___x_1446_ = lean_array_push(v___x_1445_, v___x_1371_);
v___x_1447_ = lean_array_push(v___x_1446_, v___x_1373_);
v___x_1448_ = lean_array_push(v___x_1447_, v___x_1381_);
v___x_1449_ = lean_array_push(v___x_1448_, v___x_1383_);
v___x_1450_ = lean_array_push(v___x_1449_, v___x_1439_);
v___x_1451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1451_, 0, v___y_1345_);
lean_ctor_set(v___x_1451_, 1, v___y_1339_);
lean_ctor_set(v___x_1451_, 2, v___x_1450_);
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
v___jp_1453_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1460_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1461_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1462_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1463_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1464_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1465_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_666_) == 1)
{
lean_object* v_val_1466_; lean_object* v___x_1467_; 
v_val_1466_ = lean_ctor_get(v_doc_x3f_666_, 0);
lean_inc(v_val_1466_);
lean_dec_ref(v_doc_x3f_666_);
v___x_1467_ = l_Array_mkArray1___redArg(v_val_1466_);
v___y_1335_ = v_a_1459_;
v___y_1336_ = v___y_1456_;
v___y_1337_ = v___x_1464_;
v___y_1338_ = v___x_1460_;
v___y_1339_ = v___x_1463_;
v___y_1340_ = v___y_1454_;
v___y_1341_ = v___y_1455_;
v___y_1342_ = v___x_1462_;
v___y_1343_ = v___x_1465_;
v___y_1344_ = v___y_1457_;
v___y_1345_ = v___y_1458_;
v___y_1346_ = v___x_1461_;
v___y_1347_ = v___x_1467_;
goto v___jp_1334_;
}
else
{
lean_object* v___x_1468_; 
lean_dec(v_doc_x3f_666_);
v___x_1468_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_1335_ = v_a_1459_;
v___y_1336_ = v___y_1456_;
v___y_1337_ = v___x_1464_;
v___y_1338_ = v___x_1460_;
v___y_1339_ = v___x_1463_;
v___y_1340_ = v___y_1454_;
v___y_1341_ = v___y_1455_;
v___y_1342_ = v___x_1462_;
v___y_1343_ = v___x_1465_;
v___y_1344_ = v___y_1457_;
v___y_1345_ = v___y_1458_;
v___y_1346_ = v___x_1461_;
v___y_1347_ = v___x_1468_;
goto v___jp_1334_;
}
}
v___jp_1469_:
{
lean_object* v___x_1475_; 
lean_inc(v_k_669_);
v___x_1475_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_669_, v_attrKind_668_, v_attrs_x3f_667_, v___y_1472_, v___y_1474_, v___y_1471_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref(v___x_1475_);
v___x_1477_ = l_Lean_Elab_Command_getRef___redArg(v___y_1474_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref(v___x_1477_);
v___x_1479_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1474_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v_quotContext_x3f_1481_; lean_object* v___x_1482_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref(v___x_1479_);
v_quotContext_x3f_1481_ = lean_ctor_get(v___y_1474_, 5);
lean_inc(v_quotContext_x3f_1481_);
lean_dec_ref(v___y_1474_);
v___x_1482_ = l_Lean_SourceInfo_fromRef(v_a_1478_, v___y_1470_);
lean_dec(v_a_1478_);
if (lean_obj_tag(v_quotContext_x3f_1481_) == 0)
{
lean_object* v___x_1483_; lean_object* v_a_1484_; 
v___x_1483_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1471_);
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
v___y_1168_ = v_a_1476_;
v___y_1169_ = v_a_1480_;
v___y_1170_ = v___x_1482_;
v___y_1171_ = v___y_1473_;
v_a_1172_ = v_a_1484_;
goto v___jp_1167_;
}
else
{
lean_object* v_val_1485_; 
v_val_1485_ = lean_ctor_get(v_quotContext_x3f_1481_, 0);
lean_inc(v_val_1485_);
lean_dec_ref(v_quotContext_x3f_1481_);
v___y_1168_ = v_a_1476_;
v___y_1169_ = v_a_1480_;
v___y_1170_ = v___x_1482_;
v___y_1171_ = v___y_1473_;
v_a_1172_ = v_val_1485_;
goto v___jp_1167_;
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec(v_a_1478_);
lean_dec(v_a_1476_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
v_a_1486_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1479_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1479_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
else
{
lean_dec(v_a_1476_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
return v___x_1477_;
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
v_a_1494_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1475_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1475_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
v___jp_1502_:
{
lean_object* v___x_1506_; 
lean_inc(v_attrKind_668_);
v___x_1506_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_668_);
if (lean_obj_tag(v_expty_x3f_671_) == 1)
{
lean_object* v_val_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
lean_del_object(v___x_681_);
v_val_1507_ = lean_ctor_get(v_expty_x3f_671_, 0);
lean_inc(v_val_1507_);
lean_dec_ref(v_expty_x3f_671_);
v___x_1508_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_1509_ = lean_name_eq(v_catName_1503_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
v___x_1511_ = lean_name_eq(v_catName_1503_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec(v___x_1506_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_attrKind_668_);
lean_dec(v_doc_x3f_666_);
v___x_1512_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__58, &l_Lean_Elab_Command_elabElabRulesAux___closed__58_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58);
v___x_1513_ = l_Lean_MessageData_ofName(v_catName_1503_);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__60, &l_Lean_Elab_Command_elabElabRulesAux___closed__60_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60);
v___x_1516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_val_1507_, v___x_1516_, v___y_1504_, v___y_1505_);
lean_dec(v_val_1507_);
return v___x_1517_;
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec(v_catName_1503_);
v___x_1518_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(v_k_669_);
v___x_1519_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_669_, v_attrKind_668_, v_attrs_x3f_667_, v___x_1518_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1521_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref(v___x_1519_);
v___x_1521_ = l_Lean_Elab_Command_getRef___redArg(v___y_1504_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1523_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref(v___x_1521_);
v___x_1523_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1504_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v_quotContext_x3f_1525_; lean_object* v___x_1526_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref(v___x_1523_);
v_quotContext_x3f_1525_ = lean_ctor_get(v___y_1504_, 5);
lean_inc(v_quotContext_x3f_1525_);
lean_dec_ref(v___y_1504_);
v___x_1526_ = l_Lean_SourceInfo_fromRef(v_a_1522_, v___x_1509_);
lean_dec(v_a_1522_);
if (lean_obj_tag(v_quotContext_x3f_1525_) == 0)
{
lean_object* v___x_1527_; lean_object* v_a_1528_; 
v___x_1527_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1505_);
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref(v___x_1527_);
v___y_1454_ = v_a_1520_;
v___y_1455_ = v___x_1506_;
v___y_1456_ = v_a_1524_;
v___y_1457_ = v_val_1507_;
v___y_1458_ = v___x_1526_;
v_a_1459_ = v_a_1528_;
goto v___jp_1453_;
}
else
{
lean_object* v_val_1529_; 
v_val_1529_ = lean_ctor_get(v_quotContext_x3f_1525_, 0);
lean_inc(v_val_1529_);
lean_dec_ref(v_quotContext_x3f_1525_);
v___y_1454_ = v_a_1520_;
v___y_1455_ = v___x_1506_;
v___y_1456_ = v_a_1524_;
v___y_1457_ = v_val_1507_;
v___y_1458_ = v___x_1526_;
v_a_1459_ = v_val_1529_;
goto v___jp_1453_;
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec(v_a_1522_);
lean_dec(v_a_1520_);
lean_dec(v_val_1507_);
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
v_a_1530_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1523_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1523_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
else
{
lean_dec(v_a_1520_);
lean_dec(v_val_1507_);
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
return v___x_1521_;
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec(v_val_1507_);
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
v_a_1538_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1519_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1519_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_dec(v_catName_1503_);
v___x_1546_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(v_k_669_);
v___x_1547_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_669_, v_attrKind_668_, v_attrs_x3f_667_, v___x_1546_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1549_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = l_Lean_Elab_Command_getRef___redArg(v___y_1504_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1504_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v_quotContext_x3f_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref(v___x_1551_);
v_quotContext_x3f_1553_ = lean_ctor_get(v___y_1504_, 5);
lean_inc(v_quotContext_x3f_1553_);
lean_dec_ref(v___y_1504_);
v___x_1554_ = 0;
v___x_1555_ = l_Lean_SourceInfo_fromRef(v_a_1550_, v___x_1554_);
lean_dec(v_a_1550_);
if (lean_obj_tag(v_quotContext_x3f_1553_) == 0)
{
lean_object* v___x_1556_; lean_object* v_a_1557_; 
v___x_1556_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1505_);
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref(v___x_1556_);
v___y_1319_ = v_a_1552_;
v___y_1320_ = v_a_1548_;
v___y_1321_ = v___x_1506_;
v___y_1322_ = v___x_1555_;
v___y_1323_ = v_val_1507_;
v_a_1324_ = v_a_1557_;
goto v___jp_1318_;
}
else
{
lean_object* v_val_1558_; 
v_val_1558_ = lean_ctor_get(v_quotContext_x3f_1553_, 0);
lean_inc(v_val_1558_);
lean_dec_ref(v_quotContext_x3f_1553_);
v___y_1319_ = v_a_1552_;
v___y_1320_ = v_a_1548_;
v___y_1321_ = v___x_1506_;
v___y_1322_ = v___x_1555_;
v___y_1323_ = v_val_1507_;
v_a_1324_ = v_val_1558_;
goto v___jp_1318_;
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_a_1550_);
lean_dec(v_a_1548_);
lean_dec(v_val_1507_);
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
v_a_1559_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1551_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1551_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
else
{
lean_dec(v_a_1548_);
lean_dec(v_val_1507_);
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
return v___x_1549_;
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_val_1507_);
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
v_a_1567_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1547_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1547_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
else
{
lean_object* v___x_1575_; uint8_t v___x_1576_; 
lean_dec(v_expty_x3f_671_);
v___x_1575_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_1576_ = lean_name_eq(v_catName_1503_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; uint8_t v___x_1578_; 
lean_del_object(v___x_681_);
v___x_1577_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__66));
v___x_1578_ = lean_name_eq(v_catName_1503_, v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1579_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__68));
v___x_1580_ = lean_name_eq(v_catName_1503_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__70));
v___x_1582_ = lean_name_eq(v_catName_1503_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
v___x_1584_ = lean_name_eq(v_catName_1503_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec(v___x_1506_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_attrKind_668_);
lean_dec(v_doc_x3f_666_);
v___x_1585_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__72, &l_Lean_Elab_Command_elabElabRulesAux___closed__72_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72);
v___x_1586_ = l_Lean_MessageData_ofName(v_catName_1503_);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_1589_, v___y_1504_, v___y_1505_);
return v___x_1590_;
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec(v_catName_1503_);
v___x_1591_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(v_k_669_);
v___x_1592_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_669_, v_attrKind_668_, v_attrs_x3f_667_, v___x_1591_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1594_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref(v___x_1592_);
v___x_1594_ = l_Lean_Elab_Command_getRef___redArg(v___y_1504_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1596_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref(v___x_1594_);
v___x_1596_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1504_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v_quotContext_x3f_1598_; lean_object* v___x_1599_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref(v___x_1596_);
v_quotContext_x3f_1598_ = lean_ctor_get(v___y_1504_, 5);
lean_inc(v_quotContext_x3f_1598_);
lean_dec_ref(v___y_1504_);
v___x_1599_ = l_Lean_SourceInfo_fromRef(v_a_1595_, v___x_1582_);
lean_dec(v_a_1595_);
if (lean_obj_tag(v_quotContext_x3f_1598_) == 0)
{
lean_object* v___x_1600_; lean_object* v_a_1601_; 
v___x_1600_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1505_);
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref(v___x_1600_);
v___y_1055_ = v___x_1599_;
v___y_1056_ = v_a_1597_;
v___y_1057_ = v_a_1593_;
v___y_1058_ = v___x_1506_;
v_a_1059_ = v_a_1601_;
goto v___jp_1054_;
}
else
{
lean_object* v_val_1602_; 
v_val_1602_ = lean_ctor_get(v_quotContext_x3f_1598_, 0);
lean_inc(v_val_1602_);
lean_dec_ref(v_quotContext_x3f_1598_);
v___y_1055_ = v___x_1599_;
v___y_1056_ = v_a_1597_;
v___y_1057_ = v_a_1593_;
v___y_1058_ = v___x_1506_;
v_a_1059_ = v_val_1602_;
goto v___jp_1054_;
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec(v_a_1595_);
lean_dec(v_a_1593_);
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
v_a_1603_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1596_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1596_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_dec(v_a_1593_);
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
return v___x_1594_;
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
v_a_1611_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1592_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1592_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
else
{
lean_dec(v_catName_1503_);
v___y_1470_ = v___x_1578_;
v___y_1471_ = v___y_1505_;
v___y_1472_ = v___x_1579_;
v___y_1473_ = v___x_1506_;
v___y_1474_ = v___y_1504_;
goto v___jp_1469_;
}
}
else
{
lean_dec(v_catName_1503_);
v___y_1470_ = v___x_1578_;
v___y_1471_ = v___y_1505_;
v___y_1472_ = v___x_1579_;
v___y_1473_ = v___x_1506_;
v___y_1474_ = v___y_1504_;
goto v___jp_1469_;
}
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_dec(v_catName_1503_);
v___x_1619_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__74));
lean_inc(v_k_669_);
v___x_1620_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_669_, v_attrKind_668_, v_attrs_x3f_667_, v___x_1619_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1622_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref(v___x_1620_);
v___x_1622_ = l_Lean_Elab_Command_getRef___redArg(v___y_1504_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1624_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref(v___x_1622_);
v___x_1624_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1504_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v_quotContext_x3f_1626_; lean_object* v___x_1627_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref(v___x_1624_);
v_quotContext_x3f_1626_ = lean_ctor_get(v___y_1504_, 5);
lean_inc(v_quotContext_x3f_1626_);
lean_dec_ref(v___y_1504_);
v___x_1627_ = l_Lean_SourceInfo_fromRef(v_a_1623_, v___x_1576_);
lean_dec(v_a_1623_);
if (lean_obj_tag(v_quotContext_x3f_1626_) == 0)
{
lean_object* v___x_1628_; lean_object* v_a_1629_; 
v___x_1628_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1505_);
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref(v___x_1628_);
v___y_917_ = v_a_1625_;
v___y_918_ = v___x_1506_;
v___y_919_ = v_a_1621_;
v___y_920_ = v___x_1627_;
v_a_921_ = v_a_1629_;
goto v___jp_916_;
}
else
{
lean_object* v_val_1630_; 
v_val_1630_ = lean_ctor_get(v_quotContext_x3f_1626_, 0);
lean_inc(v_val_1630_);
lean_dec_ref(v_quotContext_x3f_1626_);
v___y_917_ = v_a_1625_;
v___y_918_ = v___x_1506_;
v___y_919_ = v_a_1621_;
v___y_920_ = v___x_1627_;
v_a_921_ = v_val_1630_;
goto v___jp_916_;
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_a_1623_);
lean_dec(v_a_1621_);
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
v_a_1631_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1624_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1624_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_dec(v_a_1621_);
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
return v___x_1622_;
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
v_a_1639_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1620_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1620_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec(v_catName_1503_);
v___x_1647_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(v_k_669_);
v___x_1648_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_669_, v_attrKind_668_, v_attrs_x3f_667_, v___x_1647_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1650_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref(v___x_1648_);
v___x_1650_ = l_Lean_Elab_Command_getRef___redArg(v___y_1504_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1652_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref(v___x_1650_);
v___x_1652_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1504_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v_quotContext_x3f_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref(v___x_1652_);
v_quotContext_x3f_1654_ = lean_ctor_get(v___y_1504_, 5);
lean_inc(v_quotContext_x3f_1654_);
lean_dec_ref(v___y_1504_);
v___x_1655_ = 0;
v___x_1656_ = l_Lean_SourceInfo_fromRef(v_a_1651_, v___x_1655_);
lean_dec(v_a_1651_);
if (lean_obj_tag(v_quotContext_x3f_1654_) == 0)
{
lean_object* v___x_1657_; lean_object* v_a_1658_; 
v___x_1657_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1505_);
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref(v___x_1657_);
v___y_803_ = v___x_1506_;
v___y_804_ = v_a_1653_;
v___y_805_ = v___x_1656_;
v___y_806_ = v_a_1649_;
v_a_807_ = v_a_1658_;
goto v___jp_802_;
}
else
{
lean_object* v_val_1659_; 
v_val_1659_ = lean_ctor_get(v_quotContext_x3f_1654_, 0);
lean_inc(v_val_1659_);
lean_dec_ref(v_quotContext_x3f_1654_);
v___y_803_ = v___x_1506_;
v___y_804_ = v_a_1653_;
v___y_805_ = v___x_1656_;
v___y_806_ = v_a_1649_;
v_a_807_ = v_val_1659_;
goto v___jp_802_;
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v_a_1651_);
lean_dec(v_a_1649_);
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_del_object(v___x_681_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
v_a_1660_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1652_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1652_);
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
lean_dec(v_a_1649_);
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_del_object(v___x_681_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
return v___x_1650_;
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v___x_1506_);
lean_dec_ref(v___y_1504_);
lean_del_object(v___x_681_);
lean_dec(v_a_679_);
lean_dec(v_k_669_);
lean_dec(v_doc_x3f_666_);
v_a_1668_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1648_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1648_);
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
lean_dec_ref(v_a_673_);
lean_dec(v_expty_x3f_671_);
lean_dec(v_k_669_);
lean_dec(v_attrKind_668_);
lean_dec(v_doc_x3f_666_);
v_a_1690_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_678_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_678_);
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
v___x_1758_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
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
lean_object* v_a_1784_; lean_object* v___x_1785_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref(v___x_1783_);
v___x_1785_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1780_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1884_; 
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1884_ == 0)
{
lean_object* v_unused_1885_; 
v_unused_1885_ = lean_ctor_get(v___x_1785_, 0);
lean_dec(v_unused_1885_);
v___x_1787_ = v___x_1785_;
v_isShared_1788_ = v_isSharedCheck_1884_;
goto v_resetjp_1786_;
}
else
{
lean_dec(v___x_1785_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1884_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v_quotContext_x3f_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; 
v_quotContext_x3f_1789_ = lean_ctor_get(v___y_1780_, 5);
v___x_1790_ = 0;
v___x_1791_ = l_Lean_SourceInfo_fromRef(v_a_1784_, v___x_1790_);
lean_dec(v_a_1784_);
if (lean_obj_tag(v_quotContext_x3f_1789_) == 0)
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1781_);
lean_dec_ref(v___x_1883_);
goto v___jp_1877_;
}
else
{
goto v___jp_1877_;
}
v___jp_1792_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
lean_inc_ref(v___y_1799_);
v___x_1801_ = l_Array_append___redArg(v___y_1799_, v___y_1800_);
lean_dec_ref(v___y_1800_);
lean_inc(v___y_1798_);
lean_inc(v___x_1791_);
v___x_1802_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1791_);
lean_ctor_set(v___x_1802_, 1, v___y_1798_);
lean_ctor_set(v___x_1802_, 2, v___x_1801_);
v___x_1803_ = l_Array_append___redArg(v___y_1799_, v_alts_1779_);
lean_inc(v___x_1791_);
v___x_1804_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1791_);
lean_ctor_set(v___x_1804_, 1, v___y_1798_);
lean_ctor_set(v___x_1804_, 2, v___x_1803_);
lean_inc(v___x_1791_);
v___x_1805_ = l_Lean_Syntax_node1(v___x_1791_, v___x_1765_, v___x_1804_);
v___x_1806_ = l_Lean_Syntax_node8(v___x_1791_, v___x_1766_, v___y_1794_, v___y_1797_, v_attrKind_1767_, v___y_1795_, v___y_1796_, v___y_1793_, v___x_1802_, v___x_1805_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1806_);
v___x_1808_ = v___x_1787_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
v___jp_1810_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_inc_ref(v___y_1816_);
v___x_1818_ = l_Array_append___redArg(v___y_1816_, v___y_1817_);
lean_dec_ref(v___y_1817_);
lean_inc(v___y_1815_);
lean_inc(v___x_1791_);
v___x_1819_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1791_);
lean_ctor_set(v___x_1819_, 1, v___y_1815_);
lean_ctor_set(v___x_1819_, 2, v___x_1818_);
if (lean_obj_tag(v_expty_x3f_1768_) == 1)
{
lean_object* v_val_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec_ref(v___f_1769_);
v_val_1820_ = lean_ctor_get(v_expty_x3f_1768_, 0);
lean_inc(v_val_1820_);
lean_dec_ref(v_expty_x3f_1768_);
v___x_1821_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___x_1791_);
v___x_1822_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1791_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = l_Array_mkArray2___redArg(v___x_1822_, v_val_1820_);
v___y_1793_ = v___x_1819_;
v___y_1794_ = v___y_1811_;
v___y_1795_ = v___y_1812_;
v___y_1796_ = v___y_1813_;
v___y_1797_ = v___y_1814_;
v___y_1798_ = v___y_1815_;
v___y_1799_ = v___y_1816_;
v___y_1800_ = v___x_1823_;
goto v___jp_1792_;
}
else
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_apply_1(v___f_1769_, v_expty_x3f_1768_);
v___y_1793_ = v___x_1819_;
v___y_1794_ = v___y_1811_;
v___y_1795_ = v___y_1812_;
v___y_1796_ = v___y_1813_;
v___y_1797_ = v___y_1814_;
v___y_1798_ = v___y_1815_;
v___y_1799_ = v___y_1816_;
v___y_1800_ = v___x_1824_;
goto v___jp_1792_;
}
}
v___jp_1825_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_inc_ref(v___y_1830_);
v___x_1832_ = l_Array_append___redArg(v___y_1830_, v___y_1831_);
lean_dec_ref(v___y_1831_);
lean_inc(v___y_1829_);
lean_inc(v___x_1791_);
v___x_1833_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1791_);
lean_ctor_set(v___x_1833_, 1, v___y_1829_);
lean_ctor_set(v___x_1833_, 2, v___x_1832_);
if (lean_obj_tag(v_cat_x3f_1770_) == 1)
{
lean_object* v_val_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_val_1834_ = lean_ctor_get(v_cat_x3f_1770_, 0);
lean_inc(v_val_1834_);
lean_dec_ref(v_cat_x3f_1770_);
v___x_1835_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___x_1791_);
v___x_1836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1791_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = l_Array_mkArray2___redArg(v___x_1836_, v_val_1834_);
v___y_1811_ = v___y_1826_;
v___y_1812_ = v___y_1827_;
v___y_1813_ = v___x_1833_;
v___y_1814_ = v___y_1828_;
v___y_1815_ = v___y_1829_;
v___y_1816_ = v___y_1830_;
v___y_1817_ = v___x_1837_;
goto v___jp_1810_;
}
else
{
lean_object* v___x_1838_; 
lean_inc_ref(v___f_1769_);
v___x_1838_ = lean_apply_1(v___f_1769_, v_cat_x3f_1770_);
v___y_1811_ = v___y_1826_;
v___y_1812_ = v___y_1827_;
v___y_1813_ = v___x_1833_;
v___y_1814_ = v___y_1828_;
v___y_1815_ = v___y_1829_;
v___y_1816_ = v___y_1830_;
v___y_1817_ = v___x_1838_;
goto v___jp_1810_;
}
}
v___jp_1839_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_inc_ref(v___y_1842_);
v___x_1844_ = l_Array_append___redArg(v___y_1842_, v___y_1843_);
lean_dec_ref(v___y_1843_);
lean_inc(v___y_1841_);
lean_inc(v___x_1791_);
v___x_1845_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1791_);
lean_ctor_set(v___x_1845_, 1, v___y_1841_);
lean_ctor_set(v___x_1845_, 2, v___x_1844_);
lean_inc(v___x_1791_);
v___x_1846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1791_);
lean_ctor_set(v___x_1846_, 1, v___x_1771_);
if (lean_obj_tag(v_kind_x3f_1778_) == 0)
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_mk_empty_array_with_capacity(v___x_1772_);
v___y_1826_ = v___y_1840_;
v___y_1827_ = v___x_1846_;
v___y_1828_ = v___x_1845_;
v___y_1829_ = v___y_1841_;
v___y_1830_ = v___y_1842_;
v___y_1831_ = v___x_1847_;
goto v___jp_1825_;
}
else
{
lean_object* v_val_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v_val_1848_ = lean_ctor_get(v_kind_x3f_1778_, 0);
lean_inc(v_val_1848_);
lean_dec_ref(v_kind_x3f_1778_);
v___x_1849_ = lean_mk_syntax_ident(v_val_1848_);
v___x_1850_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc(v___x_1791_);
v___x_1851_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1791_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__2));
lean_inc(v___x_1791_);
v___x_1853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1791_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(v___x_1791_);
v___x_1855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1791_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
lean_inc(v___x_1791_);
v___x_1857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1791_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = l_Array_mkArray5___redArg(v___x_1851_, v___x_1853_, v___x_1855_, v___x_1849_, v___x_1857_);
v___y_1826_ = v___y_1840_;
v___y_1827_ = v___x_1846_;
v___y_1828_ = v___x_1845_;
v___y_1829_ = v___y_1841_;
v___y_1830_ = v___y_1842_;
v___y_1831_ = v___x_1858_;
goto v___jp_1825_;
}
}
v___jp_1859_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_inc_ref(v___y_1861_);
v___x_1863_ = l_Array_append___redArg(v___y_1861_, v___y_1862_);
lean_dec_ref(v___y_1862_);
lean_inc(v___y_1860_);
lean_inc(v___x_1791_);
v___x_1864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1791_);
lean_ctor_set(v___x_1864_, 1, v___y_1860_);
lean_ctor_set(v___x_1864_, 2, v___x_1863_);
if (lean_obj_tag(v_attrs_x3f_1773_) == 1)
{
lean_object* v_val_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v_val_1865_ = lean_ctor_get(v_attrs_x3f_1773_, 0);
v___x_1866_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
v___x_1867_ = l_Lean_Name_mkStr4(v___x_1774_, v___x_1775_, v___x_1776_, v___x_1866_);
v___x_1868_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(v___x_1791_);
v___x_1869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1791_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
lean_inc_ref(v___y_1861_);
v___x_1870_ = l_Array_append___redArg(v___y_1861_, v_val_1865_);
lean_inc(v___y_1860_);
lean_inc(v___x_1791_);
v___x_1871_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1791_);
lean_ctor_set(v___x_1871_, 1, v___y_1860_);
lean_ctor_set(v___x_1871_, 2, v___x_1870_);
v___x_1872_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(v___x_1791_);
v___x_1873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1791_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
lean_inc(v___x_1791_);
v___x_1874_ = l_Lean_Syntax_node3(v___x_1791_, v___x_1867_, v___x_1869_, v___x_1871_, v___x_1873_);
v___x_1875_ = l_Array_mkArray1___redArg(v___x_1874_);
v___y_1840_ = v___x_1864_;
v___y_1841_ = v___y_1860_;
v___y_1842_ = v___y_1861_;
v___y_1843_ = v___x_1875_;
goto v___jp_1839_;
}
else
{
lean_object* v___x_1876_; 
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1774_);
v___x_1876_ = lean_mk_empty_array_with_capacity(v___x_1772_);
v___y_1840_ = v___x_1864_;
v___y_1841_ = v___y_1860_;
v___y_1842_ = v___y_1861_;
v___y_1843_ = v___x_1876_;
goto v___jp_1839_;
}
}
v___jp_1877_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1879_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_1777_) == 1)
{
lean_object* v_val_1880_; lean_object* v___x_1881_; 
v_val_1880_ = lean_ctor_get(v_doc_x3f_1777_, 0);
lean_inc(v_val_1880_);
lean_dec_ref(v_doc_x3f_1777_);
v___x_1881_ = l_Array_mkArray1___redArg(v_val_1880_);
v___y_1860_ = v___x_1878_;
v___y_1861_ = v___x_1879_;
v___y_1862_ = v___x_1881_;
goto v___jp_1859_;
}
else
{
lean_object* v___x_1882_; 
lean_dec(v_doc_x3f_1777_);
v___x_1882_ = lean_mk_empty_array_with_capacity(v___x_1772_);
v___y_1860_ = v___x_1878_;
v___y_1861_ = v___x_1879_;
v___y_1862_ = v___x_1882_;
goto v___jp_1859_;
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_a_1784_);
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
v_a_1886_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1785_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1785_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
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
v_a_1894_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1783_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1783_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object** _args){
lean_object* v___x_1902_ = _args[0];
lean_object* v___x_1903_ = _args[1];
lean_object* v_attrKind_1904_ = _args[2];
lean_object* v_expty_x3f_1905_ = _args[3];
lean_object* v___f_1906_ = _args[4];
lean_object* v_cat_x3f_1907_ = _args[5];
lean_object* v___x_1908_ = _args[6];
lean_object* v___x_1909_ = _args[7];
lean_object* v_attrs_x3f_1910_ = _args[8];
lean_object* v___x_1911_ = _args[9];
lean_object* v___x_1912_ = _args[10];
lean_object* v___x_1913_ = _args[11];
lean_object* v_doc_x3f_1914_ = _args[12];
lean_object* v_kind_x3f_1915_ = _args[13];
lean_object* v_alts_1916_ = _args[14];
lean_object* v___y_1917_ = _args[15];
lean_object* v___y_1918_ = _args[16];
lean_object* v___y_1919_ = _args[17];
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_Elab_Command_elabElabRules___lam__1(v___x_1902_, v___x_1903_, v_attrKind_1904_, v_expty_x3f_1905_, v___f_1906_, v_cat_x3f_1907_, v___x_1908_, v___x_1909_, v_attrs_x3f_1910_, v___x_1911_, v___x_1912_, v___x_1913_, v_doc_x3f_1914_, v_kind_x3f_1915_, v_alts_1916_, v___y_1917_, v___y_1918_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec_ref(v_alts_1916_);
lean_dec(v_attrs_x3f_1910_);
lean_dec(v___x_1909_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object* v___f_1949_, lean_object* v_stx_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1954_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1955_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1956_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_1957_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
lean_inc(v_stx_1950_);
v___x_1958_ = l_Lean_Syntax_isOfKind(v_stx_1950_, v___x_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; 
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_1959_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_1959_;
}
else
{
lean_object* v___x_1960_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v_expty_x3f_1968_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v_cat_x3f_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v_expty_x3f_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v_cat_x3f_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v_attrs_x3f_2066_; lean_object* v_doc_x3f_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_2113_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_1960_);
v___x_2114_ = l_Lean_Syntax_isNone(v___x_2113_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2113_);
v___x_2116_ = l_Lean_Syntax_matchesNull(v___x_2113_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; 
lean_dec(v___x_2113_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_2117_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2117_;
}
else
{
lean_object* v_doc_x3f_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v_doc_x3f_2118_ = l_Lean_Syntax_getArg(v___x_2113_, v___x_1960_);
lean_dec(v___x_2113_);
v___x_2119_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(v_doc_x3f_2118_);
v___x_2120_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2118_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; 
lean_dec(v_doc_x3f_2118_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_2121_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; 
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v_doc_x3f_2118_);
v_doc_x3f_2097_ = v___x_2122_;
v___y_2098_ = v___y_1951_;
v___y_2099_ = v___y_1952_;
goto v___jp_2096_;
}
}
}
else
{
lean_object* v___x_2123_; 
lean_dec(v___x_2113_);
v___x_2123_ = lean_box(0);
v_doc_x3f_2097_ = v___x_2123_;
v___y_2098_ = v___y_1951_;
v___y_2099_ = v___y_1952_;
goto v___jp_2096_;
}
v___jp_1961_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1969_ = lean_unsigned_to_nat(7u);
v___x_1970_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_1969_);
lean_dec(v_stx_1950_);
v___x_1971_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1972_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__2));
lean_inc(v___x_1970_);
v___x_1973_ = l_Lean_Syntax_isOfKind(v___x_1970_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; 
lean_dec(v___x_1970_);
lean_dec(v_expty_x3f_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___f_1949_);
v___x_1974_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_1974_;
}
else
{
lean_object* v___f_1975_; lean_object* v___x_1976_; lean_object* v_alts_1977_; lean_object* v___x_1978_; 
v___f_1975_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lam__1___boxed), 18, 13);
lean_closure_set(v___f_1975_, 0, v___x_1972_);
lean_closure_set(v___f_1975_, 1, v___x_1957_);
lean_closure_set(v___f_1975_, 2, v___y_1965_);
lean_closure_set(v___f_1975_, 3, v_expty_x3f_1968_);
lean_closure_set(v___f_1975_, 4, v___f_1949_);
lean_closure_set(v___f_1975_, 5, v___y_1964_);
lean_closure_set(v___f_1975_, 6, v___x_1956_);
lean_closure_set(v___f_1975_, 7, v___x_1960_);
lean_closure_set(v___f_1975_, 8, v___y_1966_);
lean_closure_set(v___f_1975_, 9, v___x_1954_);
lean_closure_set(v___f_1975_, 10, v___x_1955_);
lean_closure_set(v___f_1975_, 11, v___x_1971_);
lean_closure_set(v___f_1975_, 12, v___y_1963_);
v___x_1976_ = l_Lean_Syntax_getArg(v___x_1970_, v___x_1960_);
lean_dec(v___x_1970_);
v_alts_1977_ = l_Lean_Syntax_getArgs(v___x_1976_);
lean_dec(v___x_1976_);
v___x_1978_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_1977_, v___x_1956_, v___f_1975_, v___y_1967_, v___y_1962_);
lean_dec_ref(v_alts_1977_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_a_1987_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1978_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1978_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
v___jp_1995_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v___x_2004_ = lean_unsigned_to_nat(6u);
v___x_2005_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2004_);
v___x_2006_ = l_Lean_Syntax_isNone(v___x_2005_);
if (v___x_2006_ == 0)
{
uint8_t v___x_2007_; 
lean_inc(v___x_2005_);
v___x_2007_ = l_Lean_Syntax_matchesNull(v___x_2005_, v___y_1999_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; 
lean_dec(v___x_2005_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v_cat_x3f_2001_);
lean_dec(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_2008_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2008_;
}
else
{
lean_object* v_expty_x3f_2009_; lean_object* v___x_2010_; 
v_expty_x3f_2009_ = l_Lean_Syntax_getArg(v___x_2005_, v___y_2000_);
lean_dec(v___x_2005_);
v___x_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2010_, 0, v_expty_x3f_2009_);
v___y_1962_ = v___y_2003_;
v___y_1963_ = v___y_1996_;
v___y_1964_ = v_cat_x3f_2001_;
v___y_1965_ = v___y_1997_;
v___y_1966_ = v___y_1998_;
v___y_1967_ = v___y_2002_;
v_expty_x3f_1968_ = v___x_2010_;
goto v___jp_1961_;
}
}
else
{
lean_object* v___x_2011_; 
lean_dec(v___x_2005_);
v___x_2011_ = lean_box(0);
v___y_1962_ = v___y_2003_;
v___y_1963_ = v___y_1996_;
v___y_1964_ = v_cat_x3f_2001_;
v___y_1965_ = v___y_1997_;
v___y_1966_ = v___y_1998_;
v___y_1967_ = v___y_2002_;
v_expty_x3f_1968_ = v___x_2011_;
goto v___jp_1961_;
}
}
v___jp_2012_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2022_ = lean_unsigned_to_nat(7u);
v___x_2023_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2022_);
lean_dec(v_stx_1950_);
v___x_2024_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_2025_ = l_Lean_Name_mkStr4(v___x_1954_, v___x_1955_, v___y_2016_, v___x_2024_);
lean_inc(v___x_2023_);
v___x_2026_ = l_Lean_Syntax_isOfKind(v___x_2023_, v___x_2025_);
lean_dec(v___x_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; 
lean_dec(v___x_2023_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v_expty_x3f_2019_);
lean_dec(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec(v___y_2013_);
v___x_2027_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = l_Lean_TSyntax_getId(v___y_2018_);
lean_dec(v___y_2018_);
lean_inc_ref(v___y_2020_);
v___x_2029_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_2028_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; lean_object* v_alts_2032_; lean_object* v___x_2033_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref(v___x_2029_);
v___x_2031_ = l_Lean_Syntax_getArg(v___x_2023_, v___x_1960_);
lean_dec(v___x_2023_);
v_alts_2032_ = l_Lean_Syntax_getArgs(v___x_2031_);
lean_dec(v___x_2031_);
v___x_2033_ = l_Lean_Elab_Command_elabElabRulesAux(v___y_2015_, v___y_2014_, v___y_2013_, v_a_2030_, v___y_2017_, v_expty_x3f_2019_, v_alts_2032_, v___y_2020_, v___y_2021_);
lean_dec(v___y_2021_);
lean_dec(v___y_2017_);
lean_dec(v___y_2014_);
return v___x_2033_;
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec(v___x_2023_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v_expty_x3f_2019_);
lean_dec(v___y_2017_);
lean_dec(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec(v___y_2013_);
v_a_2034_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2029_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2029_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
v___jp_2042_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2053_ = lean_unsigned_to_nat(6u);
v___x_2054_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2053_);
v___x_2055_ = l_Lean_Syntax_isNone(v___x_2054_);
if (v___x_2055_ == 0)
{
uint8_t v___x_2056_; 
lean_inc(v___x_2054_);
v___x_2056_ = l_Lean_Syntax_matchesNull(v___x_2054_, v___y_2043_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; 
lean_dec(v___x_2054_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v_cat_x3f_2050_);
lean_dec(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2044_);
lean_dec(v_stx_1950_);
v___x_2057_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2057_;
}
else
{
lean_object* v_expty_x3f_2058_; lean_object* v___x_2059_; 
v_expty_x3f_2058_ = l_Lean_Syntax_getArg(v___x_2054_, v___y_2045_);
lean_dec(v___x_2054_);
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v_expty_x3f_2058_);
v___y_2013_ = v___y_2044_;
v___y_2014_ = v___y_2048_;
v___y_2015_ = v___y_2047_;
v___y_2016_ = v___y_2046_;
v___y_2017_ = v_cat_x3f_2050_;
v___y_2018_ = v___y_2049_;
v_expty_x3f_2019_ = v___x_2059_;
v___y_2020_ = v___y_2051_;
v___y_2021_ = v___y_2052_;
goto v___jp_2012_;
}
}
else
{
lean_object* v___x_2060_; 
lean_dec(v___x_2054_);
v___x_2060_ = lean_box(0);
v___y_2013_ = v___y_2044_;
v___y_2014_ = v___y_2048_;
v___y_2015_ = v___y_2047_;
v___y_2016_ = v___y_2046_;
v___y_2017_ = v_cat_x3f_2050_;
v___y_2018_ = v___y_2049_;
v_expty_x3f_2019_ = v___x_2060_;
v___y_2020_ = v___y_2051_;
v___y_2021_ = v___y_2052_;
goto v___jp_2012_;
}
}
v___jp_2061_:
{
lean_object* v___x_2067_; lean_object* v_attrKind_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2067_ = lean_unsigned_to_nat(2u);
v_attrKind_2068_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2067_);
v___x_2069_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_2070_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v_attrKind_2068_);
v___x_2071_ = l_Lean_Syntax_isOfKind(v_attrKind_2068_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; 
lean_dec(v_attrKind_2068_);
lean_dec(v_attrs_x3f_2066_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_2072_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2072_;
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2073_ = lean_unsigned_to_nat(4u);
v___x_2074_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2073_);
lean_inc(v___x_2074_);
v___x_2075_ = l_Lean_Syntax_matchesNull(v___x_2074_, v___x_1960_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
lean_dec_ref(v___f_1949_);
v___x_2076_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2074_);
v___x_2077_ = l_Lean_Syntax_matchesNull(v___x_2074_, v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
lean_dec(v___x_2074_);
lean_dec(v_attrKind_2068_);
lean_dec(v_attrs_x3f_2066_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec(v_stx_1950_);
v___x_2078_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; lean_object* v_kind_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2079_ = lean_unsigned_to_nat(3u);
v_kind_2080_ = l_Lean_Syntax_getArg(v___x_2074_, v___x_2079_);
lean_dec(v___x_2074_);
v___x_2081_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2076_);
v___x_2082_ = l_Lean_Syntax_isNone(v___x_2081_);
if (v___x_2082_ == 0)
{
uint8_t v___x_2083_; 
lean_inc(v___x_2081_);
v___x_2083_ = l_Lean_Syntax_matchesNull(v___x_2081_, v___x_2067_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; 
lean_dec(v___x_2081_);
lean_dec(v_kind_2080_);
lean_dec(v_attrKind_2068_);
lean_dec(v_attrs_x3f_2066_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec(v_stx_1950_);
v___x_2084_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2084_;
}
else
{
lean_object* v_cat_x3f_2085_; lean_object* v___x_2086_; 
v_cat_x3f_2085_ = l_Lean_Syntax_getArg(v___x_2081_, v___y_2065_);
lean_dec(v___x_2081_);
v___x_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2086_, 0, v_cat_x3f_2085_);
v___y_2043_ = v___x_2067_;
v___y_2044_ = v_attrKind_2068_;
v___y_2045_ = v___y_2065_;
v___y_2046_ = v___x_2069_;
v___y_2047_ = v___y_2062_;
v___y_2048_ = v_attrs_x3f_2066_;
v___y_2049_ = v_kind_2080_;
v_cat_x3f_2050_ = v___x_2086_;
v___y_2051_ = v___y_2064_;
v___y_2052_ = v___y_2063_;
goto v___jp_2042_;
}
}
else
{
lean_object* v___x_2087_; 
lean_dec(v___x_2081_);
v___x_2087_ = lean_box(0);
v___y_2043_ = v___x_2067_;
v___y_2044_ = v_attrKind_2068_;
v___y_2045_ = v___y_2065_;
v___y_2046_ = v___x_2069_;
v___y_2047_ = v___y_2062_;
v___y_2048_ = v_attrs_x3f_2066_;
v___y_2049_ = v_kind_2080_;
v_cat_x3f_2050_ = v___x_2087_;
v___y_2051_ = v___y_2064_;
v___y_2052_ = v___y_2063_;
goto v___jp_2042_;
}
}
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
lean_dec(v___x_2074_);
v___x_2088_ = lean_unsigned_to_nat(5u);
v___x_2089_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2088_);
v___x_2090_ = l_Lean_Syntax_isNone(v___x_2089_);
if (v___x_2090_ == 0)
{
uint8_t v___x_2091_; 
lean_inc(v___x_2089_);
v___x_2091_ = l_Lean_Syntax_matchesNull(v___x_2089_, v___x_2067_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; 
lean_dec(v___x_2089_);
lean_dec(v_attrKind_2068_);
lean_dec(v_attrs_x3f_2066_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_2092_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2092_;
}
else
{
lean_object* v_cat_x3f_2093_; lean_object* v___x_2094_; 
v_cat_x3f_2093_ = l_Lean_Syntax_getArg(v___x_2089_, v___y_2065_);
lean_dec(v___x_2089_);
v___x_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2094_, 0, v_cat_x3f_2093_);
v___y_1996_ = v___y_2062_;
v___y_1997_ = v_attrKind_2068_;
v___y_1998_ = v_attrs_x3f_2066_;
v___y_1999_ = v___x_2067_;
v___y_2000_ = v___y_2065_;
v_cat_x3f_2001_ = v___x_2094_;
v___y_2002_ = v___y_2064_;
v___y_2003_ = v___y_2063_;
goto v___jp_1995_;
}
}
else
{
lean_object* v___x_2095_; 
lean_dec(v___x_2089_);
v___x_2095_ = lean_box(0);
v___y_1996_ = v___y_2062_;
v___y_1997_ = v_attrKind_2068_;
v___y_1998_ = v_attrs_x3f_2066_;
v___y_1999_ = v___x_2067_;
v___y_2000_ = v___y_2065_;
v_cat_x3f_2001_ = v___x_2095_;
v___y_2002_ = v___y_2064_;
v___y_2003_ = v___y_2063_;
goto v___jp_1995_;
}
}
}
}
v___jp_2096_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2100_ = lean_unsigned_to_nat(1u);
v___x_2101_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2100_);
v___x_2102_ = l_Lean_Syntax_isNone(v___x_2101_);
if (v___x_2102_ == 0)
{
uint8_t v___x_2103_; 
lean_inc(v___x_2101_);
v___x_2103_ = l_Lean_Syntax_matchesNull(v___x_2101_, v___x_2100_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; 
lean_dec(v___x_2101_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v_doc_x3f_2097_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_2104_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2104_;
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2105_ = l_Lean_Syntax_getArg(v___x_2101_, v___x_1960_);
lean_dec(v___x_2101_);
v___x_2106_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(v___x_2105_);
v___x_2107_ = l_Lean_Syntax_isOfKind(v___x_2105_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; 
lean_dec(v___x_2105_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v_doc_x3f_2097_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_2108_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2108_;
}
else
{
lean_object* v___x_2109_; lean_object* v_attrs_x3f_2110_; lean_object* v___x_2111_; 
v___x_2109_ = l_Lean_Syntax_getArg(v___x_2105_, v___x_2100_);
lean_dec(v___x_2105_);
v_attrs_x3f_2110_ = l_Lean_Syntax_getArgs(v___x_2109_);
lean_dec(v___x_2109_);
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_attrs_x3f_2110_);
v___y_2062_ = v_doc_x3f_2097_;
v___y_2063_ = v___y_2099_;
v___y_2064_ = v___y_2098_;
v___y_2065_ = v___x_2100_;
v_attrs_x3f_2066_ = v___x_2111_;
goto v___jp_2061_;
}
}
}
else
{
lean_object* v___x_2112_; 
lean_dec(v___x_2101_);
v___x_2112_ = lean_box(0);
v___y_2062_ = v_doc_x3f_2097_;
v___y_2063_ = v___y_2099_;
v___y_2064_ = v___y_2098_;
v___y_2065_ = v___x_2100_;
v_attrs_x3f_2066_ = v___x_2112_;
goto v___jp_2061_;
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
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1(){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2151_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2152_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
v___x_2153_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2154_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___boxed), 4, 0);
v___x_2155_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2151_, v___x_2152_, v___x_2153_, v___x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object* v_a_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3(){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2185_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6));
v___x_2186_ = l_Lean_addBuiltinDeclarationRanges(v___x_2184_, v___x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object* v_a_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
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
lean_dec_ref(v___y_2209_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v_bs_2208_);
return v___x_2213_;
}
else
{
lean_object* v_v_2214_; lean_object* v___x_2215_; 
v_v_2214_ = lean_array_uget_borrowed(v_bs_2208_, v_i_2207_);
lean_inc_ref(v___y_2209_);
lean_inc(v_v_2214_);
v___x_2215_ = l_Lean_Elab_Command_expandMacroArg(v_v_2214_, v___y_2209_, v___y_2210_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2217_; lean_object* v_bs_x27_2218_; size_t v___x_2219_; size_t v___x_2220_; lean_object* v___x_2221_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref(v___x_2215_);
v___x_2217_ = lean_unsigned_to_nat(0u);
v_bs_x27_2218_ = lean_array_uset(v_bs_2208_, v_i_2207_, v___x_2217_);
v___x_2219_ = ((size_t)1ULL);
v___x_2220_ = lean_usize_add(v_i_2207_, v___x_2219_);
v___x_2221_ = lean_array_uset(v_bs_x27_2218_, v_i_2207_, v_a_2216_);
v_i_2207_ = v___x_2220_;
v_bs_2208_ = v___x_2221_;
goto _start;
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v___y_2209_);
lean_dec_ref(v_bs_2208_);
v_a_2223_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2215_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2215_);
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
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(lean_object* v_cls_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v_scopes_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v_opts_2252_; uint8_t v_hasTrace_2253_; 
v___x_2246_ = l_Lean_inheritedTraceOptions;
v___x_2247_ = lean_st_ref_get(v___x_2246_);
v___x_2248_ = lean_st_ref_get(v___y_2244_);
v_scopes_2249_ = lean_ctor_get(v___x_2248_, 2);
lean_inc(v_scopes_2249_);
lean_dec(v___x_2248_);
v___x_2250_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2251_ = l_List_head_x21___redArg(v___x_2250_, v_scopes_2249_);
lean_dec(v_scopes_2249_);
v_opts_2252_ = lean_ctor_get(v___x_2251_, 1);
lean_inc_ref(v_opts_2252_);
lean_dec(v___x_2251_);
v_hasTrace_2253_ = lean_ctor_get_uint8(v_opts_2252_, sizeof(void*)*1);
if (v_hasTrace_2253_ == 0)
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_dec_ref(v_opts_2252_);
lean_dec(v___x_2247_);
lean_dec(v_cls_2243_);
v___x_2254_ = lean_box(v_hasTrace_2253_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
return v___x_2255_;
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; uint8_t v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2256_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__1));
v___x_2257_ = l_Lean_Name_append(v___x_2256_, v_cls_2243_);
v___x_2258_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2247_, v_opts_2252_, v___x_2257_);
lean_dec(v___x_2257_);
lean_dec_ref(v_opts_2252_);
lean_dec(v___x_2247_);
v___x_2259_ = lean_box(v___x_2258_);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
return v___x_2260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___boxed(lean_object* v_cls_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(v_cls_2261_, v___y_2262_);
lean_dec(v___y_2262_);
return v_res_2264_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2265_; double v___x_2266_; 
v___x_2265_ = lean_unsigned_to_nat(0u);
v___x_2266_ = lean_float_of_nat(v___x_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object* v_cls_2270_, lean_object* v_msg_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Elab_Command_getRef___redArg(v___y_2272_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2277_; lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2324_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref(v___x_2275_);
v___x_2277_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_2271_, v___y_2273_);
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2324_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2324_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; lean_object* v_traceState_2283_; lean_object* v_env_2284_; lean_object* v_messages_2285_; lean_object* v_scopes_2286_; lean_object* v_usedQuotCtxts_2287_; lean_object* v_nextMacroScope_2288_; lean_object* v_maxRecDepth_2289_; lean_object* v_ngen_2290_; lean_object* v_auxDeclNGen_2291_; lean_object* v_infoState_2292_; lean_object* v_snapshotTasks_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2323_; 
v___x_2282_ = lean_st_ref_take(v___y_2273_);
v_traceState_2283_ = lean_ctor_get(v___x_2282_, 9);
v_env_2284_ = lean_ctor_get(v___x_2282_, 0);
v_messages_2285_ = lean_ctor_get(v___x_2282_, 1);
v_scopes_2286_ = lean_ctor_get(v___x_2282_, 2);
v_usedQuotCtxts_2287_ = lean_ctor_get(v___x_2282_, 3);
v_nextMacroScope_2288_ = lean_ctor_get(v___x_2282_, 4);
v_maxRecDepth_2289_ = lean_ctor_get(v___x_2282_, 5);
v_ngen_2290_ = lean_ctor_get(v___x_2282_, 6);
v_auxDeclNGen_2291_ = lean_ctor_get(v___x_2282_, 7);
v_infoState_2292_ = lean_ctor_get(v___x_2282_, 8);
v_snapshotTasks_2293_ = lean_ctor_get(v___x_2282_, 10);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2295_ = v___x_2282_;
v_isShared_2296_ = v_isSharedCheck_2323_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_snapshotTasks_2293_);
lean_inc(v_traceState_2283_);
lean_inc(v_infoState_2292_);
lean_inc(v_auxDeclNGen_2291_);
lean_inc(v_ngen_2290_);
lean_inc(v_maxRecDepth_2289_);
lean_inc(v_nextMacroScope_2288_);
lean_inc(v_usedQuotCtxts_2287_);
lean_inc(v_scopes_2286_);
lean_inc(v_messages_2285_);
lean_inc(v_env_2284_);
lean_dec(v___x_2282_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2323_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
uint64_t v_tid_2297_; lean_object* v_traces_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2322_; 
v_tid_2297_ = lean_ctor_get_uint64(v_traceState_2283_, sizeof(void*)*1);
v_traces_2298_ = lean_ctor_get(v_traceState_2283_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_traceState_2283_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2300_ = v_traceState_2283_;
v_isShared_2301_ = v_isSharedCheck_2322_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_traces_2298_);
lean_dec(v_traceState_2283_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2322_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; double v___x_2303_; uint8_t v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2302_ = lean_box(0);
v___x_2303_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0);
v___x_2304_ = 0;
v___x_2305_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1));
v___x_2306_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2306_, 0, v_cls_2270_);
lean_ctor_set(v___x_2306_, 1, v___x_2302_);
lean_ctor_set(v___x_2306_, 2, v___x_2305_);
lean_ctor_set_float(v___x_2306_, sizeof(void*)*3, v___x_2303_);
lean_ctor_set_float(v___x_2306_, sizeof(void*)*3 + 8, v___x_2303_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*3 + 16, v___x_2304_);
v___x_2307_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__2));
v___x_2308_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2306_);
lean_ctor_set(v___x_2308_, 1, v_a_2278_);
lean_ctor_set(v___x_2308_, 2, v___x_2307_);
v___x_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2309_, 0, v_a_2276_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = l_Lean_PersistentArray_push___redArg(v_traces_2298_, v___x_2309_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2310_);
v___x_2312_ = v___x_2300_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2310_);
lean_ctor_set_uint64(v_reuseFailAlloc_2321_, sizeof(void*)*1, v_tid_2297_);
v___x_2312_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2314_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 9, v___x_2312_);
v___x_2314_ = v___x_2295_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_env_2284_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_messages_2285_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_scopes_2286_);
lean_ctor_set(v_reuseFailAlloc_2320_, 3, v_usedQuotCtxts_2287_);
lean_ctor_set(v_reuseFailAlloc_2320_, 4, v_nextMacroScope_2288_);
lean_ctor_set(v_reuseFailAlloc_2320_, 5, v_maxRecDepth_2289_);
lean_ctor_set(v_reuseFailAlloc_2320_, 6, v_ngen_2290_);
lean_ctor_set(v_reuseFailAlloc_2320_, 7, v_auxDeclNGen_2291_);
lean_ctor_set(v_reuseFailAlloc_2320_, 8, v_infoState_2292_);
lean_ctor_set(v_reuseFailAlloc_2320_, 9, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2320_, 10, v_snapshotTasks_2293_);
v___x_2314_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2315_ = lean_st_ref_set(v___y_2273_, v___x_2314_);
v___x_2316_ = lean_box(0);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2316_);
v___x_2318_ = v___x_2280_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
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
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec_ref(v_msg_2271_);
lean_dec(v_cls_2270_);
v_a_2325_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2275_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2275_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object* v_cls_2333_, lean_object* v_msg_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(v_cls_2333_, v_msg_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object* v_as_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
if (lean_obj_tag(v_as_2339_) == 0)
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_box(0);
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
return v___x_2344_;
}
else
{
lean_object* v_head_2345_; lean_object* v_tail_2346_; lean_object* v_fst_2347_; lean_object* v_snd_2348_; lean_object* v___x_2349_; lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2362_; 
v_head_2345_ = lean_ctor_get(v_as_2339_, 0);
lean_inc(v_head_2345_);
v_tail_2346_ = lean_ctor_get(v_as_2339_, 1);
lean_inc(v_tail_2346_);
lean_dec_ref(v_as_2339_);
v_fst_2347_ = lean_ctor_get(v_head_2345_, 0);
lean_inc(v_fst_2347_);
v_snd_2348_ = lean_ctor_get(v_head_2345_, 1);
lean_inc(v_snd_2348_);
lean_dec(v_head_2345_);
lean_inc(v_fst_2347_);
v___x_2349_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(v_fst_2347_, v___y_2341_);
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2362_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2362_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
uint8_t v___x_2354_; 
v___x_2354_ = lean_unbox(v_a_2350_);
lean_dec(v_a_2350_);
if (v___x_2354_ == 0)
{
lean_del_object(v___x_2352_);
lean_dec(v_snd_2348_);
lean_dec(v_fst_2347_);
v_as_2339_ = v_tail_2346_;
goto _start;
}
else
{
lean_object* v___x_2357_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set_tag(v___x_2352_, 3);
lean_ctor_set(v___x_2352_, 0, v_snd_2348_);
v___x_2357_ = v___x_2352_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_snd_2348_);
v___x_2357_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = l_Lean_MessageData_ofFormat(v___x_2357_);
v___x_2359_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(v_fst_2347_, v___x_2358_, v___y_2340_, v___y_2341_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_dec_ref(v___x_2359_);
v_as_2339_ = v_tail_2346_;
goto _start;
}
else
{
lean_dec(v_tail_2346_);
return v___x_2359_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object* v_as_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(v_as_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object* v_currNamespace_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v_currNamespace_2368_);
lean_ctor_set(v___x_2371_, 1, v___y_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(v_currNamespace_2372_, v___y_2373_, v___y_2374_);
lean_dec_ref(v___y_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object* v_env_2376_, lean_object* v_declName_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
uint8_t v___x_2380_; lean_object* v_env_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; uint8_t v___x_2384_; 
v___x_2380_ = 0;
v_env_2381_ = l_Lean_Environment_setExporting(v_env_2376_, v___x_2380_);
lean_inc(v_declName_2377_);
v___x_2382_ = l_Lean_mkPrivateName(v_env_2381_, v_declName_2377_);
v___x_2383_ = 1;
lean_inc_ref(v_env_2381_);
v___x_2384_ = l_Lean_Environment_contains(v_env_2381_, v___x_2382_, v___x_2383_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2385_; uint8_t v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2385_ = l_Lean_privateToUserName(v_declName_2377_);
v___x_2386_ = l_Lean_Environment_contains(v_env_2381_, v___x_2385_, v___x_2383_);
v___x_2387_ = lean_box(v___x_2386_);
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
lean_ctor_set(v___x_2388_, 1, v___y_2379_);
return v___x_2388_;
}
else
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_dec_ref(v_env_2381_);
lean_dec(v_declName_2377_);
v___x_2389_ = lean_box(v___x_2384_);
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
lean_ctor_set(v___x_2390_, 1, v___y_2379_);
return v___x_2390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object* v_env_2391_, lean_object* v_declName_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(v_env_2391_, v_declName_2392_, v___y_2393_, v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(lean_object* v_x_2396_, lean_object* v___y_2397_){
_start:
{
if (lean_obj_tag(v_x_2396_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2399_; 
v_a_2398_ = lean_ctor_get(v_x_2396_, 0);
lean_inc(v_a_2398_);
v___x_2399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2399_, 0, v_a_2398_);
lean_ctor_set(v___x_2399_, 1, v___y_2397_);
return v___x_2399_;
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2401_; 
v_a_2400_ = lean_ctor_get(v_x_2396_, 0);
lean_inc(v_a_2400_);
v___x_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2401_, 0, v_a_2400_);
lean_ctor_set(v___x_2401_, 1, v___y_2397_);
return v___x_2401_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg___boxed(lean_object* v_x_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(v_x_2402_, v___y_2403_);
lean_dec_ref(v_x_2402_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object* v_env_2405_, lean_object* v_stx_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2405_, v_stx_2406_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
if (lean_obj_tag(v_a_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2419_; 
v_a_2411_ = lean_ctor_get(v___x_2409_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2419_ == 0)
{
lean_object* v_unused_2420_; 
v_unused_2420_ = lean_ctor_get(v___x_2409_, 0);
lean_dec(v_unused_2420_);
v___x_2413_ = v___x_2409_;
v_isShared_2414_ = v_isSharedCheck_2419_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2409_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2419_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2415_ = lean_box(0);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2415_);
v___x_2417_ = v___x_2413_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_a_2411_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
else
{
lean_object* v_val_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2449_; 
v_val_2421_ = lean_ctor_get(v_a_2410_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_a_2410_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2423_ = v_a_2410_;
v_isShared_2424_ = v_isSharedCheck_2449_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_val_2421_);
lean_dec(v_a_2410_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2449_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v_snd_2425_; 
v_snd_2425_ = lean_ctor_get(v_val_2421_, 1);
lean_inc(v_snd_2425_);
lean_dec(v_val_2421_);
if (lean_obj_tag(v_snd_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2435_; 
lean_del_object(v___x_2423_);
v_a_2426_ = lean_ctor_get(v___x_2409_, 1);
lean_inc(v_a_2426_);
lean_dec_ref(v___x_2409_);
v_a_2427_ = lean_ctor_get(v_snd_2425_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_snd_2425_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2429_ = v_snd_2425_;
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v_snd_2425_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(v___x_2432_, v_a_2426_);
lean_dec_ref(v___x_2432_);
return v___x_2433_;
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2448_; 
v_a_2436_ = lean_ctor_get(v___x_2409_, 1);
lean_inc(v_a_2436_);
lean_dec_ref(v___x_2409_);
v_a_2437_ = lean_ctor_get(v_snd_2425_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_snd_2425_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2439_ = v_snd_2425_;
v_isShared_2440_ = v_isSharedCheck_2448_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v_snd_2425_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2448_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v_a_2437_);
v___x_2442_ = v___x_2423_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2444_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2442_);
v___x_2444_ = v___x_2439_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2442_);
v___x_2444_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2445_; 
v___x_2445_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(v___x_2444_, v_a_2436_);
lean_dec_ref(v___x_2444_);
return v___x_2445_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
v_a_2450_ = lean_ctor_get(v___x_2409_, 0);
v_a_2451_ = lean_ctor_get(v___x_2409_, 1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2409_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_inc(v_a_2450_);
lean_dec(v___x_2409_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2450_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object* v_env_2459_, lean_object* v_stx_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(v_env_2459_, v_stx_2460_, v___y_2461_, v___y_2462_);
lean_dec_ref(v___y_2461_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object* v_env_2464_, lean_object* v_currNamespace_2465_, lean_object* v_openDecls_2466_, lean_object* v_n_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = l_Lean_ResolveName_resolveNamespace(v_env_2464_, v_currNamespace_2465_, v_openDecls_2466_, v_n_2467_);
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
lean_ctor_set(v___x_2471_, 1, v___y_2469_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object* v_env_2472_, lean_object* v_currNamespace_2473_, lean_object* v_openDecls_2474_, lean_object* v_n_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(v_env_2472_, v_currNamespace_2473_, v_openDecls_2474_, v_n_2475_, v___y_2476_, v___y_2477_);
lean_dec_ref(v___y_2476_);
return v_res_2478_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(lean_object* v_keys_2479_, lean_object* v_i_2480_, lean_object* v_k_2481_){
_start:
{
lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2482_ = lean_array_get_size(v_keys_2479_);
v___x_2483_ = lean_nat_dec_lt(v_i_2480_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_dec(v_i_2480_);
return v___x_2483_;
}
else
{
lean_object* v_k_x27_2484_; uint8_t v___x_2485_; 
v_k_x27_2484_ = lean_array_fget_borrowed(v_keys_2479_, v_i_2480_);
v___x_2485_ = l_Lean_instBEqExtraModUse_beq(v_k_2481_, v_k_x27_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_unsigned_to_nat(1u);
v___x_2487_ = lean_nat_add(v_i_2480_, v___x_2486_);
lean_dec(v_i_2480_);
v_i_2480_ = v___x_2487_;
goto _start;
}
else
{
lean_dec(v_i_2480_);
return v___x_2485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg___boxed(lean_object* v_keys_2489_, lean_object* v_i_2490_, lean_object* v_k_2491_){
_start:
{
uint8_t v_res_2492_; lean_object* v_r_2493_; 
v_res_2492_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(v_keys_2489_, v_i_2490_, v_k_2491_);
lean_dec_ref(v_k_2491_);
lean_dec_ref(v_keys_2489_);
v_r_2493_ = lean_box(v_res_2492_);
return v_r_2493_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0(void){
_start:
{
size_t v___x_2494_; size_t v___x_2495_; size_t v___x_2496_; 
v___x_2494_ = ((size_t)5ULL);
v___x_2495_ = ((size_t)1ULL);
v___x_2496_ = lean_usize_shift_left(v___x_2495_, v___x_2494_);
return v___x_2496_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1(void){
_start:
{
size_t v___x_2497_; size_t v___x_2498_; size_t v___x_2499_; 
v___x_2497_ = ((size_t)1ULL);
v___x_2498_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0);
v___x_2499_ = lean_usize_sub(v___x_2498_, v___x_2497_);
return v___x_2499_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(lean_object* v_x_2500_, size_t v_x_2501_, lean_object* v_x_2502_){
_start:
{
if (lean_obj_tag(v_x_2500_) == 0)
{
lean_object* v_es_2503_; lean_object* v___x_2504_; size_t v___x_2505_; size_t v___x_2506_; size_t v___x_2507_; lean_object* v_j_2508_; lean_object* v___x_2509_; 
v_es_2503_ = lean_ctor_get(v_x_2500_, 0);
lean_inc_ref(v_es_2503_);
lean_dec_ref(v_x_2500_);
v___x_2504_ = lean_box(2);
v___x_2505_ = ((size_t)5ULL);
v___x_2506_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1);
v___x_2507_ = lean_usize_land(v_x_2501_, v___x_2506_);
v_j_2508_ = lean_usize_to_nat(v___x_2507_);
v___x_2509_ = lean_array_get(v___x_2504_, v_es_2503_, v_j_2508_);
lean_dec(v_j_2508_);
lean_dec_ref(v_es_2503_);
switch(lean_obj_tag(v___x_2509_))
{
case 0:
{
lean_object* v_key_2510_; uint8_t v___x_2511_; 
v_key_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_key_2510_);
lean_dec_ref(v___x_2509_);
v___x_2511_ = l_Lean_instBEqExtraModUse_beq(v_x_2502_, v_key_2510_);
lean_dec(v_key_2510_);
return v___x_2511_;
}
case 1:
{
lean_object* v_node_2512_; size_t v___x_2513_; 
v_node_2512_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_node_2512_);
lean_dec_ref(v___x_2509_);
v___x_2513_ = lean_usize_shift_right(v_x_2501_, v___x_2505_);
v_x_2500_ = v_node_2512_;
v_x_2501_ = v___x_2513_;
goto _start;
}
default: 
{
uint8_t v___x_2515_; 
v___x_2515_ = 0;
return v___x_2515_;
}
}
}
else
{
lean_object* v_ks_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v_ks_2516_ = lean_ctor_get(v_x_2500_, 0);
lean_inc_ref(v_ks_2516_);
lean_dec_ref(v_x_2500_);
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(v_ks_2516_, v___x_2517_, v_x_2502_);
lean_dec_ref(v_ks_2516_);
return v___x_2518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___boxed(lean_object* v_x_2519_, lean_object* v_x_2520_, lean_object* v_x_2521_){
_start:
{
size_t v_x_19590__boxed_2522_; uint8_t v_res_2523_; lean_object* v_r_2524_; 
v_x_19590__boxed_2522_ = lean_unbox_usize(v_x_2520_);
lean_dec(v_x_2520_);
v_res_2523_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(v_x_2519_, v_x_19590__boxed_2522_, v_x_2521_);
lean_dec_ref(v_x_2521_);
v_r_2524_ = lean_box(v_res_2523_);
return v_r_2524_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(lean_object* v_x_2525_, lean_object* v_x_2526_){
_start:
{
uint64_t v___x_2527_; size_t v___x_2528_; uint8_t v___x_2529_; 
v___x_2527_ = l_Lean_instHashableExtraModUse_hash(v_x_2526_);
v___x_2528_ = lean_uint64_to_usize(v___x_2527_);
v___x_2529_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(v_x_2525_, v___x_2528_, v_x_2526_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_x_2530_, lean_object* v_x_2531_){
_start:
{
uint8_t v_res_2532_; lean_object* v_r_2533_; 
v_res_2532_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(v_x_2530_, v_x_2531_);
lean_dec_ref(v_x_2531_);
v_r_2533_ = lean_box(v_res_2532_);
return v_r_2533_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__1));
v___x_2537_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__0));
v___x_2538_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2537_, v___x_2536_);
return v___x_2538_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__5));
v___x_2544_ = l_Lean_stringToMessageData(v___x_2543_);
return v___x_2544_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__7));
v___x_2547_ = l_Lean_stringToMessageData(v___x_2546_);
return v___x_2547_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1));
v___x_2549_ = l_Lean_stringToMessageData(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__10));
v___x_2552_ = l_Lean_stringToMessageData(v___x_2551_);
return v___x_2552_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__12));
v___x_2555_ = l_Lean_stringToMessageData(v___x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(lean_object* v_mod_2560_, uint8_t v_isMeta_2561_, lean_object* v_hint_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; lean_object* v_env_2567_; uint8_t v_isExporting_2568_; lean_object* v___x_2569_; lean_object* v_env_2570_; lean_object* v___x_2571_; lean_object* v_entry_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___y_2577_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2566_ = lean_st_ref_get(v___y_2564_);
v_env_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc_ref(v_env_2567_);
lean_dec(v___x_2566_);
v_isExporting_2568_ = lean_ctor_get_uint8(v_env_2567_, sizeof(void*)*8);
lean_dec_ref(v_env_2567_);
v___x_2569_ = lean_st_ref_get(v___y_2564_);
v_env_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc_ref(v_env_2570_);
lean_dec(v___x_2569_);
v___x_2571_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2);
lean_inc(v_mod_2560_);
v_entry_2572_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2572_, 0, v_mod_2560_);
lean_ctor_set_uint8(v_entry_2572_, sizeof(void*)*1, v_isExporting_2568_);
lean_ctor_set_uint8(v_entry_2572_, sizeof(void*)*1 + 1, v_isMeta_2561_);
v___x_2573_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2574_ = lean_box(1);
v___x_2575_ = lean_box(0);
v___x_2603_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2571_, v___x_2573_, v_env_2570_, v___x_2574_, v___x_2575_);
v___x_2604_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(v___x_2603_, v_entry_2572_);
if (v___x_2604_ == 0)
{
lean_object* v_cls_2605_; lean_object* v___x_2606_; lean_object* v_a_2607_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2614_; lean_object* v___y_2615_; uint8_t v___x_2627_; 
v_cls_2605_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__4));
v___x_2606_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(v_cls_2605_, v___y_2564_);
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref(v___x_2606_);
v___x_2627_ = lean_unbox(v_a_2607_);
lean_dec(v_a_2607_);
if (v___x_2627_ == 0)
{
lean_dec(v_hint_2562_);
lean_dec(v_mod_2560_);
v___y_2577_ = v___y_2564_;
goto v___jp_2576_;
}
else
{
lean_object* v___x_2628_; lean_object* v___y_2630_; 
v___x_2628_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11);
if (v_isExporting_2568_ == 0)
{
lean_object* v___x_2637_; 
v___x_2637_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__16));
v___y_2630_ = v___x_2637_;
goto v___jp_2629_;
}
else
{
lean_object* v___x_2638_; 
v___x_2638_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__17));
v___y_2630_ = v___x_2638_;
goto v___jp_2629_;
}
v___jp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2631_ = l_Lean_stringToMessageData(v___y_2630_);
v___x_2632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2628_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13);
v___x_2634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2632_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
if (v_isMeta_2561_ == 0)
{
lean_object* v___x_2635_; 
v___x_2635_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__14));
v___y_2614_ = v___x_2634_;
v___y_2615_ = v___x_2635_;
goto v___jp_2613_;
}
else
{
lean_object* v___x_2636_; 
v___x_2636_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__15));
v___y_2614_ = v___x_2634_;
v___y_2615_ = v___x_2636_;
goto v___jp_2613_;
}
}
}
v___jp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___y_2609_);
lean_ctor_set(v___x_2611_, 1, v___y_2610_);
v___x_2612_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(v_cls_2605_, v___x_2611_, v___y_2563_, v___y_2564_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_dec_ref(v___x_2612_);
v___y_2577_ = v___y_2564_;
goto v___jp_2576_;
}
else
{
lean_dec_ref(v_entry_2572_);
return v___x_2612_;
}
}
v___jp_2613_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2616_ = l_Lean_stringToMessageData(v___y_2615_);
v___x_2617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___y_2614_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6);
v___x_2619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2617_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = l_Lean_MessageData_ofName(v_mod_2560_);
v___x_2621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2619_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
v___x_2622_ = l_Lean_Name_isAnonymous(v_hint_2562_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8);
v___x_2624_ = l_Lean_MessageData_ofName(v_hint_2562_);
v___x_2625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___y_2609_ = v___x_2621_;
v___y_2610_ = v___x_2625_;
goto v___jp_2608_;
}
else
{
lean_object* v___x_2626_; 
lean_dec(v_hint_2562_);
v___x_2626_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9);
v___y_2609_ = v___x_2621_;
v___y_2610_ = v___x_2626_;
goto v___jp_2608_;
}
}
}
else
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
lean_dec_ref(v_entry_2572_);
lean_dec(v_hint_2562_);
lean_dec(v_mod_2560_);
v___x_2639_ = lean_box(0);
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
return v___x_2640_;
}
v___jp_2576_:
{
lean_object* v___x_2578_; lean_object* v_toEnvExtension_2579_; lean_object* v_env_2580_; lean_object* v_messages_2581_; lean_object* v_scopes_2582_; lean_object* v_usedQuotCtxts_2583_; lean_object* v_nextMacroScope_2584_; lean_object* v_maxRecDepth_2585_; lean_object* v_ngen_2586_; lean_object* v_auxDeclNGen_2587_; lean_object* v_infoState_2588_; lean_object* v_traceState_2589_; lean_object* v_snapshotTasks_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2602_; 
v___x_2578_ = lean_st_ref_take(v___y_2577_);
v_toEnvExtension_2579_ = lean_ctor_get(v___x_2573_, 0);
lean_inc_ref(v_toEnvExtension_2579_);
v_env_2580_ = lean_ctor_get(v___x_2578_, 0);
v_messages_2581_ = lean_ctor_get(v___x_2578_, 1);
v_scopes_2582_ = lean_ctor_get(v___x_2578_, 2);
v_usedQuotCtxts_2583_ = lean_ctor_get(v___x_2578_, 3);
v_nextMacroScope_2584_ = lean_ctor_get(v___x_2578_, 4);
v_maxRecDepth_2585_ = lean_ctor_get(v___x_2578_, 5);
v_ngen_2586_ = lean_ctor_get(v___x_2578_, 6);
v_auxDeclNGen_2587_ = lean_ctor_get(v___x_2578_, 7);
v_infoState_2588_ = lean_ctor_get(v___x_2578_, 8);
v_traceState_2589_ = lean_ctor_get(v___x_2578_, 9);
v_snapshotTasks_2590_ = lean_ctor_get(v___x_2578_, 10);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2592_ = v___x_2578_;
v_isShared_2593_ = v_isSharedCheck_2602_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_snapshotTasks_2590_);
lean_inc(v_traceState_2589_);
lean_inc(v_infoState_2588_);
lean_inc(v_auxDeclNGen_2587_);
lean_inc(v_ngen_2586_);
lean_inc(v_maxRecDepth_2585_);
lean_inc(v_nextMacroScope_2584_);
lean_inc(v_usedQuotCtxts_2583_);
lean_inc(v_scopes_2582_);
lean_inc(v_messages_2581_);
lean_inc(v_env_2580_);
lean_dec(v___x_2578_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2602_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v_asyncMode_2594_; lean_object* v___x_2595_; lean_object* v___x_2597_; 
v_asyncMode_2594_ = lean_ctor_get(v_toEnvExtension_2579_, 2);
lean_inc(v_asyncMode_2594_);
lean_dec_ref(v_toEnvExtension_2579_);
v___x_2595_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2573_, v_env_2580_, v_entry_2572_, v_asyncMode_2594_, v___x_2575_);
lean_dec(v_asyncMode_2594_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 0, v___x_2595_);
v___x_2597_ = v___x_2592_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_messages_2581_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_scopes_2582_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_usedQuotCtxts_2583_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_nextMacroScope_2584_);
lean_ctor_set(v_reuseFailAlloc_2601_, 5, v_maxRecDepth_2585_);
lean_ctor_set(v_reuseFailAlloc_2601_, 6, v_ngen_2586_);
lean_ctor_set(v_reuseFailAlloc_2601_, 7, v_auxDeclNGen_2587_);
lean_ctor_set(v_reuseFailAlloc_2601_, 8, v_infoState_2588_);
lean_ctor_set(v_reuseFailAlloc_2601_, 9, v_traceState_2589_);
lean_ctor_set(v_reuseFailAlloc_2601_, 10, v_snapshotTasks_2590_);
v___x_2597_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_st_ref_set(v___y_2577_, v___x_2597_);
v___x_2599_ = lean_box(0);
v___x_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
return v___x_2600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___boxed(lean_object* v_mod_2641_, lean_object* v_isMeta_2642_, lean_object* v_hint_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
uint8_t v_isMeta_boxed_2647_; lean_object* v_res_2648_; 
v_isMeta_boxed_2647_ = lean_unbox(v_isMeta_2642_);
v_res_2648_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(v_mod_2641_, v_isMeta_boxed_2647_, v_hint_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5(lean_object* v___x_2649_, lean_object* v_declName_2650_, lean_object* v_as_2651_, size_t v_sz_2652_, size_t v_i_2653_, lean_object* v_b_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
uint8_t v___x_2658_; 
v___x_2658_ = lean_usize_dec_lt(v_i_2653_, v_sz_2652_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; 
lean_dec(v_declName_2650_);
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v_b_2654_);
return v___x_2659_;
}
else
{
lean_object* v___x_2660_; lean_object* v_modules_2661_; lean_object* v___x_2662_; lean_object* v_a_2663_; lean_object* v___x_2664_; lean_object* v_toImport_2665_; lean_object* v_module_2666_; uint8_t v___x_2667_; lean_object* v___x_2668_; 
v___x_2660_ = l_Lean_Environment_header(v___x_2649_);
v_modules_2661_ = lean_ctor_get(v___x_2660_, 3);
lean_inc_ref(v_modules_2661_);
lean_dec_ref(v___x_2660_);
v___x_2662_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2663_ = lean_array_uget_borrowed(v_as_2651_, v_i_2653_);
v___x_2664_ = lean_array_get(v___x_2662_, v_modules_2661_, v_a_2663_);
lean_dec_ref(v_modules_2661_);
v_toImport_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc_ref(v_toImport_2665_);
lean_dec(v___x_2664_);
v_module_2666_ = lean_ctor_get(v_toImport_2665_, 0);
lean_inc(v_module_2666_);
lean_dec_ref(v_toImport_2665_);
v___x_2667_ = 0;
lean_inc(v_declName_2650_);
v___x_2668_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(v_module_2666_, v___x_2667_, v_declName_2650_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v___x_2669_; size_t v___x_2670_; size_t v___x_2671_; 
lean_dec_ref(v___x_2668_);
v___x_2669_ = lean_box(0);
v___x_2670_ = ((size_t)1ULL);
v___x_2671_ = lean_usize_add(v_i_2653_, v___x_2670_);
v_i_2653_ = v___x_2671_;
v_b_2654_ = v___x_2669_;
goto _start;
}
else
{
lean_dec(v_declName_2650_);
return v___x_2668_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5___boxed(lean_object* v___x_2673_, lean_object* v_declName_2674_, lean_object* v_as_2675_, lean_object* v_sz_2676_, lean_object* v_i_2677_, lean_object* v_b_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
size_t v_sz_boxed_2682_; size_t v_i_boxed_2683_; lean_object* v_res_2684_; 
v_sz_boxed_2682_ = lean_unbox_usize(v_sz_2676_);
lean_dec(v_sz_2676_);
v_i_boxed_2683_ = lean_unbox_usize(v_i_2677_);
lean_dec(v_i_2677_);
v_res_2684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5(v___x_2673_, v_declName_2674_, v_as_2675_, v_sz_boxed_2682_, v_i_boxed_2683_, v_b_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec_ref(v_as_2675_);
lean_dec_ref(v___x_2673_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(lean_object* v_a_2685_, lean_object* v_x_2686_){
_start:
{
if (lean_obj_tag(v_x_2686_) == 0)
{
lean_object* v___x_2687_; 
v___x_2687_ = lean_box(0);
return v___x_2687_;
}
else
{
lean_object* v_key_2688_; lean_object* v_value_2689_; lean_object* v_tail_2690_; uint8_t v___x_2691_; 
v_key_2688_ = lean_ctor_get(v_x_2686_, 0);
v_value_2689_ = lean_ctor_get(v_x_2686_, 1);
v_tail_2690_ = lean_ctor_get(v_x_2686_, 2);
v___x_2691_ = lean_name_eq(v_key_2688_, v_a_2685_);
if (v___x_2691_ == 0)
{
v_x_2686_ = v_tail_2690_;
goto _start;
}
else
{
lean_object* v___x_2693_; 
lean_inc(v_value_2689_);
v___x_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2693_, 0, v_value_2689_);
return v___x_2693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg___boxed(lean_object* v_a_2694_, lean_object* v_x_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(v_a_2694_, v_x_2695_);
lean_dec(v_x_2695_);
lean_dec(v_a_2694_);
return v_res_2696_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2697_; uint64_t v___x_2698_; 
v___x_2697_ = lean_unsigned_to_nat(1723u);
v___x_2698_ = lean_uint64_of_nat(v___x_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(lean_object* v_m_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v_buckets_2701_; lean_object* v___x_2702_; uint64_t v___y_2704_; 
v_buckets_2701_ = lean_ctor_get(v_m_2699_, 1);
v___x_2702_ = lean_array_get_size(v_buckets_2701_);
if (lean_obj_tag(v_a_2700_) == 0)
{
uint64_t v___x_2718_; 
v___x_2718_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0);
v___y_2704_ = v___x_2718_;
goto v___jp_2703_;
}
else
{
uint64_t v_hash_2719_; 
v_hash_2719_ = lean_ctor_get_uint64(v_a_2700_, sizeof(void*)*2);
v___y_2704_ = v_hash_2719_;
goto v___jp_2703_;
}
v___jp_2703_:
{
uint64_t v___x_2705_; uint64_t v___x_2706_; uint64_t v_fold_2707_; uint64_t v___x_2708_; uint64_t v___x_2709_; uint64_t v___x_2710_; size_t v___x_2711_; size_t v___x_2712_; size_t v___x_2713_; size_t v___x_2714_; size_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2705_ = 32ULL;
v___x_2706_ = lean_uint64_shift_right(v___y_2704_, v___x_2705_);
v_fold_2707_ = lean_uint64_xor(v___y_2704_, v___x_2706_);
v___x_2708_ = 16ULL;
v___x_2709_ = lean_uint64_shift_right(v_fold_2707_, v___x_2708_);
v___x_2710_ = lean_uint64_xor(v_fold_2707_, v___x_2709_);
v___x_2711_ = lean_uint64_to_usize(v___x_2710_);
v___x_2712_ = lean_usize_of_nat(v___x_2702_);
v___x_2713_ = ((size_t)1ULL);
v___x_2714_ = lean_usize_sub(v___x_2712_, v___x_2713_);
v___x_2715_ = lean_usize_land(v___x_2711_, v___x_2714_);
v___x_2716_ = lean_array_uget_borrowed(v_buckets_2701_, v___x_2715_);
v___x_2717_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(v_a_2700_, v___x_2716_);
return v___x_2717_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_m_2720_, lean_object* v_a_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(v_m_2720_, v_a_2721_);
lean_dec(v_a_2721_);
lean_dec_ref(v_m_2720_);
return v_res_2722_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2725_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__1));
v___x_2726_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__0));
v___x_2727_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2726_, v___x_2725_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object* v_declName_2730_, uint8_t v_isMeta_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2735_; lean_object* v_env_2739_; lean_object* v___y_2741_; lean_object* v___x_2754_; 
v___x_2735_ = lean_st_ref_get(v___y_2733_);
v_env_2739_ = lean_ctor_get(v___x_2735_, 0);
lean_inc_ref(v_env_2739_);
lean_dec(v___x_2735_);
v___x_2754_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2739_, v_declName_2730_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_dec_ref(v_env_2739_);
lean_dec(v_declName_2730_);
goto v___jp_2736_;
}
else
{
lean_object* v_val_2755_; lean_object* v___x_2756_; lean_object* v_modules_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v_val_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_val_2755_);
lean_dec_ref(v___x_2754_);
v___x_2756_ = l_Lean_Environment_header(v_env_2739_);
v_modules_2757_ = lean_ctor_get(v___x_2756_, 3);
lean_inc_ref(v_modules_2757_);
lean_dec_ref(v___x_2756_);
v___x_2758_ = lean_array_get_size(v_modules_2757_);
v___x_2759_ = lean_nat_dec_lt(v_val_2755_, v___x_2758_);
if (v___x_2759_ == 0)
{
lean_dec_ref(v_modules_2757_);
lean_dec(v_val_2755_);
lean_dec_ref(v_env_2739_);
lean_dec(v_declName_2730_);
goto v___jp_2736_;
}
else
{
lean_object* v___x_2760_; lean_object* v_env_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___y_2765_; 
v___x_2760_ = lean_st_ref_get(v___y_2733_);
v_env_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc_ref(v_env_2761_);
lean_dec(v___x_2760_);
v___x_2762_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2);
v___x_2763_ = lean_array_fget(v_modules_2757_, v_val_2755_);
lean_dec(v_val_2755_);
lean_dec_ref(v_modules_2757_);
if (v_isMeta_2731_ == 0)
{
lean_dec_ref(v_env_2761_);
v___y_2765_ = v_isMeta_2731_;
goto v___jp_2764_;
}
else
{
uint8_t v___x_2776_; 
lean_inc(v_declName_2730_);
v___x_2776_ = l_Lean_isMarkedMeta(v_env_2761_, v_declName_2730_);
if (v___x_2776_ == 0)
{
v___y_2765_ = v_isMeta_2731_;
goto v___jp_2764_;
}
else
{
uint8_t v___x_2777_; 
v___x_2777_ = 0;
v___y_2765_ = v___x_2777_;
goto v___jp_2764_;
}
}
v___jp_2764_:
{
lean_object* v_toImport_2766_; lean_object* v_module_2767_; lean_object* v___x_2768_; 
v_toImport_2766_ = lean_ctor_get(v___x_2763_, 0);
lean_inc_ref(v_toImport_2766_);
lean_dec(v___x_2763_);
v_module_2767_ = lean_ctor_get(v_toImport_2766_, 0);
lean_inc(v_module_2767_);
lean_dec_ref(v_toImport_2766_);
lean_inc(v_declName_2730_);
v___x_2768_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(v_module_2767_, v___y_2765_, v_declName_2730_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_dec_ref(v___x_2768_);
v___x_2769_ = l_Lean_indirectModUseExt;
v___x_2770_ = lean_box(1);
v___x_2771_ = lean_box(0);
lean_inc_ref(v_env_2739_);
v___x_2772_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2762_, v___x_2769_, v_env_2739_, v___x_2770_, v___x_2771_);
v___x_2773_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(v___x_2772_, v_declName_2730_);
lean_dec(v___x_2772_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v___x_2774_; 
v___x_2774_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__3));
v___y_2741_ = v___x_2774_;
goto v___jp_2740_;
}
else
{
lean_object* v_val_2775_; 
v_val_2775_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_val_2775_);
lean_dec_ref(v___x_2773_);
v___y_2741_ = v_val_2775_;
goto v___jp_2740_;
}
}
else
{
lean_dec_ref(v_env_2739_);
lean_dec(v_declName_2730_);
return v___x_2768_;
}
}
}
}
v___jp_2736_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = lean_box(0);
v___x_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
return v___x_2738_;
}
v___jp_2740_:
{
lean_object* v___x_2742_; size_t v_sz_2743_; size_t v___x_2744_; lean_object* v___x_2745_; 
v___x_2742_ = lean_box(0);
v_sz_2743_ = lean_array_size(v___y_2741_);
v___x_2744_ = ((size_t)0ULL);
v___x_2745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5(v_env_2739_, v_declName_2730_, v___y_2741_, v_sz_2743_, v___x_2744_, v___x_2742_, v___y_2732_, v___y_2733_);
lean_dec_ref(v___y_2741_);
lean_dec_ref(v_env_2739_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2752_ == 0)
{
lean_object* v_unused_2753_; 
v_unused_2753_ = lean_ctor_get(v___x_2745_, 0);
lean_dec(v_unused_2753_);
v___x_2747_ = v___x_2745_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_dec(v___x_2745_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v___x_2742_);
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2742_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
else
{
return v___x_2745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object* v_declName_2778_, lean_object* v_isMeta_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
uint8_t v_isMeta_boxed_2783_; lean_object* v_res_2784_; 
v_isMeta_boxed_2783_ = lean_unbox(v_isMeta_2779_);
v_res_2784_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(v_declName_2778_, v_isMeta_boxed_2783_, v___y_2780_, v___y_2781_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(lean_object* v_as_x27_2785_, lean_object* v_b_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
if (lean_obj_tag(v_as_x27_2785_) == 0)
{
lean_object* v___x_2790_; 
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v_b_2786_);
return v___x_2790_;
}
else
{
lean_object* v_head_2791_; lean_object* v_tail_2792_; uint8_t v___x_2793_; lean_object* v___x_2794_; 
v_head_2791_ = lean_ctor_get(v_as_x27_2785_, 0);
lean_inc(v_head_2791_);
v_tail_2792_ = lean_ctor_get(v_as_x27_2785_, 1);
lean_inc(v_tail_2792_);
lean_dec_ref(v_as_x27_2785_);
v___x_2793_ = 1;
v___x_2794_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(v_head_2791_, v___x_2793_, v___y_2787_, v___y_2788_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v___x_2795_; 
lean_dec_ref(v___x_2794_);
v___x_2795_ = lean_box(0);
v_as_x27_2785_ = v_tail_2792_;
v_b_2786_ = v___x_2795_;
goto _start;
}
else
{
lean_dec(v_tail_2792_);
return v___x_2794_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg___boxed(lean_object* v_as_x27_2797_, lean_object* v_b_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(v_as_x27_2797_, v_b_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
return v_res_2802_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = l_Lean_maxRecDepthErrorMessage;
v___x_2809_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
return v___x_2809_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3);
v___x_2811_ = l_Lean_MessageData_ofFormat(v___x_2810_);
return v___x_2811_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2812_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4);
v___x_2813_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2));
v___x_2814_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
lean_ctor_set(v___x_2814_, 1, v___x_2812_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(lean_object* v_ref_2815_){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2817_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5);
v___x_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2818_, 0, v_ref_2815_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
v___x_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___boxed(lean_object* v_ref_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(v_ref_2820_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object* v_env_2823_, lean_object* v_opts_2824_, lean_object* v_currNamespace_2825_, lean_object* v_openDecls_2826_, lean_object* v_n_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = l_Lean_ResolveName_resolveGlobalName(v_env_2823_, v_opts_2824_, v_currNamespace_2825_, v_openDecls_2826_, v_n_2827_);
v___x_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
lean_ctor_set(v___x_2831_, 1, v___y_2829_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object* v_env_2832_, lean_object* v_opts_2833_, lean_object* v_currNamespace_2834_, lean_object* v_openDecls_2835_, lean_object* v_n_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(v_env_2832_, v_opts_2833_, v_currNamespace_2834_, v_openDecls_2835_, v_n_2836_, v___y_2837_, v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec_ref(v_opts_2833_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object* v_x_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v___x_2845_; lean_object* v_env_2846_; lean_object* v___x_2847_; lean_object* v_scopes_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v_opts_2851_; lean_object* v___x_2852_; 
v___x_2845_ = lean_st_ref_get(v___y_2843_);
v_env_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc_ref(v_env_2846_);
lean_dec(v___x_2845_);
v___x_2847_ = lean_st_ref_get(v___y_2843_);
v_scopes_2848_ = lean_ctor_get(v___x_2847_, 2);
lean_inc(v_scopes_2848_);
lean_dec(v___x_2847_);
v___x_2849_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2850_ = l_List_head_x21___redArg(v___x_2849_, v_scopes_2848_);
lean_dec(v_scopes_2848_);
v_opts_2851_ = lean_ctor_get(v___x_2850_, 1);
lean_inc_ref(v_opts_2851_);
lean_dec(v___x_2850_);
v___x_2852_ = l_Lean_Elab_Command_getScope___redArg(v___y_2843_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v_currNamespace_2854_; lean_object* v___x_2855_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref(v___x_2852_);
v_currNamespace_2854_ = lean_ctor_get(v_a_2853_, 2);
lean_inc(v_currNamespace_2854_);
lean_dec(v_a_2853_);
v___x_2855_ = l_Lean_Elab_Command_getScope___redArg(v___y_2843_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v_openDecls_2857_; lean_object* v___x_2858_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref(v___x_2855_);
v_openDecls_2857_ = lean_ctor_get(v_a_2856_, 3);
lean_inc(v_openDecls_2857_);
lean_dec(v_a_2856_);
v___x_2858_ = l_Lean_Elab_Command_getRef___redArg(v___y_2842_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2860_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref(v___x_2858_);
v___x_2860_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2842_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v_currRecDepth_2862_; lean_object* v_quotContext_x3f_2863_; lean_object* v___f_2864_; lean_object* v___f_2865_; lean_object* v___f_2866_; lean_object* v___f_2867_; lean_object* v___f_2868_; lean_object* v_methods_2869_; lean_object* v_a_2871_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2860_);
v_currRecDepth_2862_ = lean_ctor_get(v___y_2842_, 2);
v_quotContext_x3f_2863_ = lean_ctor_get(v___y_2842_, 5);
lean_inc_ref(v_env_2846_);
v___f_2864_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2864_, 0, v_env_2846_);
lean_inc_ref(v_env_2846_);
v___f_2865_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2865_, 0, v_env_2846_);
lean_inc(v_currNamespace_2854_);
v___f_2866_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2866_, 0, v_currNamespace_2854_);
lean_inc(v_openDecls_2857_);
lean_inc(v_currNamespace_2854_);
lean_inc_ref(v_env_2846_);
v___f_2867_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2867_, 0, v_env_2846_);
lean_closure_set(v___f_2867_, 1, v_currNamespace_2854_);
lean_closure_set(v___f_2867_, 2, v_openDecls_2857_);
v___f_2868_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2868_, 0, v_env_2846_);
lean_closure_set(v___f_2868_, 1, v_opts_2851_);
lean_closure_set(v___f_2868_, 2, v_currNamespace_2854_);
lean_closure_set(v___f_2868_, 3, v_openDecls_2857_);
v_methods_2869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2869_, 0, v___f_2865_);
lean_ctor_set(v_methods_2869_, 1, v___f_2866_);
lean_ctor_set(v_methods_2869_, 2, v___f_2864_);
lean_ctor_set(v_methods_2869_, 3, v___f_2867_);
lean_ctor_set(v_methods_2869_, 4, v___f_2868_);
if (lean_obj_tag(v_quotContext_x3f_2863_) == 0)
{
lean_object* v___x_2943_; lean_object* v_a_2944_; 
v___x_2943_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_2843_);
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref(v___x_2943_);
v_a_2871_ = v_a_2944_;
goto v___jp_2870_;
}
else
{
lean_object* v_val_2945_; 
v_val_2945_ = lean_ctor_get(v_quotContext_x3f_2863_, 0);
lean_inc(v_val_2945_);
v_a_2871_ = v_val_2945_;
goto v___jp_2870_;
}
v___jp_2870_:
{
lean_object* v___x_2872_; lean_object* v_maxRecDepth_2873_; lean_object* v___x_2874_; lean_object* v_nextMacroScope_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2872_ = lean_st_ref_get(v___y_2843_);
v_maxRecDepth_2873_ = lean_ctor_get(v___x_2872_, 5);
lean_inc(v_maxRecDepth_2873_);
lean_dec(v___x_2872_);
v___x_2874_ = lean_st_ref_get(v___y_2843_);
v_nextMacroScope_2875_ = lean_ctor_get(v___x_2874_, 4);
lean_inc(v_nextMacroScope_2875_);
lean_dec(v___x_2874_);
lean_inc(v_currRecDepth_2862_);
v___x_2876_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2876_, 0, v_methods_2869_);
lean_ctor_set(v___x_2876_, 1, v_a_2871_);
lean_ctor_set(v___x_2876_, 2, v_a_2861_);
lean_ctor_set(v___x_2876_, 3, v_currRecDepth_2862_);
lean_ctor_set(v___x_2876_, 4, v_maxRecDepth_2873_);
lean_ctor_set(v___x_2876_, 5, v_a_2859_);
v___x_2877_ = lean_box(0);
v___x_2878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2878_, 0, v_nextMacroScope_2875_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
lean_ctor_set(v___x_2878_, 2, v___x_2877_);
v___x_2879_ = lean_apply_2(v_x_2841_, v___x_2876_, v___x_2878_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v_a_2881_; lean_object* v_macroScope_2882_; lean_object* v_traceMsgs_2883_; lean_object* v_expandedMacroDecls_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 1);
lean_inc(v_a_2880_);
v_a_2881_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2881_);
lean_dec_ref(v___x_2879_);
v_macroScope_2882_ = lean_ctor_get(v_a_2880_, 0);
lean_inc(v_macroScope_2882_);
v_traceMsgs_2883_ = lean_ctor_get(v_a_2880_, 1);
lean_inc(v_traceMsgs_2883_);
v_expandedMacroDecls_2884_ = lean_ctor_get(v_a_2880_, 2);
lean_inc(v_expandedMacroDecls_2884_);
lean_dec(v_a_2880_);
v___x_2885_ = lean_box(0);
v___x_2886_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(v_expandedMacroDecls_2884_, v___x_2885_, v___y_2842_, v___y_2843_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v___x_2887_; lean_object* v_env_2888_; lean_object* v_messages_2889_; lean_object* v_scopes_2890_; lean_object* v_usedQuotCtxts_2891_; lean_object* v_maxRecDepth_2892_; lean_object* v_ngen_2893_; lean_object* v_auxDeclNGen_2894_; lean_object* v_infoState_2895_; lean_object* v_traceState_2896_; lean_object* v_snapshotTasks_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref(v___x_2886_);
v___x_2887_ = lean_st_ref_take(v___y_2843_);
v_env_2888_ = lean_ctor_get(v___x_2887_, 0);
v_messages_2889_ = lean_ctor_get(v___x_2887_, 1);
v_scopes_2890_ = lean_ctor_get(v___x_2887_, 2);
v_usedQuotCtxts_2891_ = lean_ctor_get(v___x_2887_, 3);
v_maxRecDepth_2892_ = lean_ctor_get(v___x_2887_, 5);
v_ngen_2893_ = lean_ctor_get(v___x_2887_, 6);
v_auxDeclNGen_2894_ = lean_ctor_get(v___x_2887_, 7);
v_infoState_2895_ = lean_ctor_get(v___x_2887_, 8);
v_traceState_2896_ = lean_ctor_get(v___x_2887_, 9);
v_snapshotTasks_2897_ = lean_ctor_get(v___x_2887_, 10);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2923_ == 0)
{
lean_object* v_unused_2924_; 
v_unused_2924_ = lean_ctor_get(v___x_2887_, 4);
lean_dec(v_unused_2924_);
v___x_2899_ = v___x_2887_;
v_isShared_2900_ = v_isSharedCheck_2923_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_snapshotTasks_2897_);
lean_inc(v_traceState_2896_);
lean_inc(v_infoState_2895_);
lean_inc(v_auxDeclNGen_2894_);
lean_inc(v_ngen_2893_);
lean_inc(v_maxRecDepth_2892_);
lean_inc(v_usedQuotCtxts_2891_);
lean_inc(v_scopes_2890_);
lean_inc(v_messages_2889_);
lean_inc(v_env_2888_);
lean_dec(v___x_2887_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2923_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 4, v_macroScope_2882_);
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_env_2888_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v_messages_2889_);
lean_ctor_set(v_reuseFailAlloc_2922_, 2, v_scopes_2890_);
lean_ctor_set(v_reuseFailAlloc_2922_, 3, v_usedQuotCtxts_2891_);
lean_ctor_set(v_reuseFailAlloc_2922_, 4, v_macroScope_2882_);
lean_ctor_set(v_reuseFailAlloc_2922_, 5, v_maxRecDepth_2892_);
lean_ctor_set(v_reuseFailAlloc_2922_, 6, v_ngen_2893_);
lean_ctor_set(v_reuseFailAlloc_2922_, 7, v_auxDeclNGen_2894_);
lean_ctor_set(v_reuseFailAlloc_2922_, 8, v_infoState_2895_);
lean_ctor_set(v_reuseFailAlloc_2922_, 9, v_traceState_2896_);
lean_ctor_set(v_reuseFailAlloc_2922_, 10, v_snapshotTasks_2897_);
v___x_2902_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2903_ = lean_st_ref_set(v___y_2843_, v___x_2902_);
v___x_2904_ = l_List_reverse___redArg(v_traceMsgs_2883_);
v___x_2905_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(v___x_2904_, v___y_2842_, v___y_2843_);
lean_dec_ref(v___y_2842_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2912_ == 0)
{
lean_object* v_unused_2913_; 
v_unused_2913_ = lean_ctor_get(v___x_2905_, 0);
lean_dec(v_unused_2913_);
v___x_2907_ = v___x_2905_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_dec(v___x_2905_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v_a_2881_);
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2881_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec(v_a_2881_);
v_a_2914_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2905_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2905_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_traceMsgs_2883_);
lean_dec(v_macroScope_2882_);
lean_dec(v_a_2881_);
lean_dec_ref(v___y_2842_);
v_a_2925_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2886_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2886_);
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
lean_object* v_a_2933_; 
v_a_2933_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2933_);
lean_dec_ref(v___x_2879_);
if (lean_obj_tag(v_a_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v_a_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v_a_2934_ = lean_ctor_get(v_a_2933_, 0);
lean_inc(v_a_2934_);
v_a_2935_ = lean_ctor_get(v_a_2933_, 1);
lean_inc_ref(v_a_2935_);
lean_dec_ref(v_a_2933_);
v___x_2936_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0));
v___x_2937_ = lean_string_dec_eq(v_a_2935_, v___x_2936_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2938_, 0, v_a_2935_);
v___x_2939_ = l_Lean_MessageData_ofFormat(v___x_2938_);
v___x_2940_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_a_2934_, v___x_2939_, v___y_2842_, v___y_2843_);
lean_dec(v_a_2934_);
return v___x_2940_;
}
else
{
lean_object* v___x_2941_; 
lean_dec_ref(v_a_2935_);
lean_dec_ref(v___y_2842_);
v___x_2941_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(v_a_2934_);
return v___x_2941_;
}
}
else
{
lean_object* v___x_2942_; 
lean_dec_ref(v___y_2842_);
v___x_2942_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2942_;
}
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_dec(v_a_2859_);
lean_dec(v_openDecls_2857_);
lean_dec(v_currNamespace_2854_);
lean_dec_ref(v_opts_2851_);
lean_dec_ref(v_env_2846_);
lean_dec_ref(v___y_2842_);
lean_dec_ref(v_x_2841_);
v_a_2946_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2860_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2860_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec(v_openDecls_2857_);
lean_dec(v_currNamespace_2854_);
lean_dec_ref(v_opts_2851_);
lean_dec_ref(v_env_2846_);
lean_dec_ref(v___y_2842_);
lean_dec_ref(v_x_2841_);
v_a_2954_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2858_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2858_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_dec(v_currNamespace_2854_);
lean_dec_ref(v_opts_2851_);
lean_dec_ref(v_env_2846_);
lean_dec_ref(v___y_2842_);
lean_dec_ref(v_x_2841_);
v_a_2962_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2855_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2855_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec_ref(v_opts_2851_);
lean_dec_ref(v_env_2846_);
lean_dec_ref(v___y_2842_);
lean_dec_ref(v_x_2841_);
v_a_2970_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2852_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2852_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object* v_x_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_2978_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2980_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object* v_x_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3026_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_3027_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_3068_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
lean_inc(v_x_3022_);
v___x_3069_ = l_Lean_Syntax_isOfKind(v_x_3022_, v___x_3068_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; 
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_x_3022_);
v___x_3070_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3070_;
}
else
{
lean_object* v___x_3071_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; uint8_t v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; size_t v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; uint8_t v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; size_t v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; uint8_t v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; size_t v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; uint8_t v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; size_t v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; uint8_t v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; size_t v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v_expectedType_x3f_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v_prio_x3f_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v_name_x3f_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v_prec_x3f_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v_attrs_x3f_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v_doc_x3f_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___x_3548_; uint8_t v___x_3549_; 
v___x_3071_ = lean_unsigned_to_nat(0u);
v___x_3548_ = l_Lean_Syntax_getArg(v_x_3022_, v___x_3071_);
v___x_3549_ = l_Lean_Syntax_isNone(v___x_3548_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; uint8_t v___x_3551_; 
v___x_3550_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3548_);
v___x_3551_ = l_Lean_Syntax_matchesNull(v___x_3548_, v___x_3550_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; 
lean_dec(v___x_3548_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_x_3022_);
v___x_3552_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3552_;
}
else
{
lean_object* v_doc_x3f_3553_; lean_object* v___x_3554_; uint8_t v___x_3555_; 
v_doc_x3f_3553_ = l_Lean_Syntax_getArg(v___x_3548_, v___x_3071_);
lean_dec(v___x_3548_);
v___x_3554_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(v_doc_x3f_3553_);
v___x_3555_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3553_, v___x_3554_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; 
lean_dec(v_doc_x3f_3553_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_x_3022_);
v___x_3556_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3556_;
}
else
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3557_, 0, v_doc_x3f_3553_);
v_doc_x3f_3532_ = v___x_3557_;
v___y_3533_ = v_a_3023_;
v___y_3534_ = v_a_3024_;
goto v___jp_3531_;
}
}
}
else
{
lean_object* v___x_3558_; 
lean_dec(v___x_3548_);
v___x_3558_ = lean_box(0);
v_doc_x3f_3532_ = v___x_3558_;
v___y_3533_ = v_a_3023_;
v___y_3534_ = v_a_3024_;
goto v___jp_3531_;
}
v___jp_3072_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_inc_ref(v___y_3083_);
v___x_3089_ = l_Array_append___redArg(v___y_3083_, v___y_3088_);
lean_dec_ref(v___y_3088_);
lean_inc(v___y_3081_);
lean_inc(v___y_3079_);
v___x_3090_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3090_, 0, v___y_3079_);
lean_ctor_set(v___x_3090_, 1, v___y_3081_);
lean_ctor_set(v___x_3090_, 2, v___x_3089_);
lean_inc_ref(v___y_3083_);
lean_inc(v___y_3081_);
lean_inc(v___y_3079_);
v___x_3091_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3091_, 0, v___y_3079_);
lean_ctor_set(v___x_3091_, 1, v___y_3081_);
lean_ctor_set(v___x_3091_, 2, v___y_3083_);
lean_inc_ref(v___x_3091_);
lean_inc(v___y_3079_);
v___x_3092_ = l_Lean_Syntax_node1(v___y_3079_, v___y_3085_, v___x_3091_);
lean_inc(v___y_3079_);
v___x_3093_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___y_3079_);
lean_ctor_set(v___x_3093_, 1, v___y_3080_);
lean_inc(v___y_3079_);
v___x_3094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___y_3079_);
lean_ctor_set(v___x_3094_, 1, v___y_3076_);
lean_inc(v___y_3081_);
lean_inc(v___y_3079_);
v___x_3095_ = l_Lean_Syntax_node2(v___y_3079_, v___y_3081_, v___x_3094_, v___y_3073_);
if (lean_obj_tag(v___y_3086_) == 1)
{
lean_object* v_val_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v_val_3096_ = lean_ctor_get(v___y_3086_, 0);
lean_inc(v_val_3096_);
lean_dec_ref(v___y_3086_);
v___x_3097_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___y_3079_);
v___x_3098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___y_3079_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = l_Array_mkArray2___redArg(v___x_3098_, v_val_3096_);
v___y_3029_ = v___y_3074_;
v___y_3030_ = v___x_3093_;
v___y_3031_ = v___y_3075_;
v___y_3032_ = v___x_3095_;
v___y_3033_ = v___y_3077_;
v___y_3034_ = v___y_3078_;
v___y_3035_ = v___y_3079_;
v___y_3036_ = v___x_3092_;
v___y_3037_ = v___y_3081_;
v___y_3038_ = v___y_3082_;
v___y_3039_ = v___x_3090_;
v___y_3040_ = v___y_3083_;
v___y_3041_ = v___y_3084_;
v___y_3042_ = v___x_3091_;
v___y_3043_ = v___y_3087_;
v___y_3044_ = v___x_3099_;
goto v___jp_3028_;
}
else
{
lean_object* v___x_3100_; 
lean_dec(v___y_3086_);
v___x_3100_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3029_ = v___y_3074_;
v___y_3030_ = v___x_3093_;
v___y_3031_ = v___y_3075_;
v___y_3032_ = v___x_3095_;
v___y_3033_ = v___y_3077_;
v___y_3034_ = v___y_3078_;
v___y_3035_ = v___y_3079_;
v___y_3036_ = v___x_3092_;
v___y_3037_ = v___y_3081_;
v___y_3038_ = v___y_3082_;
v___y_3039_ = v___x_3090_;
v___y_3040_ = v___y_3083_;
v___y_3041_ = v___y_3084_;
v___y_3042_ = v___x_3091_;
v___y_3043_ = v___y_3087_;
v___y_3044_ = v___x_3100_;
goto v___jp_3028_;
}
}
v___jp_3101_:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_3117_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
if (lean_obj_tag(v___y_3104_) == 1)
{
lean_object* v_val_3118_; lean_object* v___x_3119_; 
v_val_3118_ = lean_ctor_get(v___y_3104_, 0);
lean_inc(v_val_3118_);
lean_dec_ref(v___y_3104_);
v___x_3119_ = l_Array_mkArray1___redArg(v_val_3118_);
v___y_3073_ = v___y_3102_;
v___y_3074_ = v___y_3103_;
v___y_3075_ = v___x_3117_;
v___y_3076_ = v___y_3105_;
v___y_3077_ = v___y_3106_;
v___y_3078_ = v___y_3107_;
v___y_3079_ = v___y_3108_;
v___y_3080_ = v___x_3116_;
v___y_3081_ = v___y_3109_;
v___y_3082_ = v___y_3110_;
v___y_3083_ = v___y_3111_;
v___y_3084_ = v___y_3112_;
v___y_3085_ = v___y_3113_;
v___y_3086_ = v___y_3114_;
v___y_3087_ = v___y_3115_;
v___y_3088_ = v___x_3119_;
goto v___jp_3072_;
}
else
{
lean_object* v___x_3120_; 
lean_dec(v___y_3104_);
v___x_3120_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3073_ = v___y_3102_;
v___y_3074_ = v___y_3103_;
v___y_3075_ = v___x_3117_;
v___y_3076_ = v___y_3105_;
v___y_3077_ = v___y_3106_;
v___y_3078_ = v___y_3107_;
v___y_3079_ = v___y_3108_;
v___y_3080_ = v___x_3116_;
v___y_3081_ = v___y_3109_;
v___y_3082_ = v___y_3110_;
v___y_3083_ = v___y_3111_;
v___y_3084_ = v___y_3112_;
v___y_3085_ = v___y_3113_;
v___y_3086_ = v___y_3114_;
v___y_3087_ = v___y_3115_;
v___y_3088_ = v___x_3120_;
goto v___jp_3072_;
}
}
v___jp_3121_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; size_t v_sz_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
lean_inc_ref(v___y_3138_);
v___x_3145_ = l_Array_append___redArg(v___y_3138_, v___y_3144_);
lean_dec_ref(v___y_3144_);
lean_inc(v___y_3134_);
lean_inc(v___y_3139_);
v___x_3146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3146_, 0, v___y_3139_);
lean_ctor_set(v___x_3146_, 1, v___y_3134_);
lean_ctor_set(v___x_3146_, 2, v___x_3145_);
v___x_3147_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
v___x_3148_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc(v___y_3139_);
v___x_3149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___y_3139_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
v___x_3150_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__6));
lean_inc(v___y_3139_);
v___x_3151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___y_3139_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
v___x_3152_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(v___y_3139_);
v___x_3153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___y_3139_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v___x_3154_ = l_Nat_reprFast(v___y_3127_);
v___x_3155_ = lean_box(2);
v___x_3156_ = l_Lean_Syntax_mkNumLit(v___x_3154_, v___x_3155_);
v___x_3157_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
lean_inc(v___y_3139_);
v___x_3158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___y_3139_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
lean_inc(v___y_3139_);
v___x_3159_ = l_Lean_Syntax_node5(v___y_3139_, v___x_3147_, v___x_3149_, v___x_3151_, v___x_3153_, v___x_3156_, v___x_3158_);
lean_inc(v___y_3134_);
lean_inc(v___y_3139_);
v___x_3160_ = l_Lean_Syntax_node1(v___y_3139_, v___y_3134_, v___x_3159_);
v_sz_3161_ = lean_array_size(v___y_3122_);
v___x_3162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_3161_, v___y_3141_, v___y_3122_);
lean_inc_ref(v___y_3138_);
v___x_3163_ = l_Array_append___redArg(v___y_3138_, v___x_3162_);
lean_dec_ref(v___x_3162_);
lean_inc(v___y_3134_);
lean_inc(v___y_3139_);
v___x_3164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3164_, 0, v___y_3139_);
lean_ctor_set(v___x_3164_, 1, v___y_3134_);
lean_ctor_set(v___x_3164_, 2, v___x_3163_);
v___x_3165_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___y_3139_);
v___x_3166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___y_3139_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = lean_unsigned_to_nat(10u);
v___x_3168_ = lean_mk_empty_array_with_capacity(v___x_3167_);
v___x_3169_ = lean_array_push(v___x_3168_, v___y_3130_);
v___x_3170_ = lean_array_push(v___x_3169_, v___y_3131_);
v___x_3171_ = lean_array_push(v___x_3170_, v___y_3137_);
v___x_3172_ = lean_array_push(v___x_3171_, v___y_3132_);
v___x_3173_ = lean_array_push(v___x_3172_, v___y_3135_);
v___x_3174_ = lean_array_push(v___x_3173_, v___x_3146_);
v___x_3175_ = lean_array_push(v___x_3174_, v___x_3160_);
v___x_3176_ = lean_array_push(v___x_3175_, v___x_3164_);
v___x_3177_ = lean_array_push(v___x_3176_, v___x_3166_);
lean_inc(v___y_3124_);
v___x_3178_ = lean_array_push(v___x_3177_, v___y_3124_);
v___x_3179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3179_, 0, v___y_3139_);
lean_ctor_set(v___x_3179_, 1, v___y_3125_);
lean_ctor_set(v___x_3179_, 2, v___x_3178_);
lean_inc(v___y_3136_);
lean_inc_ref(v___y_3143_);
v___x_3180_ = l_Lean_Elab_Command_elabSyntax(v___x_3179_, v___y_3143_, v___y_3136_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3182_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_a_3181_);
lean_dec_ref(v___x_3180_);
v___x_3182_ = l_Lean_Elab_Command_getRef___redArg(v___y_3143_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3184_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3183_);
lean_dec_ref(v___x_3182_);
v___x_3184_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3143_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_quotContext_x3f_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_dec_ref(v___x_3184_);
v_quotContext_x3f_3185_ = lean_ctor_get(v___y_3143_, 5);
v___x_3186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3155_);
lean_ctor_set(v___x_3186_, 1, v_a_3181_);
lean_ctor_set(v___x_3186_, 2, v___y_3129_);
v___x_3187_ = l_Lean_SourceInfo_fromRef(v_a_3183_, v___y_3126_);
lean_dec(v_a_3183_);
if (lean_obj_tag(v_quotContext_x3f_3185_) == 0)
{
lean_object* v___x_3188_; 
v___x_3188_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3136_);
lean_dec_ref(v___x_3188_);
v___y_3102_ = v___y_3124_;
v___y_3103_ = v___y_3123_;
v___y_3104_ = v___y_3128_;
v___y_3105_ = v___x_3165_;
v___y_3106_ = v___y_3133_;
v___y_3107_ = v___x_3157_;
v___y_3108_ = v___x_3187_;
v___y_3109_ = v___y_3134_;
v___y_3110_ = v___y_3136_;
v___y_3111_ = v___y_3138_;
v___y_3112_ = v___x_3186_;
v___y_3113_ = v___y_3140_;
v___y_3114_ = v___y_3142_;
v___y_3115_ = v___y_3143_;
goto v___jp_3101_;
}
else
{
v___y_3102_ = v___y_3124_;
v___y_3103_ = v___y_3123_;
v___y_3104_ = v___y_3128_;
v___y_3105_ = v___x_3165_;
v___y_3106_ = v___y_3133_;
v___y_3107_ = v___x_3157_;
v___y_3108_ = v___x_3187_;
v___y_3109_ = v___y_3134_;
v___y_3110_ = v___y_3136_;
v___y_3111_ = v___y_3138_;
v___y_3112_ = v___x_3186_;
v___y_3113_ = v___y_3140_;
v___y_3114_ = v___y_3142_;
v___y_3115_ = v___y_3143_;
goto v___jp_3101_;
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v_a_3183_);
lean_dec(v_a_3181_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3138_);
lean_dec(v___y_3136_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec(v___y_3124_);
lean_dec(v___y_3123_);
v_a_3189_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3184_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3184_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec(v_a_3181_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3138_);
lean_dec(v___y_3136_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec(v___y_3124_);
lean_dec(v___y_3123_);
v_a_3197_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3182_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3182_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3138_);
lean_dec(v___y_3136_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec(v___y_3124_);
lean_dec(v___y_3123_);
v_a_3205_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3180_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3180_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
v___jp_3213_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_inc_ref(v___y_3230_);
v___x_3237_ = l_Array_append___redArg(v___y_3230_, v___y_3236_);
lean_dec_ref(v___y_3236_);
lean_inc(v___y_3226_);
lean_inc(v___y_3231_);
v___x_3238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3238_, 0, v___y_3231_);
lean_ctor_set(v___x_3238_, 1, v___y_3226_);
lean_ctor_set(v___x_3238_, 2, v___x_3237_);
if (lean_obj_tag(v___y_3229_) == 1)
{
lean_object* v_val_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v_val_3239_ = lean_ctor_get(v___y_3229_, 0);
lean_inc(v_val_3239_);
lean_dec_ref(v___y_3229_);
v___x_3240_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
v___x_3241_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc(v___y_3231_);
v___x_3242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___y_3231_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__9));
lean_inc(v___y_3231_);
v___x_3244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___y_3231_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(v___y_3231_);
v___x_3246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___y_3231_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
lean_inc(v___y_3231_);
v___x_3248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___y_3231_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
lean_inc(v___y_3231_);
v___x_3249_ = l_Lean_Syntax_node5(v___y_3231_, v___x_3240_, v___x_3242_, v___x_3244_, v___x_3246_, v_val_3239_, v___x_3248_);
v___x_3250_ = l_Array_mkArray1___redArg(v___x_3249_);
v___y_3122_ = v___y_3214_;
v___y_3123_ = v___y_3215_;
v___y_3124_ = v___y_3216_;
v___y_3125_ = v___y_3217_;
v___y_3126_ = v___y_3218_;
v___y_3127_ = v___y_3219_;
v___y_3128_ = v___y_3220_;
v___y_3129_ = v___y_3221_;
v___y_3130_ = v___y_3222_;
v___y_3131_ = v___y_3223_;
v___y_3132_ = v___y_3224_;
v___y_3133_ = v___y_3225_;
v___y_3134_ = v___y_3226_;
v___y_3135_ = v___x_3238_;
v___y_3136_ = v___y_3227_;
v___y_3137_ = v___y_3228_;
v___y_3138_ = v___y_3230_;
v___y_3139_ = v___y_3231_;
v___y_3140_ = v___y_3232_;
v___y_3141_ = v___y_3233_;
v___y_3142_ = v___y_3234_;
v___y_3143_ = v___y_3235_;
v___y_3144_ = v___x_3250_;
goto v___jp_3121_;
}
else
{
lean_object* v___x_3251_; 
lean_dec(v___y_3229_);
v___x_3251_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3122_ = v___y_3214_;
v___y_3123_ = v___y_3215_;
v___y_3124_ = v___y_3216_;
v___y_3125_ = v___y_3217_;
v___y_3126_ = v___y_3218_;
v___y_3127_ = v___y_3219_;
v___y_3128_ = v___y_3220_;
v___y_3129_ = v___y_3221_;
v___y_3130_ = v___y_3222_;
v___y_3131_ = v___y_3223_;
v___y_3132_ = v___y_3224_;
v___y_3133_ = v___y_3225_;
v___y_3134_ = v___y_3226_;
v___y_3135_ = v___x_3238_;
v___y_3136_ = v___y_3227_;
v___y_3137_ = v___y_3228_;
v___y_3138_ = v___y_3230_;
v___y_3139_ = v___y_3231_;
v___y_3140_ = v___y_3232_;
v___y_3141_ = v___y_3233_;
v___y_3142_ = v___y_3234_;
v___y_3143_ = v___y_3235_;
v___y_3144_ = v___x_3251_;
goto v___jp_3121_;
}
}
v___jp_3252_:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
lean_inc_ref(v___y_3268_);
v___x_3277_ = l_Array_append___redArg(v___y_3268_, v___y_3276_);
lean_dec_ref(v___y_3276_);
lean_inc(v___y_3264_);
lean_inc(v___y_3269_);
v___x_3278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3278_, 0, v___y_3269_);
lean_ctor_set(v___x_3278_, 1, v___y_3264_);
lean_ctor_set(v___x_3278_, 2, v___x_3277_);
v___x_3279_ = l_Lean_SourceInfo_fromRef(v___y_3271_, v___x_3069_);
lean_dec(v___y_3271_);
v___x_3280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
lean_ctor_set(v___x_3280_, 1, v___y_3262_);
if (lean_obj_tag(v___y_3272_) == 1)
{
lean_object* v_val_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_val_3281_ = lean_ctor_get(v___y_3272_, 0);
lean_inc(v_val_3281_);
lean_dec_ref(v___y_3272_);
v___x_3282_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
v___x_3283_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___y_3269_);
v___x_3284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___y_3269_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
lean_inc(v___y_3269_);
v___x_3285_ = l_Lean_Syntax_node2(v___y_3269_, v___x_3282_, v___x_3284_, v_val_3281_);
v___x_3286_ = l_Array_mkArray1___redArg(v___x_3285_);
v___y_3214_ = v___y_3253_;
v___y_3215_ = v___y_3254_;
v___y_3216_ = v___y_3255_;
v___y_3217_ = v___y_3256_;
v___y_3218_ = v___y_3257_;
v___y_3219_ = v___y_3258_;
v___y_3220_ = v___y_3260_;
v___y_3221_ = v___y_3261_;
v___y_3222_ = v___y_3259_;
v___y_3223_ = v___x_3278_;
v___y_3224_ = v___x_3280_;
v___y_3225_ = v___y_3263_;
v___y_3226_ = v___y_3264_;
v___y_3227_ = v___y_3265_;
v___y_3228_ = v___y_3266_;
v___y_3229_ = v___y_3267_;
v___y_3230_ = v___y_3268_;
v___y_3231_ = v___y_3269_;
v___y_3232_ = v___y_3270_;
v___y_3233_ = v___y_3273_;
v___y_3234_ = v___y_3274_;
v___y_3235_ = v___y_3275_;
v___y_3236_ = v___x_3286_;
goto v___jp_3213_;
}
else
{
lean_object* v___x_3287_; 
lean_dec(v___y_3272_);
v___x_3287_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3214_ = v___y_3253_;
v___y_3215_ = v___y_3254_;
v___y_3216_ = v___y_3255_;
v___y_3217_ = v___y_3256_;
v___y_3218_ = v___y_3257_;
v___y_3219_ = v___y_3258_;
v___y_3220_ = v___y_3260_;
v___y_3221_ = v___y_3261_;
v___y_3222_ = v___y_3259_;
v___y_3223_ = v___x_3278_;
v___y_3224_ = v___x_3280_;
v___y_3225_ = v___y_3263_;
v___y_3226_ = v___y_3264_;
v___y_3227_ = v___y_3265_;
v___y_3228_ = v___y_3266_;
v___y_3229_ = v___y_3267_;
v___y_3230_ = v___y_3268_;
v___y_3231_ = v___y_3269_;
v___y_3232_ = v___y_3270_;
v___y_3233_ = v___y_3273_;
v___y_3234_ = v___y_3274_;
v___y_3235_ = v___y_3275_;
v___y_3236_ = v___x_3287_;
goto v___jp_3213_;
}
}
v___jp_3288_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
lean_inc_ref(v___y_3304_);
v___x_3313_ = l_Array_append___redArg(v___y_3304_, v___y_3312_);
lean_dec_ref(v___y_3312_);
lean_inc(v___y_3299_);
lean_inc(v___y_3305_);
v___x_3314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3314_, 0, v___y_3305_);
lean_ctor_set(v___x_3314_, 1, v___y_3299_);
lean_ctor_set(v___x_3314_, 2, v___x_3313_);
if (lean_obj_tag(v___y_3301_) == 1)
{
lean_object* v_val_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v_val_3315_ = lean_ctor_get(v___y_3301_, 0);
lean_inc(v_val_3315_);
lean_dec_ref(v___y_3301_);
v___x_3316_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_3298_);
v___x_3317_ = l_Lean_Name_mkStr4(v___x_3026_, v___x_3027_, v___y_3298_, v___x_3316_);
v___x_3318_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(v___y_3305_);
v___x_3319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___y_3305_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
lean_inc_ref(v___y_3304_);
v___x_3320_ = l_Array_append___redArg(v___y_3304_, v_val_3315_);
lean_dec(v_val_3315_);
lean_inc(v___y_3299_);
lean_inc(v___y_3305_);
v___x_3321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3321_, 0, v___y_3305_);
lean_ctor_set(v___x_3321_, 1, v___y_3299_);
lean_ctor_set(v___x_3321_, 2, v___x_3320_);
v___x_3322_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(v___y_3305_);
v___x_3323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___y_3305_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
lean_inc(v___y_3305_);
v___x_3324_ = l_Lean_Syntax_node3(v___y_3305_, v___x_3317_, v___x_3319_, v___x_3321_, v___x_3323_);
v___x_3325_ = l_Array_mkArray1___redArg(v___x_3324_);
v___y_3253_ = v___y_3289_;
v___y_3254_ = v___y_3290_;
v___y_3255_ = v___y_3291_;
v___y_3256_ = v___y_3292_;
v___y_3257_ = v___y_3293_;
v___y_3258_ = v___y_3294_;
v___y_3259_ = v___x_3314_;
v___y_3260_ = v___y_3295_;
v___y_3261_ = v___y_3296_;
v___y_3262_ = v___y_3297_;
v___y_3263_ = v___y_3298_;
v___y_3264_ = v___y_3299_;
v___y_3265_ = v___y_3300_;
v___y_3266_ = v___y_3302_;
v___y_3267_ = v___y_3303_;
v___y_3268_ = v___y_3304_;
v___y_3269_ = v___y_3305_;
v___y_3270_ = v___y_3307_;
v___y_3271_ = v___y_3306_;
v___y_3272_ = v___y_3308_;
v___y_3273_ = v___y_3309_;
v___y_3274_ = v___y_3310_;
v___y_3275_ = v___y_3311_;
v___y_3276_ = v___x_3325_;
goto v___jp_3252_;
}
else
{
lean_object* v___x_3326_; 
lean_dec(v___y_3301_);
v___x_3326_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3253_ = v___y_3289_;
v___y_3254_ = v___y_3290_;
v___y_3255_ = v___y_3291_;
v___y_3256_ = v___y_3292_;
v___y_3257_ = v___y_3293_;
v___y_3258_ = v___y_3294_;
v___y_3259_ = v___x_3314_;
v___y_3260_ = v___y_3295_;
v___y_3261_ = v___y_3296_;
v___y_3262_ = v___y_3297_;
v___y_3263_ = v___y_3298_;
v___y_3264_ = v___y_3299_;
v___y_3265_ = v___y_3300_;
v___y_3266_ = v___y_3302_;
v___y_3267_ = v___y_3303_;
v___y_3268_ = v___y_3304_;
v___y_3269_ = v___y_3305_;
v___y_3270_ = v___y_3307_;
v___y_3271_ = v___y_3306_;
v___y_3272_ = v___y_3308_;
v___y_3273_ = v___y_3309_;
v___y_3274_ = v___y_3310_;
v___y_3275_ = v___y_3311_;
v___y_3276_ = v___x_3326_;
goto v___jp_3252_;
}
}
v___jp_3327_:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3347_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__12));
v___x_3348_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__13));
v___x_3349_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_3350_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v___y_3333_) == 1)
{
lean_object* v_val_3351_; lean_object* v___x_3352_; 
v_val_3351_ = lean_ctor_get(v___y_3333_, 0);
lean_inc(v_val_3351_);
v___x_3352_ = l_Array_mkArray1___redArg(v_val_3351_);
v___y_3289_ = v___y_3328_;
v___y_3290_ = v___y_3329_;
v___y_3291_ = v___y_3330_;
v___y_3292_ = v___x_3348_;
v___y_3293_ = v___y_3331_;
v___y_3294_ = v___y_3332_;
v___y_3295_ = v___y_3333_;
v___y_3296_ = v___y_3334_;
v___y_3297_ = v___x_3347_;
v___y_3298_ = v___y_3335_;
v___y_3299_ = v___x_3349_;
v___y_3300_ = v___y_3336_;
v___y_3301_ = v___y_3337_;
v___y_3302_ = v___y_3338_;
v___y_3303_ = v___y_3339_;
v___y_3304_ = v___x_3350_;
v___y_3305_ = v___y_3340_;
v___y_3306_ = v___y_3342_;
v___y_3307_ = v___y_3341_;
v___y_3308_ = v___y_3343_;
v___y_3309_ = v___y_3344_;
v___y_3310_ = v___y_3345_;
v___y_3311_ = v___y_3346_;
v___y_3312_ = v___x_3352_;
goto v___jp_3288_;
}
else
{
lean_object* v___x_3353_; 
v___x_3353_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3289_ = v___y_3328_;
v___y_3290_ = v___y_3329_;
v___y_3291_ = v___y_3330_;
v___y_3292_ = v___x_3348_;
v___y_3293_ = v___y_3331_;
v___y_3294_ = v___y_3332_;
v___y_3295_ = v___y_3333_;
v___y_3296_ = v___y_3334_;
v___y_3297_ = v___x_3347_;
v___y_3298_ = v___y_3335_;
v___y_3299_ = v___x_3349_;
v___y_3300_ = v___y_3336_;
v___y_3301_ = v___y_3337_;
v___y_3302_ = v___y_3338_;
v___y_3303_ = v___y_3339_;
v___y_3304_ = v___x_3350_;
v___y_3305_ = v___y_3340_;
v___y_3306_ = v___y_3342_;
v___y_3307_ = v___y_3341_;
v___y_3308_ = v___y_3343_;
v___y_3309_ = v___y_3344_;
v___y_3310_ = v___y_3345_;
v___y_3311_ = v___y_3346_;
v___y_3312_ = v___x_3353_;
goto v___jp_3288_;
}
}
v___jp_3354_:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio), 3, 1);
lean_closure_set(v___x_3371_, 0, v___y_3356_);
lean_inc_ref(v___y_3369_);
v___x_3372_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v___x_3371_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v_args_3374_; size_t v_sz_3375_; size_t v___x_3376_; lean_object* v___x_3377_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref(v___x_3372_);
v_args_3374_ = l_Lean_Syntax_getArgs(v___y_3362_);
lean_dec(v___y_3362_);
v_sz_3375_ = lean_array_size(v_args_3374_);
v___x_3376_ = ((size_t)0ULL);
lean_inc_ref(v___y_3369_);
v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_3375_, v___x_3376_, v_args_3374_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3379_; lean_object* v_fst_3380_; lean_object* v_snd_3381_; lean_object* v___x_3382_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref(v___x_3377_);
v___x_3379_ = l_Array_unzip___redArg(v_a_3378_);
lean_dec(v_a_3378_);
v_fst_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_fst_3380_);
v_snd_3381_ = lean_ctor_get(v___x_3379_, 1);
lean_inc(v_snd_3381_);
lean_dec_ref(v___x_3379_);
v___x_3382_ = l_Lean_Elab_Command_getRef___redArg(v___y_3369_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref(v___x_3382_);
v___x_3384_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3369_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_quotContext_x3f_3385_; lean_object* v___x_3386_; uint8_t v___x_3387_; lean_object* v___x_3388_; 
lean_dec_ref(v___x_3384_);
v_quotContext_x3f_3385_ = lean_ctor_get(v___y_3369_, 5);
v___x_3386_ = l_Lean_Syntax_getArg(v___y_3366_, v___y_3367_);
lean_dec(v___y_3366_);
v___x_3387_ = 0;
v___x_3388_ = l_Lean_SourceInfo_fromRef(v_a_3383_, v___x_3387_);
lean_dec(v_a_3383_);
if (lean_obj_tag(v_quotContext_x3f_3385_) == 0)
{
lean_object* v___x_3389_; 
v___x_3389_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3370_);
lean_dec_ref(v___x_3389_);
v___y_3328_ = v_fst_3380_;
v___y_3329_ = v___x_3386_;
v___y_3330_ = v___y_3355_;
v___y_3331_ = v___x_3387_;
v___y_3332_ = v_a_3373_;
v___y_3333_ = v___y_3357_;
v___y_3334_ = v_snd_3381_;
v___y_3335_ = v___y_3358_;
v___y_3336_ = v___y_3370_;
v___y_3337_ = v___y_3359_;
v___y_3338_ = v___y_3360_;
v___y_3339_ = v___y_3361_;
v___y_3340_ = v___x_3388_;
v___y_3341_ = v___y_3363_;
v___y_3342_ = v___y_3364_;
v___y_3343_ = v___y_3365_;
v___y_3344_ = v___x_3376_;
v___y_3345_ = v_expectedType_x3f_3368_;
v___y_3346_ = v___y_3369_;
goto v___jp_3327_;
}
else
{
v___y_3328_ = v_fst_3380_;
v___y_3329_ = v___x_3386_;
v___y_3330_ = v___y_3355_;
v___y_3331_ = v___x_3387_;
v___y_3332_ = v_a_3373_;
v___y_3333_ = v___y_3357_;
v___y_3334_ = v_snd_3381_;
v___y_3335_ = v___y_3358_;
v___y_3336_ = v___y_3370_;
v___y_3337_ = v___y_3359_;
v___y_3338_ = v___y_3360_;
v___y_3339_ = v___y_3361_;
v___y_3340_ = v___x_3388_;
v___y_3341_ = v___y_3363_;
v___y_3342_ = v___y_3364_;
v___y_3343_ = v___y_3365_;
v___y_3344_ = v___x_3376_;
v___y_3345_ = v_expectedType_x3f_3368_;
v___y_3346_ = v___y_3369_;
goto v___jp_3327_;
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec(v_a_3383_);
lean_dec(v_snd_3381_);
lean_dec(v_fst_3380_);
lean_dec(v_a_3373_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v_expectedType_x3f_3368_);
lean_dec(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec(v___y_3355_);
v_a_3390_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3384_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3384_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec(v_snd_3381_);
lean_dec(v_fst_3380_);
lean_dec(v_a_3373_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v_expectedType_x3f_3368_);
lean_dec(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec(v___y_3355_);
v_a_3398_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3382_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3382_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec(v_a_3373_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v_expectedType_x3f_3368_);
lean_dec(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec(v___y_3355_);
v_a_3406_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3377_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3377_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v_expectedType_x3f_3368_);
lean_dec(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec(v___y_3355_);
v_a_3414_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3372_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3372_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
v___jp_3422_:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; uint8_t v___x_3440_; 
v___x_3437_ = lean_unsigned_to_nat(8u);
v___x_3438_ = l_Lean_Syntax_getArg(v_x_3022_, v___x_3437_);
v___x_3439_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__15));
lean_inc(v___x_3438_);
v___x_3440_ = l_Lean_Syntax_isOfKind(v___x_3438_, v___x_3439_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; 
lean_dec(v___x_3438_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v_prio_x3f_3434_);
lean_dec(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec(v_x_3022_);
v___x_3441_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3441_;
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v___x_3442_ = lean_unsigned_to_nat(7u);
v___x_3443_ = l_Lean_Syntax_getArg(v_x_3022_, v___x_3442_);
lean_dec(v_x_3022_);
v___x_3444_ = l_Lean_Syntax_getArg(v___x_3438_, v___y_3432_);
v___x_3445_ = l_Lean_Syntax_getArg(v___x_3438_, v___y_3423_);
v___x_3446_ = l_Lean_Syntax_isNone(v___x_3445_);
if (v___x_3446_ == 0)
{
uint8_t v___x_3447_; 
lean_inc(v___x_3445_);
v___x_3447_ = l_Lean_Syntax_matchesNull(v___x_3445_, v___y_3423_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; 
lean_dec(v___x_3445_);
lean_dec(v___x_3444_);
lean_dec(v___x_3443_);
lean_dec(v___x_3438_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v_prio_x3f_3434_);
lean_dec(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec(v___y_3424_);
v___x_3448_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3448_;
}
else
{
lean_object* v_expectedType_x3f_3449_; lean_object* v___x_3450_; 
v_expectedType_x3f_3449_ = l_Lean_Syntax_getArg(v___x_3445_, v___y_3432_);
lean_dec(v___x_3445_);
v___x_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3450_, 0, v_expectedType_x3f_3449_);
v___y_3355_ = v___x_3444_;
v___y_3356_ = v_prio_x3f_3434_;
v___y_3357_ = v___y_3427_;
v___y_3358_ = v___y_3428_;
v___y_3359_ = v___y_3425_;
v___y_3360_ = v___y_3424_;
v___y_3361_ = v___y_3426_;
v___y_3362_ = v___x_3443_;
v___y_3363_ = v___y_3430_;
v___y_3364_ = v___y_3429_;
v___y_3365_ = v___y_3431_;
v___y_3366_ = v___x_3438_;
v___y_3367_ = v___y_3433_;
v_expectedType_x3f_3368_ = v___x_3450_;
v___y_3369_ = v___y_3435_;
v___y_3370_ = v___y_3436_;
goto v___jp_3354_;
}
}
else
{
lean_object* v___x_3451_; 
lean_dec(v___x_3445_);
v___x_3451_ = lean_box(0);
v___y_3355_ = v___x_3444_;
v___y_3356_ = v_prio_x3f_3434_;
v___y_3357_ = v___y_3427_;
v___y_3358_ = v___y_3428_;
v___y_3359_ = v___y_3425_;
v___y_3360_ = v___y_3424_;
v___y_3361_ = v___y_3426_;
v___y_3362_ = v___x_3443_;
v___y_3363_ = v___y_3430_;
v___y_3364_ = v___y_3429_;
v___y_3365_ = v___y_3431_;
v___y_3366_ = v___x_3438_;
v___y_3367_ = v___y_3433_;
v_expectedType_x3f_3368_ = v___x_3451_;
v___y_3369_ = v___y_3435_;
v___y_3370_ = v___y_3436_;
goto v___jp_3354_;
}
}
}
v___jp_3452_:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; 
v___x_3467_ = lean_unsigned_to_nat(6u);
v___x_3468_ = l_Lean_Syntax_getArg(v_x_3022_, v___x_3467_);
v___x_3469_ = l_Lean_Syntax_isNone(v___x_3468_);
if (v___x_3469_ == 0)
{
uint8_t v___x_3470_; 
lean_inc(v___x_3468_);
v___x_3470_ = l_Lean_Syntax_matchesNull(v___x_3468_, v___y_3461_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3471_; 
lean_dec(v___x_3468_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v_name_x3f_3464_);
lean_dec(v___y_3462_);
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec(v_x_3022_);
v___x_3471_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3471_;
}
else
{
lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v___x_3472_ = l_Lean_Syntax_getArg(v___x_3468_, v___x_3071_);
lean_dec(v___x_3468_);
v___x_3473_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
lean_inc(v___x_3472_);
v___x_3474_ = l_Lean_Syntax_isOfKind(v___x_3472_, v___x_3473_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; 
lean_dec(v___x_3472_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v_name_x3f_3464_);
lean_dec(v___y_3462_);
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec(v_x_3022_);
v___x_3475_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3475_;
}
else
{
lean_object* v_prio_x3f_3476_; lean_object* v___x_3477_; 
v_prio_x3f_3476_ = l_Lean_Syntax_getArg(v___x_3472_, v___y_3456_);
lean_dec(v___x_3472_);
v___x_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3477_, 0, v_prio_x3f_3476_);
v___y_3423_ = v___y_3453_;
v___y_3424_ = v___y_3455_;
v___y_3425_ = v___y_3454_;
v___y_3426_ = v_name_x3f_3464_;
v___y_3427_ = v___y_3457_;
v___y_3428_ = v___y_3458_;
v___y_3429_ = v___y_3460_;
v___y_3430_ = v___y_3459_;
v___y_3431_ = v___y_3462_;
v___y_3432_ = v___y_3461_;
v___y_3433_ = v___y_3463_;
v_prio_x3f_3434_ = v___x_3477_;
v___y_3435_ = v___y_3465_;
v___y_3436_ = v___y_3466_;
goto v___jp_3422_;
}
}
}
else
{
lean_object* v___x_3478_; 
lean_dec(v___x_3468_);
v___x_3478_ = lean_box(0);
v___y_3423_ = v___y_3453_;
v___y_3424_ = v___y_3455_;
v___y_3425_ = v___y_3454_;
v___y_3426_ = v_name_x3f_3464_;
v___y_3427_ = v___y_3457_;
v___y_3428_ = v___y_3458_;
v___y_3429_ = v___y_3460_;
v___y_3430_ = v___y_3459_;
v___y_3431_ = v___y_3462_;
v___y_3432_ = v___y_3461_;
v___y_3433_ = v___y_3463_;
v_prio_x3f_3434_ = v___x_3478_;
v___y_3435_ = v___y_3465_;
v___y_3436_ = v___y_3466_;
goto v___jp_3422_;
}
}
v___jp_3479_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3493_ = lean_unsigned_to_nat(5u);
v___x_3494_ = l_Lean_Syntax_getArg(v_x_3022_, v___x_3493_);
v___x_3495_ = l_Lean_Syntax_isNone(v___x_3494_);
if (v___x_3495_ == 0)
{
uint8_t v___x_3496_; 
lean_inc(v___x_3494_);
v___x_3496_ = l_Lean_Syntax_matchesNull(v___x_3494_, v___y_3488_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
lean_dec(v___x_3494_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v_prec_x3f_3490_);
lean_dec(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec(v_x_3022_);
v___x_3497_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3497_;
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v___x_3498_ = l_Lean_Syntax_getArg(v___x_3494_, v___x_3071_);
lean_dec(v___x_3494_);
v___x_3499_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
lean_inc(v___x_3498_);
v___x_3500_ = l_Lean_Syntax_isOfKind(v___x_3498_, v___x_3499_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
lean_dec(v___x_3498_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v_prec_x3f_3490_);
lean_dec(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec(v_x_3022_);
v___x_3501_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3501_;
}
else
{
lean_object* v_name_x3f_3502_; lean_object* v___x_3503_; 
v_name_x3f_3502_ = l_Lean_Syntax_getArg(v___x_3498_, v___y_3484_);
lean_dec(v___x_3498_);
v___x_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3503_, 0, v_name_x3f_3502_);
v___y_3453_ = v___y_3480_;
v___y_3454_ = v___y_3482_;
v___y_3455_ = v___y_3481_;
v___y_3456_ = v___y_3484_;
v___y_3457_ = v___y_3483_;
v___y_3458_ = v___y_3485_;
v___y_3459_ = v___y_3487_;
v___y_3460_ = v___y_3486_;
v___y_3461_ = v___y_3488_;
v___y_3462_ = v_prec_x3f_3490_;
v___y_3463_ = v___y_3489_;
v_name_x3f_3464_ = v___x_3503_;
v___y_3465_ = v___y_3491_;
v___y_3466_ = v___y_3492_;
goto v___jp_3452_;
}
}
}
else
{
lean_object* v___x_3504_; 
lean_dec(v___x_3494_);
v___x_3504_ = lean_box(0);
v___y_3453_ = v___y_3480_;
v___y_3454_ = v___y_3482_;
v___y_3455_ = v___y_3481_;
v___y_3456_ = v___y_3484_;
v___y_3457_ = v___y_3483_;
v___y_3458_ = v___y_3485_;
v___y_3459_ = v___y_3487_;
v___y_3460_ = v___y_3486_;
v___y_3461_ = v___y_3488_;
v___y_3462_ = v_prec_x3f_3490_;
v___y_3463_ = v___y_3489_;
v_name_x3f_3464_ = v___x_3504_;
v___y_3465_ = v___y_3491_;
v___y_3466_ = v___y_3492_;
goto v___jp_3452_;
}
}
v___jp_3505_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; 
v___x_3511_ = lean_unsigned_to_nat(2u);
v___x_3512_ = l_Lean_Syntax_getArg(v_x_3022_, v___x_3511_);
v___x_3513_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_3514_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v___x_3512_);
v___x_3515_ = l_Lean_Syntax_isOfKind(v___x_3512_, v___x_3514_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; 
lean_dec(v___x_3512_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v_attrs_x3f_3508_);
lean_dec(v___y_3506_);
lean_dec(v_x_3022_);
v___x_3516_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3516_;
}
else
{
lean_object* v___x_3517_; lean_object* v_tk_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; uint8_t v___x_3521_; 
v___x_3517_ = lean_unsigned_to_nat(3u);
v_tk_3518_ = l_Lean_Syntax_getArg(v_x_3022_, v___x_3517_);
v___x_3519_ = lean_unsigned_to_nat(4u);
v___x_3520_ = l_Lean_Syntax_getArg(v_x_3022_, v___x_3519_);
v___x_3521_ = l_Lean_Syntax_isNone(v___x_3520_);
if (v___x_3521_ == 0)
{
uint8_t v___x_3522_; 
lean_inc(v___x_3520_);
v___x_3522_ = l_Lean_Syntax_matchesNull(v___x_3520_, v___y_3507_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; 
lean_dec(v___x_3520_);
lean_dec(v_tk_3518_);
lean_dec(v___x_3512_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v_attrs_x3f_3508_);
lean_dec(v___y_3506_);
lean_dec(v_x_3022_);
v___x_3523_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3523_;
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; uint8_t v___x_3526_; 
v___x_3524_ = l_Lean_Syntax_getArg(v___x_3520_, v___x_3071_);
lean_dec(v___x_3520_);
v___x_3525_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
lean_inc(v___x_3524_);
v___x_3526_ = l_Lean_Syntax_isOfKind(v___x_3524_, v___x_3525_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3527_; 
lean_dec(v___x_3524_);
lean_dec(v_tk_3518_);
lean_dec(v___x_3512_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v_attrs_x3f_3508_);
lean_dec(v___y_3506_);
lean_dec(v_x_3022_);
v___x_3527_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3527_;
}
else
{
lean_object* v_prec_x3f_3528_; lean_object* v___x_3529_; 
v_prec_x3f_3528_ = l_Lean_Syntax_getArg(v___x_3524_, v___y_3507_);
lean_dec(v___x_3524_);
v___x_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3529_, 0, v_prec_x3f_3528_);
v___y_3480_ = v___x_3511_;
v___y_3481_ = v___x_3512_;
v___y_3482_ = v_attrs_x3f_3508_;
v___y_3483_ = v___y_3506_;
v___y_3484_ = v___x_3517_;
v___y_3485_ = v___x_3513_;
v___y_3486_ = v_tk_3518_;
v___y_3487_ = v___x_3514_;
v___y_3488_ = v___y_3507_;
v___y_3489_ = v___x_3519_;
v_prec_x3f_3490_ = v___x_3529_;
v___y_3491_ = v___y_3509_;
v___y_3492_ = v___y_3510_;
goto v___jp_3479_;
}
}
}
else
{
lean_object* v___x_3530_; 
lean_dec(v___x_3520_);
v___x_3530_ = lean_box(0);
v___y_3480_ = v___x_3511_;
v___y_3481_ = v___x_3512_;
v___y_3482_ = v_attrs_x3f_3508_;
v___y_3483_ = v___y_3506_;
v___y_3484_ = v___x_3517_;
v___y_3485_ = v___x_3513_;
v___y_3486_ = v_tk_3518_;
v___y_3487_ = v___x_3514_;
v___y_3488_ = v___y_3507_;
v___y_3489_ = v___x_3519_;
v_prec_x3f_3490_ = v___x_3530_;
v___y_3491_ = v___y_3509_;
v___y_3492_ = v___y_3510_;
goto v___jp_3479_;
}
}
}
v___jp_3531_:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; 
v___x_3535_ = lean_unsigned_to_nat(1u);
v___x_3536_ = l_Lean_Syntax_getArg(v_x_3022_, v___x_3535_);
v___x_3537_ = l_Lean_Syntax_isNone(v___x_3536_);
if (v___x_3537_ == 0)
{
uint8_t v___x_3538_; 
lean_inc(v___x_3536_);
v___x_3538_ = l_Lean_Syntax_matchesNull(v___x_3536_, v___x_3535_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; 
lean_dec(v___x_3536_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v_doc_x3f_3532_);
lean_dec(v_x_3022_);
v___x_3539_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3539_;
}
else
{
lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v___x_3540_ = l_Lean_Syntax_getArg(v___x_3536_, v___x_3071_);
lean_dec(v___x_3536_);
v___x_3541_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(v___x_3540_);
v___x_3542_ = l_Lean_Syntax_isOfKind(v___x_3540_, v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; 
lean_dec(v___x_3540_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v_doc_x3f_3532_);
lean_dec(v_x_3022_);
v___x_3543_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3543_;
}
else
{
lean_object* v___x_3544_; lean_object* v_attrs_x3f_3545_; lean_object* v___x_3546_; 
v___x_3544_ = l_Lean_Syntax_getArg(v___x_3540_, v___x_3535_);
lean_dec(v___x_3540_);
v_attrs_x3f_3545_ = l_Lean_Syntax_getArgs(v___x_3544_);
lean_dec(v___x_3544_);
v___x_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3546_, 0, v_attrs_x3f_3545_);
v___y_3506_ = v_doc_x3f_3532_;
v___y_3507_ = v___x_3535_;
v_attrs_x3f_3508_ = v___x_3546_;
v___y_3509_ = v___y_3533_;
v___y_3510_ = v___y_3534_;
goto v___jp_3505_;
}
}
}
else
{
lean_object* v___x_3547_; 
lean_dec(v___x_3536_);
v___x_3547_ = lean_box(0);
v___y_3506_ = v_doc_x3f_3532_;
v___y_3507_ = v___x_3535_;
v_attrs_x3f_3508_ = v___x_3547_;
v___y_3509_ = v___y_3533_;
v___y_3510_ = v___y_3534_;
goto v___jp_3505_;
}
}
}
v___jp_3028_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3045_ = l_Array_append___redArg(v___y_3040_, v___y_3044_);
lean_dec_ref(v___y_3044_);
lean_inc(v___y_3037_);
lean_inc(v___y_3035_);
v___x_3046_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3046_, 0, v___y_3035_);
lean_ctor_set(v___x_3046_, 1, v___y_3037_);
lean_ctor_set(v___x_3046_, 2, v___x_3045_);
v___x_3047_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(v___y_3033_);
v___x_3048_ = l_Lean_Name_mkStr4(v___x_3026_, v___x_3027_, v___y_3033_, v___x_3047_);
v___x_3049_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(v___y_3033_);
v___x_3050_ = l_Lean_Name_mkStr4(v___x_3026_, v___x_3027_, v___y_3033_, v___x_3049_);
v___x_3051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(v___y_3035_);
v___x_3052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___y_3035_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__0));
v___x_3054_ = l_Lean_Name_mkStr4(v___x_3026_, v___x_3027_, v___y_3033_, v___x_3053_);
v___x_3055_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__1));
lean_inc(v___y_3035_);
v___x_3056_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___y_3035_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
lean_inc(v___y_3035_);
v___x_3057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___y_3035_);
lean_ctor_set(v___x_3057_, 1, v___y_3034_);
lean_inc(v___y_3035_);
v___x_3058_ = l_Lean_Syntax_node3(v___y_3035_, v___x_3054_, v___x_3056_, v___y_3041_, v___x_3057_);
lean_inc(v___y_3037_);
lean_inc(v___y_3035_);
v___x_3059_ = l_Lean_Syntax_node1(v___y_3035_, v___y_3037_, v___x_3058_);
lean_inc(v___y_3037_);
lean_inc(v___y_3035_);
v___x_3060_ = l_Lean_Syntax_node1(v___y_3035_, v___y_3037_, v___x_3059_);
v___x_3061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(v___y_3035_);
v___x_3062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___y_3035_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
lean_inc(v___y_3035_);
v___x_3063_ = l_Lean_Syntax_node4(v___y_3035_, v___x_3050_, v___x_3052_, v___x_3060_, v___x_3062_, v___y_3029_);
lean_inc(v___y_3035_);
v___x_3064_ = l_Lean_Syntax_node1(v___y_3035_, v___y_3037_, v___x_3063_);
lean_inc(v___y_3035_);
v___x_3065_ = l_Lean_Syntax_node1(v___y_3035_, v___x_3048_, v___x_3064_);
lean_inc(v___y_3042_);
v___x_3066_ = l_Lean_Syntax_node8(v___y_3035_, v___y_3031_, v___y_3039_, v___y_3042_, v___y_3036_, v___y_3030_, v___y_3042_, v___y_3032_, v___x_3046_, v___x_3065_);
v___x_3067_ = l_Lean_Elab_Command_elabCommand(v___x_3066_, v___y_3043_, v___y_3038_);
return v___x_3067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object* v_x_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Lean_Elab_Command_elabElab(v_x_3559_, v_a_3560_, v_a_3561_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object* v_cls_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v___x_3568_; 
v___x_3568_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(v_cls_3564_, v___y_3566_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object* v_cls_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_3569_, v___y_3570_, v___y_3571_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object* v_00_u03b1_3574_, lean_object* v_x_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(v_x_3575_, v___y_3577_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3579_, lean_object* v_x_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_00_u03b1_3579_, v_x_3580_, v___y_3581_, v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v_x_3580_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6(lean_object* v_00_u03b1_3584_, lean_object* v_ref_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(v_ref_3585_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___boxed(lean_object* v_00_u03b1_3590_, lean_object* v_ref_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6(v_00_u03b1_3590_, v_ref_3591_, v___y_3592_, v___y_3593_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object* v_00_u03b1_3596_, lean_object* v_x_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_3597_, v___y_3598_, v___y_3599_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object* v_00_u03b1_3602_, lean_object* v_x_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(v_00_u03b1_3602_, v_x_3603_, v___y_3604_, v___y_3605_);
lean_dec(v___y_3605_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object* v_as_3608_, lean_object* v_as_x27_3609_, lean_object* v_b_3610_, lean_object* v_a_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(v_as_x27_3609_, v_b_3610_, v___y_3612_, v___y_3613_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object* v_as_3616_, lean_object* v_as_x27_3617_, lean_object* v_b_3618_, lean_object* v_a_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v_as_3616_, v_as_x27_3617_, v_b_3618_, v_a_3619_, v___y_3620_, v___y_3621_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v_as_3616_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6(lean_object* v_00_u03b2_3624_, lean_object* v_m_3625_, lean_object* v_a_3626_){
_start:
{
lean_object* v___x_3627_; 
v___x_3627_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(v_m_3625_, v_a_3626_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3628_, lean_object* v_m_3629_, lean_object* v_a_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6(v_00_u03b2_3628_, v_m_3629_, v_a_3630_);
lean_dec(v_a_3630_);
lean_dec_ref(v_m_3629_);
return v_res_3631_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8(lean_object* v_00_u03b2_3632_, lean_object* v_x_3633_, lean_object* v_x_3634_){
_start:
{
uint8_t v___x_3635_; 
v___x_3635_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(v_x_3633_, v_x_3634_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___boxed(lean_object* v_00_u03b2_3636_, lean_object* v_x_3637_, lean_object* v_x_3638_){
_start:
{
uint8_t v_res_3639_; lean_object* v_r_3640_; 
v_res_3639_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8(v_00_u03b2_3636_, v_x_3637_, v_x_3638_);
lean_dec_ref(v_x_3638_);
v_r_3640_ = lean_box(v_res_3639_);
return v_r_3640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11(lean_object* v_00_u03b2_3641_, lean_object* v_a_3642_, lean_object* v_x_3643_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(v_a_3642_, v_x_3643_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___boxed(lean_object* v_00_u03b2_3645_, lean_object* v_a_3646_, lean_object* v_x_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11(v_00_u03b2_3645_, v_a_3646_, v_x_3647_);
lean_dec(v_x_3647_);
lean_dec(v_a_3646_);
return v_res_3648_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11(lean_object* v_00_u03b2_3649_, lean_object* v_x_3650_, size_t v_x_3651_, lean_object* v_x_3652_){
_start:
{
uint8_t v___x_3653_; 
v___x_3653_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(v_x_3650_, v_x_3651_, v_x_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___boxed(lean_object* v_00_u03b2_3654_, lean_object* v_x_3655_, lean_object* v_x_3656_, lean_object* v_x_3657_){
_start:
{
size_t v_x_21689__boxed_3658_; uint8_t v_res_3659_; lean_object* v_r_3660_; 
v_x_21689__boxed_3658_ = lean_unbox_usize(v_x_3656_);
lean_dec(v_x_3656_);
v_res_3659_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11(v_00_u03b2_3654_, v_x_3655_, v_x_21689__boxed_3658_, v_x_3657_);
lean_dec_ref(v_x_3657_);
v_r_3660_ = lean_box(v_res_3659_);
return v_r_3660_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14(lean_object* v_00_u03b2_3661_, lean_object* v_keys_3662_, lean_object* v_vals_3663_, lean_object* v_heq_3664_, lean_object* v_i_3665_, lean_object* v_k_3666_){
_start:
{
uint8_t v___x_3667_; 
v___x_3667_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(v_keys_3662_, v_i_3665_, v_k_3666_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___boxed(lean_object* v_00_u03b2_3668_, lean_object* v_keys_3669_, lean_object* v_vals_3670_, lean_object* v_heq_3671_, lean_object* v_i_3672_, lean_object* v_k_3673_){
_start:
{
uint8_t v_res_3674_; lean_object* v_r_3675_; 
v_res_3674_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14(v_00_u03b2_3668_, v_keys_3669_, v_vals_3670_, v_heq_3671_, v_i_3672_, v_k_3673_);
lean_dec_ref(v_k_3673_);
lean_dec_ref(v_vals_3670_);
lean_dec_ref(v_keys_3669_);
v_r_3675_ = lean_box(v_res_3674_);
return v_r_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1(){
_start:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3683_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3684_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
v___x_3685_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3686_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElab___boxed), 4, 0);
v___x_3687_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3683_, v___x_3684_, v___x_3685_, v___x_3686_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object* v_a_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3(){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3716_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3717_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6));
v___x_3718_ = l_Lean_addBuiltinDeclarationRanges(v___x_3716_, v___x_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object* v_a_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
return v_res_3720_;
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
res = l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
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
