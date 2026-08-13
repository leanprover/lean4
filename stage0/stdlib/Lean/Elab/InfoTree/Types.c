// Lean compiler output
// Module: Lean.Elab.InfoTree.Types
// Imports: public import Lean.Data.DeclarationRange public import Lean.Data.OpenDecl public import Lean.Data.PPContext public import Lean.MetavarContext public import Lean.Environment public import Lean.Widget.Types
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_Lean_instInhabitedLocalContext_default;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_commandCtx_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_commandCtx_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_parentDeclCtx_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_parentDeclCtx_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_autoImplicitCtx_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_autoImplicitCtx_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instInhabitedElabInfo_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedElabInfo_default = (const lean_object*)&l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedElabInfo = (const lean_object*)&l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value;
static const lean_string_object l_Lean_Elab_instInhabitedTermInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Elab_instInhabitedTermInfo_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedTermInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_instInhabitedTermInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instInhabitedTermInfo_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Elab_instInhabitedTermInfo_default___closed__1 = (const lean_object*)&l_Lean_Elab_instInhabitedTermInfo_default___closed__1_value;
static lean_once_cell_t l_Lean_Elab_instInhabitedTermInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedTermInfo_default___closed__2;
static lean_once_cell_t l_Lean_Elab_instInhabitedTermInfo_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedTermInfo_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedTermInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedTermInfo;
static lean_once_cell_t l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedPartialTermInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedPartialTermInfo;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedCommandInfo_default = (const lean_object*)&l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedCommandInfo = (const lean_object*)&l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_dot_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_dot_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_id_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_id_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_dotId_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_dotId_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_fieldId_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_fieldId_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_namespaceId_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_namespaceId_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_option_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_option_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_errorName_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_errorName_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_endSection_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_endSection_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_tactic_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_tactic_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_instInhabitedFieldInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedFieldInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedFieldInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedFieldInfo;
static lean_once_cell_t l_Lean_Elab_instInhabitedTacticInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedTacticInfo_default___closed__0;
static lean_once_cell_t l_Lean_Elab_instInhabitedTacticInfo_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedTacticInfo_default___closed__1;
static lean_once_cell_t l_Lean_Elab_instInhabitedTacticInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedTacticInfo_default___closed__2;
static lean_once_cell_t l_Lean_Elab_instInhabitedTacticInfo_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedTacticInfo_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedTacticInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedTacticInfo;
static lean_once_cell_t l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedMacroExpansionInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedMacroExpansionInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_instReprDocElabKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Elab.DocElabKind.role"};
static const lean_object* l_Lean_Elab_instReprDocElabKind_repr___closed__0 = (const lean_object*)&l_Lean_Elab_instReprDocElabKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_Elab_instReprDocElabKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instReprDocElabKind_repr___closed__0_value)}};
static const lean_object* l_Lean_Elab_instReprDocElabKind_repr___closed__1 = (const lean_object*)&l_Lean_Elab_instReprDocElabKind_repr___closed__1_value;
static const lean_string_object l_Lean_Elab_instReprDocElabKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Elab.DocElabKind.codeBlock"};
static const lean_object* l_Lean_Elab_instReprDocElabKind_repr___closed__2 = (const lean_object*)&l_Lean_Elab_instReprDocElabKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_Elab_instReprDocElabKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instReprDocElabKind_repr___closed__2_value)}};
static const lean_object* l_Lean_Elab_instReprDocElabKind_repr___closed__3 = (const lean_object*)&l_Lean_Elab_instReprDocElabKind_repr___closed__3_value;
static const lean_string_object l_Lean_Elab_instReprDocElabKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Elab.DocElabKind.directive"};
static const lean_object* l_Lean_Elab_instReprDocElabKind_repr___closed__4 = (const lean_object*)&l_Lean_Elab_instReprDocElabKind_repr___closed__4_value;
static const lean_ctor_object l_Lean_Elab_instReprDocElabKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instReprDocElabKind_repr___closed__4_value)}};
static const lean_object* l_Lean_Elab_instReprDocElabKind_repr___closed__5 = (const lean_object*)&l_Lean_Elab_instReprDocElabKind_repr___closed__5_value;
static const lean_string_object l_Lean_Elab_instReprDocElabKind_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Elab.DocElabKind.command"};
static const lean_object* l_Lean_Elab_instReprDocElabKind_repr___closed__6 = (const lean_object*)&l_Lean_Elab_instReprDocElabKind_repr___closed__6_value;
static const lean_ctor_object l_Lean_Elab_instReprDocElabKind_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instReprDocElabKind_repr___closed__6_value)}};
static const lean_object* l_Lean_Elab_instReprDocElabKind_repr___closed__7 = (const lean_object*)&l_Lean_Elab_instReprDocElabKind_repr___closed__7_value;
static lean_once_cell_t l_Lean_Elab_instReprDocElabKind_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instReprDocElabKind_repr___closed__8;
static lean_once_cell_t l_Lean_Elab_instReprDocElabKind_repr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instReprDocElabKind_repr___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_instReprDocElabKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instReprDocElabKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instReprDocElabKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instReprDocElabKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instReprDocElabKind___closed__0 = (const lean_object*)&l_Lean_Elab_instReprDocElabKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instReprDocElabKind = (const lean_object*)&l_Lean_Elab_instReprDocElabKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTacticInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTacticInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTermInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTermInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofPartialTermInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofPartialTermInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCommandInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCommandInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofMacroExpansionInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofMacroExpansionInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofOptionInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofOptionInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofErrorNameInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofErrorNameInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCompletionInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCompletionInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofUserWidgetInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofUserWidgetInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCustomInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCustomInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFVarAliasInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFVarAliasInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldRedeclInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldRedeclInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDelabTermInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDelabTermInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocElabInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocElabInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_instInhabitedInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_context_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_context_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_node_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hole_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hole_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_instInhabitedInfoTree_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedInfoTree_default___closed__0;
static lean_once_cell_t l_Lean_Elab_instInhabitedInfoTree_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedInfoTree_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedInfoTree_default;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedInfoTree;
static lean_once_cell_t l_Lean_Elab_instInhabitedInfoState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedInfoState_default___closed__0;
static lean_once_cell_t l_Lean_Elab_instInhabitedInfoState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedInfoState_default___closed__1;
static lean_once_cell_t l_Lean_Elab_instInhabitedInfoState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedInfoState_default___closed__2;
static lean_once_cell_t l_Lean_Elab_instInhabitedInfoState_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedInfoState_default___closed__3;
static lean_once_cell_t l_Lean_Elab_instInhabitedInfoState_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedInfoState_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedInfoState_default;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedInfoState;
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Elab_PartialContextInfo_ctorIdx(v_x_5_);
lean_dec_ref(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 1)
{
lean_object* v_parentDecl_9_; lean_object* v___x_10_; 
v_parentDecl_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_parentDecl_9_);
lean_dec_ref_known(v_t_7_, 1);
v___x_10_ = lean_apply_1(v_k_8_, v_parentDecl_9_);
return v___x_10_;
}
else
{
lean_object* v_info_11_; lean_object* v___x_12_; 
v_info_11_ = lean_ctor_get(v_t_7_, 0);
lean_inc_ref(v_info_11_);
lean_dec_ref(v_t_7_);
v___x_12_ = lean_apply_1(v_k_8_, v_info_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Elab_PartialContextInfo_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_commandCtx_elim___redArg(lean_object* v_t_25_, lean_object* v_commandCtx_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_25_, v_commandCtx_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_commandCtx_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_commandCtx_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_29_, v_commandCtx_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_parentDeclCtx_elim___redArg(lean_object* v_t_33_, lean_object* v_parentDeclCtx_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_33_, v_parentDeclCtx_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_parentDeclCtx_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_parentDeclCtx_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_37_, v_parentDeclCtx_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_autoImplicitCtx_elim___redArg(lean_object* v_t_41_, lean_object* v_autoImplicitCtx_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_41_, v_autoImplicitCtx_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_autoImplicitCtx_elim(lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_autoImplicitCtx_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_45_, v_autoImplicitCtx_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__2(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_box(0);
v___x_58_ = ((lean_object*)(l_Lean_Elab_instInhabitedTermInfo_default___closed__1));
v___x_59_ = l_Lean_Expr_const___override(v___x_58_, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__3(void){
_start:
{
uint8_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_60_ = 0;
v___x_61_ = lean_obj_once(&l_Lean_Elab_instInhabitedTermInfo_default___closed__2, &l_Lean_Elab_instInhabitedTermInfo_default___closed__2_once, _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__2);
v___x_62_ = lean_box(0);
v___x_63_ = l_Lean_instInhabitedLocalContext_default;
v___x_64_ = ((lean_object*)(l_Lean_Elab_instInhabitedElabInfo_default));
v___x_65_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
lean_ctor_set(v___x_65_, 2, v___x_62_);
lean_ctor_set(v___x_65_, 3, v___x_61_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*4, v___x_60_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*4 + 1, v___x_60_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo_default(void){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_obj_once(&l_Lean_Elab_instInhabitedTermInfo_default___closed__3, &l_Lean_Elab_instInhabitedTermInfo_default___closed__3_once, _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__3);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo(void){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Elab_instInhabitedTermInfo_default;
return v___x_67_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_box(0);
v___x_69_ = l_Lean_instInhabitedLocalContext_default;
v___x_70_ = ((lean_object*)(l_Lean_Elab_instInhabitedElabInfo_default));
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPartialTermInfo_default(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0, &l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPartialTermInfo(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Elab_instInhabitedPartialTermInfo_default;
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorIdx(lean_object* v_x_76_){
_start:
{
switch(lean_obj_tag(v_x_76_))
{
case 0:
{
lean_object* v___x_77_; 
v___x_77_ = lean_unsigned_to_nat(0u);
return v___x_77_;
}
case 1:
{
lean_object* v___x_78_; 
v___x_78_ = lean_unsigned_to_nat(1u);
return v___x_78_;
}
case 2:
{
lean_object* v___x_79_; 
v___x_79_ = lean_unsigned_to_nat(2u);
return v___x_79_;
}
case 3:
{
lean_object* v___x_80_; 
v___x_80_ = lean_unsigned_to_nat(3u);
return v___x_80_;
}
case 4:
{
lean_object* v___x_81_; 
v___x_81_ = lean_unsigned_to_nat(4u);
return v___x_81_;
}
case 5:
{
lean_object* v___x_82_; 
v___x_82_ = lean_unsigned_to_nat(5u);
return v___x_82_;
}
case 6:
{
lean_object* v___x_83_; 
v___x_83_ = lean_unsigned_to_nat(6u);
return v___x_83_;
}
case 7:
{
lean_object* v___x_84_; 
v___x_84_ = lean_unsigned_to_nat(7u);
return v___x_84_;
}
default: 
{
lean_object* v___x_85_; 
v___x_85_ = lean_unsigned_to_nat(8u);
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorIdx___boxed(lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Elab_CompletionInfo_ctorIdx(v_x_86_);
lean_dec_ref(v_x_86_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorElim___redArg(lean_object* v_t_88_, lean_object* v_k_89_){
_start:
{
switch(lean_obj_tag(v_t_88_))
{
case 0:
{
lean_object* v_termInfo_90_; lean_object* v_expectedType_x3f_91_; lean_object* v___x_92_; 
v_termInfo_90_ = lean_ctor_get(v_t_88_, 0);
lean_inc_ref(v_termInfo_90_);
v_expectedType_x3f_91_ = lean_ctor_get(v_t_88_, 1);
lean_inc(v_expectedType_x3f_91_);
lean_dec_ref_known(v_t_88_, 2);
v___x_92_ = lean_apply_2(v_k_89_, v_termInfo_90_, v_expectedType_x3f_91_);
return v___x_92_;
}
case 1:
{
lean_object* v_stx_93_; lean_object* v_id_94_; uint8_t v_danglingDot_95_; lean_object* v_lctx_96_; lean_object* v_expectedType_x3f_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_stx_93_ = lean_ctor_get(v_t_88_, 0);
lean_inc(v_stx_93_);
v_id_94_ = lean_ctor_get(v_t_88_, 1);
lean_inc(v_id_94_);
v_danglingDot_95_ = lean_ctor_get_uint8(v_t_88_, sizeof(void*)*4);
v_lctx_96_ = lean_ctor_get(v_t_88_, 2);
lean_inc_ref(v_lctx_96_);
v_expectedType_x3f_97_ = lean_ctor_get(v_t_88_, 3);
lean_inc(v_expectedType_x3f_97_);
lean_dec_ref_known(v_t_88_, 4);
v___x_98_ = lean_box(v_danglingDot_95_);
v___x_99_ = lean_apply_5(v_k_89_, v_stx_93_, v_id_94_, v___x_98_, v_lctx_96_, v_expectedType_x3f_97_);
return v___x_99_;
}
case 2:
{
lean_object* v_stx_100_; lean_object* v_id_101_; lean_object* v_lctx_102_; lean_object* v_expectedType_x3f_103_; lean_object* v___x_104_; 
v_stx_100_ = lean_ctor_get(v_t_88_, 0);
lean_inc(v_stx_100_);
v_id_101_ = lean_ctor_get(v_t_88_, 1);
lean_inc(v_id_101_);
v_lctx_102_ = lean_ctor_get(v_t_88_, 2);
lean_inc_ref(v_lctx_102_);
v_expectedType_x3f_103_ = lean_ctor_get(v_t_88_, 3);
lean_inc(v_expectedType_x3f_103_);
lean_dec_ref_known(v_t_88_, 4);
v___x_104_ = lean_apply_4(v_k_89_, v_stx_100_, v_id_101_, v_lctx_102_, v_expectedType_x3f_103_);
return v___x_104_;
}
case 3:
{
lean_object* v_stx_105_; lean_object* v_id_106_; lean_object* v_lctx_107_; lean_object* v_structName_108_; lean_object* v___x_109_; 
v_stx_105_ = lean_ctor_get(v_t_88_, 0);
lean_inc(v_stx_105_);
v_id_106_ = lean_ctor_get(v_t_88_, 1);
lean_inc(v_id_106_);
v_lctx_107_ = lean_ctor_get(v_t_88_, 2);
lean_inc_ref(v_lctx_107_);
v_structName_108_ = lean_ctor_get(v_t_88_, 3);
lean_inc(v_structName_108_);
lean_dec_ref_known(v_t_88_, 4);
v___x_109_ = lean_apply_4(v_k_89_, v_stx_105_, v_id_106_, v_lctx_107_, v_structName_108_);
return v___x_109_;
}
case 6:
{
lean_object* v_stx_110_; lean_object* v_partialId_111_; lean_object* v___x_112_; 
v_stx_110_ = lean_ctor_get(v_t_88_, 0);
lean_inc(v_stx_110_);
v_partialId_111_ = lean_ctor_get(v_t_88_, 1);
lean_inc(v_partialId_111_);
lean_dec_ref_known(v_t_88_, 2);
v___x_112_ = lean_apply_2(v_k_89_, v_stx_110_, v_partialId_111_);
return v___x_112_;
}
case 7:
{
lean_object* v_stx_113_; lean_object* v_id_x3f_114_; uint8_t v_danglingDot_115_; lean_object* v_scopeNames_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_stx_113_ = lean_ctor_get(v_t_88_, 0);
lean_inc(v_stx_113_);
v_id_x3f_114_ = lean_ctor_get(v_t_88_, 1);
lean_inc(v_id_x3f_114_);
v_danglingDot_115_ = lean_ctor_get_uint8(v_t_88_, sizeof(void*)*3);
v_scopeNames_116_ = lean_ctor_get(v_t_88_, 2);
lean_inc(v_scopeNames_116_);
lean_dec_ref_known(v_t_88_, 3);
v___x_117_ = lean_box(v_danglingDot_115_);
v___x_118_ = lean_apply_4(v_k_89_, v_stx_113_, v_id_x3f_114_, v___x_117_, v_scopeNames_116_);
return v___x_118_;
}
default: 
{
lean_object* v_stx_119_; lean_object* v___x_120_; 
v_stx_119_ = lean_ctor_get(v_t_88_, 0);
lean_inc(v_stx_119_);
lean_dec_ref(v_t_88_);
v___x_120_ = lean_apply_1(v_k_89_, v_stx_119_);
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorElim(lean_object* v_motive_121_, lean_object* v_ctorIdx_122_, lean_object* v_t_123_, lean_object* v_h_124_, lean_object* v_k_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_123_, v_k_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorElim___boxed(lean_object* v_motive_127_, lean_object* v_ctorIdx_128_, lean_object* v_t_129_, lean_object* v_h_130_, lean_object* v_k_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_Elab_CompletionInfo_ctorElim(v_motive_127_, v_ctorIdx_128_, v_t_129_, v_h_130_, v_k_131_);
lean_dec(v_ctorIdx_128_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_dot_elim___redArg(lean_object* v_t_133_, lean_object* v_dot_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_133_, v_dot_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_dot_elim(lean_object* v_motive_136_, lean_object* v_t_137_, lean_object* v_h_138_, lean_object* v_dot_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_137_, v_dot_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_id_elim___redArg(lean_object* v_t_141_, lean_object* v_id_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_141_, v_id_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_id_elim(lean_object* v_motive_144_, lean_object* v_t_145_, lean_object* v_h_146_, lean_object* v_id_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_145_, v_id_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_dotId_elim___redArg(lean_object* v_t_149_, lean_object* v_dotId_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_149_, v_dotId_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_dotId_elim(lean_object* v_motive_152_, lean_object* v_t_153_, lean_object* v_h_154_, lean_object* v_dotId_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_153_, v_dotId_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_fieldId_elim___redArg(lean_object* v_t_157_, lean_object* v_fieldId_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_157_, v_fieldId_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_fieldId_elim(lean_object* v_motive_160_, lean_object* v_t_161_, lean_object* v_h_162_, lean_object* v_fieldId_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_161_, v_fieldId_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_namespaceId_elim___redArg(lean_object* v_t_165_, lean_object* v_namespaceId_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_165_, v_namespaceId_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_namespaceId_elim(lean_object* v_motive_168_, lean_object* v_t_169_, lean_object* v_h_170_, lean_object* v_namespaceId_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_169_, v_namespaceId_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_option_elim___redArg(lean_object* v_t_173_, lean_object* v_option_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_173_, v_option_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_option_elim(lean_object* v_motive_176_, lean_object* v_t_177_, lean_object* v_h_178_, lean_object* v_option_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_177_, v_option_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_errorName_elim___redArg(lean_object* v_t_181_, lean_object* v_errorName_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_181_, v_errorName_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_errorName_elim(lean_object* v_motive_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_errorName_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_185_, v_errorName_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_endSection_elim___redArg(lean_object* v_t_189_, lean_object* v_endSection_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_189_, v_endSection_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_endSection_elim(lean_object* v_motive_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_endSection_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_193_, v_endSection_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_tactic_elim___redArg(lean_object* v_t_197_, lean_object* v_tactic_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_197_, v_tactic_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_tactic_elim(lean_object* v_motive_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_tactic_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_201_, v_tactic_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFieldInfo_default___closed__0(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_205_ = lean_box(0);
v___x_206_ = lean_obj_once(&l_Lean_Elab_instInhabitedTermInfo_default___closed__2, &l_Lean_Elab_instInhabitedTermInfo_default___closed__2_once, _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__2);
v___x_207_ = l_Lean_instInhabitedLocalContext_default;
v___x_208_ = lean_box(0);
v___x_209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
lean_ctor_set(v___x_209_, 2, v___x_207_);
lean_ctor_set(v___x_209_, 3, v___x_206_);
lean_ctor_set(v___x_209_, 4, v___x_205_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFieldInfo_default(void){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = lean_obj_once(&l_Lean_Elab_instInhabitedFieldInfo_default___closed__0, &l_Lean_Elab_instInhabitedFieldInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedFieldInfo_default___closed__0);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFieldInfo(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Elab_instInhabitedFieldInfo_default;
return v___x_211_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__0(void){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__1(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_obj_once(&l_Lean_Elab_instInhabitedTacticInfo_default___closed__0, &l_Lean_Elab_instInhabitedTacticInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__0);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__2(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_obj_once(&l_Lean_Elab_instInhabitedTacticInfo_default___closed__1, &l_Lean_Elab_instInhabitedTacticInfo_default___closed__1_once, _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__1);
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
lean_ctor_set(v___x_217_, 2, v___x_216_);
lean_ctor_set(v___x_217_, 3, v___x_216_);
lean_ctor_set(v___x_217_, 4, v___x_215_);
lean_ctor_set(v___x_217_, 5, v___x_215_);
lean_ctor_set(v___x_217_, 6, v___x_215_);
lean_ctor_set(v___x_217_, 7, v___x_215_);
lean_ctor_set(v___x_217_, 8, v___x_215_);
lean_ctor_set(v___x_217_, 9, v___x_215_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__3(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_218_ = lean_box(0);
v___x_219_ = lean_obj_once(&l_Lean_Elab_instInhabitedTacticInfo_default___closed__2, &l_Lean_Elab_instInhabitedTacticInfo_default___closed__2_once, _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__2);
v___x_220_ = ((lean_object*)(l_Lean_Elab_instInhabitedElabInfo_default));
v___x_221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_219_);
lean_ctor_set(v___x_221_, 2, v___x_218_);
lean_ctor_set(v___x_221_, 3, v___x_219_);
lean_ctor_set(v___x_221_, 4, v___x_218_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo_default(void){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_obj_once(&l_Lean_Elab_instInhabitedTacticInfo_default___closed__3, &l_Lean_Elab_instInhabitedTacticInfo_default___closed__3_once, _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__3);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Elab_instInhabitedTacticInfo_default;
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_box(0);
v___x_225_ = l_Lean_instInhabitedLocalContext_default;
v___x_226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
lean_ctor_set(v___x_226_, 2, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default(void){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = lean_obj_once(&l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0, &l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo(void){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Elab_instInhabitedMacroExpansionInfo_default;
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorIdx(uint8_t v_x_229_){
_start:
{
switch(v_x_229_)
{
case 0:
{
lean_object* v___x_230_; 
v___x_230_ = lean_unsigned_to_nat(0u);
return v___x_230_;
}
case 1:
{
lean_object* v___x_231_; 
v___x_231_ = lean_unsigned_to_nat(1u);
return v___x_231_;
}
case 2:
{
lean_object* v___x_232_; 
v___x_232_ = lean_unsigned_to_nat(2u);
return v___x_232_;
}
default: 
{
lean_object* v___x_233_; 
v___x_233_ = lean_unsigned_to_nat(3u);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorIdx___boxed(lean_object* v_x_234_){
_start:
{
uint8_t v_x_boxed_235_; lean_object* v_res_236_; 
v_x_boxed_235_ = lean_unbox(v_x_234_);
v_res_236_ = l_Lean_Elab_DocElabKind_ctorIdx(v_x_boxed_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___redArg(lean_object* v_k_237_){
_start:
{
lean_inc(v_k_237_);
return v_k_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___redArg___boxed(lean_object* v_k_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Elab_DocElabKind_ctorElim___redArg(v_k_238_);
lean_dec(v_k_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim(lean_object* v_motive_240_, lean_object* v_ctorIdx_241_, uint8_t v_t_242_, lean_object* v_h_243_, lean_object* v_k_244_){
_start:
{
lean_inc(v_k_244_);
return v_k_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___boxed(lean_object* v_motive_245_, lean_object* v_ctorIdx_246_, lean_object* v_t_247_, lean_object* v_h_248_, lean_object* v_k_249_){
_start:
{
uint8_t v_t_boxed_250_; lean_object* v_res_251_; 
v_t_boxed_250_ = lean_unbox(v_t_247_);
v_res_251_ = l_Lean_Elab_DocElabKind_ctorElim(v_motive_245_, v_ctorIdx_246_, v_t_boxed_250_, v_h_248_, v_k_249_);
lean_dec(v_k_249_);
lean_dec(v_ctorIdx_246_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___redArg(lean_object* v_role_252_){
_start:
{
lean_inc(v_role_252_);
return v_role_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___redArg___boxed(lean_object* v_role_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Elab_DocElabKind_role_elim___redArg(v_role_253_);
lean_dec(v_role_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim(lean_object* v_motive_255_, uint8_t v_t_256_, lean_object* v_h_257_, lean_object* v_role_258_){
_start:
{
lean_inc(v_role_258_);
return v_role_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___boxed(lean_object* v_motive_259_, lean_object* v_t_260_, lean_object* v_h_261_, lean_object* v_role_262_){
_start:
{
uint8_t v_t_boxed_263_; lean_object* v_res_264_; 
v_t_boxed_263_ = lean_unbox(v_t_260_);
v_res_264_ = l_Lean_Elab_DocElabKind_role_elim(v_motive_259_, v_t_boxed_263_, v_h_261_, v_role_262_);
lean_dec(v_role_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___redArg(lean_object* v_codeBlock_265_){
_start:
{
lean_inc(v_codeBlock_265_);
return v_codeBlock_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___redArg___boxed(lean_object* v_codeBlock_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Elab_DocElabKind_codeBlock_elim___redArg(v_codeBlock_266_);
lean_dec(v_codeBlock_266_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim(lean_object* v_motive_268_, uint8_t v_t_269_, lean_object* v_h_270_, lean_object* v_codeBlock_271_){
_start:
{
lean_inc(v_codeBlock_271_);
return v_codeBlock_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___boxed(lean_object* v_motive_272_, lean_object* v_t_273_, lean_object* v_h_274_, lean_object* v_codeBlock_275_){
_start:
{
uint8_t v_t_boxed_276_; lean_object* v_res_277_; 
v_t_boxed_276_ = lean_unbox(v_t_273_);
v_res_277_ = l_Lean_Elab_DocElabKind_codeBlock_elim(v_motive_272_, v_t_boxed_276_, v_h_274_, v_codeBlock_275_);
lean_dec(v_codeBlock_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___redArg(lean_object* v_directive_278_){
_start:
{
lean_inc(v_directive_278_);
return v_directive_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___redArg___boxed(lean_object* v_directive_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Elab_DocElabKind_directive_elim___redArg(v_directive_279_);
lean_dec(v_directive_279_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim(lean_object* v_motive_281_, uint8_t v_t_282_, lean_object* v_h_283_, lean_object* v_directive_284_){
_start:
{
lean_inc(v_directive_284_);
return v_directive_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___boxed(lean_object* v_motive_285_, lean_object* v_t_286_, lean_object* v_h_287_, lean_object* v_directive_288_){
_start:
{
uint8_t v_t_boxed_289_; lean_object* v_res_290_; 
v_t_boxed_289_ = lean_unbox(v_t_286_);
v_res_290_ = l_Lean_Elab_DocElabKind_directive_elim(v_motive_285_, v_t_boxed_289_, v_h_287_, v_directive_288_);
lean_dec(v_directive_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___redArg(lean_object* v_command_291_){
_start:
{
lean_inc(v_command_291_);
return v_command_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___redArg___boxed(lean_object* v_command_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Elab_DocElabKind_command_elim___redArg(v_command_292_);
lean_dec(v_command_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim(lean_object* v_motive_294_, uint8_t v_t_295_, lean_object* v_h_296_, lean_object* v_command_297_){
_start:
{
lean_inc(v_command_297_);
return v_command_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___boxed(lean_object* v_motive_298_, lean_object* v_t_299_, lean_object* v_h_300_, lean_object* v_command_301_){
_start:
{
uint8_t v_t_boxed_302_; lean_object* v_res_303_; 
v_t_boxed_302_ = lean_unbox(v_t_299_);
v_res_303_ = l_Lean_Elab_DocElabKind_command_elim(v_motive_298_, v_t_boxed_302_, v_h_300_, v_command_301_);
lean_dec(v_command_301_);
return v_res_303_;
}
}
static lean_object* _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_unsigned_to_nat(2u);
v___x_317_ = lean_nat_to_int(v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_to_int(v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprDocElabKind_repr(uint8_t v_x_320_, lean_object* v_prec_321_){
_start:
{
lean_object* v___y_323_; lean_object* v___y_330_; lean_object* v___y_337_; lean_object* v___y_344_; 
switch(v_x_320_)
{
case 0:
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(1024u);
v___x_351_ = lean_nat_dec_le(v___x_350_, v_prec_321_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_323_ = v___x_352_;
goto v___jp_322_;
}
else
{
lean_object* v___x_353_; 
v___x_353_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_323_ = v___x_353_;
goto v___jp_322_;
}
}
case 1:
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(1024u);
v___x_355_ = lean_nat_dec_le(v___x_354_, v_prec_321_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
v___x_356_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_330_ = v___x_356_;
goto v___jp_329_;
}
else
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_330_ = v___x_357_;
goto v___jp_329_;
}
}
case 2:
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(1024u);
v___x_359_ = lean_nat_dec_le(v___x_358_, v_prec_321_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
v___x_360_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_337_ = v___x_360_;
goto v___jp_336_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_337_ = v___x_361_;
goto v___jp_336_;
}
}
default: 
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = lean_unsigned_to_nat(1024u);
v___x_363_ = lean_nat_dec_le(v___x_362_, v_prec_321_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_344_ = v___x_364_;
goto v___jp_343_;
}
else
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_344_ = v___x_365_;
goto v___jp_343_;
}
}
}
v___jp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_324_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__1));
lean_inc(v___y_323_);
v___x_325_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_325_, 0, v___y_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = 0;
v___x_327_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*1, v___x_326_);
v___x_328_ = l_Repr_addAppParen(v___x_327_, v_prec_321_);
return v___x_328_;
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_331_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__3));
lean_inc(v___y_330_);
v___x_332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_332_, 0, v___y_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = 0;
v___x_334_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*1, v___x_333_);
v___x_335_ = l_Repr_addAppParen(v___x_334_, v_prec_321_);
return v___x_335_;
}
v___jp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_338_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__5));
lean_inc(v___y_337_);
v___x_339_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_339_, 0, v___y_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = 0;
v___x_341_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set_uint8(v___x_341_, sizeof(void*)*1, v___x_340_);
v___x_342_ = l_Repr_addAppParen(v___x_341_, v_prec_321_);
return v___x_342_;
}
v___jp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_345_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__7));
lean_inc(v___y_344_);
v___x_346_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_346_, 0, v___y_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = 0;
v___x_348_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*1, v___x_347_);
v___x_349_ = l_Repr_addAppParen(v___x_348_, v_prec_321_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprDocElabKind_repr___boxed(lean_object* v_x_366_, lean_object* v_prec_367_){
_start:
{
uint8_t v_x_233__boxed_368_; lean_object* v_res_369_; 
v_x_233__boxed_368_ = lean_unbox(v_x_366_);
v_res_369_ = l_Lean_Elab_instReprDocElabKind_repr(v_x_233__boxed_368_, v_prec_367_);
lean_dec(v_prec_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx(lean_object* v_x_372_){
_start:
{
switch(lean_obj_tag(v_x_372_))
{
case 0:
{
lean_object* v___x_373_; 
v___x_373_ = lean_unsigned_to_nat(0u);
return v___x_373_;
}
case 1:
{
lean_object* v___x_374_; 
v___x_374_ = lean_unsigned_to_nat(1u);
return v___x_374_;
}
case 2:
{
lean_object* v___x_375_; 
v___x_375_ = lean_unsigned_to_nat(2u);
return v___x_375_;
}
case 3:
{
lean_object* v___x_376_; 
v___x_376_ = lean_unsigned_to_nat(3u);
return v___x_376_;
}
case 4:
{
lean_object* v___x_377_; 
v___x_377_ = lean_unsigned_to_nat(4u);
return v___x_377_;
}
case 5:
{
lean_object* v___x_378_; 
v___x_378_ = lean_unsigned_to_nat(5u);
return v___x_378_;
}
case 6:
{
lean_object* v___x_379_; 
v___x_379_ = lean_unsigned_to_nat(6u);
return v___x_379_;
}
case 7:
{
lean_object* v___x_380_; 
v___x_380_ = lean_unsigned_to_nat(7u);
return v___x_380_;
}
case 8:
{
lean_object* v___x_381_; 
v___x_381_ = lean_unsigned_to_nat(8u);
return v___x_381_;
}
case 9:
{
lean_object* v___x_382_; 
v___x_382_ = lean_unsigned_to_nat(9u);
return v___x_382_;
}
case 10:
{
lean_object* v___x_383_; 
v___x_383_ = lean_unsigned_to_nat(10u);
return v___x_383_;
}
case 11:
{
lean_object* v___x_384_; 
v___x_384_ = lean_unsigned_to_nat(11u);
return v___x_384_;
}
case 12:
{
lean_object* v___x_385_; 
v___x_385_ = lean_unsigned_to_nat(12u);
return v___x_385_;
}
case 13:
{
lean_object* v___x_386_; 
v___x_386_ = lean_unsigned_to_nat(13u);
return v___x_386_;
}
case 14:
{
lean_object* v___x_387_; 
v___x_387_ = lean_unsigned_to_nat(14u);
return v___x_387_;
}
case 15:
{
lean_object* v___x_388_; 
v___x_388_ = lean_unsigned_to_nat(15u);
return v___x_388_;
}
default: 
{
lean_object* v___x_389_; 
v___x_389_ = lean_unsigned_to_nat(16u);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx___boxed(lean_object* v_x_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Elab_Info_ctorIdx(v_x_390_);
lean_dec_ref(v_x_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim___redArg(lean_object* v_t_392_, lean_object* v_k_393_){
_start:
{
if (lean_obj_tag(v_t_392_) == 12)
{
lean_object* v_i_394_; lean_object* v___x_395_; 
v_i_394_ = lean_ctor_get(v_t_392_, 0);
lean_inc(v_i_394_);
lean_dec_ref_known(v_t_392_, 1);
v___x_395_ = lean_apply_1(v_k_393_, v_i_394_);
return v___x_395_;
}
else
{
lean_object* v_i_396_; lean_object* v___x_397_; 
v_i_396_ = lean_ctor_get(v_t_392_, 0);
lean_inc_ref(v_i_396_);
lean_dec_ref(v_t_392_);
v___x_397_ = lean_apply_1(v_k_393_, v_i_396_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim(lean_object* v_motive_398_, lean_object* v_ctorIdx_399_, lean_object* v_t_400_, lean_object* v_h_401_, lean_object* v_k_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_400_, v_k_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim___boxed(lean_object* v_motive_404_, lean_object* v_ctorIdx_405_, lean_object* v_t_406_, lean_object* v_h_407_, lean_object* v_k_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Elab_Info_ctorElim(v_motive_404_, v_ctorIdx_405_, v_t_406_, v_h_407_, v_k_408_);
lean_dec(v_ctorIdx_405_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTacticInfo_elim___redArg(lean_object* v_t_410_, lean_object* v_ofTacticInfo_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_410_, v_ofTacticInfo_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTacticInfo_elim(lean_object* v_motive_413_, lean_object* v_t_414_, lean_object* v_h_415_, lean_object* v_ofTacticInfo_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_414_, v_ofTacticInfo_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTermInfo_elim___redArg(lean_object* v_t_418_, lean_object* v_ofTermInfo_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_418_, v_ofTermInfo_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTermInfo_elim(lean_object* v_motive_421_, lean_object* v_t_422_, lean_object* v_h_423_, lean_object* v_ofTermInfo_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_422_, v_ofTermInfo_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofPartialTermInfo_elim___redArg(lean_object* v_t_426_, lean_object* v_ofPartialTermInfo_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_426_, v_ofPartialTermInfo_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofPartialTermInfo_elim(lean_object* v_motive_429_, lean_object* v_t_430_, lean_object* v_h_431_, lean_object* v_ofPartialTermInfo_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_430_, v_ofPartialTermInfo_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCommandInfo_elim___redArg(lean_object* v_t_434_, lean_object* v_ofCommandInfo_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_434_, v_ofCommandInfo_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCommandInfo_elim(lean_object* v_motive_437_, lean_object* v_t_438_, lean_object* v_h_439_, lean_object* v_ofCommandInfo_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_438_, v_ofCommandInfo_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofMacroExpansionInfo_elim___redArg(lean_object* v_t_442_, lean_object* v_ofMacroExpansionInfo_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_442_, v_ofMacroExpansionInfo_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofMacroExpansionInfo_elim(lean_object* v_motive_445_, lean_object* v_t_446_, lean_object* v_h_447_, lean_object* v_ofMacroExpansionInfo_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_446_, v_ofMacroExpansionInfo_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofOptionInfo_elim___redArg(lean_object* v_t_450_, lean_object* v_ofOptionInfo_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_450_, v_ofOptionInfo_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofOptionInfo_elim(lean_object* v_motive_453_, lean_object* v_t_454_, lean_object* v_h_455_, lean_object* v_ofOptionInfo_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_454_, v_ofOptionInfo_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofErrorNameInfo_elim___redArg(lean_object* v_t_458_, lean_object* v_ofErrorNameInfo_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_458_, v_ofErrorNameInfo_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofErrorNameInfo_elim(lean_object* v_motive_461_, lean_object* v_t_462_, lean_object* v_h_463_, lean_object* v_ofErrorNameInfo_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_462_, v_ofErrorNameInfo_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldInfo_elim___redArg(lean_object* v_t_466_, lean_object* v_ofFieldInfo_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_466_, v_ofFieldInfo_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldInfo_elim(lean_object* v_motive_469_, lean_object* v_t_470_, lean_object* v_h_471_, lean_object* v_ofFieldInfo_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_470_, v_ofFieldInfo_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCompletionInfo_elim___redArg(lean_object* v_t_474_, lean_object* v_ofCompletionInfo_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_474_, v_ofCompletionInfo_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCompletionInfo_elim(lean_object* v_motive_477_, lean_object* v_t_478_, lean_object* v_h_479_, lean_object* v_ofCompletionInfo_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_478_, v_ofCompletionInfo_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofUserWidgetInfo_elim___redArg(lean_object* v_t_482_, lean_object* v_ofUserWidgetInfo_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_482_, v_ofUserWidgetInfo_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofUserWidgetInfo_elim(lean_object* v_motive_485_, lean_object* v_t_486_, lean_object* v_h_487_, lean_object* v_ofUserWidgetInfo_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_486_, v_ofUserWidgetInfo_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCustomInfo_elim___redArg(lean_object* v_t_490_, lean_object* v_ofCustomInfo_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_490_, v_ofCustomInfo_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCustomInfo_elim(lean_object* v_motive_493_, lean_object* v_t_494_, lean_object* v_h_495_, lean_object* v_ofCustomInfo_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_494_, v_ofCustomInfo_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFVarAliasInfo_elim___redArg(lean_object* v_t_498_, lean_object* v_ofFVarAliasInfo_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_498_, v_ofFVarAliasInfo_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFVarAliasInfo_elim(lean_object* v_motive_501_, lean_object* v_t_502_, lean_object* v_h_503_, lean_object* v_ofFVarAliasInfo_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_502_, v_ofFVarAliasInfo_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldRedeclInfo_elim___redArg(lean_object* v_t_506_, lean_object* v_ofFieldRedeclInfo_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_506_, v_ofFieldRedeclInfo_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldRedeclInfo_elim(lean_object* v_motive_509_, lean_object* v_t_510_, lean_object* v_h_511_, lean_object* v_ofFieldRedeclInfo_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_510_, v_ofFieldRedeclInfo_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDelabTermInfo_elim___redArg(lean_object* v_t_514_, lean_object* v_ofDelabTermInfo_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_514_, v_ofDelabTermInfo_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDelabTermInfo_elim(lean_object* v_motive_517_, lean_object* v_t_518_, lean_object* v_h_519_, lean_object* v_ofDelabTermInfo_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_518_, v_ofDelabTermInfo_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceInfo_elim___redArg(lean_object* v_t_522_, lean_object* v_ofChoiceInfo_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_522_, v_ofChoiceInfo_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceInfo_elim(lean_object* v_motive_525_, lean_object* v_t_526_, lean_object* v_h_527_, lean_object* v_ofChoiceInfo_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_526_, v_ofChoiceInfo_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocInfo_elim___redArg(lean_object* v_t_530_, lean_object* v_ofDocInfo_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_530_, v_ofDocInfo_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocInfo_elim(lean_object* v_motive_533_, lean_object* v_t_534_, lean_object* v_h_535_, lean_object* v_ofDocInfo_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_534_, v_ofDocInfo_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocElabInfo_elim___redArg(lean_object* v_t_538_, lean_object* v_ofDocElabInfo_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_538_, v_ofDocElabInfo_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocElabInfo_elim(lean_object* v_motive_541_, lean_object* v_t_542_, lean_object* v_h_543_, lean_object* v_ofDocElabInfo_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_542_, v_ofDocElabInfo_544_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo_default___closed__0(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = l_Lean_Elab_instInhabitedTacticInfo_default;
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo_default(void){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfo_default___closed__0, &l_Lean_Elab_instInhabitedInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedInfo_default___closed__0);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo(void){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Elab_instInhabitedInfo_default;
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx(lean_object* v_x_550_){
_start:
{
switch(lean_obj_tag(v_x_550_))
{
case 0:
{
lean_object* v___x_551_; 
v___x_551_ = lean_unsigned_to_nat(0u);
return v___x_551_;
}
case 1:
{
lean_object* v___x_552_; 
v___x_552_ = lean_unsigned_to_nat(1u);
return v___x_552_;
}
default: 
{
lean_object* v___x_553_; 
v___x_553_ = lean_unsigned_to_nat(2u);
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx___boxed(lean_object* v_x_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Elab_InfoTree_ctorIdx(v_x_554_);
lean_dec_ref(v_x_554_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim___redArg(lean_object* v_t_556_, lean_object* v_k_557_){
_start:
{
if (lean_obj_tag(v_t_556_) == 2)
{
lean_object* v_mvarId_558_; lean_object* v___x_559_; 
v_mvarId_558_ = lean_ctor_get(v_t_556_, 0);
lean_inc(v_mvarId_558_);
lean_dec_ref_known(v_t_556_, 1);
v___x_559_ = lean_apply_1(v_k_557_, v_mvarId_558_);
return v___x_559_;
}
else
{
lean_object* v_i_560_; lean_object* v_t_561_; lean_object* v___x_562_; 
v_i_560_ = lean_ctor_get(v_t_556_, 0);
lean_inc_ref(v_i_560_);
v_t_561_ = lean_ctor_get(v_t_556_, 1);
lean_inc_ref(v_t_561_);
lean_dec_ref(v_t_556_);
v___x_562_ = lean_apply_2(v_k_557_, v_i_560_, v_t_561_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim(lean_object* v_motive__1_563_, lean_object* v_ctorIdx_564_, lean_object* v_t_565_, lean_object* v_h_566_, lean_object* v_k_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_565_, v_k_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim___boxed(lean_object* v_motive__1_569_, lean_object* v_ctorIdx_570_, lean_object* v_t_571_, lean_object* v_h_572_, lean_object* v_k_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Elab_InfoTree_ctorElim(v_motive__1_569_, v_ctorIdx_570_, v_t_571_, v_h_572_, v_k_573_);
lean_dec(v_ctorIdx_570_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_context_elim___redArg(lean_object* v_t_575_, lean_object* v_context_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_575_, v_context_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_context_elim(lean_object* v_motive__1_578_, lean_object* v_t_579_, lean_object* v_h_580_, lean_object* v_context_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_579_, v_context_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_node_elim___redArg(lean_object* v_t_583_, lean_object* v_node_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_583_, v_node_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_node_elim(lean_object* v_motive__1_586_, lean_object* v_t_587_, lean_object* v_h_588_, lean_object* v_node_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_587_, v_node_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hole_elim___redArg(lean_object* v_t_591_, lean_object* v_hole_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_591_, v_hole_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hole_elim(lean_object* v_motive__1_594_, lean_object* v_t_595_, lean_object* v_h_596_, lean_object* v_hole_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_595_, v_hole_597_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__0(void){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_599_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__1(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoTree_default___closed__0, &l_Lean_Elab_instInhabitedInfoTree_default___closed__0_once, _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__0);
v___x_601_ = l_Lean_Elab_instInhabitedInfo_default;
v___x_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_600_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree_default(void){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoTree_default___closed__1, &l_Lean_Elab_instInhabitedInfoTree_default___closed__1_once, _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__1);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree(void){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Elab_instInhabitedInfoTree_default;
return v___x_604_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__0(void){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_605_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__1(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__0, &l_Lean_Elab_instInhabitedInfoState_default___closed__0_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__0);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__2(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_unsigned_to_nat(32u);
v___x_609_ = lean_mk_empty_array_with_capacity(v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__3(void){
_start:
{
size_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_611_ = ((size_t)5ULL);
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_unsigned_to_nat(32u);
v___x_614_ = lean_mk_empty_array_with_capacity(v___x_613_);
v___x_615_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__2, &l_Lean_Elab_instInhabitedInfoState_default___closed__2_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__2);
v___x_616_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v___x_614_);
lean_ctor_set(v___x_616_, 2, v___x_612_);
lean_ctor_set(v___x_616_, 3, v___x_612_);
lean_ctor_set_usize(v___x_616_, 4, v___x_611_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__4(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; 
v___x_617_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__3, &l_Lean_Elab_instInhabitedInfoState_default___closed__3_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__3);
v___x_618_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__1, &l_Lean_Elab_instInhabitedInfoState_default___closed__1_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__1);
v___x_619_ = 1;
v___x_620_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_618_);
lean_ctor_set(v___x_620_, 2, v___x_617_);
lean_ctor_set_uint8(v___x_620_, sizeof(void*)*3, v___x_619_);
return v___x_620_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default(void){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__4, &l_Lean_Elab_instInhabitedInfoState_default___closed__4_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__4);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState(void){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Elab_instInhabitedInfoState_default;
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0(lean_object* v_modifyInfoState_623_, lean_object* v_inst_624_, lean_object* v_f_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_apply_1(v_modifyInfoState_623_, v_f_625_);
v___x_627_ = lean_apply_2(v_inst_624_, lean_box(0), v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(lean_object* v_inst_628_, lean_object* v_inst_629_){
_start:
{
lean_object* v_getInfoState_630_; lean_object* v_modifyInfoState_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_640_; 
v_getInfoState_630_ = lean_ctor_get(v_inst_629_, 0);
v_modifyInfoState_631_ = lean_ctor_get(v_inst_629_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_inst_629_);
if (v_isSharedCheck_640_ == 0)
{
v___x_633_ = v_inst_629_;
v_isShared_634_ = v_isSharedCheck_640_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_modifyInfoState_631_);
lean_inc(v_getInfoState_630_);
lean_dec(v_inst_629_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_640_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___f_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
lean_inc(v_inst_628_);
v___f_635_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_635_, 0, v_modifyInfoState_631_);
lean_closure_set(v___f_635_, 1, v_inst_628_);
v___x_636_ = lean_apply_2(v_inst_628_, lean_box(0), v_getInfoState_630_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___f_635_);
lean_ctor_set(v___x_633_, 0, v___x_636_);
v___x_638_ = v___x_633_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___f_635_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift(lean_object* v_m_641_, lean_object* v_n_642_, lean_object* v_inst_643_, lean_object* v_inst_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v_inst_643_, v_inst_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg___lam__0(lean_object* v_s_646_, lean_object* v_x_647_){
_start:
{
lean_inc_ref(v_s_646_);
return v_s_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg___lam__0___boxed(lean_object* v_s_648_, lean_object* v_x_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_Elab_setInfoState___redArg___lam__0(v_s_648_, v_x_649_);
lean_dec_ref(v_x_649_);
lean_dec_ref(v_s_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg(lean_object* v_inst_651_, lean_object* v_s_652_){
_start:
{
lean_object* v_modifyInfoState_653_; lean_object* v___f_654_; lean_object* v___x_655_; 
v_modifyInfoState_653_ = lean_ctor_get(v_inst_651_, 1);
lean_inc(v_modifyInfoState_653_);
lean_dec_ref(v_inst_651_);
v___f_654_ = lean_alloc_closure((void*)(l_Lean_Elab_setInfoState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_654_, 0, v_s_652_);
v___x_655_ = lean_apply_1(v_modifyInfoState_653_, v___f_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState(lean_object* v_m_656_, lean_object* v_inst_657_, lean_object* v_s_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Elab_setInfoState___redArg(v_inst_657_, v_s_658_);
return v___x_659_;
}
}
lean_object* runtime_initialize_Lean_Data_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_OpenDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PPContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_MetavarContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Widget_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_InfoTree_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_OpenDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PPContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_MetavarContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Widget_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_instInhabitedTermInfo_default = _init_l_Lean_Elab_instInhabitedTermInfo_default();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo_default);
l_Lean_Elab_instInhabitedTermInfo = _init_l_Lean_Elab_instInhabitedTermInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo);
l_Lean_Elab_instInhabitedPartialTermInfo_default = _init_l_Lean_Elab_instInhabitedPartialTermInfo_default();
lean_mark_persistent(l_Lean_Elab_instInhabitedPartialTermInfo_default);
l_Lean_Elab_instInhabitedPartialTermInfo = _init_l_Lean_Elab_instInhabitedPartialTermInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedPartialTermInfo);
l_Lean_Elab_instInhabitedFieldInfo_default = _init_l_Lean_Elab_instInhabitedFieldInfo_default();
lean_mark_persistent(l_Lean_Elab_instInhabitedFieldInfo_default);
l_Lean_Elab_instInhabitedFieldInfo = _init_l_Lean_Elab_instInhabitedFieldInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedFieldInfo);
l_Lean_Elab_instInhabitedTacticInfo_default = _init_l_Lean_Elab_instInhabitedTacticInfo_default();
lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo_default);
l_Lean_Elab_instInhabitedTacticInfo = _init_l_Lean_Elab_instInhabitedTacticInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo);
l_Lean_Elab_instInhabitedMacroExpansionInfo_default = _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default();
lean_mark_persistent(l_Lean_Elab_instInhabitedMacroExpansionInfo_default);
l_Lean_Elab_instInhabitedMacroExpansionInfo = _init_l_Lean_Elab_instInhabitedMacroExpansionInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedMacroExpansionInfo);
l_Lean_Elab_instInhabitedInfo_default = _init_l_Lean_Elab_instInhabitedInfo_default();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfo_default);
l_Lean_Elab_instInhabitedInfo = _init_l_Lean_Elab_instInhabitedInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfo);
l_Lean_Elab_instInhabitedInfoTree_default = _init_l_Lean_Elab_instInhabitedInfoTree_default();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree_default);
l_Lean_Elab_instInhabitedInfoTree = _init_l_Lean_Elab_instInhabitedInfoTree();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree);
l_Lean_Elab_instInhabitedInfoState_default = _init_l_Lean_Elab_instInhabitedInfoState_default();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoState_default);
l_Lean_Elab_instInhabitedInfoState = _init_l_Lean_Elab_instInhabitedInfoState();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_InfoTree_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_DeclarationRange(uint8_t builtin);
lean_object* initialize_Lean_Data_OpenDecl(uint8_t builtin);
lean_object* initialize_Lean_Data_PPContext(uint8_t builtin);
lean_object* initialize_Lean_MetavarContext(uint8_t builtin);
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Lean_Widget_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_InfoTree_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_OpenDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PPContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_InfoTree_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_InfoTree_Types(builtin);
}
#ifdef __cplusplus
}
#endif
