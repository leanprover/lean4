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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_Lean_instInhabitedLocalContext_default;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default___redArg();
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
static const lean_ctor_object l_Lean_Elab_instInhabitedChoiceResolutionInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instInhabitedChoiceResolutionInfo_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedChoiceResolutionInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedChoiceResolutionInfo_default = (const lean_object*)&l_Lean_Elab_instInhabitedChoiceResolutionInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedChoiceResolutionInfo = (const lean_object*)&l_Lean_Elab_instInhabitedChoiceResolutionInfo_default___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceResolutionInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceResolutionInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_212_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_217_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_217_, 10, v___x_215_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorIdx(uint8_t v_x_234_){
_start:
{
switch(v_x_234_)
{
case 0:
{
lean_object* v___x_235_; 
v___x_235_ = lean_unsigned_to_nat(0u);
return v___x_235_;
}
case 1:
{
lean_object* v___x_236_; 
v___x_236_ = lean_unsigned_to_nat(1u);
return v___x_236_;
}
case 2:
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(2u);
return v___x_237_;
}
default: 
{
lean_object* v___x_238_; 
v___x_238_ = lean_unsigned_to_nat(3u);
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorIdx___boxed(lean_object* v_x_239_){
_start:
{
uint8_t v_x_boxed_240_; lean_object* v_res_241_; 
v_x_boxed_240_ = lean_unbox(v_x_239_);
v_res_241_ = l_Lean_Elab_DocElabKind_ctorIdx(v_x_boxed_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___redArg(lean_object* v_k_242_){
_start:
{
lean_inc(v_k_242_);
return v_k_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___redArg___boxed(lean_object* v_k_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Elab_DocElabKind_ctorElim___redArg(v_k_243_);
lean_dec(v_k_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim(lean_object* v_motive_245_, lean_object* v_ctorIdx_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_k_249_){
_start:
{
lean_inc(v_k_249_);
return v_k_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___boxed(lean_object* v_motive_250_, lean_object* v_ctorIdx_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_k_254_){
_start:
{
uint8_t v_t_boxed_255_; lean_object* v_res_256_; 
v_t_boxed_255_ = lean_unbox(v_t_252_);
v_res_256_ = l_Lean_Elab_DocElabKind_ctorElim(v_motive_250_, v_ctorIdx_251_, v_t_boxed_255_, v_h_253_, v_k_254_);
lean_dec(v_k_254_);
lean_dec(v_ctorIdx_251_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___redArg(lean_object* v_role_257_){
_start:
{
lean_inc(v_role_257_);
return v_role_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___redArg___boxed(lean_object* v_role_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Elab_DocElabKind_role_elim___redArg(v_role_258_);
lean_dec(v_role_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim(lean_object* v_motive_260_, uint8_t v_t_261_, lean_object* v_h_262_, lean_object* v_role_263_){
_start:
{
lean_inc(v_role_263_);
return v_role_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___boxed(lean_object* v_motive_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_role_267_){
_start:
{
uint8_t v_t_boxed_268_; lean_object* v_res_269_; 
v_t_boxed_268_ = lean_unbox(v_t_265_);
v_res_269_ = l_Lean_Elab_DocElabKind_role_elim(v_motive_264_, v_t_boxed_268_, v_h_266_, v_role_267_);
lean_dec(v_role_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___redArg(lean_object* v_codeBlock_270_){
_start:
{
lean_inc(v_codeBlock_270_);
return v_codeBlock_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___redArg___boxed(lean_object* v_codeBlock_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Elab_DocElabKind_codeBlock_elim___redArg(v_codeBlock_271_);
lean_dec(v_codeBlock_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim(lean_object* v_motive_273_, uint8_t v_t_274_, lean_object* v_h_275_, lean_object* v_codeBlock_276_){
_start:
{
lean_inc(v_codeBlock_276_);
return v_codeBlock_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___boxed(lean_object* v_motive_277_, lean_object* v_t_278_, lean_object* v_h_279_, lean_object* v_codeBlock_280_){
_start:
{
uint8_t v_t_boxed_281_; lean_object* v_res_282_; 
v_t_boxed_281_ = lean_unbox(v_t_278_);
v_res_282_ = l_Lean_Elab_DocElabKind_codeBlock_elim(v_motive_277_, v_t_boxed_281_, v_h_279_, v_codeBlock_280_);
lean_dec(v_codeBlock_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___redArg(lean_object* v_directive_283_){
_start:
{
lean_inc(v_directive_283_);
return v_directive_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___redArg___boxed(lean_object* v_directive_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Elab_DocElabKind_directive_elim___redArg(v_directive_284_);
lean_dec(v_directive_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim(lean_object* v_motive_286_, uint8_t v_t_287_, lean_object* v_h_288_, lean_object* v_directive_289_){
_start:
{
lean_inc(v_directive_289_);
return v_directive_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___boxed(lean_object* v_motive_290_, lean_object* v_t_291_, lean_object* v_h_292_, lean_object* v_directive_293_){
_start:
{
uint8_t v_t_boxed_294_; lean_object* v_res_295_; 
v_t_boxed_294_ = lean_unbox(v_t_291_);
v_res_295_ = l_Lean_Elab_DocElabKind_directive_elim(v_motive_290_, v_t_boxed_294_, v_h_292_, v_directive_293_);
lean_dec(v_directive_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___redArg(lean_object* v_command_296_){
_start:
{
lean_inc(v_command_296_);
return v_command_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___redArg___boxed(lean_object* v_command_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Elab_DocElabKind_command_elim___redArg(v_command_297_);
lean_dec(v_command_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim(lean_object* v_motive_299_, uint8_t v_t_300_, lean_object* v_h_301_, lean_object* v_command_302_){
_start:
{
lean_inc(v_command_302_);
return v_command_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___boxed(lean_object* v_motive_303_, lean_object* v_t_304_, lean_object* v_h_305_, lean_object* v_command_306_){
_start:
{
uint8_t v_t_boxed_307_; lean_object* v_res_308_; 
v_t_boxed_307_ = lean_unbox(v_t_304_);
v_res_308_ = l_Lean_Elab_DocElabKind_command_elim(v_motive_303_, v_t_boxed_307_, v_h_305_, v_command_306_);
lean_dec(v_command_306_);
return v_res_308_;
}
}
static lean_object* _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(2u);
v___x_322_ = lean_nat_to_int(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = lean_nat_to_int(v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprDocElabKind_repr(uint8_t v_x_325_, lean_object* v_prec_326_){
_start:
{
lean_object* v___y_328_; lean_object* v___y_335_; lean_object* v___y_342_; lean_object* v___y_349_; 
switch(v_x_325_)
{
case 0:
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = lean_unsigned_to_nat(1024u);
v___x_356_ = lean_nat_dec_le(v___x_355_, v_prec_326_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_328_ = v___x_357_;
goto v___jp_327_;
}
else
{
lean_object* v___x_358_; 
v___x_358_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_328_ = v___x_358_;
goto v___jp_327_;
}
}
case 1:
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(1024u);
v___x_360_ = lean_nat_dec_le(v___x_359_, v_prec_326_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_335_ = v___x_361_;
goto v___jp_334_;
}
else
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_335_ = v___x_362_;
goto v___jp_334_;
}
}
case 2:
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = lean_unsigned_to_nat(1024u);
v___x_364_ = lean_nat_dec_le(v___x_363_, v_prec_326_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_342_ = v___x_365_;
goto v___jp_341_;
}
else
{
lean_object* v___x_366_; 
v___x_366_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_342_ = v___x_366_;
goto v___jp_341_;
}
}
default: 
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = lean_unsigned_to_nat(1024u);
v___x_368_ = lean_nat_dec_le(v___x_367_, v_prec_326_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
v___x_369_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_349_ = v___x_369_;
goto v___jp_348_;
}
else
{
lean_object* v___x_370_; 
v___x_370_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_349_ = v___x_370_;
goto v___jp_348_;
}
}
}
v___jp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_329_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__1));
lean_inc(v___y_328_);
v___x_330_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_330_, 0, v___y_328_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = 0;
v___x_332_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*1, v___x_331_);
v___x_333_ = l_Repr_addAppParen(v___x_332_, v_prec_326_);
return v___x_333_;
}
v___jp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_336_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__3));
lean_inc(v___y_335_);
v___x_337_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_337_, 0, v___y_335_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = 0;
v___x_339_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set_uint8(v___x_339_, sizeof(void*)*1, v___x_338_);
v___x_340_ = l_Repr_addAppParen(v___x_339_, v_prec_326_);
return v___x_340_;
}
v___jp_341_:
{
lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_343_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__5));
lean_inc(v___y_342_);
v___x_344_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_344_, 0, v___y_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = 0;
v___x_346_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set_uint8(v___x_346_, sizeof(void*)*1, v___x_345_);
v___x_347_ = l_Repr_addAppParen(v___x_346_, v_prec_326_);
return v___x_347_;
}
v___jp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_350_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__7));
lean_inc(v___y_349_);
v___x_351_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_351_, 0, v___y_349_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = 0;
v___x_353_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_353_, 0, v___x_351_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*1, v___x_352_);
v___x_354_ = l_Repr_addAppParen(v___x_353_, v_prec_326_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprDocElabKind_repr___boxed(lean_object* v_x_371_, lean_object* v_prec_372_){
_start:
{
uint8_t v_x_225__boxed_373_; lean_object* v_res_374_; 
v_x_225__boxed_373_ = lean_unbox(v_x_371_);
v_res_374_ = l_Lean_Elab_instReprDocElabKind_repr(v_x_225__boxed_373_, v_prec_372_);
lean_dec(v_prec_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx(lean_object* v_x_377_){
_start:
{
switch(lean_obj_tag(v_x_377_))
{
case 0:
{
lean_object* v___x_378_; 
v___x_378_ = lean_unsigned_to_nat(0u);
return v___x_378_;
}
case 1:
{
lean_object* v___x_379_; 
v___x_379_ = lean_unsigned_to_nat(1u);
return v___x_379_;
}
case 2:
{
lean_object* v___x_380_; 
v___x_380_ = lean_unsigned_to_nat(2u);
return v___x_380_;
}
case 3:
{
lean_object* v___x_381_; 
v___x_381_ = lean_unsigned_to_nat(3u);
return v___x_381_;
}
case 4:
{
lean_object* v___x_382_; 
v___x_382_ = lean_unsigned_to_nat(4u);
return v___x_382_;
}
case 5:
{
lean_object* v___x_383_; 
v___x_383_ = lean_unsigned_to_nat(5u);
return v___x_383_;
}
case 6:
{
lean_object* v___x_384_; 
v___x_384_ = lean_unsigned_to_nat(6u);
return v___x_384_;
}
case 7:
{
lean_object* v___x_385_; 
v___x_385_ = lean_unsigned_to_nat(7u);
return v___x_385_;
}
case 8:
{
lean_object* v___x_386_; 
v___x_386_ = lean_unsigned_to_nat(8u);
return v___x_386_;
}
case 9:
{
lean_object* v___x_387_; 
v___x_387_ = lean_unsigned_to_nat(9u);
return v___x_387_;
}
case 10:
{
lean_object* v___x_388_; 
v___x_388_ = lean_unsigned_to_nat(10u);
return v___x_388_;
}
case 11:
{
lean_object* v___x_389_; 
v___x_389_ = lean_unsigned_to_nat(11u);
return v___x_389_;
}
case 12:
{
lean_object* v___x_390_; 
v___x_390_ = lean_unsigned_to_nat(12u);
return v___x_390_;
}
case 13:
{
lean_object* v___x_391_; 
v___x_391_ = lean_unsigned_to_nat(13u);
return v___x_391_;
}
case 14:
{
lean_object* v___x_392_; 
v___x_392_ = lean_unsigned_to_nat(14u);
return v___x_392_;
}
case 15:
{
lean_object* v___x_393_; 
v___x_393_ = lean_unsigned_to_nat(15u);
return v___x_393_;
}
case 16:
{
lean_object* v___x_394_; 
v___x_394_ = lean_unsigned_to_nat(16u);
return v___x_394_;
}
default: 
{
lean_object* v___x_395_; 
v___x_395_ = lean_unsigned_to_nat(17u);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx___boxed(lean_object* v_x_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Elab_Info_ctorIdx(v_x_396_);
lean_dec_ref(v_x_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim___redArg(lean_object* v_t_398_, lean_object* v_k_399_){
_start:
{
if (lean_obj_tag(v_t_398_) == 12)
{
lean_object* v_i_400_; lean_object* v___x_401_; 
v_i_400_ = lean_ctor_get(v_t_398_, 0);
lean_inc(v_i_400_);
lean_dec_ref_known(v_t_398_, 1);
v___x_401_ = lean_apply_1(v_k_399_, v_i_400_);
return v___x_401_;
}
else
{
lean_object* v_i_402_; lean_object* v___x_403_; 
v_i_402_ = lean_ctor_get(v_t_398_, 0);
lean_inc_ref(v_i_402_);
lean_dec_ref(v_t_398_);
v___x_403_ = lean_apply_1(v_k_399_, v_i_402_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim(lean_object* v_motive_404_, lean_object* v_ctorIdx_405_, lean_object* v_t_406_, lean_object* v_h_407_, lean_object* v_k_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_406_, v_k_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim___boxed(lean_object* v_motive_410_, lean_object* v_ctorIdx_411_, lean_object* v_t_412_, lean_object* v_h_413_, lean_object* v_k_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Elab_Info_ctorElim(v_motive_410_, v_ctorIdx_411_, v_t_412_, v_h_413_, v_k_414_);
lean_dec(v_ctorIdx_411_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTacticInfo_elim___redArg(lean_object* v_t_416_, lean_object* v_ofTacticInfo_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_416_, v_ofTacticInfo_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTacticInfo_elim(lean_object* v_motive_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_ofTacticInfo_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_420_, v_ofTacticInfo_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTermInfo_elim___redArg(lean_object* v_t_424_, lean_object* v_ofTermInfo_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_424_, v_ofTermInfo_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTermInfo_elim(lean_object* v_motive_427_, lean_object* v_t_428_, lean_object* v_h_429_, lean_object* v_ofTermInfo_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_428_, v_ofTermInfo_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofPartialTermInfo_elim___redArg(lean_object* v_t_432_, lean_object* v_ofPartialTermInfo_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_432_, v_ofPartialTermInfo_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofPartialTermInfo_elim(lean_object* v_motive_435_, lean_object* v_t_436_, lean_object* v_h_437_, lean_object* v_ofPartialTermInfo_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_436_, v_ofPartialTermInfo_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCommandInfo_elim___redArg(lean_object* v_t_440_, lean_object* v_ofCommandInfo_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_440_, v_ofCommandInfo_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCommandInfo_elim(lean_object* v_motive_443_, lean_object* v_t_444_, lean_object* v_h_445_, lean_object* v_ofCommandInfo_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_444_, v_ofCommandInfo_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofMacroExpansionInfo_elim___redArg(lean_object* v_t_448_, lean_object* v_ofMacroExpansionInfo_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_448_, v_ofMacroExpansionInfo_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofMacroExpansionInfo_elim(lean_object* v_motive_451_, lean_object* v_t_452_, lean_object* v_h_453_, lean_object* v_ofMacroExpansionInfo_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_452_, v_ofMacroExpansionInfo_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofOptionInfo_elim___redArg(lean_object* v_t_456_, lean_object* v_ofOptionInfo_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_456_, v_ofOptionInfo_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofOptionInfo_elim(lean_object* v_motive_459_, lean_object* v_t_460_, lean_object* v_h_461_, lean_object* v_ofOptionInfo_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_460_, v_ofOptionInfo_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofErrorNameInfo_elim___redArg(lean_object* v_t_464_, lean_object* v_ofErrorNameInfo_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_464_, v_ofErrorNameInfo_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofErrorNameInfo_elim(lean_object* v_motive_467_, lean_object* v_t_468_, lean_object* v_h_469_, lean_object* v_ofErrorNameInfo_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_468_, v_ofErrorNameInfo_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldInfo_elim___redArg(lean_object* v_t_472_, lean_object* v_ofFieldInfo_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_472_, v_ofFieldInfo_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldInfo_elim(lean_object* v_motive_475_, lean_object* v_t_476_, lean_object* v_h_477_, lean_object* v_ofFieldInfo_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_476_, v_ofFieldInfo_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCompletionInfo_elim___redArg(lean_object* v_t_480_, lean_object* v_ofCompletionInfo_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_480_, v_ofCompletionInfo_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCompletionInfo_elim(lean_object* v_motive_483_, lean_object* v_t_484_, lean_object* v_h_485_, lean_object* v_ofCompletionInfo_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_484_, v_ofCompletionInfo_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofUserWidgetInfo_elim___redArg(lean_object* v_t_488_, lean_object* v_ofUserWidgetInfo_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_488_, v_ofUserWidgetInfo_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofUserWidgetInfo_elim(lean_object* v_motive_491_, lean_object* v_t_492_, lean_object* v_h_493_, lean_object* v_ofUserWidgetInfo_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_492_, v_ofUserWidgetInfo_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCustomInfo_elim___redArg(lean_object* v_t_496_, lean_object* v_ofCustomInfo_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_496_, v_ofCustomInfo_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCustomInfo_elim(lean_object* v_motive_499_, lean_object* v_t_500_, lean_object* v_h_501_, lean_object* v_ofCustomInfo_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_500_, v_ofCustomInfo_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFVarAliasInfo_elim___redArg(lean_object* v_t_504_, lean_object* v_ofFVarAliasInfo_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_504_, v_ofFVarAliasInfo_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFVarAliasInfo_elim(lean_object* v_motive_507_, lean_object* v_t_508_, lean_object* v_h_509_, lean_object* v_ofFVarAliasInfo_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_508_, v_ofFVarAliasInfo_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldRedeclInfo_elim___redArg(lean_object* v_t_512_, lean_object* v_ofFieldRedeclInfo_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_512_, v_ofFieldRedeclInfo_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldRedeclInfo_elim(lean_object* v_motive_515_, lean_object* v_t_516_, lean_object* v_h_517_, lean_object* v_ofFieldRedeclInfo_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_516_, v_ofFieldRedeclInfo_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDelabTermInfo_elim___redArg(lean_object* v_t_520_, lean_object* v_ofDelabTermInfo_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_520_, v_ofDelabTermInfo_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDelabTermInfo_elim(lean_object* v_motive_523_, lean_object* v_t_524_, lean_object* v_h_525_, lean_object* v_ofDelabTermInfo_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_524_, v_ofDelabTermInfo_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceInfo_elim___redArg(lean_object* v_t_528_, lean_object* v_ofChoiceInfo_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_528_, v_ofChoiceInfo_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceInfo_elim(lean_object* v_motive_531_, lean_object* v_t_532_, lean_object* v_h_533_, lean_object* v_ofChoiceInfo_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_532_, v_ofChoiceInfo_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceResolutionInfo_elim___redArg(lean_object* v_t_536_, lean_object* v_ofChoiceResolutionInfo_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_536_, v_ofChoiceResolutionInfo_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceResolutionInfo_elim(lean_object* v_motive_539_, lean_object* v_t_540_, lean_object* v_h_541_, lean_object* v_ofChoiceResolutionInfo_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_540_, v_ofChoiceResolutionInfo_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocInfo_elim___redArg(lean_object* v_t_544_, lean_object* v_ofDocInfo_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_544_, v_ofDocInfo_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocInfo_elim(lean_object* v_motive_547_, lean_object* v_t_548_, lean_object* v_h_549_, lean_object* v_ofDocInfo_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_548_, v_ofDocInfo_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocElabInfo_elim___redArg(lean_object* v_t_552_, lean_object* v_ofDocElabInfo_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_552_, v_ofDocElabInfo_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocElabInfo_elim(lean_object* v_motive_555_, lean_object* v_t_556_, lean_object* v_h_557_, lean_object* v_ofDocElabInfo_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_556_, v_ofDocElabInfo_558_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo_default___closed__0(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = l_Lean_Elab_instInhabitedTacticInfo_default;
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo_default(void){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfo_default___closed__0, &l_Lean_Elab_instInhabitedInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedInfo_default___closed__0);
return v___x_562_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo(void){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Elab_instInhabitedInfo_default;
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx(lean_object* v_x_564_){
_start:
{
switch(lean_obj_tag(v_x_564_))
{
case 0:
{
lean_object* v___x_565_; 
v___x_565_ = lean_unsigned_to_nat(0u);
return v___x_565_;
}
case 1:
{
lean_object* v___x_566_; 
v___x_566_ = lean_unsigned_to_nat(1u);
return v___x_566_;
}
default: 
{
lean_object* v___x_567_; 
v___x_567_ = lean_unsigned_to_nat(2u);
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx___boxed(lean_object* v_x_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Elab_InfoTree_ctorIdx(v_x_568_);
lean_dec_ref(v_x_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim___redArg(lean_object* v_t_570_, lean_object* v_k_571_){
_start:
{
if (lean_obj_tag(v_t_570_) == 2)
{
lean_object* v_mvarId_572_; lean_object* v___x_573_; 
v_mvarId_572_ = lean_ctor_get(v_t_570_, 0);
lean_inc(v_mvarId_572_);
lean_dec_ref_known(v_t_570_, 1);
v___x_573_ = lean_apply_1(v_k_571_, v_mvarId_572_);
return v___x_573_;
}
else
{
lean_object* v_i_574_; lean_object* v_t_575_; lean_object* v___x_576_; 
v_i_574_ = lean_ctor_get(v_t_570_, 0);
lean_inc_ref(v_i_574_);
v_t_575_ = lean_ctor_get(v_t_570_, 1);
lean_inc_ref(v_t_575_);
lean_dec_ref(v_t_570_);
v___x_576_ = lean_apply_2(v_k_571_, v_i_574_, v_t_575_);
return v___x_576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim(lean_object* v_motive__1_577_, lean_object* v_ctorIdx_578_, lean_object* v_t_579_, lean_object* v_h_580_, lean_object* v_k_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_579_, v_k_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim___boxed(lean_object* v_motive__1_583_, lean_object* v_ctorIdx_584_, lean_object* v_t_585_, lean_object* v_h_586_, lean_object* v_k_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Elab_InfoTree_ctorElim(v_motive__1_583_, v_ctorIdx_584_, v_t_585_, v_h_586_, v_k_587_);
lean_dec(v_ctorIdx_584_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_context_elim___redArg(lean_object* v_t_589_, lean_object* v_context_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_589_, v_context_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_context_elim(lean_object* v_motive__1_592_, lean_object* v_t_593_, lean_object* v_h_594_, lean_object* v_context_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_593_, v_context_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_node_elim___redArg(lean_object* v_t_597_, lean_object* v_node_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_597_, v_node_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_node_elim(lean_object* v_motive__1_600_, lean_object* v_t_601_, lean_object* v_h_602_, lean_object* v_node_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_601_, v_node_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hole_elim___redArg(lean_object* v_t_605_, lean_object* v_hole_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_605_, v_hole_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hole_elim(lean_object* v_motive__1_608_, lean_object* v_t_609_, lean_object* v_h_610_, lean_object* v_hole_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_609_, v_hole_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__0(void){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__1(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoTree_default___closed__0, &l_Lean_Elab_instInhabitedInfoTree_default___closed__0_once, _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__0);
v___x_615_ = l_Lean_Elab_instInhabitedInfo_default;
v___x_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v___x_614_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree_default(void){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoTree_default___closed__1, &l_Lean_Elab_instInhabitedInfoTree_default___closed__1_once, _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__1);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree(void){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_Elab_instInhabitedInfoTree_default;
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__0(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_obj_once(&l_Lean_Elab_instInhabitedTacticInfo_default___closed__0, &l_Lean_Elab_instInhabitedTacticInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__0);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
return v___x_620_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__1(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_unsigned_to_nat(32u);
v___x_622_ = lean_mk_empty_array_with_capacity(v___x_621_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__2(void){
_start:
{
size_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_624_ = ((size_t)5ULL);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_unsigned_to_nat(32u);
v___x_627_ = lean_mk_empty_array_with_capacity(v___x_626_);
v___x_628_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__1, &l_Lean_Elab_instInhabitedInfoState_default___closed__1_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__1);
v___x_629_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v___x_627_);
lean_ctor_set(v___x_629_, 2, v___x_625_);
lean_ctor_set(v___x_629_, 3, v___x_625_);
lean_ctor_set_usize(v___x_629_, 4, v___x_624_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__3(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; 
v___x_630_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__2, &l_Lean_Elab_instInhabitedInfoState_default___closed__2_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__2);
v___x_631_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__0, &l_Lean_Elab_instInhabitedInfoState_default___closed__0_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__0);
v___x_632_ = 1;
v___x_633_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
lean_ctor_set(v___x_633_, 2, v___x_630_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3, v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default(void){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__3, &l_Lean_Elab_instInhabitedInfoState_default___closed__3_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__3);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState(void){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Elab_instInhabitedInfoState_default;
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0(lean_object* v_modifyInfoState_636_, lean_object* v_inst_637_, lean_object* v_f_638_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_apply_1(v_modifyInfoState_636_, v_f_638_);
v___x_640_ = lean_apply_2(v_inst_637_, lean_box(0), v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(lean_object* v_inst_641_, lean_object* v_inst_642_){
_start:
{
lean_object* v_getInfoState_643_; lean_object* v_modifyInfoState_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_653_; 
v_getInfoState_643_ = lean_ctor_get(v_inst_642_, 0);
v_modifyInfoState_644_ = lean_ctor_get(v_inst_642_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_inst_642_);
if (v_isSharedCheck_653_ == 0)
{
v___x_646_ = v_inst_642_;
v_isShared_647_ = v_isSharedCheck_653_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_modifyInfoState_644_);
lean_inc(v_getInfoState_643_);
lean_dec(v_inst_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_653_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___f_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
lean_inc(v_inst_641_);
v___f_648_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_648_, 0, v_modifyInfoState_644_);
lean_closure_set(v___f_648_, 1, v_inst_641_);
v___x_649_ = lean_apply_2(v_inst_641_, lean_box(0), v_getInfoState_643_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 1, v___f_648_);
lean_ctor_set(v___x_646_, 0, v___x_649_);
v___x_651_ = v___x_646_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___f_648_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift(lean_object* v_m_654_, lean_object* v_n_655_, lean_object* v_inst_656_, lean_object* v_inst_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v_inst_656_, v_inst_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg___lam__0(lean_object* v_s_659_, lean_object* v_x_660_){
_start:
{
lean_inc_ref(v_s_659_);
return v_s_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg___lam__0___boxed(lean_object* v_s_661_, lean_object* v_x_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Elab_setInfoState___redArg___lam__0(v_s_661_, v_x_662_);
lean_dec_ref(v_x_662_);
lean_dec_ref(v_s_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg(lean_object* v_inst_664_, lean_object* v_s_665_){
_start:
{
lean_object* v_modifyInfoState_666_; lean_object* v___f_667_; lean_object* v___x_668_; 
v_modifyInfoState_666_ = lean_ctor_get(v_inst_664_, 1);
lean_inc(v_modifyInfoState_666_);
lean_dec_ref(v_inst_664_);
v___f_667_ = lean_alloc_closure((void*)(l_Lean_Elab_setInfoState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_667_, 0, v_s_665_);
v___x_668_ = lean_apply_1(v_modifyInfoState_666_, v___f_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState(lean_object* v_m_669_, lean_object* v_inst_670_, lean_object* v_s_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_Elab_setInfoState___redArg(v_inst_670_, v_s_671_);
return v___x_672_;
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
