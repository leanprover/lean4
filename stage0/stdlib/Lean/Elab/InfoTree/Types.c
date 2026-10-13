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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_Lean_instInhabitedLocalContext_default;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Elab_PartialContextInfo_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 1)
{
lean_object* v_parentDecl_7_; lean_object* v___x_8_; 
v_parentDecl_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_parentDecl_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_parentDecl_7_);
return v___x_8_;
}
else
{
lean_object* v_info_9_; lean_object* v___x_10_; 
v_info_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_info_9_);
lean_dec_ref(v_t_5_);
v___x_10_ = lean_apply_1(v_k_6_, v_info_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Elab_PartialContextInfo_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_commandCtx_elim___redArg(lean_object* v_t_23_, lean_object* v_commandCtx_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_23_, v_commandCtx_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_commandCtx_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_commandCtx_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_27_, v_commandCtx_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_parentDeclCtx_elim___redArg(lean_object* v_t_31_, lean_object* v_parentDeclCtx_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_31_, v_parentDeclCtx_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_parentDeclCtx_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_parentDeclCtx_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_35_, v_parentDeclCtx_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_autoImplicitCtx_elim___redArg(lean_object* v_t_39_, lean_object* v_autoImplicitCtx_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_39_, v_autoImplicitCtx_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_autoImplicitCtx_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_autoImplicitCtx_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_43_, v_autoImplicitCtx_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__2(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_box(0);
v___x_56_ = ((lean_object*)(l_Lean_Elab_instInhabitedTermInfo_default___closed__1));
v___x_57_ = l_Lean_Expr_const___override(v___x_56_, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__3(void){
_start:
{
uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_58_ = 0;
v___x_59_ = lean_obj_once(&l_Lean_Elab_instInhabitedTermInfo_default___closed__2, &l_Lean_Elab_instInhabitedTermInfo_default___closed__2_once, _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__2);
v___x_60_ = lean_box(0);
v___x_61_ = l_Lean_instInhabitedLocalContext_default;
v___x_62_ = ((lean_object*)(l_Lean_Elab_instInhabitedElabInfo_default));
v___x_63_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_61_);
lean_ctor_set(v___x_63_, 2, v___x_60_);
lean_ctor_set(v___x_63_, 3, v___x_59_);
lean_ctor_set_uint8(v___x_63_, sizeof(void*)*4, v___x_58_);
lean_ctor_set_uint8(v___x_63_, sizeof(void*)*4 + 1, v___x_58_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo_default(void){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_obj_once(&l_Lean_Elab_instInhabitedTermInfo_default___closed__3, &l_Lean_Elab_instInhabitedTermInfo_default___closed__3_once, _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__3);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo(void){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Elab_instInhabitedTermInfo_default;
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_box(0);
v___x_67_ = l_Lean_instInhabitedLocalContext_default;
v___x_68_ = ((lean_object*)(l_Lean_Elab_instInhabitedElabInfo_default));
v___x_69_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPartialTermInfo_default(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_obj_once(&l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0, &l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPartialTermInfo(void){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Elab_instInhabitedPartialTermInfo_default;
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorIdx___impl(lean_object* v_x_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_obj_tag_nat(v_x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorIdx___impl___boxed(lean_object* v_x_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Elab_CompletionInfo_ctorIdx___impl(v_x_76_);
lean_dec_ref(v_x_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorElim___redArg(lean_object* v_t_78_, lean_object* v_k_79_){
_start:
{
switch(lean_obj_tag(v_t_78_))
{
case 0:
{
lean_object* v_termInfo_80_; lean_object* v_expectedType_x3f_81_; lean_object* v___x_82_; 
v_termInfo_80_ = lean_ctor_get(v_t_78_, 0);
lean_inc_ref(v_termInfo_80_);
v_expectedType_x3f_81_ = lean_ctor_get(v_t_78_, 1);
lean_inc(v_expectedType_x3f_81_);
lean_dec_ref_known(v_t_78_, 2);
v___x_82_ = lean_apply_2(v_k_79_, v_termInfo_80_, v_expectedType_x3f_81_);
return v___x_82_;
}
case 1:
{
lean_object* v_stx_83_; lean_object* v_id_84_; uint8_t v_danglingDot_85_; lean_object* v_lctx_86_; lean_object* v_expectedType_x3f_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_stx_83_ = lean_ctor_get(v_t_78_, 0);
lean_inc(v_stx_83_);
v_id_84_ = lean_ctor_get(v_t_78_, 1);
lean_inc(v_id_84_);
v_danglingDot_85_ = lean_ctor_get_uint8(v_t_78_, sizeof(void*)*4);
v_lctx_86_ = lean_ctor_get(v_t_78_, 2);
lean_inc_ref(v_lctx_86_);
v_expectedType_x3f_87_ = lean_ctor_get(v_t_78_, 3);
lean_inc(v_expectedType_x3f_87_);
lean_dec_ref_known(v_t_78_, 4);
v___x_88_ = lean_box(v_danglingDot_85_);
v___x_89_ = lean_apply_5(v_k_79_, v_stx_83_, v_id_84_, v___x_88_, v_lctx_86_, v_expectedType_x3f_87_);
return v___x_89_;
}
case 2:
{
lean_object* v_stx_90_; lean_object* v_id_91_; lean_object* v_lctx_92_; lean_object* v_expectedType_x3f_93_; lean_object* v___x_94_; 
v_stx_90_ = lean_ctor_get(v_t_78_, 0);
lean_inc(v_stx_90_);
v_id_91_ = lean_ctor_get(v_t_78_, 1);
lean_inc(v_id_91_);
v_lctx_92_ = lean_ctor_get(v_t_78_, 2);
lean_inc_ref(v_lctx_92_);
v_expectedType_x3f_93_ = lean_ctor_get(v_t_78_, 3);
lean_inc(v_expectedType_x3f_93_);
lean_dec_ref_known(v_t_78_, 4);
v___x_94_ = lean_apply_4(v_k_79_, v_stx_90_, v_id_91_, v_lctx_92_, v_expectedType_x3f_93_);
return v___x_94_;
}
case 3:
{
lean_object* v_stx_95_; lean_object* v_id_96_; lean_object* v_lctx_97_; lean_object* v_structName_98_; lean_object* v___x_99_; 
v_stx_95_ = lean_ctor_get(v_t_78_, 0);
lean_inc(v_stx_95_);
v_id_96_ = lean_ctor_get(v_t_78_, 1);
lean_inc(v_id_96_);
v_lctx_97_ = lean_ctor_get(v_t_78_, 2);
lean_inc_ref(v_lctx_97_);
v_structName_98_ = lean_ctor_get(v_t_78_, 3);
lean_inc(v_structName_98_);
lean_dec_ref_known(v_t_78_, 4);
v___x_99_ = lean_apply_4(v_k_79_, v_stx_95_, v_id_96_, v_lctx_97_, v_structName_98_);
return v___x_99_;
}
case 6:
{
lean_object* v_stx_100_; lean_object* v_partialId_101_; lean_object* v___x_102_; 
v_stx_100_ = lean_ctor_get(v_t_78_, 0);
lean_inc(v_stx_100_);
v_partialId_101_ = lean_ctor_get(v_t_78_, 1);
lean_inc(v_partialId_101_);
lean_dec_ref_known(v_t_78_, 2);
v___x_102_ = lean_apply_2(v_k_79_, v_stx_100_, v_partialId_101_);
return v___x_102_;
}
case 7:
{
lean_object* v_stx_103_; lean_object* v_id_x3f_104_; uint8_t v_danglingDot_105_; lean_object* v_scopeNames_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_stx_103_ = lean_ctor_get(v_t_78_, 0);
lean_inc(v_stx_103_);
v_id_x3f_104_ = lean_ctor_get(v_t_78_, 1);
lean_inc(v_id_x3f_104_);
v_danglingDot_105_ = lean_ctor_get_uint8(v_t_78_, sizeof(void*)*3);
v_scopeNames_106_ = lean_ctor_get(v_t_78_, 2);
lean_inc(v_scopeNames_106_);
lean_dec_ref_known(v_t_78_, 3);
v___x_107_ = lean_box(v_danglingDot_105_);
v___x_108_ = lean_apply_4(v_k_79_, v_stx_103_, v_id_x3f_104_, v___x_107_, v_scopeNames_106_);
return v___x_108_;
}
default: 
{
lean_object* v_stx_109_; lean_object* v___x_110_; 
v_stx_109_ = lean_ctor_get(v_t_78_, 0);
lean_inc(v_stx_109_);
lean_dec_ref(v_t_78_);
v___x_110_ = lean_apply_1(v_k_79_, v_stx_109_);
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorElim(lean_object* v_motive_111_, lean_object* v_ctorIdx_112_, lean_object* v_t_113_, lean_object* v_h_114_, lean_object* v_k_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_113_, v_k_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorElim___boxed(lean_object* v_motive_117_, lean_object* v_ctorIdx_118_, lean_object* v_t_119_, lean_object* v_h_120_, lean_object* v_k_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Elab_CompletionInfo_ctorElim(v_motive_117_, v_ctorIdx_118_, v_t_119_, v_h_120_, v_k_121_);
lean_dec(v_ctorIdx_118_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_dot_elim___redArg(lean_object* v_t_123_, lean_object* v_dot_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_123_, v_dot_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_dot_elim(lean_object* v_motive_126_, lean_object* v_t_127_, lean_object* v_h_128_, lean_object* v_dot_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_127_, v_dot_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_id_elim___redArg(lean_object* v_t_131_, lean_object* v_id_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_131_, v_id_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_id_elim(lean_object* v_motive_134_, lean_object* v_t_135_, lean_object* v_h_136_, lean_object* v_id_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_135_, v_id_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_dotId_elim___redArg(lean_object* v_t_139_, lean_object* v_dotId_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_139_, v_dotId_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_dotId_elim(lean_object* v_motive_142_, lean_object* v_t_143_, lean_object* v_h_144_, lean_object* v_dotId_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_143_, v_dotId_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_fieldId_elim___redArg(lean_object* v_t_147_, lean_object* v_fieldId_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_147_, v_fieldId_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_fieldId_elim(lean_object* v_motive_150_, lean_object* v_t_151_, lean_object* v_h_152_, lean_object* v_fieldId_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_151_, v_fieldId_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_namespaceId_elim___redArg(lean_object* v_t_155_, lean_object* v_namespaceId_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_155_, v_namespaceId_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_namespaceId_elim(lean_object* v_motive_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_namespaceId_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_159_, v_namespaceId_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_option_elim___redArg(lean_object* v_t_163_, lean_object* v_option_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_163_, v_option_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_option_elim(lean_object* v_motive_166_, lean_object* v_t_167_, lean_object* v_h_168_, lean_object* v_option_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_167_, v_option_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_errorName_elim___redArg(lean_object* v_t_171_, lean_object* v_errorName_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_171_, v_errorName_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_errorName_elim(lean_object* v_motive_174_, lean_object* v_t_175_, lean_object* v_h_176_, lean_object* v_errorName_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_175_, v_errorName_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_endSection_elim___redArg(lean_object* v_t_179_, lean_object* v_endSection_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_179_, v_endSection_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_endSection_elim(lean_object* v_motive_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_endSection_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_183_, v_endSection_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_tactic_elim___redArg(lean_object* v_t_187_, lean_object* v_tactic_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_187_, v_tactic_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_tactic_elim(lean_object* v_motive_190_, lean_object* v_t_191_, lean_object* v_h_192_, lean_object* v_tactic_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_191_, v_tactic_193_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFieldInfo_default___closed__0(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_195_ = lean_box(0);
v___x_196_ = lean_obj_once(&l_Lean_Elab_instInhabitedTermInfo_default___closed__2, &l_Lean_Elab_instInhabitedTermInfo_default___closed__2_once, _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__2);
v___x_197_ = l_Lean_instInhabitedLocalContext_default;
v___x_198_ = lean_box(0);
v___x_199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
lean_ctor_set(v___x_199_, 2, v___x_197_);
lean_ctor_set(v___x_199_, 3, v___x_196_);
lean_ctor_set(v___x_199_, 4, v___x_195_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFieldInfo_default(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Lean_Elab_instInhabitedFieldInfo_default___closed__0, &l_Lean_Elab_instInhabitedFieldInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedFieldInfo_default___closed__0);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFieldInfo(void){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Elab_instInhabitedFieldInfo_default;
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__0(void){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__1(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_obj_once(&l_Lean_Elab_instInhabitedTacticInfo_default___closed__0, &l_Lean_Elab_instInhabitedTacticInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__0);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__2(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&l_Lean_Elab_instInhabitedTacticInfo_default___closed__1, &l_Lean_Elab_instInhabitedTacticInfo_default___closed__1_once, _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__1);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
lean_ctor_set(v___x_207_, 2, v___x_206_);
lean_ctor_set(v___x_207_, 3, v___x_206_);
lean_ctor_set(v___x_207_, 4, v___x_205_);
lean_ctor_set(v___x_207_, 5, v___x_205_);
lean_ctor_set(v___x_207_, 6, v___x_205_);
lean_ctor_set(v___x_207_, 7, v___x_205_);
lean_ctor_set(v___x_207_, 8, v___x_205_);
lean_ctor_set(v___x_207_, 9, v___x_205_);
lean_ctor_set(v___x_207_, 10, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__3(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_208_ = lean_box(0);
v___x_209_ = lean_obj_once(&l_Lean_Elab_instInhabitedTacticInfo_default___closed__2, &l_Lean_Elab_instInhabitedTacticInfo_default___closed__2_once, _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__2);
v___x_210_ = ((lean_object*)(l_Lean_Elab_instInhabitedElabInfo_default));
v___x_211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_209_);
lean_ctor_set(v___x_211_, 2, v___x_208_);
lean_ctor_set(v___x_211_, 3, v___x_209_);
lean_ctor_set(v___x_211_, 4, v___x_208_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo_default(void){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lean_obj_once(&l_Lean_Elab_instInhabitedTacticInfo_default___closed__3, &l_Lean_Elab_instInhabitedTacticInfo_default___closed__3_once, _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__3);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo(void){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Elab_instInhabitedTacticInfo_default;
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_box(0);
v___x_215_ = l_Lean_instInhabitedLocalContext_default;
v___x_216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_214_);
lean_ctor_set(v___x_216_, 2, v___x_214_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0, &l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo(void){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Elab_instInhabitedMacroExpansionInfo_default;
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorIdx___impl(uint8_t v_x_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_box(v_x_224_);
v___x_226_ = lean_obj_tag_nat(v___x_225_);
lean_dec(v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorIdx___impl___boxed(lean_object* v_x_227_){
_start:
{
uint8_t v_x_4__boxed_228_; lean_object* v_res_229_; 
v_x_4__boxed_228_ = lean_unbox(v_x_227_);
v_res_229_ = l_Lean_Elab_DocElabKind_ctorIdx___impl(v_x_4__boxed_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___redArg(lean_object* v_k_230_){
_start:
{
lean_inc(v_k_230_);
return v_k_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___redArg___boxed(lean_object* v_k_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Elab_DocElabKind_ctorElim___redArg(v_k_231_);
lean_dec(v_k_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim(lean_object* v_motive_233_, lean_object* v_ctorIdx_234_, uint8_t v_t_235_, lean_object* v_h_236_, lean_object* v_k_237_){
_start:
{
lean_inc(v_k_237_);
return v_k_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___boxed(lean_object* v_motive_238_, lean_object* v_ctorIdx_239_, lean_object* v_t_240_, lean_object* v_h_241_, lean_object* v_k_242_){
_start:
{
uint8_t v_t_boxed_243_; lean_object* v_res_244_; 
v_t_boxed_243_ = lean_unbox(v_t_240_);
v_res_244_ = l_Lean_Elab_DocElabKind_ctorElim(v_motive_238_, v_ctorIdx_239_, v_t_boxed_243_, v_h_241_, v_k_242_);
lean_dec(v_k_242_);
lean_dec(v_ctorIdx_239_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___redArg(lean_object* v_role_245_){
_start:
{
lean_inc(v_role_245_);
return v_role_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___redArg___boxed(lean_object* v_role_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Elab_DocElabKind_role_elim___redArg(v_role_246_);
lean_dec(v_role_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim(lean_object* v_motive_248_, uint8_t v_t_249_, lean_object* v_h_250_, lean_object* v_role_251_){
_start:
{
lean_inc(v_role_251_);
return v_role_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___boxed(lean_object* v_motive_252_, lean_object* v_t_253_, lean_object* v_h_254_, lean_object* v_role_255_){
_start:
{
uint8_t v_t_boxed_256_; lean_object* v_res_257_; 
v_t_boxed_256_ = lean_unbox(v_t_253_);
v_res_257_ = l_Lean_Elab_DocElabKind_role_elim(v_motive_252_, v_t_boxed_256_, v_h_254_, v_role_255_);
lean_dec(v_role_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___redArg(lean_object* v_codeBlock_258_){
_start:
{
lean_inc(v_codeBlock_258_);
return v_codeBlock_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___redArg___boxed(lean_object* v_codeBlock_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Elab_DocElabKind_codeBlock_elim___redArg(v_codeBlock_259_);
lean_dec(v_codeBlock_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim(lean_object* v_motive_261_, uint8_t v_t_262_, lean_object* v_h_263_, lean_object* v_codeBlock_264_){
_start:
{
lean_inc(v_codeBlock_264_);
return v_codeBlock_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___boxed(lean_object* v_motive_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_codeBlock_268_){
_start:
{
uint8_t v_t_boxed_269_; lean_object* v_res_270_; 
v_t_boxed_269_ = lean_unbox(v_t_266_);
v_res_270_ = l_Lean_Elab_DocElabKind_codeBlock_elim(v_motive_265_, v_t_boxed_269_, v_h_267_, v_codeBlock_268_);
lean_dec(v_codeBlock_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___redArg(lean_object* v_directive_271_){
_start:
{
lean_inc(v_directive_271_);
return v_directive_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___redArg___boxed(lean_object* v_directive_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Elab_DocElabKind_directive_elim___redArg(v_directive_272_);
lean_dec(v_directive_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim(lean_object* v_motive_274_, uint8_t v_t_275_, lean_object* v_h_276_, lean_object* v_directive_277_){
_start:
{
lean_inc(v_directive_277_);
return v_directive_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___boxed(lean_object* v_motive_278_, lean_object* v_t_279_, lean_object* v_h_280_, lean_object* v_directive_281_){
_start:
{
uint8_t v_t_boxed_282_; lean_object* v_res_283_; 
v_t_boxed_282_ = lean_unbox(v_t_279_);
v_res_283_ = l_Lean_Elab_DocElabKind_directive_elim(v_motive_278_, v_t_boxed_282_, v_h_280_, v_directive_281_);
lean_dec(v_directive_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___redArg(lean_object* v_command_284_){
_start:
{
lean_inc(v_command_284_);
return v_command_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___redArg___boxed(lean_object* v_command_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Elab_DocElabKind_command_elim___redArg(v_command_285_);
lean_dec(v_command_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim(lean_object* v_motive_287_, uint8_t v_t_288_, lean_object* v_h_289_, lean_object* v_command_290_){
_start:
{
lean_inc(v_command_290_);
return v_command_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___boxed(lean_object* v_motive_291_, lean_object* v_t_292_, lean_object* v_h_293_, lean_object* v_command_294_){
_start:
{
uint8_t v_t_boxed_295_; lean_object* v_res_296_; 
v_t_boxed_295_ = lean_unbox(v_t_292_);
v_res_296_ = l_Lean_Elab_DocElabKind_command_elim(v_motive_291_, v_t_boxed_295_, v_h_293_, v_command_294_);
lean_dec(v_command_294_);
return v_res_296_;
}
}
static lean_object* _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(2u);
v___x_310_ = lean_nat_to_int(v___x_309_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_to_int(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprDocElabKind_repr(uint8_t v_x_313_, lean_object* v_prec_314_){
_start:
{
lean_object* v___y_316_; lean_object* v___y_323_; lean_object* v___y_330_; lean_object* v___y_337_; 
switch(v_x_313_)
{
case 0:
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(1024u);
v___x_344_ = lean_nat_dec_le(v___x_343_, v_prec_314_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
v___x_345_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_316_ = v___x_345_;
goto v___jp_315_;
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_316_ = v___x_346_;
goto v___jp_315_;
}
}
case 1:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1024u);
v___x_348_ = lean_nat_dec_le(v___x_347_, v_prec_314_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
v___x_349_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_323_ = v___x_349_;
goto v___jp_322_;
}
else
{
lean_object* v___x_350_; 
v___x_350_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_323_ = v___x_350_;
goto v___jp_322_;
}
}
case 2:
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = lean_unsigned_to_nat(1024u);
v___x_352_ = lean_nat_dec_le(v___x_351_, v_prec_314_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
v___x_353_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_330_ = v___x_353_;
goto v___jp_329_;
}
else
{
lean_object* v___x_354_; 
v___x_354_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_330_ = v___x_354_;
goto v___jp_329_;
}
}
default: 
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = lean_unsigned_to_nat(1024u);
v___x_356_ = lean_nat_dec_le(v___x_355_, v_prec_314_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_337_ = v___x_357_;
goto v___jp_336_;
}
else
{
lean_object* v___x_358_; 
v___x_358_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_337_ = v___x_358_;
goto v___jp_336_;
}
}
}
v___jp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_317_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__1));
lean_inc(v___y_316_);
v___x_318_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_318_, 0, v___y_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = 0;
v___x_320_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set_uint8(v___x_320_, sizeof(void*)*1, v___x_319_);
v___x_321_ = l_Repr_addAppParen(v___x_320_, v_prec_314_);
return v___x_321_;
}
v___jp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_324_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__3));
lean_inc(v___y_323_);
v___x_325_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_325_, 0, v___y_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = 0;
v___x_327_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*1, v___x_326_);
v___x_328_ = l_Repr_addAppParen(v___x_327_, v_prec_314_);
return v___x_328_;
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_331_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__5));
lean_inc(v___y_330_);
v___x_332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_332_, 0, v___y_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = 0;
v___x_334_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*1, v___x_333_);
v___x_335_ = l_Repr_addAppParen(v___x_334_, v_prec_314_);
return v___x_335_;
}
v___jp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_338_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__7));
lean_inc(v___y_337_);
v___x_339_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_339_, 0, v___y_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = 0;
v___x_341_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set_uint8(v___x_341_, sizeof(void*)*1, v___x_340_);
v___x_342_ = l_Repr_addAppParen(v___x_341_, v_prec_314_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprDocElabKind_repr___boxed(lean_object* v_x_359_, lean_object* v_prec_360_){
_start:
{
uint8_t v_x_225__boxed_361_; lean_object* v_res_362_; 
v_x_225__boxed_361_ = lean_unbox(v_x_359_);
v_res_362_ = l_Lean_Elab_instReprDocElabKind_repr(v_x_225__boxed_361_, v_prec_360_);
lean_dec(v_prec_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx___impl(lean_object* v_x_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_obj_tag_nat(v_x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx___impl___boxed(lean_object* v_x_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Elab_Info_ctorIdx___impl(v_x_367_);
lean_dec_ref(v_x_367_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim___redArg(lean_object* v_t_369_, lean_object* v_k_370_){
_start:
{
if (lean_obj_tag(v_t_369_) == 12)
{
lean_object* v_i_371_; lean_object* v___x_372_; 
v_i_371_ = lean_ctor_get(v_t_369_, 0);
lean_inc(v_i_371_);
lean_dec_ref_known(v_t_369_, 1);
v___x_372_ = lean_apply_1(v_k_370_, v_i_371_);
return v___x_372_;
}
else
{
lean_object* v_i_373_; lean_object* v___x_374_; 
v_i_373_ = lean_ctor_get(v_t_369_, 0);
lean_inc_ref(v_i_373_);
lean_dec_ref(v_t_369_);
v___x_374_ = lean_apply_1(v_k_370_, v_i_373_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim(lean_object* v_motive_375_, lean_object* v_ctorIdx_376_, lean_object* v_t_377_, lean_object* v_h_378_, lean_object* v_k_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_377_, v_k_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim___boxed(lean_object* v_motive_381_, lean_object* v_ctorIdx_382_, lean_object* v_t_383_, lean_object* v_h_384_, lean_object* v_k_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Elab_Info_ctorElim(v_motive_381_, v_ctorIdx_382_, v_t_383_, v_h_384_, v_k_385_);
lean_dec(v_ctorIdx_382_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTacticInfo_elim___redArg(lean_object* v_t_387_, lean_object* v_ofTacticInfo_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_387_, v_ofTacticInfo_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTacticInfo_elim(lean_object* v_motive_390_, lean_object* v_t_391_, lean_object* v_h_392_, lean_object* v_ofTacticInfo_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_391_, v_ofTacticInfo_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTermInfo_elim___redArg(lean_object* v_t_395_, lean_object* v_ofTermInfo_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_395_, v_ofTermInfo_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTermInfo_elim(lean_object* v_motive_398_, lean_object* v_t_399_, lean_object* v_h_400_, lean_object* v_ofTermInfo_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_399_, v_ofTermInfo_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofPartialTermInfo_elim___redArg(lean_object* v_t_403_, lean_object* v_ofPartialTermInfo_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_403_, v_ofPartialTermInfo_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofPartialTermInfo_elim(lean_object* v_motive_406_, lean_object* v_t_407_, lean_object* v_h_408_, lean_object* v_ofPartialTermInfo_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_407_, v_ofPartialTermInfo_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCommandInfo_elim___redArg(lean_object* v_t_411_, lean_object* v_ofCommandInfo_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_411_, v_ofCommandInfo_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCommandInfo_elim(lean_object* v_motive_414_, lean_object* v_t_415_, lean_object* v_h_416_, lean_object* v_ofCommandInfo_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_415_, v_ofCommandInfo_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofMacroExpansionInfo_elim___redArg(lean_object* v_t_419_, lean_object* v_ofMacroExpansionInfo_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_419_, v_ofMacroExpansionInfo_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofMacroExpansionInfo_elim(lean_object* v_motive_422_, lean_object* v_t_423_, lean_object* v_h_424_, lean_object* v_ofMacroExpansionInfo_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_423_, v_ofMacroExpansionInfo_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofOptionInfo_elim___redArg(lean_object* v_t_427_, lean_object* v_ofOptionInfo_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_427_, v_ofOptionInfo_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofOptionInfo_elim(lean_object* v_motive_430_, lean_object* v_t_431_, lean_object* v_h_432_, lean_object* v_ofOptionInfo_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_431_, v_ofOptionInfo_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofErrorNameInfo_elim___redArg(lean_object* v_t_435_, lean_object* v_ofErrorNameInfo_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_435_, v_ofErrorNameInfo_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofErrorNameInfo_elim(lean_object* v_motive_438_, lean_object* v_t_439_, lean_object* v_h_440_, lean_object* v_ofErrorNameInfo_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_439_, v_ofErrorNameInfo_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldInfo_elim___redArg(lean_object* v_t_443_, lean_object* v_ofFieldInfo_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_443_, v_ofFieldInfo_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldInfo_elim(lean_object* v_motive_446_, lean_object* v_t_447_, lean_object* v_h_448_, lean_object* v_ofFieldInfo_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_447_, v_ofFieldInfo_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCompletionInfo_elim___redArg(lean_object* v_t_451_, lean_object* v_ofCompletionInfo_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_451_, v_ofCompletionInfo_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCompletionInfo_elim(lean_object* v_motive_454_, lean_object* v_t_455_, lean_object* v_h_456_, lean_object* v_ofCompletionInfo_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_455_, v_ofCompletionInfo_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofUserWidgetInfo_elim___redArg(lean_object* v_t_459_, lean_object* v_ofUserWidgetInfo_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_459_, v_ofUserWidgetInfo_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofUserWidgetInfo_elim(lean_object* v_motive_462_, lean_object* v_t_463_, lean_object* v_h_464_, lean_object* v_ofUserWidgetInfo_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_463_, v_ofUserWidgetInfo_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCustomInfo_elim___redArg(lean_object* v_t_467_, lean_object* v_ofCustomInfo_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_467_, v_ofCustomInfo_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCustomInfo_elim(lean_object* v_motive_470_, lean_object* v_t_471_, lean_object* v_h_472_, lean_object* v_ofCustomInfo_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_471_, v_ofCustomInfo_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFVarAliasInfo_elim___redArg(lean_object* v_t_475_, lean_object* v_ofFVarAliasInfo_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_475_, v_ofFVarAliasInfo_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFVarAliasInfo_elim(lean_object* v_motive_478_, lean_object* v_t_479_, lean_object* v_h_480_, lean_object* v_ofFVarAliasInfo_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_479_, v_ofFVarAliasInfo_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldRedeclInfo_elim___redArg(lean_object* v_t_483_, lean_object* v_ofFieldRedeclInfo_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_483_, v_ofFieldRedeclInfo_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldRedeclInfo_elim(lean_object* v_motive_486_, lean_object* v_t_487_, lean_object* v_h_488_, lean_object* v_ofFieldRedeclInfo_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_487_, v_ofFieldRedeclInfo_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDelabTermInfo_elim___redArg(lean_object* v_t_491_, lean_object* v_ofDelabTermInfo_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_491_, v_ofDelabTermInfo_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDelabTermInfo_elim(lean_object* v_motive_494_, lean_object* v_t_495_, lean_object* v_h_496_, lean_object* v_ofDelabTermInfo_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_495_, v_ofDelabTermInfo_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceInfo_elim___redArg(lean_object* v_t_499_, lean_object* v_ofChoiceInfo_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_499_, v_ofChoiceInfo_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceInfo_elim(lean_object* v_motive_502_, lean_object* v_t_503_, lean_object* v_h_504_, lean_object* v_ofChoiceInfo_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_503_, v_ofChoiceInfo_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceResolutionInfo_elim___redArg(lean_object* v_t_507_, lean_object* v_ofChoiceResolutionInfo_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_507_, v_ofChoiceResolutionInfo_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceResolutionInfo_elim(lean_object* v_motive_510_, lean_object* v_t_511_, lean_object* v_h_512_, lean_object* v_ofChoiceResolutionInfo_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_511_, v_ofChoiceResolutionInfo_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocInfo_elim___redArg(lean_object* v_t_515_, lean_object* v_ofDocInfo_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_515_, v_ofDocInfo_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocInfo_elim(lean_object* v_motive_518_, lean_object* v_t_519_, lean_object* v_h_520_, lean_object* v_ofDocInfo_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_519_, v_ofDocInfo_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocElabInfo_elim___redArg(lean_object* v_t_523_, lean_object* v_ofDocElabInfo_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_523_, v_ofDocElabInfo_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocElabInfo_elim(lean_object* v_motive_526_, lean_object* v_t_527_, lean_object* v_h_528_, lean_object* v_ofDocElabInfo_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_527_, v_ofDocElabInfo_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo_default___closed__0(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = l_Lean_Elab_instInhabitedTacticInfo_default;
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo_default(void){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfo_default___closed__0, &l_Lean_Elab_instInhabitedInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedInfo_default___closed__0);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo(void){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Elab_instInhabitedInfo_default;
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx___impl(lean_object* v_x_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = lean_obj_tag_nat(v_x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx___impl___boxed(lean_object* v_x_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Elab_InfoTree_ctorIdx___impl(v_x_537_);
lean_dec_ref(v_x_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim___redArg(lean_object* v_t_539_, lean_object* v_k_540_){
_start:
{
if (lean_obj_tag(v_t_539_) == 2)
{
lean_object* v_mvarId_541_; lean_object* v___x_542_; 
v_mvarId_541_ = lean_ctor_get(v_t_539_, 0);
lean_inc(v_mvarId_541_);
lean_dec_ref_known(v_t_539_, 1);
v___x_542_ = lean_apply_1(v_k_540_, v_mvarId_541_);
return v___x_542_;
}
else
{
lean_object* v_i_543_; lean_object* v_t_544_; lean_object* v___x_545_; 
v_i_543_ = lean_ctor_get(v_t_539_, 0);
lean_inc_ref(v_i_543_);
v_t_544_ = lean_ctor_get(v_t_539_, 1);
lean_inc_ref(v_t_544_);
lean_dec_ref(v_t_539_);
v___x_545_ = lean_apply_2(v_k_540_, v_i_543_, v_t_544_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim(lean_object* v_motive__1_546_, lean_object* v_ctorIdx_547_, lean_object* v_t_548_, lean_object* v_h_549_, lean_object* v_k_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_548_, v_k_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim___boxed(lean_object* v_motive__1_552_, lean_object* v_ctorIdx_553_, lean_object* v_t_554_, lean_object* v_h_555_, lean_object* v_k_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Elab_InfoTree_ctorElim(v_motive__1_552_, v_ctorIdx_553_, v_t_554_, v_h_555_, v_k_556_);
lean_dec(v_ctorIdx_553_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_context_elim___redArg(lean_object* v_t_558_, lean_object* v_context_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_558_, v_context_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_context_elim(lean_object* v_motive__1_561_, lean_object* v_t_562_, lean_object* v_h_563_, lean_object* v_context_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_562_, v_context_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_node_elim___redArg(lean_object* v_t_566_, lean_object* v_node_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_566_, v_node_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_node_elim(lean_object* v_motive__1_569_, lean_object* v_t_570_, lean_object* v_h_571_, lean_object* v_node_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_570_, v_node_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hole_elim___redArg(lean_object* v_t_574_, lean_object* v_hole_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_574_, v_hole_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hole_elim(lean_object* v_motive__1_577_, lean_object* v_t_578_, lean_object* v_h_579_, lean_object* v_hole_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_578_, v_hole_580_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__0(void){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__1(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoTree_default___closed__0, &l_Lean_Elab_instInhabitedInfoTree_default___closed__0_once, _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__0);
v___x_584_ = l_Lean_Elab_instInhabitedInfo_default;
v___x_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___x_583_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree_default(void){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoTree_default___closed__1, &l_Lean_Elab_instInhabitedInfoTree_default___closed__1_once, _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__1);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree(void){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Elab_instInhabitedInfoTree_default;
return v___x_587_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__0(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_obj_once(&l_Lean_Elab_instInhabitedTacticInfo_default___closed__0, &l_Lean_Elab_instInhabitedTacticInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__0);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__1(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_unsigned_to_nat(32u);
v___x_591_ = lean_mk_empty_array_with_capacity(v___x_590_);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__2(void){
_start:
{
size_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_593_ = ((size_t)5ULL);
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = lean_unsigned_to_nat(32u);
v___x_596_ = lean_mk_empty_array_with_capacity(v___x_595_);
v___x_597_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__1, &l_Lean_Elab_instInhabitedInfoState_default___closed__1_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__1);
v___x_598_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___x_596_);
lean_ctor_set(v___x_598_, 2, v___x_594_);
lean_ctor_set(v___x_598_, 3, v___x_594_);
lean_ctor_set_usize(v___x_598_, 4, v___x_593_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__3(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; lean_object* v___x_602_; 
v___x_599_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__2, &l_Lean_Elab_instInhabitedInfoState_default___closed__2_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__2);
v___x_600_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__0, &l_Lean_Elab_instInhabitedInfoState_default___closed__0_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__0);
v___x_601_ = 1;
v___x_602_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_600_);
lean_ctor_set(v___x_602_, 2, v___x_599_);
lean_ctor_set_uint8(v___x_602_, sizeof(void*)*3, v___x_601_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default(void){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__3, &l_Lean_Elab_instInhabitedInfoState_default___closed__3_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__3);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState(void){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Elab_instInhabitedInfoState_default;
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0(lean_object* v_modifyInfoState_605_, lean_object* v_inst_606_, lean_object* v_f_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_apply_1(v_modifyInfoState_605_, v_f_607_);
v___x_609_ = lean_apply_2(v_inst_606_, lean_box(0), v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(lean_object* v_inst_610_, lean_object* v_inst_611_){
_start:
{
lean_object* v_getInfoState_612_; lean_object* v_modifyInfoState_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_622_; 
v_getInfoState_612_ = lean_ctor_get(v_inst_611_, 0);
v_modifyInfoState_613_ = lean_ctor_get(v_inst_611_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v_inst_611_);
if (v_isSharedCheck_622_ == 0)
{
v___x_615_ = v_inst_611_;
v_isShared_616_ = v_isSharedCheck_622_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_modifyInfoState_613_);
lean_inc(v_getInfoState_612_);
lean_dec(v_inst_611_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_622_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___f_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
lean_inc(v_inst_610_);
v___f_617_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_617_, 0, v_modifyInfoState_613_);
lean_closure_set(v___f_617_, 1, v_inst_610_);
v___x_618_ = lean_apply_2(v_inst_610_, lean_box(0), v_getInfoState_612_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 1, v___f_617_);
lean_ctor_set(v___x_615_, 0, v___x_618_);
v___x_620_ = v___x_615_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v___f_617_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift(lean_object* v_m_623_, lean_object* v_n_624_, lean_object* v_inst_625_, lean_object* v_inst_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v_inst_625_, v_inst_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg___lam__0(lean_object* v_s_628_, lean_object* v_x_629_){
_start:
{
lean_inc_ref(v_s_628_);
return v_s_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg___lam__0___boxed(lean_object* v_s_630_, lean_object* v_x_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Elab_setInfoState___redArg___lam__0(v_s_630_, v_x_631_);
lean_dec_ref(v_x_631_);
lean_dec_ref(v_s_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg(lean_object* v_inst_633_, lean_object* v_s_634_){
_start:
{
lean_object* v_modifyInfoState_635_; lean_object* v___f_636_; lean_object* v___x_637_; 
v_modifyInfoState_635_ = lean_ctor_get(v_inst_633_, 1);
lean_inc(v_modifyInfoState_635_);
lean_dec_ref(v_inst_633_);
v___f_636_ = lean_alloc_closure((void*)(l_Lean_Elab_setInfoState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_636_, 0, v_s_634_);
v___x_637_ = lean_apply_1(v_modifyInfoState_635_, v___f_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState(lean_object* v_m_638_, lean_object* v_inst_639_, lean_object* v_s_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_Elab_setInfoState___redArg(v_inst_639_, v_s_640_);
return v___x_641_;
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
