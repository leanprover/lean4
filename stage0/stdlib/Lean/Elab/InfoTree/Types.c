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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_205_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_206_ = lean_obj_once(&l_Lean_Elab_instInhabitedTacticInfo_default___closed__1, &l_Lean_Elab_instInhabitedTacticInfo_default___closed__1_once, _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__1);
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
lean_ctor_set(v___x_208_, 2, v___x_207_);
lean_ctor_set(v___x_208_, 3, v___x_207_);
lean_ctor_set(v___x_208_, 4, v___x_206_);
lean_ctor_set(v___x_208_, 5, v___x_206_);
lean_ctor_set(v___x_208_, 6, v___x_206_);
lean_ctor_set(v___x_208_, 7, v___x_206_);
lean_ctor_set(v___x_208_, 8, v___x_206_);
lean_ctor_set(v___x_208_, 9, v___x_206_);
lean_ctor_set(v___x_208_, 10, v___x_206_);
lean_ctor_set(v___x_208_, 11, v___x_205_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__3(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_209_ = lean_box(0);
v___x_210_ = lean_obj_once(&l_Lean_Elab_instInhabitedTacticInfo_default___closed__2, &l_Lean_Elab_instInhabitedTacticInfo_default___closed__2_once, _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__2);
v___x_211_ = ((lean_object*)(l_Lean_Elab_instInhabitedElabInfo_default));
v___x_212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
lean_ctor_set(v___x_212_, 2, v___x_209_);
lean_ctor_set(v___x_212_, 3, v___x_210_);
lean_ctor_set(v___x_212_, 4, v___x_209_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo_default(void){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_obj_once(&l_Lean_Elab_instInhabitedTacticInfo_default___closed__3, &l_Lean_Elab_instInhabitedTacticInfo_default___closed__3_once, _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__3);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo(void){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Elab_instInhabitedTacticInfo_default;
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_box(0);
v___x_216_ = l_Lean_instInhabitedLocalContext_default;
v___x_217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_215_);
lean_ctor_set(v___x_217_, 2, v___x_215_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default(void){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0, &l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo(void){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Elab_instInhabitedMacroExpansionInfo_default;
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorIdx___impl(uint8_t v_x_225_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_box(v_x_225_);
v___x_227_ = lean_obj_tag_nat(v___x_226_);
lean_dec(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorIdx___impl___boxed(lean_object* v_x_228_){
_start:
{
uint8_t v_x_4__boxed_229_; lean_object* v_res_230_; 
v_x_4__boxed_229_ = lean_unbox(v_x_228_);
v_res_230_ = l_Lean_Elab_DocElabKind_ctorIdx___impl(v_x_4__boxed_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___redArg(lean_object* v_k_231_){
_start:
{
lean_inc(v_k_231_);
return v_k_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___redArg___boxed(lean_object* v_k_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Elab_DocElabKind_ctorElim___redArg(v_k_232_);
lean_dec(v_k_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim(lean_object* v_motive_234_, lean_object* v_ctorIdx_235_, uint8_t v_t_236_, lean_object* v_h_237_, lean_object* v_k_238_){
_start:
{
lean_inc(v_k_238_);
return v_k_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_ctorElim___boxed(lean_object* v_motive_239_, lean_object* v_ctorIdx_240_, lean_object* v_t_241_, lean_object* v_h_242_, lean_object* v_k_243_){
_start:
{
uint8_t v_t_boxed_244_; lean_object* v_res_245_; 
v_t_boxed_244_ = lean_unbox(v_t_241_);
v_res_245_ = l_Lean_Elab_DocElabKind_ctorElim(v_motive_239_, v_ctorIdx_240_, v_t_boxed_244_, v_h_242_, v_k_243_);
lean_dec(v_k_243_);
lean_dec(v_ctorIdx_240_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___redArg(lean_object* v_role_246_){
_start:
{
lean_inc(v_role_246_);
return v_role_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___redArg___boxed(lean_object* v_role_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Elab_DocElabKind_role_elim___redArg(v_role_247_);
lean_dec(v_role_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim(lean_object* v_motive_249_, uint8_t v_t_250_, lean_object* v_h_251_, lean_object* v_role_252_){
_start:
{
lean_inc(v_role_252_);
return v_role_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_role_elim___boxed(lean_object* v_motive_253_, lean_object* v_t_254_, lean_object* v_h_255_, lean_object* v_role_256_){
_start:
{
uint8_t v_t_boxed_257_; lean_object* v_res_258_; 
v_t_boxed_257_ = lean_unbox(v_t_254_);
v_res_258_ = l_Lean_Elab_DocElabKind_role_elim(v_motive_253_, v_t_boxed_257_, v_h_255_, v_role_256_);
lean_dec(v_role_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___redArg(lean_object* v_codeBlock_259_){
_start:
{
lean_inc(v_codeBlock_259_);
return v_codeBlock_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___redArg___boxed(lean_object* v_codeBlock_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Elab_DocElabKind_codeBlock_elim___redArg(v_codeBlock_260_);
lean_dec(v_codeBlock_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim(lean_object* v_motive_262_, uint8_t v_t_263_, lean_object* v_h_264_, lean_object* v_codeBlock_265_){
_start:
{
lean_inc(v_codeBlock_265_);
return v_codeBlock_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_codeBlock_elim___boxed(lean_object* v_motive_266_, lean_object* v_t_267_, lean_object* v_h_268_, lean_object* v_codeBlock_269_){
_start:
{
uint8_t v_t_boxed_270_; lean_object* v_res_271_; 
v_t_boxed_270_ = lean_unbox(v_t_267_);
v_res_271_ = l_Lean_Elab_DocElabKind_codeBlock_elim(v_motive_266_, v_t_boxed_270_, v_h_268_, v_codeBlock_269_);
lean_dec(v_codeBlock_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___redArg(lean_object* v_directive_272_){
_start:
{
lean_inc(v_directive_272_);
return v_directive_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___redArg___boxed(lean_object* v_directive_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Elab_DocElabKind_directive_elim___redArg(v_directive_273_);
lean_dec(v_directive_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim(lean_object* v_motive_275_, uint8_t v_t_276_, lean_object* v_h_277_, lean_object* v_directive_278_){
_start:
{
lean_inc(v_directive_278_);
return v_directive_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_directive_elim___boxed(lean_object* v_motive_279_, lean_object* v_t_280_, lean_object* v_h_281_, lean_object* v_directive_282_){
_start:
{
uint8_t v_t_boxed_283_; lean_object* v_res_284_; 
v_t_boxed_283_ = lean_unbox(v_t_280_);
v_res_284_ = l_Lean_Elab_DocElabKind_directive_elim(v_motive_279_, v_t_boxed_283_, v_h_281_, v_directive_282_);
lean_dec(v_directive_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___redArg(lean_object* v_command_285_){
_start:
{
lean_inc(v_command_285_);
return v_command_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___redArg___boxed(lean_object* v_command_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Elab_DocElabKind_command_elim___redArg(v_command_286_);
lean_dec(v_command_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim(lean_object* v_motive_288_, uint8_t v_t_289_, lean_object* v_h_290_, lean_object* v_command_291_){
_start:
{
lean_inc(v_command_291_);
return v_command_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabKind_command_elim___boxed(lean_object* v_motive_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_command_295_){
_start:
{
uint8_t v_t_boxed_296_; lean_object* v_res_297_; 
v_t_boxed_296_ = lean_unbox(v_t_293_);
v_res_297_ = l_Lean_Elab_DocElabKind_command_elim(v_motive_292_, v_t_boxed_296_, v_h_294_, v_command_295_);
lean_dec(v_command_295_);
return v_res_297_;
}
}
static lean_object* _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_unsigned_to_nat(2u);
v___x_311_ = lean_nat_to_int(v___x_310_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_to_int(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprDocElabKind_repr(uint8_t v_x_314_, lean_object* v_prec_315_){
_start:
{
lean_object* v___y_317_; lean_object* v___y_324_; lean_object* v___y_331_; lean_object* v___y_338_; 
switch(v_x_314_)
{
case 0:
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(1024u);
v___x_345_ = lean_nat_dec_le(v___x_344_, v_prec_315_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
v___x_346_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_317_ = v___x_346_;
goto v___jp_316_;
}
else
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_317_ = v___x_347_;
goto v___jp_316_;
}
}
case 1:
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(1024u);
v___x_349_ = lean_nat_dec_le(v___x_348_, v_prec_315_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
v___x_350_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_324_ = v___x_350_;
goto v___jp_323_;
}
else
{
lean_object* v___x_351_; 
v___x_351_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_324_ = v___x_351_;
goto v___jp_323_;
}
}
case 2:
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(1024u);
v___x_353_ = lean_nat_dec_le(v___x_352_, v_prec_315_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; 
v___x_354_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_331_ = v___x_354_;
goto v___jp_330_;
}
else
{
lean_object* v___x_355_; 
v___x_355_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_331_ = v___x_355_;
goto v___jp_330_;
}
}
default: 
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_unsigned_to_nat(1024u);
v___x_357_ = lean_nat_dec_le(v___x_356_, v_prec_315_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
v___x_358_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__8, &l_Lean_Elab_instReprDocElabKind_repr___closed__8_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8);
v___y_338_ = v___x_358_;
goto v___jp_337_;
}
else
{
lean_object* v___x_359_; 
v___x_359_ = lean_obj_once(&l_Lean_Elab_instReprDocElabKind_repr___closed__9, &l_Lean_Elab_instReprDocElabKind_repr___closed__9_once, _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9);
v___y_338_ = v___x_359_;
goto v___jp_337_;
}
}
}
v___jp_316_:
{
lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_318_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__1));
lean_inc(v___y_317_);
v___x_319_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_319_, 0, v___y_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = 0;
v___x_321_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set_uint8(v___x_321_, sizeof(void*)*1, v___x_320_);
v___x_322_ = l_Repr_addAppParen(v___x_321_, v_prec_315_);
return v___x_322_;
}
v___jp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_325_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__3));
lean_inc(v___y_324_);
v___x_326_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_326_, 0, v___y_324_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = 0;
v___x_328_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set_uint8(v___x_328_, sizeof(void*)*1, v___x_327_);
v___x_329_ = l_Repr_addAppParen(v___x_328_, v_prec_315_);
return v___x_329_;
}
v___jp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_332_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__5));
lean_inc(v___y_331_);
v___x_333_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_333_, 0, v___y_331_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = 0;
v___x_335_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*1, v___x_334_);
v___x_336_ = l_Repr_addAppParen(v___x_335_, v_prec_315_);
return v___x_336_;
}
v___jp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_339_ = ((lean_object*)(l_Lean_Elab_instReprDocElabKind_repr___closed__7));
lean_inc(v___y_338_);
v___x_340_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_340_, 0, v___y_338_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = 0;
v___x_342_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*1, v___x_341_);
v___x_343_ = l_Repr_addAppParen(v___x_342_, v_prec_315_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprDocElabKind_repr___boxed(lean_object* v_x_360_, lean_object* v_prec_361_){
_start:
{
uint8_t v_x_225__boxed_362_; lean_object* v_res_363_; 
v_x_225__boxed_362_ = lean_unbox(v_x_360_);
v_res_363_ = l_Lean_Elab_instReprDocElabKind_repr(v_x_225__boxed_362_, v_prec_361_);
lean_dec(v_prec_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx___impl(lean_object* v_x_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_obj_tag_nat(v_x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx___impl___boxed(lean_object* v_x_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Elab_Info_ctorIdx___impl(v_x_368_);
lean_dec_ref(v_x_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim___redArg(lean_object* v_t_370_, lean_object* v_k_371_){
_start:
{
if (lean_obj_tag(v_t_370_) == 12)
{
lean_object* v_i_372_; lean_object* v___x_373_; 
v_i_372_ = lean_ctor_get(v_t_370_, 0);
lean_inc(v_i_372_);
lean_dec_ref_known(v_t_370_, 1);
v___x_373_ = lean_apply_1(v_k_371_, v_i_372_);
return v___x_373_;
}
else
{
lean_object* v_i_374_; lean_object* v___x_375_; 
v_i_374_ = lean_ctor_get(v_t_370_, 0);
lean_inc_ref(v_i_374_);
lean_dec_ref(v_t_370_);
v___x_375_ = lean_apply_1(v_k_371_, v_i_374_);
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim(lean_object* v_motive_376_, lean_object* v_ctorIdx_377_, lean_object* v_t_378_, lean_object* v_h_379_, lean_object* v_k_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_378_, v_k_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorElim___boxed(lean_object* v_motive_382_, lean_object* v_ctorIdx_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_k_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Elab_Info_ctorElim(v_motive_382_, v_ctorIdx_383_, v_t_384_, v_h_385_, v_k_386_);
lean_dec(v_ctorIdx_383_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTacticInfo_elim___redArg(lean_object* v_t_388_, lean_object* v_ofTacticInfo_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_388_, v_ofTacticInfo_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTacticInfo_elim(lean_object* v_motive_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_ofTacticInfo_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_392_, v_ofTacticInfo_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTermInfo_elim___redArg(lean_object* v_t_396_, lean_object* v_ofTermInfo_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_396_, v_ofTermInfo_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofTermInfo_elim(lean_object* v_motive_399_, lean_object* v_t_400_, lean_object* v_h_401_, lean_object* v_ofTermInfo_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_400_, v_ofTermInfo_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofPartialTermInfo_elim___redArg(lean_object* v_t_404_, lean_object* v_ofPartialTermInfo_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_404_, v_ofPartialTermInfo_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofPartialTermInfo_elim(lean_object* v_motive_407_, lean_object* v_t_408_, lean_object* v_h_409_, lean_object* v_ofPartialTermInfo_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_408_, v_ofPartialTermInfo_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCommandInfo_elim___redArg(lean_object* v_t_412_, lean_object* v_ofCommandInfo_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_412_, v_ofCommandInfo_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCommandInfo_elim(lean_object* v_motive_415_, lean_object* v_t_416_, lean_object* v_h_417_, lean_object* v_ofCommandInfo_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_416_, v_ofCommandInfo_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofMacroExpansionInfo_elim___redArg(lean_object* v_t_420_, lean_object* v_ofMacroExpansionInfo_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_420_, v_ofMacroExpansionInfo_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofMacroExpansionInfo_elim(lean_object* v_motive_423_, lean_object* v_t_424_, lean_object* v_h_425_, lean_object* v_ofMacroExpansionInfo_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_424_, v_ofMacroExpansionInfo_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofOptionInfo_elim___redArg(lean_object* v_t_428_, lean_object* v_ofOptionInfo_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_428_, v_ofOptionInfo_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofOptionInfo_elim(lean_object* v_motive_431_, lean_object* v_t_432_, lean_object* v_h_433_, lean_object* v_ofOptionInfo_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_432_, v_ofOptionInfo_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofErrorNameInfo_elim___redArg(lean_object* v_t_436_, lean_object* v_ofErrorNameInfo_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_436_, v_ofErrorNameInfo_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofErrorNameInfo_elim(lean_object* v_motive_439_, lean_object* v_t_440_, lean_object* v_h_441_, lean_object* v_ofErrorNameInfo_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_440_, v_ofErrorNameInfo_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldInfo_elim___redArg(lean_object* v_t_444_, lean_object* v_ofFieldInfo_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_444_, v_ofFieldInfo_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldInfo_elim(lean_object* v_motive_447_, lean_object* v_t_448_, lean_object* v_h_449_, lean_object* v_ofFieldInfo_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_448_, v_ofFieldInfo_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCompletionInfo_elim___redArg(lean_object* v_t_452_, lean_object* v_ofCompletionInfo_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_452_, v_ofCompletionInfo_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCompletionInfo_elim(lean_object* v_motive_455_, lean_object* v_t_456_, lean_object* v_h_457_, lean_object* v_ofCompletionInfo_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_456_, v_ofCompletionInfo_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofUserWidgetInfo_elim___redArg(lean_object* v_t_460_, lean_object* v_ofUserWidgetInfo_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_460_, v_ofUserWidgetInfo_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofUserWidgetInfo_elim(lean_object* v_motive_463_, lean_object* v_t_464_, lean_object* v_h_465_, lean_object* v_ofUserWidgetInfo_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_464_, v_ofUserWidgetInfo_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCustomInfo_elim___redArg(lean_object* v_t_468_, lean_object* v_ofCustomInfo_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_468_, v_ofCustomInfo_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofCustomInfo_elim(lean_object* v_motive_471_, lean_object* v_t_472_, lean_object* v_h_473_, lean_object* v_ofCustomInfo_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_472_, v_ofCustomInfo_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFVarAliasInfo_elim___redArg(lean_object* v_t_476_, lean_object* v_ofFVarAliasInfo_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_476_, v_ofFVarAliasInfo_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFVarAliasInfo_elim(lean_object* v_motive_479_, lean_object* v_t_480_, lean_object* v_h_481_, lean_object* v_ofFVarAliasInfo_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_480_, v_ofFVarAliasInfo_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldRedeclInfo_elim___redArg(lean_object* v_t_484_, lean_object* v_ofFieldRedeclInfo_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_484_, v_ofFieldRedeclInfo_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofFieldRedeclInfo_elim(lean_object* v_motive_487_, lean_object* v_t_488_, lean_object* v_h_489_, lean_object* v_ofFieldRedeclInfo_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_488_, v_ofFieldRedeclInfo_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDelabTermInfo_elim___redArg(lean_object* v_t_492_, lean_object* v_ofDelabTermInfo_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_492_, v_ofDelabTermInfo_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDelabTermInfo_elim(lean_object* v_motive_495_, lean_object* v_t_496_, lean_object* v_h_497_, lean_object* v_ofDelabTermInfo_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_496_, v_ofDelabTermInfo_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceInfo_elim___redArg(lean_object* v_t_500_, lean_object* v_ofChoiceInfo_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_500_, v_ofChoiceInfo_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceInfo_elim(lean_object* v_motive_503_, lean_object* v_t_504_, lean_object* v_h_505_, lean_object* v_ofChoiceInfo_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_504_, v_ofChoiceInfo_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceResolutionInfo_elim___redArg(lean_object* v_t_508_, lean_object* v_ofChoiceResolutionInfo_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_508_, v_ofChoiceResolutionInfo_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofChoiceResolutionInfo_elim(lean_object* v_motive_511_, lean_object* v_t_512_, lean_object* v_h_513_, lean_object* v_ofChoiceResolutionInfo_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_512_, v_ofChoiceResolutionInfo_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocInfo_elim___redArg(lean_object* v_t_516_, lean_object* v_ofDocInfo_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_516_, v_ofDocInfo_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocInfo_elim(lean_object* v_motive_519_, lean_object* v_t_520_, lean_object* v_h_521_, lean_object* v_ofDocInfo_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_520_, v_ofDocInfo_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocElabInfo_elim___redArg(lean_object* v_t_524_, lean_object* v_ofDocElabInfo_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_524_, v_ofDocElabInfo_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ofDocElabInfo_elim(lean_object* v_motive_527_, lean_object* v_t_528_, lean_object* v_h_529_, lean_object* v_ofDocElabInfo_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_528_, v_ofDocElabInfo_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo_default___closed__0(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = l_Lean_Elab_instInhabitedTacticInfo_default;
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo_default(void){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfo_default___closed__0, &l_Lean_Elab_instInhabitedInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedInfo_default___closed__0);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo(void){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Elab_instInhabitedInfo_default;
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx___impl(lean_object* v_x_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = lean_obj_tag_nat(v_x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx___impl___boxed(lean_object* v_x_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Elab_InfoTree_ctorIdx___impl(v_x_538_);
lean_dec_ref(v_x_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim___redArg(lean_object* v_t_540_, lean_object* v_k_541_){
_start:
{
if (lean_obj_tag(v_t_540_) == 2)
{
lean_object* v_mvarId_542_; lean_object* v___x_543_; 
v_mvarId_542_ = lean_ctor_get(v_t_540_, 0);
lean_inc(v_mvarId_542_);
lean_dec_ref_known(v_t_540_, 1);
v___x_543_ = lean_apply_1(v_k_541_, v_mvarId_542_);
return v___x_543_;
}
else
{
lean_object* v_i_544_; lean_object* v_t_545_; lean_object* v___x_546_; 
v_i_544_ = lean_ctor_get(v_t_540_, 0);
lean_inc_ref(v_i_544_);
v_t_545_ = lean_ctor_get(v_t_540_, 1);
lean_inc_ref(v_t_545_);
lean_dec_ref(v_t_540_);
v___x_546_ = lean_apply_2(v_k_541_, v_i_544_, v_t_545_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim(lean_object* v_motive__1_547_, lean_object* v_ctorIdx_548_, lean_object* v_t_549_, lean_object* v_h_550_, lean_object* v_k_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_549_, v_k_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorElim___boxed(lean_object* v_motive__1_553_, lean_object* v_ctorIdx_554_, lean_object* v_t_555_, lean_object* v_h_556_, lean_object* v_k_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Elab_InfoTree_ctorElim(v_motive__1_553_, v_ctorIdx_554_, v_t_555_, v_h_556_, v_k_557_);
lean_dec(v_ctorIdx_554_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_context_elim___redArg(lean_object* v_t_559_, lean_object* v_context_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_559_, v_context_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_context_elim(lean_object* v_motive__1_562_, lean_object* v_t_563_, lean_object* v_h_564_, lean_object* v_context_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_563_, v_context_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_node_elim___redArg(lean_object* v_t_567_, lean_object* v_node_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_567_, v_node_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_node_elim(lean_object* v_motive__1_570_, lean_object* v_t_571_, lean_object* v_h_572_, lean_object* v_node_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_571_, v_node_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hole_elim___redArg(lean_object* v_t_575_, lean_object* v_hole_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_575_, v_hole_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hole_elim(lean_object* v_motive__1_578_, lean_object* v_t_579_, lean_object* v_h_580_, lean_object* v_hole_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_579_, v_hole_581_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__0(void){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_583_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__1(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoTree_default___closed__0, &l_Lean_Elab_instInhabitedInfoTree_default___closed__0_once, _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__0);
v___x_585_ = l_Lean_Elab_instInhabitedInfo_default;
v___x_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree_default(void){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoTree_default___closed__1, &l_Lean_Elab_instInhabitedInfoTree_default___closed__1_once, _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__1);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree(void){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Elab_instInhabitedInfoTree_default;
return v___x_588_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__0(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_obj_once(&l_Lean_Elab_instInhabitedTacticInfo_default___closed__0, &l_Lean_Elab_instInhabitedTacticInfo_default___closed__0_once, _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__0);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__1(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_unsigned_to_nat(32u);
v___x_592_ = lean_mk_empty_array_with_capacity(v___x_591_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__2(void){
_start:
{
size_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_594_ = ((size_t)5ULL);
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_unsigned_to_nat(32u);
v___x_597_ = lean_mk_empty_array_with_capacity(v___x_596_);
v___x_598_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__1, &l_Lean_Elab_instInhabitedInfoState_default___closed__1_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__1);
v___x_599_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v___x_597_);
lean_ctor_set(v___x_599_, 2, v___x_595_);
lean_ctor_set(v___x_599_, 3, v___x_595_);
lean_ctor_set_usize(v___x_599_, 4, v___x_594_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default___closed__3(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; lean_object* v___x_603_; 
v___x_600_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__2, &l_Lean_Elab_instInhabitedInfoState_default___closed__2_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__2);
v___x_601_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__0, &l_Lean_Elab_instInhabitedInfoState_default___closed__0_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__0);
v___x_602_ = 1;
v___x_603_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_601_);
lean_ctor_set(v___x_603_, 2, v___x_600_);
lean_ctor_set_uint8(v___x_603_, sizeof(void*)*3, v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState_default(void){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = lean_obj_once(&l_Lean_Elab_instInhabitedInfoState_default___closed__3, &l_Lean_Elab_instInhabitedInfoState_default___closed__3_once, _init_l_Lean_Elab_instInhabitedInfoState_default___closed__3);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState(void){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Elab_instInhabitedInfoState_default;
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0(lean_object* v_modifyInfoState_606_, lean_object* v_inst_607_, lean_object* v_f_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_apply_1(v_modifyInfoState_606_, v_f_608_);
v___x_610_ = lean_apply_2(v_inst_607_, lean_box(0), v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(lean_object* v_inst_611_, lean_object* v_inst_612_){
_start:
{
lean_object* v_getInfoState_613_; lean_object* v_modifyInfoState_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_623_; 
v_getInfoState_613_ = lean_ctor_get(v_inst_612_, 0);
v_modifyInfoState_614_ = lean_ctor_get(v_inst_612_, 1);
v_isSharedCheck_623_ = !lean_is_exclusive(v_inst_612_);
if (v_isSharedCheck_623_ == 0)
{
v___x_616_ = v_inst_612_;
v_isShared_617_ = v_isSharedCheck_623_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_modifyInfoState_614_);
lean_inc(v_getInfoState_613_);
lean_dec(v_inst_612_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_623_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
lean_inc(v_inst_611_);
v___f_618_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_618_, 0, v_modifyInfoState_614_);
lean_closure_set(v___f_618_, 1, v_inst_611_);
v___x_619_ = lean_apply_2(v_inst_611_, lean_box(0), v_getInfoState_613_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v___f_618_);
lean_ctor_set(v___x_616_, 0, v___x_619_);
v___x_621_ = v___x_616_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v___f_618_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift(lean_object* v_m_624_, lean_object* v_n_625_, lean_object* v_inst_626_, lean_object* v_inst_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v_inst_626_, v_inst_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg___lam__0(lean_object* v_s_629_, lean_object* v_x_630_){
_start:
{
lean_inc_ref(v_s_629_);
return v_s_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg___lam__0___boxed(lean_object* v_s_631_, lean_object* v_x_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Elab_setInfoState___redArg___lam__0(v_s_631_, v_x_632_);
lean_dec_ref(v_x_632_);
lean_dec_ref(v_s_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg(lean_object* v_inst_634_, lean_object* v_s_635_){
_start:
{
lean_object* v_modifyInfoState_636_; lean_object* v___f_637_; lean_object* v___x_638_; 
v_modifyInfoState_636_ = lean_ctor_get(v_inst_634_, 1);
lean_inc(v_modifyInfoState_636_);
lean_dec_ref(v_inst_634_);
v___f_637_ = lean_alloc_closure((void*)(l_Lean_Elab_setInfoState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_637_, 0, v_s_635_);
v___x_638_ = lean_apply_1(v_modifyInfoState_636_, v___f_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState(lean_object* v_m_639_, lean_object* v_inst_640_, lean_object* v_s_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Elab_setInfoState___redArg(v_inst_640_, v_s_641_);
return v___x_642_;
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
