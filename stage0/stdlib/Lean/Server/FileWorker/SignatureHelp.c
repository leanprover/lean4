// Lean compiler output
// Module: Lean.Server.FileWorker.SignatureHelp
// Imports: public import Lean.Server.InfoUtils public import Lean.Data.Lsp public import Init.Data.List.Sort.Basic import Lean.PrettyPrinter.Delaborator
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lineStart(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_findStack_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_mergeSort___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabForallWithSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delabForallWithSignature___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1;
static lean_once_cell_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2;
static lean_once_cell_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3;
static lean_once_cell_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4;
static lean_once_cell_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__6 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pipeProj"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value),LEAN_SCALAR_PTR_LITERAL(104, 78, 204, 170, 128, 130, 207, 24)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_<|_"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value),LEAN_SCALAR_PTR_LITERAL(152, 38, 96, 140, 215, 46, 31, 82)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_$__"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18_value),LEAN_SCALAR_PTR_LITERAL(19, 217, 134, 45, 19, 162, 148, 100)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0_value;
static const lean_closure_object l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
else
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
}
else
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 0;
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v_val_7_; uint8_t v___x_8_; 
v_val_6_ = lean_ctor_get(v_x_1_, 0);
v_val_7_ = lean_ctor_get(v_x_2_, 0);
v___x_8_ = l_Lean_Syntax_instBEqRange_beq(v_val_6_, v_val_7_);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(v_x_9_, v_x_10_);
lean_dec(v_x_10_);
lean_dec(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(lean_object* v_e_13_, lean_object* v___y_14_){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = l_Lean_Expr_hasMVar(v_e_13_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; 
v___x_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_17_, 0, v_e_13_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v_mctx_19_; lean_object* v___x_20_; lean_object* v_fst_21_; lean_object* v_snd_22_; lean_object* v___x_23_; lean_object* v_cache_24_; lean_object* v_zetaDeltaFVarIds_25_; lean_object* v_postponed_26_; lean_object* v_diag_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_36_; 
v___x_18_ = lean_st_ref_get(v___y_14_);
v_mctx_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc_ref(v_mctx_19_);
lean_dec(v___x_18_);
v___x_20_ = l_Lean_instantiateMVarsCore(v_mctx_19_, v_e_13_);
v_fst_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_fst_21_);
v_snd_22_ = lean_ctor_get(v___x_20_, 1);
lean_inc(v_snd_22_);
lean_dec_ref(v___x_20_);
v___x_23_ = lean_st_ref_take(v___y_14_);
v_cache_24_ = lean_ctor_get(v___x_23_, 1);
v_zetaDeltaFVarIds_25_ = lean_ctor_get(v___x_23_, 2);
v_postponed_26_ = lean_ctor_get(v___x_23_, 3);
v_diag_27_ = lean_ctor_get(v___x_23_, 4);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_36_ == 0)
{
lean_object* v_unused_37_; 
v_unused_37_ = lean_ctor_get(v___x_23_, 0);
lean_dec(v_unused_37_);
v___x_29_ = v___x_23_;
v_isShared_30_ = v_isSharedCheck_36_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_diag_27_);
lean_inc(v_postponed_26_);
lean_inc(v_zetaDeltaFVarIds_25_);
lean_inc(v_cache_24_);
lean_dec(v___x_23_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_36_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_32_; 
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 0, v_snd_22_);
v___x_32_ = v___x_29_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_snd_22_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v_cache_24_);
lean_ctor_set(v_reuseFailAlloc_35_, 2, v_zetaDeltaFVarIds_25_);
lean_ctor_set(v_reuseFailAlloc_35_, 3, v_postponed_26_);
lean_ctor_set(v_reuseFailAlloc_35_, 4, v_diag_27_);
v___x_32_ = v_reuseFailAlloc_35_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_st_ref_set(v___y_14_, v___x_32_);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v_fst_21_);
return v___x_34_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg___boxed(lean_object* v_e_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_e_38_, v___y_39_);
lean_dec(v___y_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1(lean_object* v_e_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_e_42_, v___y_44_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___boxed(lean_object* v_e_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1(v_e_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_55_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0(lean_object* v_appStx_56_, lean_object* v_x_57_){
_start:
{
if (lean_obj_tag(v_x_57_) == 1)
{
lean_object* v_i_58_; lean_object* v_toElabInfo_59_; lean_object* v_stx_60_; uint8_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v_i_58_ = lean_ctor_get(v_x_57_, 0);
v_toElabInfo_59_ = lean_ctor_get(v_i_58_, 0);
v_stx_60_ = lean_ctor_get(v_toElabInfo_59_, 1);
v___x_61_ = 0;
v___x_62_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_60_, v___x_61_);
v___x_63_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_appStx_56_, v___x_61_);
v___x_64_ = l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(v___x_62_, v___x_63_);
lean_dec(v___x_63_);
lean_dec(v___x_62_);
return v___x_64_;
}
else
{
uint8_t v___x_65_; 
v___x_65_ = 0;
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0___boxed(lean_object* v_appStx_66_, lean_object* v_x_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0(v_appStx_66_, v_x_67_);
lean_dec_ref(v_x_67_);
lean_dec(v_appStx_66_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1(lean_object* v_expr_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; 
lean_inc(v___y_75_);
lean_inc_ref(v___y_74_);
lean_inc(v___y_73_);
lean_inc_ref(v___y_72_);
v___x_77_ = lean_infer_type(v_expr_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_79_; lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_120_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_a_78_);
lean_dec_ref(v___x_77_);
v___x_79_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_a_78_, v___y_73_);
v_a_80_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_120_ == 0)
{
v___x_82_ = v___x_79_;
v_isShared_83_ = v_isSharedCheck_120_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_79_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_120_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
uint8_t v___x_84_; 
v___x_84_ = l_Lean_Expr_isForall(v_a_80_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_87_; 
lean_dec(v_a_80_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
v___x_85_ = lean_box(0);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_85_);
v___x_87_ = v___x_82_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
else
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
lean_del_object(v___x_82_);
v___x_89_ = lean_box(1);
v___x_90_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___closed__0));
v___x_91_ = l_Lean_PrettyPrinter_delabCore___redArg(v_a_80_, v___x_89_, v___x_90_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v_fst_93_; lean_object* v___x_94_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_a_92_);
lean_dec_ref(v___x_91_);
v_fst_93_ = lean_ctor_get(v_a_92_, 0);
lean_inc(v_fst_93_);
lean_dec(v_a_92_);
v___x_94_ = l_Lean_PrettyPrinter_ppTerm(v_fst_93_, v___y_74_, v___y_75_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_103_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_103_ == 0)
{
v___x_97_ = v___x_94_;
v_isShared_98_ = v_isSharedCheck_103_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_103_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; lean_object* v___x_101_; 
v___x_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_99_, 0, v_a_95_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_99_);
v___x_101_ = v___x_97_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
v_a_104_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_94_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_94_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
v_a_112_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_91_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_91_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
v_a_121_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_77_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_77_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___boxed(lean_object* v_expr_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1(v_expr_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(lean_object* v_tree_138_, lean_object* v_appStx_139_){
_start:
{
lean_object* v___f_144_; lean_object* v___x_145_; 
v___f_144_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0___boxed), 2, 1);
lean_closure_set(v___f_144_, 0, v_appStx_139_);
v___x_145_ = l_Lean_Elab_InfoTree_smallestInfo_x3f(v___f_144_, v_tree_138_);
if (lean_obj_tag(v___x_145_) == 1)
{
lean_object* v_val_146_; lean_object* v_snd_147_; 
v_val_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_val_146_);
lean_dec_ref(v___x_145_);
v_snd_147_ = lean_ctor_get(v_val_146_, 1);
if (lean_obj_tag(v_snd_147_) == 1)
{
lean_object* v_i_148_; lean_object* v_fst_149_; lean_object* v_lctx_150_; lean_object* v_expr_151_; lean_object* v___f_152_; lean_object* v___x_153_; 
v_i_148_ = lean_ctor_get(v_snd_147_, 0);
lean_inc_ref(v_i_148_);
v_fst_149_ = lean_ctor_get(v_val_146_, 0);
lean_inc(v_fst_149_);
lean_dec(v_val_146_);
v_lctx_150_ = lean_ctor_get(v_i_148_, 1);
lean_inc_ref(v_lctx_150_);
v_expr_151_ = lean_ctor_get(v_i_148_, 3);
lean_inc_ref(v_expr_151_);
lean_dec_ref(v_i_148_);
v___f_152_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___boxed), 6, 1);
lean_closure_set(v___f_152_, 0, v_expr_151_);
v___x_153_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_fst_149_, v_lctx_150_, v___f_152_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_183_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_183_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_183_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_183_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
if (lean_obj_tag(v_a_154_) == 1)
{
lean_object* v_val_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_178_; 
v_val_158_ = lean_ctor_get(v_a_154_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v_a_154_);
if (v_isSharedCheck_178_ == 0)
{
v___x_160_ = v_a_154_;
v_isShared_161_ = v_isSharedCheck_178_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_val_158_);
lean_dec(v_a_154_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_178_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_162_ = l_Std_Format_defWidth;
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = l_Std_Format_pretty(v_val_158_, v___x_162_, v___x_163_, v___x_163_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
lean_ctor_set(v___x_166_, 2, v___x_165_);
lean_ctor_set(v___x_166_, 3, v___x_165_);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_mk_empty_array_with_capacity(v___x_167_);
v___x_169_ = lean_array_push(v___x_168_, v___x_166_);
v___x_170_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__0));
v___x_171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
lean_ctor_set(v___x_171_, 2, v___x_165_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v___x_171_);
v___x_173_ = v___x_160_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_177_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_175_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_173_);
v___x_175_ = v___x_156_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
else
{
lean_object* v___x_179_; lean_object* v___x_181_; 
lean_dec(v_a_154_);
v___x_179_ = lean_box(0);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_179_);
v___x_181_ = v___x_156_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
v_a_184_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_153_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_153_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
else
{
lean_dec(v_val_146_);
goto v___jp_141_;
}
}
else
{
lean_dec(v___x_145_);
goto v___jp_141_;
}
v___jp_141_:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_box(0);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___boxed(lean_object* v_tree_192_, lean_object* v_appStx_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_192_, v_appStx_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx(uint8_t v_x_196_){
_start:
{
switch(v_x_196_)
{
case 0:
{
lean_object* v___x_197_; 
v___x_197_ = lean_unsigned_to_nat(0u);
return v___x_197_;
}
case 1:
{
lean_object* v___x_198_; 
v___x_198_ = lean_unsigned_to_nat(1u);
return v___x_198_;
}
default: 
{
lean_object* v___x_199_; 
v___x_199_ = lean_unsigned_to_nat(2u);
return v___x_199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___boxed(lean_object* v_x_200_){
_start:
{
uint8_t v_x_boxed_201_; lean_object* v_res_202_; 
v_x_boxed_201_ = lean_unbox(v_x_200_);
v_res_202_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx(v_x_boxed_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx(uint8_t v_x_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx(v_x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx___boxed(lean_object* v_x_205_){
_start:
{
uint8_t v_x_4__boxed_206_; lean_object* v_res_207_; 
v_x_4__boxed_206_ = lean_unbox(v_x_205_);
v_res_207_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx(v_x_4__boxed_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(lean_object* v_k_208_){
_start:
{
lean_inc(v_k_208_);
return v_k_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg___boxed(lean_object* v_k_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(v_k_209_);
lean_dec(v_k_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(lean_object* v_motive_211_, lean_object* v_ctorIdx_212_, uint8_t v_t_213_, lean_object* v_h_214_, lean_object* v_k_215_){
_start:
{
lean_inc(v_k_215_);
return v_k_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___boxed(lean_object* v_motive_216_, lean_object* v_ctorIdx_217_, lean_object* v_t_218_, lean_object* v_h_219_, lean_object* v_k_220_){
_start:
{
uint8_t v_t_boxed_221_; lean_object* v_res_222_; 
v_t_boxed_221_ = lean_unbox(v_t_218_);
v_res_222_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(v_motive_216_, v_ctorIdx_217_, v_t_boxed_221_, v_h_219_, v_k_220_);
lean_dec(v_k_220_);
lean_dec(v_ctorIdx_217_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg(lean_object* v_pipeArg_223_){
_start:
{
lean_inc(v_pipeArg_223_);
return v_pipeArg_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg___boxed(lean_object* v_pipeArg_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg(v_pipeArg_224_);
lean_dec(v_pipeArg_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(lean_object* v_motive_226_, uint8_t v_t_227_, lean_object* v_h_228_, lean_object* v_pipeArg_229_){
_start:
{
lean_inc(v_pipeArg_229_);
return v_pipeArg_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___boxed(lean_object* v_motive_230_, lean_object* v_t_231_, lean_object* v_h_232_, lean_object* v_pipeArg_233_){
_start:
{
uint8_t v_t_boxed_234_; lean_object* v_res_235_; 
v_t_boxed_234_ = lean_unbox(v_t_231_);
v_res_235_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(v_motive_230_, v_t_boxed_234_, v_h_232_, v_pipeArg_233_);
lean_dec(v_pipeArg_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(lean_object* v_termArg_236_){
_start:
{
lean_inc(v_termArg_236_);
return v_termArg_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg___boxed(lean_object* v_termArg_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(v_termArg_237_);
lean_dec(v_termArg_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(lean_object* v_motive_239_, uint8_t v_t_240_, lean_object* v_h_241_, lean_object* v_termArg_242_){
_start:
{
lean_inc(v_termArg_242_);
return v_termArg_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___boxed(lean_object* v_motive_243_, lean_object* v_t_244_, lean_object* v_h_245_, lean_object* v_termArg_246_){
_start:
{
uint8_t v_t_boxed_247_; lean_object* v_res_248_; 
v_t_boxed_247_ = lean_unbox(v_t_244_);
v_res_248_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(v_motive_243_, v_t_boxed_247_, v_h_245_, v_termArg_246_);
lean_dec(v_termArg_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(lean_object* v_appArg_249_){
_start:
{
lean_inc(v_appArg_249_);
return v_appArg_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg___boxed(lean_object* v_appArg_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(v_appArg_250_);
lean_dec(v_appArg_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(lean_object* v_motive_252_, uint8_t v_t_253_, lean_object* v_h_254_, lean_object* v_appArg_255_){
_start:
{
lean_inc(v_appArg_255_);
return v_appArg_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___boxed(lean_object* v_motive_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_appArg_259_){
_start:
{
uint8_t v_t_boxed_260_; lean_object* v_res_261_; 
v_t_boxed_260_ = lean_unbox(v_t_257_);
v_res_261_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(v_motive_256_, v_t_boxed_260_, v_h_258_, v_appArg_259_);
lean_dec(v_appArg_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(uint8_t v_x_262_){
_start:
{
switch(v_x_262_)
{
case 0:
{
lean_object* v___x_263_; 
v___x_263_ = lean_unsigned_to_nat(0u);
return v___x_263_;
}
case 1:
{
lean_object* v___x_264_; 
v___x_264_ = lean_unsigned_to_nat(1u);
return v___x_264_;
}
default: 
{
lean_object* v___x_265_; 
v___x_265_ = lean_unsigned_to_nat(2u);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio___boxed(lean_object* v_x_266_){
_start:
{
uint8_t v_x_34__boxed_267_; lean_object* v_res_268_; 
v_x_34__boxed_267_ = lean_unbox(v_x_266_);
v_res_268_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_x_34__boxed_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(uint8_t v_x_269_){
_start:
{
if (v_x_269_ == 0)
{
lean_object* v___x_270_; 
v___x_270_ = lean_unsigned_to_nat(0u);
return v___x_270_;
}
else
{
lean_object* v___x_271_; 
v___x_271_ = lean_unsigned_to_nat(1u);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___boxed(lean_object* v_x_272_){
_start:
{
uint8_t v_x_boxed_273_; lean_object* v_res_274_; 
v_x_boxed_273_ = lean_unbox(v_x_272_);
v_res_274_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(v_x_boxed_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx(uint8_t v_x_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(v_x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx___boxed(lean_object* v_x_277_){
_start:
{
uint8_t v_x_4__boxed_278_; lean_object* v_res_279_; 
v_x_4__boxed_278_ = lean_unbox(v_x_277_);
v_res_279_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx(v_x_4__boxed_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg(lean_object* v_k_280_){
_start:
{
lean_inc(v_k_280_);
return v_k_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg___boxed(lean_object* v_k_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg(v_k_281_);
lean_dec(v_k_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(lean_object* v_motive_283_, lean_object* v_ctorIdx_284_, uint8_t v_t_285_, lean_object* v_h_286_, lean_object* v_k_287_){
_start:
{
lean_inc(v_k_287_);
return v_k_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___boxed(lean_object* v_motive_288_, lean_object* v_ctorIdx_289_, lean_object* v_t_290_, lean_object* v_h_291_, lean_object* v_k_292_){
_start:
{
uint8_t v_t_boxed_293_; lean_object* v_res_294_; 
v_t_boxed_293_ = lean_unbox(v_t_290_);
v_res_294_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(v_motive_288_, v_ctorIdx_289_, v_t_boxed_293_, v_h_291_, v_k_292_);
lean_dec(v_k_292_);
lean_dec(v_ctorIdx_289_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(lean_object* v_continue_295_){
_start:
{
lean_inc(v_continue_295_);
return v_continue_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg___boxed(lean_object* v_continue_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(v_continue_296_);
lean_dec(v_continue_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(lean_object* v_motive_298_, uint8_t v_t_299_, lean_object* v_h_300_, lean_object* v_continue_301_){
_start:
{
lean_inc(v_continue_301_);
return v_continue_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___boxed(lean_object* v_motive_302_, lean_object* v_t_303_, lean_object* v_h_304_, lean_object* v_continue_305_){
_start:
{
uint8_t v_t_boxed_306_; lean_object* v_res_307_; 
v_t_boxed_306_ = lean_unbox(v_t_303_);
v_res_307_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(v_motive_302_, v_t_boxed_306_, v_h_304_, v_continue_305_);
lean_dec(v_continue_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(lean_object* v_stop_308_){
_start:
{
lean_inc(v_stop_308_);
return v_stop_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg___boxed(lean_object* v_stop_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(v_stop_309_);
lean_dec(v_stop_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(lean_object* v_motive_311_, uint8_t v_t_312_, lean_object* v_h_313_, lean_object* v_stop_314_){
_start:
{
lean_inc(v_stop_314_);
return v_stop_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___boxed(lean_object* v_motive_315_, lean_object* v_t_316_, lean_object* v_h_317_, lean_object* v_stop_318_){
_start:
{
uint8_t v_t_boxed_319_; lean_object* v_res_320_; 
v_t_boxed_319_ = lean_unbox(v_t_316_);
v_res_320_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(v_motive_315_, v_t_boxed_319_, v_h_317_, v_stop_318_);
lean_dec(v_stop_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(lean_object* v_s_321_, lean_object* v___x_322_, lean_object* v___x_323_, lean_object* v_a_324_, lean_object* v_b_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = lean_box(0);
switch(lean_obj_tag(v_a_324_))
{
case 0:
{
lean_object* v_pos_327_; lean_object* v___x_328_; 
v_pos_327_ = lean_ctor_get(v_a_324_, 0);
lean_inc(v_pos_327_);
lean_dec_ref(v_a_324_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v_pos_327_);
return v___x_328_;
}
case 1:
{
lean_object* v_pos_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_338_; 
v_pos_329_ = lean_ctor_get(v_a_324_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v_a_324_);
if (v_isSharedCheck_338_ == 0)
{
v___x_331_ = v_a_324_;
v_isShared_332_ = v_isSharedCheck_338_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_pos_329_);
lean_dec(v_a_324_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_338_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lean_string_utf8_next_fast(v_s_321_, v_pos_329_);
lean_dec(v_pos_329_);
if (v_isShared_332_ == 0)
{
lean_ctor_set_tag(v___x_331_, 0);
lean_ctor_set(v___x_331_, 0, v___x_333_);
v___x_335_ = v___x_331_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_337_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
v_a_324_ = v___x_335_;
v_b_325_ = v___x_326_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_339_; lean_object* v_table_340_; lean_object* v_stackPos_341_; lean_object* v_needlePos_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_393_; 
v_needle_339_ = lean_ctor_get(v_a_324_, 0);
v_table_340_ = lean_ctor_get(v_a_324_, 1);
v_stackPos_341_ = lean_ctor_get(v_a_324_, 2);
v_needlePos_342_ = lean_ctor_get(v_a_324_, 3);
v_isSharedCheck_393_ = !lean_is_exclusive(v_a_324_);
if (v_isSharedCheck_393_ == 0)
{
v___x_344_ = v_a_324_;
v_isShared_345_ = v_isSharedCheck_393_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_needlePos_342_);
lean_inc(v_stackPos_341_);
lean_inc(v_table_340_);
lean_inc(v_needle_339_);
lean_dec(v_a_324_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_393_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v_str_346_; lean_object* v_startInclusive_347_; lean_object* v_endExclusive_348_; lean_object* v_basePos_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_str_346_ = lean_ctor_get(v_needle_339_, 0);
v_startInclusive_347_ = lean_ctor_get(v_needle_339_, 1);
v_endExclusive_348_ = lean_ctor_get(v_needle_339_, 2);
v_basePos_349_ = lean_nat_sub(v_stackPos_341_, v_needlePos_342_);
v___x_350_ = lean_nat_sub(v_endExclusive_348_, v_startInclusive_347_);
v___x_351_ = lean_nat_add(v_basePos_349_, v___x_350_);
v___x_352_ = lean_nat_dec_le(v___x_351_, v___x_323_);
lean_dec(v___x_351_);
if (v___x_352_ == 0)
{
uint8_t v___x_353_; 
lean_dec(v___x_350_);
lean_del_object(v___x_344_);
lean_dec(v_needlePos_342_);
lean_dec(v_stackPos_341_);
lean_dec_ref(v_table_340_);
lean_dec_ref(v_needle_339_);
v___x_353_ = lean_nat_dec_lt(v_basePos_349_, v___x_323_);
lean_dec(v_basePos_349_);
if (v___x_353_ == 0)
{
lean_inc(v_b_325_);
return v_b_325_;
}
else
{
lean_object* v___x_354_; 
v___x_354_ = lean_box(3);
v_a_324_ = v___x_354_;
v_b_325_ = v___x_326_;
goto _start;
}
}
else
{
uint8_t v_stackByte_356_; lean_object* v___x_357_; uint8_t v_patByte_358_; uint8_t v___x_359_; 
lean_dec(v_basePos_349_);
lean_inc(v_stackPos_341_);
v_stackByte_356_ = lean_string_get_byte_fast(v_s_321_, v_stackPos_341_);
v___x_357_ = lean_nat_add(v_startInclusive_347_, v_needlePos_342_);
v_patByte_358_ = lean_string_get_byte_fast(v_str_346_, v___x_357_);
v___x_359_ = lean_uint8_dec_eq(v_stackByte_356_, v_patByte_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; uint8_t v___x_361_; 
lean_dec(v___x_350_);
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = lean_nat_dec_eq(v_needlePos_342_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_newNeedlePos_364_; uint8_t v___x_365_; 
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_nat_sub(v_needlePos_342_, v___x_362_);
lean_dec(v_needlePos_342_);
v_newNeedlePos_364_ = lean_array_fget_borrowed(v_table_340_, v___x_363_);
lean_dec(v___x_363_);
v___x_365_ = lean_nat_dec_eq(v_newNeedlePos_364_, v___x_360_);
if (v___x_365_ == 0)
{
lean_object* v___x_367_; 
lean_inc(v_newNeedlePos_364_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 3, v_newNeedlePos_364_);
v___x_367_ = v___x_344_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_needle_339_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_table_340_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_stackPos_341_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_newNeedlePos_364_);
v___x_367_ = v_reuseFailAlloc_369_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
v_a_324_ = v___x_367_;
v_b_325_ = v___x_326_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_370_; lean_object* v___x_372_; 
v_nextStackPos_370_ = l_String_Slice_posGE___redArg(v___x_322_, v_stackPos_341_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 3, v___x_360_);
lean_ctor_set(v___x_344_, 2, v_nextStackPos_370_);
v___x_372_ = v___x_344_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_needle_339_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_table_340_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_nextStackPos_370_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v___x_360_);
v___x_372_ = v_reuseFailAlloc_374_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
v_a_324_ = v___x_372_;
v_b_325_ = v___x_326_;
goto _start;
}
}
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v_nextStackPos_377_; lean_object* v___x_379_; 
lean_dec(v_needlePos_342_);
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_add(v_stackPos_341_, v___x_375_);
lean_dec(v_stackPos_341_);
v_nextStackPos_377_ = l_String_Slice_posGE___redArg(v___x_322_, v___x_376_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 3, v___x_360_);
lean_ctor_set(v___x_344_, 2, v_nextStackPos_377_);
v___x_379_ = v___x_344_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_needle_339_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_table_340_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_nextStackPos_377_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v___x_360_);
v___x_379_ = v_reuseFailAlloc_381_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
v_a_324_ = v___x_379_;
v_b_325_ = v___x_326_;
goto _start;
}
}
}
else
{
lean_object* v___x_382_; lean_object* v_nextStackPos_383_; lean_object* v_nextNeedlePos_384_; uint8_t v___x_385_; 
v___x_382_ = lean_unsigned_to_nat(1u);
v_nextStackPos_383_ = lean_nat_add(v_stackPos_341_, v___x_382_);
lean_dec(v_stackPos_341_);
v_nextNeedlePos_384_ = lean_nat_add(v_needlePos_342_, v___x_382_);
lean_dec(v_needlePos_342_);
v___x_385_ = lean_nat_dec_eq(v_nextNeedlePos_384_, v___x_350_);
lean_dec(v___x_350_);
if (v___x_385_ == 0)
{
lean_object* v___x_387_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 3, v_nextNeedlePos_384_);
lean_ctor_set(v___x_344_, 2, v_nextStackPos_383_);
v___x_387_ = v___x_344_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_needle_339_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_table_340_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v_nextStackPos_383_);
lean_ctor_set(v_reuseFailAlloc_389_, 3, v_nextNeedlePos_384_);
v___x_387_ = v_reuseFailAlloc_389_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
v_a_324_ = v___x_387_;
goto _start;
}
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
lean_del_object(v___x_344_);
lean_dec_ref(v_table_340_);
lean_dec_ref(v_needle_339_);
v___x_390_ = lean_nat_sub(v_nextStackPos_383_, v_nextNeedlePos_384_);
lean_dec(v_nextNeedlePos_384_);
lean_dec(v_nextStackPos_383_);
v___x_391_ = l_String_Slice_pos_x21(v___x_322_, v___x_390_);
lean_dec(v___x_390_);
v___x_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
}
}
}
default: 
{
lean_inc(v_b_325_);
return v_b_325_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg___boxed(lean_object* v_s_394_, lean_object* v___x_395_, lean_object* v___x_396_, lean_object* v_a_397_, lean_object* v_b_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_394_, v___x_395_, v___x_396_, v_a_397_, v_b_398_);
lean_dec(v_b_398_);
lean_dec(v___x_396_);
lean_dec_ref(v___x_395_);
lean_dec_ref(v_s_394_);
return v_res_399_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0));
v___x_402_ = lean_string_utf8_byte_size(v___x_401_);
return v___x_402_;
}
}
static uint8_t _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1);
v___x_405_ = lean_nat_dec_eq(v___x_404_, v___x_403_);
return v___x_405_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1);
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0));
v___x_409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___x_407_);
lean_ctor_set(v___x_409_, 2, v___x_406_);
return v___x_409_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3);
v___x_411_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_410_);
return v___x_411_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4);
v___x_414_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3);
v___x_415_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___x_413_);
lean_ctor_set(v___x_415_, 2, v___x_412_);
lean_ctor_set(v___x_415_, 3, v___x_412_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(lean_object* v_s_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___y_423_; uint8_t v___x_434_; 
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_string_utf8_byte_size(v_s_418_);
lean_inc_ref(v_s_418_);
v___x_421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_421_, 0, v_s_418_);
lean_ctor_set(v___x_421_, 1, v___x_419_);
lean_ctor_set(v___x_421_, 2, v___x_420_);
v___x_434_ = lean_uint8_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
v___x_435_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5);
v___y_423_ = v___x_435_;
goto v___jp_422_;
}
else
{
lean_object* v___x_436_; 
v___x_436_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__6));
v___y_423_ = v___x_436_;
goto v___jp_422_;
}
v___jp_422_:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_box(0);
lean_inc(v___y_423_);
v___x_425_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_418_, v___x_421_, v___x_420_, v___y_423_, v___x_424_);
lean_dec_ref(v___x_421_);
lean_dec_ref(v_s_418_);
if (lean_obj_tag(v___x_425_) == 0)
{
return v___x_424_;
}
else
{
lean_object* v_val_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
v_val_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_val_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_val_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(lean_object* v_s_437_, lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v_inst_440_, lean_object* v_R_441_, lean_object* v_a_442_, lean_object* v_b_443_, lean_object* v_c_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_437_, v___x_438_, v___x_439_, v_a_442_, v_b_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___boxed(lean_object* v_s_446_, lean_object* v___x_447_, lean_object* v___x_448_, lean_object* v_inst_449_, lean_object* v_R_450_, lean_object* v_a_451_, lean_object* v_b_452_, lean_object* v_c_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(v_s_446_, v___x_447_, v___x_448_, v_inst_449_, v_R_450_, v_a_451_, v_b_452_, v_c_453_);
lean_dec(v_b_452_);
lean_dec(v___x_448_);
lean_dec_ref(v___x_447_);
lean_dec_ref(v_s_446_);
return v_res_454_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(lean_object* v_text_455_, lean_object* v_pos_456_){
_start:
{
lean_object* v___x_457_; lean_object* v_line_458_; lean_object* v_source_459_; lean_object* v_lineStartPos_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v_lineEndPos_463_; lean_object* v_line_464_; lean_object* v___x_465_; 
lean_inc_ref(v_text_455_);
v___x_457_ = l_Lean_FileMap_toPosition(v_text_455_, v_pos_456_);
v_line_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_line_458_);
lean_dec_ref(v___x_457_);
v_source_459_ = lean_ctor_get(v_text_455_, 0);
lean_inc_ref(v_source_459_);
v_lineStartPos_460_ = l_Lean_FileMap_lineStart(v_text_455_, v_line_458_);
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = lean_nat_add(v_line_458_, v___x_461_);
lean_dec(v_line_458_);
v_lineEndPos_463_ = l_Lean_FileMap_lineStart(v_text_455_, v___x_462_);
lean_dec(v___x_462_);
lean_dec_ref(v_text_455_);
v_line_464_ = lean_string_utf8_extract(v_source_459_, v_lineStartPos_460_, v_lineEndPos_463_);
lean_dec(v_lineEndPos_463_);
lean_dec_ref(v_source_459_);
v___x_465_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(v_line_464_);
if (lean_obj_tag(v___x_465_) == 1)
{
lean_object* v_val_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_val_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_466_);
lean_dec_ref(v___x_465_);
v___x_467_ = lean_nat_add(v_lineStartPos_460_, v_val_466_);
lean_dec(v_val_466_);
lean_dec(v_lineStartPos_460_);
v___x_468_ = lean_nat_dec_le(v___x_467_, v_pos_456_);
lean_dec(v___x_467_);
return v___x_468_;
}
else
{
uint8_t v___x_469_; 
lean_dec(v___x_465_);
lean_dec(v_lineStartPos_460_);
v___x_469_ = 0;
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment___boxed(lean_object* v_text_470_, lean_object* v_pos_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_470_, v_pos_471_);
lean_dec(v_pos_471_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(lean_object* v_text_530_, lean_object* v_ctx_x3f_531_, lean_object* v_requestedPos_532_, lean_object* v_stx_533_, lean_object* v_parent_534_){
_start:
{
lean_object* v_kind_x3f_536_; uint8_t v___y_635_; uint8_t v___y_636_; uint8_t v___y_637_; uint8_t v___x_639_; lean_object* v___x_640_; 
v___x_639_ = 1;
v___x_640_ = l_Lean_Syntax_getTailPos_x3f(v_stx_533_, v___x_639_);
if (lean_obj_tag(v___x_640_) == 1)
{
lean_object* v_val_641_; uint8_t v___x_642_; uint8_t v___y_644_; uint8_t v___y_645_; uint8_t v___y_652_; 
v_val_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_val_641_);
lean_dec_ref(v___x_640_);
v___x_642_ = lean_nat_dec_lt(v_requestedPos_532_, v_val_641_);
if (v___x_642_ == 0)
{
if (lean_obj_tag(v_ctx_x3f_531_) == 0)
{
v___y_652_ = v___x_642_;
goto v___jp_651_;
}
else
{
lean_object* v_val_655_; uint8_t v_triggerKind_656_; 
v_val_655_ = lean_ctor_get(v_ctx_x3f_531_, 0);
v_triggerKind_656_ = lean_ctor_get_uint8(v_val_655_, sizeof(void*)*2);
if (v_triggerKind_656_ == 0)
{
v___y_652_ = v___x_639_;
goto v___jp_651_;
}
else
{
v___y_652_ = v___x_642_;
goto v___jp_651_;
}
}
}
else
{
lean_object* v___x_657_; 
lean_dec(v_val_641_);
lean_dec(v_parent_534_);
lean_dec(v_stx_533_);
lean_dec_ref(v_text_530_);
v___x_657_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23));
return v___x_657_;
}
v___jp_643_:
{
lean_object* v___x_646_; lean_object* v_line_647_; lean_object* v___x_648_; lean_object* v_line_649_; uint8_t v___x_650_; 
lean_inc_ref(v_text_530_);
v___x_646_ = l_Lean_FileMap_toPosition(v_text_530_, v_requestedPos_532_);
v_line_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_line_647_);
lean_dec_ref(v___x_646_);
v___x_648_ = l_Lean_FileMap_toPosition(v_text_530_, v_val_641_);
lean_dec(v_val_641_);
v_line_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_line_649_);
lean_dec_ref(v___x_648_);
v___x_650_ = lean_nat_dec_eq(v_line_647_, v_line_649_);
lean_dec(v_line_649_);
lean_dec(v_line_647_);
if (v___x_650_ == 0)
{
v___y_635_ = v___y_645_;
v___y_636_ = v___y_644_;
v___y_637_ = v___x_639_;
goto v___jp_634_;
}
else
{
v___y_635_ = v___y_645_;
v___y_636_ = v___y_644_;
v___y_637_ = v___x_642_;
goto v___jp_634_;
}
}
v___jp_651_:
{
if (lean_obj_tag(v_ctx_x3f_531_) == 0)
{
v___y_644_ = v___y_652_;
v___y_645_ = v___x_642_;
goto v___jp_643_;
}
else
{
lean_object* v_val_653_; uint8_t v_isRetrigger_654_; 
v_val_653_ = lean_ctor_get(v_ctx_x3f_531_, 0);
v_isRetrigger_654_ = lean_ctor_get_uint8(v_val_653_, sizeof(void*)*2 + 1);
v___y_644_ = v___y_652_;
v___y_645_ = v_isRetrigger_654_;
goto v___jp_643_;
}
}
}
else
{
lean_object* v___x_658_; 
lean_dec(v___x_640_);
lean_dec(v_parent_534_);
lean_dec(v_stx_533_);
lean_dec_ref(v_text_530_);
v___x_658_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22));
return v___x_658_;
}
v___jp_535_:
{
uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = 0;
v___x_538_ = lean_box(v___x_537_);
lean_inc(v_kind_x3f_536_);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v_kind_x3f_536_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
return v___x_539_;
}
v___jp_540_:
{
if (lean_obj_tag(v_stx_533_) == 3)
{
lean_object* v___x_541_; uint8_t v___x_542_; 
lean_dec_ref(v_stx_533_);
v___x_541_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4));
lean_inc(v_parent_534_);
v___x_542_ = l_Lean_Syntax_isOfKind(v_parent_534_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_543_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6));
lean_inc(v_parent_534_);
v___x_544_ = l_Lean_Syntax_isOfKind(v_parent_534_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8));
lean_inc(v_parent_534_);
v___x_546_ = l_Lean_Syntax_isOfKind(v_parent_534_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
lean_dec(v_parent_534_);
v___x_547_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_536_ = v___x_547_;
goto v___jp_535_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = l_Lean_Syntax_getArg(v_parent_534_, v___x_548_);
lean_dec(v_parent_534_);
v___x_550_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_551_ = l_Lean_Syntax_isOfKind(v___x_549_, v___x_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
v___x_552_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_536_ = v___x_552_;
goto v___jp_535_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = lean_box(0);
v_kind_x3f_536_ = v___x_553_;
goto v___jp_535_;
}
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_554_ = lean_unsigned_to_nat(2u);
v___x_555_ = l_Lean_Syntax_getArg(v_parent_534_, v___x_554_);
lean_dec(v_parent_534_);
v___x_556_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_557_ = l_Lean_Syntax_isOfKind(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
v___x_558_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_536_ = v___x_558_;
goto v___jp_535_;
}
else
{
lean_object* v___x_559_; 
v___x_559_ = lean_box(0);
v_kind_x3f_536_ = v___x_559_;
goto v___jp_535_;
}
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_560_ = lean_unsigned_to_nat(2u);
v___x_561_ = l_Lean_Syntax_getArg(v_parent_534_, v___x_560_);
v___x_562_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_563_ = l_Lean_Syntax_isOfKind(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
lean_dec(v_parent_534_);
v___x_564_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_536_ = v___x_564_;
goto v___jp_535_;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_unsigned_to_nat(3u);
v___x_567_ = l_Lean_Syntax_getArg(v_parent_534_, v___x_566_);
lean_dec(v_parent_534_);
v___x_568_ = l_Lean_Syntax_matchesNull(v___x_567_, v___x_565_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
v___x_569_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_536_ = v___x_569_;
goto v___jp_535_;
}
else
{
lean_object* v___x_570_; 
v___x_570_ = lean_box(0);
v_kind_x3f_536_ = v___x_570_;
goto v___jp_535_;
}
}
}
}
else
{
lean_dec(v_parent_534_);
if (lean_obj_tag(v_stx_533_) == 1)
{
lean_object* v_kind_571_; lean_object* v_args_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v_kind_571_ = lean_ctor_get(v_stx_533_, 1);
v_args_572_ = lean_ctor_get(v_stx_533_, 2);
lean_inc_ref(v_args_572_);
v___x_573_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13));
v___x_574_ = lean_name_eq(v_kind_571_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15));
v___x_576_ = lean_name_eq(v_kind_571_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17));
lean_inc_ref(v_stx_533_);
v___x_578_ = l_Lean_Syntax_isOfKind(v_stx_533_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19));
lean_inc_ref(v_stx_533_);
v___x_580_ = l_Lean_Syntax_isOfKind(v_stx_533_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4));
lean_inc_ref(v_stx_533_);
v___x_582_ = l_Lean_Syntax_isOfKind(v_stx_533_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8));
lean_inc_ref(v_stx_533_);
v___x_584_ = l_Lean_Syntax_isOfKind(v_stx_533_, v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6));
lean_inc_ref(v_stx_533_);
v___x_586_ = l_Lean_Syntax_isOfKind(v_stx_533_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
lean_dec_ref(v_stx_533_);
v___x_587_ = lean_array_get_size(v_args_572_);
lean_dec_ref(v_args_572_);
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_nat_dec_le(v___x_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_536_ = v___x_590_;
goto v___jp_535_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = lean_box(0);
v_kind_x3f_536_ = v___x_591_;
goto v___jp_535_;
}
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_592_ = lean_unsigned_to_nat(2u);
v___x_593_ = l_Lean_Syntax_getArg(v_stx_533_, v___x_592_);
lean_dec_ref(v_stx_533_);
v___x_594_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_595_ = l_Lean_Syntax_isOfKind(v___x_593_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = lean_array_get_size(v_args_572_);
lean_dec_ref(v_args_572_);
v___x_598_ = lean_nat_dec_le(v___x_597_, v___x_596_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
v___x_599_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_536_ = v___x_599_;
goto v___jp_535_;
}
else
{
lean_object* v___x_600_; 
v___x_600_ = lean_box(0);
v_kind_x3f_536_ = v___x_600_;
goto v___jp_535_;
}
}
else
{
lean_object* v___x_601_; 
lean_dec_ref(v_args_572_);
v___x_601_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_536_ = v___x_601_;
goto v___jp_535_;
}
}
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = l_Lean_Syntax_getArg(v_stx_533_, v___x_602_);
lean_dec_ref(v_stx_533_);
v___x_604_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_605_ = l_Lean_Syntax_isOfKind(v___x_603_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_array_get_size(v_args_572_);
lean_dec_ref(v_args_572_);
v___x_607_ = lean_nat_dec_le(v___x_606_, v___x_602_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
v___x_608_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_536_ = v___x_608_;
goto v___jp_535_;
}
else
{
lean_object* v___x_609_; 
v___x_609_ = lean_box(0);
v_kind_x3f_536_ = v___x_609_;
goto v___jp_535_;
}
}
else
{
lean_object* v___x_610_; 
lean_dec_ref(v_args_572_);
v___x_610_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_536_ = v___x_610_;
goto v___jp_535_;
}
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_unsigned_to_nat(2u);
v___x_613_ = l_Lean_Syntax_getArg(v_stx_533_, v___x_612_);
v___x_614_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_615_ = l_Lean_Syntax_isOfKind(v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; uint8_t v___x_617_; 
lean_dec_ref(v_stx_533_);
v___x_616_ = lean_array_get_size(v_args_572_);
lean_dec_ref(v_args_572_);
v___x_617_ = lean_nat_dec_le(v___x_616_, v___x_611_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_536_ = v___x_618_;
goto v___jp_535_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = lean_box(0);
v_kind_x3f_536_ = v___x_619_;
goto v___jp_535_;
}
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_unsigned_to_nat(3u);
v___x_622_ = l_Lean_Syntax_getArg(v_stx_533_, v___x_621_);
lean_dec_ref(v_stx_533_);
v___x_623_ = l_Lean_Syntax_matchesNull(v___x_622_, v___x_620_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = lean_array_get_size(v_args_572_);
lean_dec_ref(v_args_572_);
v___x_625_ = lean_nat_dec_le(v___x_624_, v___x_611_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
v___x_626_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_536_ = v___x_626_;
goto v___jp_535_;
}
else
{
lean_object* v___x_627_; 
v___x_627_ = lean_box(0);
v_kind_x3f_536_ = v___x_627_;
goto v___jp_535_;
}
}
else
{
lean_object* v___x_628_; 
lean_dec_ref(v_args_572_);
v___x_628_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20));
v_kind_x3f_536_ = v___x_628_;
goto v___jp_535_;
}
}
}
}
else
{
lean_object* v___x_629_; 
lean_dec_ref(v_args_572_);
lean_dec_ref(v_stx_533_);
v___x_629_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20));
v_kind_x3f_536_ = v___x_629_;
goto v___jp_535_;
}
}
else
{
lean_object* v___x_630_; 
lean_dec_ref(v_args_572_);
lean_dec_ref(v_stx_533_);
v___x_630_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20));
v_kind_x3f_536_ = v___x_630_;
goto v___jp_535_;
}
}
else
{
lean_object* v___x_631_; 
lean_dec_ref(v_args_572_);
lean_dec_ref(v_stx_533_);
v___x_631_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21));
v_kind_x3f_536_ = v___x_631_;
goto v___jp_535_;
}
}
else
{
lean_object* v___x_632_; 
lean_dec_ref(v_args_572_);
lean_dec_ref(v_stx_533_);
v___x_632_ = lean_box(0);
v_kind_x3f_536_ = v___x_632_;
goto v___jp_535_;
}
}
else
{
lean_object* v___x_633_; 
lean_dec(v_stx_533_);
v___x_633_ = lean_box(0);
v_kind_x3f_536_ = v___x_633_;
goto v___jp_535_;
}
}
}
v___jp_634_:
{
if (v___y_636_ == 0)
{
if (v___y_635_ == 0)
{
if (v___y_637_ == 0)
{
goto v___jp_540_;
}
else
{
lean_object* v___x_638_; 
lean_dec(v_parent_534_);
lean_dec(v_stx_533_);
v___x_638_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22));
return v___x_638_;
}
}
else
{
goto v___jp_540_;
}
}
else
{
goto v___jp_540_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___boxed(lean_object* v_text_659_, lean_object* v_ctx_x3f_660_, lean_object* v_requestedPos_661_, lean_object* v_stx_662_, lean_object* v_parent_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_659_, v_ctx_x3f_660_, v_requestedPos_661_, v_stx_662_, v_parent_663_);
lean_dec(v_requestedPos_661_);
lean_dec(v_ctx_x3f_660_);
return v_res_664_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(uint8_t v___x_665_, lean_object* v_stx_666_){
_start:
{
uint8_t v___x_667_; 
v___x_667_ = l_Lean_Syntax_hasArgs(v_stx_666_);
if (v___x_667_ == 0)
{
uint8_t v___x_668_; 
v___x_668_ = 1;
return v___x_668_;
}
else
{
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed(lean_object* v___x_669_, lean_object* v_stx_670_){
_start:
{
uint8_t v___x_3192__boxed_671_; uint8_t v_res_672_; lean_object* v_r_673_; 
v___x_3192__boxed_671_ = lean_unbox(v___x_669_);
v_res_672_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(v___x_3192__boxed_671_, v_stx_670_);
lean_dec(v_stx_670_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(uint8_t v___x_674_, lean_object* v_requestedPos_675_, uint8_t v___x_676_, lean_object* v_stx_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_677_, v___x_674_);
if (lean_obj_tag(v___x_678_) == 1)
{
lean_object* v_val_679_; uint8_t v___x_680_; 
v_val_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_val_679_);
lean_dec_ref(v___x_678_);
v___x_680_ = l_Lean_Syntax_Range_contains(v_val_679_, v_requestedPos_675_, v___x_674_);
lean_dec(v_val_679_);
return v___x_680_;
}
else
{
lean_dec(v___x_678_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed(lean_object* v___x_681_, lean_object* v_requestedPos_682_, lean_object* v___x_683_, lean_object* v_stx_684_){
_start:
{
uint8_t v___x_3199__boxed_685_; uint8_t v___x_3200__boxed_686_; uint8_t v_res_687_; lean_object* v_r_688_; 
v___x_3199__boxed_685_ = lean_unbox(v___x_681_);
v___x_3200__boxed_686_ = lean_unbox(v___x_683_);
v_res_687_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(v___x_3199__boxed_685_, v_requestedPos_682_, v___x_3200__boxed_686_, v_stx_684_);
lean_dec(v_stx_684_);
lean_dec(v_requestedPos_682_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(lean_object* v_c1_689_, lean_object* v_c2_690_){
_start:
{
uint8_t v_kind_691_; uint8_t v_kind_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v_kind_691_ = lean_ctor_get_uint8(v_c2_690_, sizeof(void*)*1);
v_kind_692_ = lean_ctor_get_uint8(v_c1_689_, sizeof(void*)*1);
v___x_693_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_691_);
v___x_694_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_692_);
v___x_695_ = lean_nat_dec_le(v___x_693_, v___x_694_);
lean_dec(v___x_694_);
lean_dec(v___x_693_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2___boxed(lean_object* v_c1_696_, lean_object* v_c2_697_){
_start:
{
uint8_t v_res_698_; lean_object* v_r_699_; 
v_res_698_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(v_c1_696_, v_c2_697_);
lean_dec_ref(v_c2_697_);
lean_dec_ref(v_c1_696_);
v_r_699_ = lean_box(v_res_698_);
return v_r_699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(lean_object* v_tree_708_, uint8_t v___y_709_, uint8_t v___x_710_, lean_object* v_as_711_, size_t v_sz_712_, size_t v_i_713_, lean_object* v_b_714_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = lean_usize_dec_lt(v_i_713_, v_sz_712_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
lean_dec_ref(v_tree_708_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_b_714_);
return v___x_717_;
}
else
{
lean_object* v_a_718_; uint8_t v_kind_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec_ref(v_b_714_);
v_a_718_ = lean_array_uget_borrowed(v_as_711_, v_i_713_);
v_kind_719_ = lean_ctor_get_uint8(v_a_718_, sizeof(void*)*1);
v___x_720_ = lean_box(0);
v___x_721_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0));
if (v_kind_719_ == 1)
{
goto v___jp_746_;
}
else
{
if (v___x_710_ == 0)
{
goto v___jp_722_;
}
else
{
goto v___jp_746_;
}
}
v___jp_722_:
{
lean_object* v_appStx_723_; lean_object* v___x_724_; 
v_appStx_723_ = lean_ctor_get(v_a_718_, 0);
lean_inc(v_appStx_723_);
lean_inc_ref(v_tree_708_);
v___x_724_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_708_, v_appStx_723_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_737_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_737_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_737_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_737_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
if (lean_obj_tag(v_a_725_) == 1)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
lean_dec_ref(v_tree_708_);
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v_a_725_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___x_720_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_730_);
v___x_732_ = v___x_727_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
else
{
size_t v___x_734_; size_t v___x_735_; 
lean_del_object(v___x_727_);
lean_dec(v_a_725_);
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_add(v_i_713_, v___x_734_);
v_i_713_ = v___x_735_;
v_b_714_ = v___x_721_;
goto _start;
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v_tree_708_);
v_a_738_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_724_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_724_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
v___jp_746_:
{
if (v___y_709_ == 0)
{
goto v___jp_722_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec_ref(v_tree_708_);
v___x_747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__2));
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___boxed(lean_object* v_tree_749_, lean_object* v___y_750_, lean_object* v___x_751_, lean_object* v_as_752_, lean_object* v_sz_753_, lean_object* v_i_754_, lean_object* v_b_755_, lean_object* v___y_756_){
_start:
{
uint8_t v___y_3233__boxed_757_; uint8_t v___x_3234__boxed_758_; size_t v_sz_boxed_759_; size_t v_i_boxed_760_; lean_object* v_res_761_; 
v___y_3233__boxed_757_ = lean_unbox(v___y_750_);
v___x_3234__boxed_758_ = lean_unbox(v___x_751_);
v_sz_boxed_759_ = lean_unbox_usize(v_sz_753_);
lean_dec(v_sz_753_);
v_i_boxed_760_ = lean_unbox_usize(v_i_754_);
lean_dec(v_i_754_);
v_res_761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v_tree_749_, v___y_3233__boxed_757_, v___x_3234__boxed_758_, v_as_752_, v_sz_boxed_759_, v_i_boxed_760_, v_b_755_);
lean_dec_ref(v_as_752_);
return v_res_761_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0(void){
_start:
{
uint8_t v___x_762_; lean_object* v___x_763_; 
v___x_762_ = 1;
v___x_763_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(lean_object* v_as_764_, size_t v_i_765_, size_t v_stop_766_){
_start:
{
uint8_t v___x_767_; 
v___x_767_ = lean_usize_dec_eq(v_i_765_, v_stop_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; uint8_t v_kind_769_; lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_768_ = lean_array_uget_borrowed(v_as_764_, v_i_765_);
v_kind_769_ = lean_ctor_get_uint8(v___x_768_, sizeof(void*)*1);
v___x_770_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0);
v___x_771_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_769_);
v___x_772_ = lean_nat_dec_lt(v___x_770_, v___x_771_);
lean_dec(v___x_771_);
if (v___x_772_ == 0)
{
size_t v___x_773_; size_t v___x_774_; 
v___x_773_ = ((size_t)1ULL);
v___x_774_ = lean_usize_add(v_i_765_, v___x_773_);
v_i_765_ = v___x_774_;
goto _start;
}
else
{
return v___x_772_;
}
}
else
{
uint8_t v___x_776_; 
v___x_776_ = 0;
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___boxed(lean_object* v_as_777_, lean_object* v_i_778_, lean_object* v_stop_779_){
_start:
{
size_t v_i_boxed_780_; size_t v_stop_boxed_781_; uint8_t v_res_782_; lean_object* v_r_783_; 
v_i_boxed_780_ = lean_unbox_usize(v_i_778_);
lean_dec(v_i_778_);
v_stop_boxed_781_ = lean_unbox_usize(v_stop_779_);
lean_dec(v_stop_779_);
v_res_782_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v_as_777_, v_i_boxed_780_, v_stop_boxed_781_);
lean_dec_ref(v_as_777_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(uint8_t v_snd_784_, uint8_t v___x_785_, lean_object* v_____r_786_, lean_object* v_candidates_787_){
_start:
{
if (v_snd_784_ == 1)
{
goto v___jp_789_;
}
else
{
if (v___x_785_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_792_, 0, v_candidates_787_);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
else
{
goto v___jp_789_;
}
}
v___jp_789_:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v_candidates_787_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0___boxed(lean_object* v_snd_794_, lean_object* v___x_795_, lean_object* v_____r_796_, lean_object* v_candidates_797_, lean_object* v___y_798_){
_start:
{
uint8_t v_snd_3335__boxed_799_; uint8_t v___x_3336__boxed_800_; lean_object* v_res_801_; 
v_snd_3335__boxed_799_ = lean_unbox(v_snd_794_);
v___x_3336__boxed_800_ = lean_unbox(v___x_795_);
v_res_801_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v_snd_3335__boxed_799_, v___x_3336__boxed_800_, v_____r_796_, v_candidates_797_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(lean_object* v_upperBound_802_, lean_object* v_stack_803_, lean_object* v_text_804_, lean_object* v_ctx_x3f_805_, lean_object* v_requestedPos_806_, uint8_t v___x_807_, lean_object* v_a_808_, lean_object* v_b_809_){
_start:
{
lean_object* v___y_812_; uint8_t v___x_834_; 
v___x_834_ = lean_nat_dec_lt(v_a_808_, v_upperBound_802_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
lean_dec(v_a_808_);
lean_dec_ref(v_text_804_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v_b_809_);
return v___x_835_;
}
else
{
lean_object* v___x_836_; lean_object* v___y_838_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_836_ = lean_array_fget_borrowed(v_stack_803_, v_a_808_);
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = lean_nat_add(v_a_808_, v___x_853_);
v___x_855_ = lean_array_get_size(v_stack_803_);
v___x_856_ = lean_nat_dec_lt(v___x_854_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v___y_838_ = v___x_857_;
goto v___jp_837_;
}
else
{
lean_object* v___x_858_; 
v___x_858_ = lean_array_fget_borrowed(v_stack_803_, v___x_854_);
lean_dec(v___x_854_);
lean_inc(v___x_858_);
v___y_838_ = v___x_858_;
goto v___jp_837_;
}
v___jp_837_:
{
lean_object* v___x_839_; lean_object* v_fst_840_; 
lean_inc(v___x_836_);
lean_inc_ref(v_text_804_);
v___x_839_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_804_, v_ctx_x3f_805_, v_requestedPos_806_, v___x_836_, v___y_838_);
v_fst_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_fst_840_);
if (lean_obj_tag(v_fst_840_) == 1)
{
lean_object* v_snd_841_; lean_object* v_val_842_; lean_object* v___x_843_; uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; 
v_snd_841_ = lean_ctor_get(v___x_839_, 1);
lean_inc(v_snd_841_);
lean_dec_ref(v___x_839_);
v_val_842_ = lean_ctor_get(v_fst_840_, 0);
lean_inc(v_val_842_);
lean_dec_ref(v_fst_840_);
lean_inc(v___x_836_);
v___x_843_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_843_, 0, v___x_836_);
v___x_844_ = lean_unbox(v_val_842_);
lean_dec(v_val_842_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*1, v___x_844_);
v___x_845_ = lean_array_push(v_b_809_, v___x_843_);
v___x_846_ = lean_box(0);
v___x_847_ = lean_unbox(v_snd_841_);
lean_dec(v_snd_841_);
v___x_848_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_847_, v___x_807_, v___x_846_, v___x_845_);
v___y_812_ = v___x_848_;
goto v___jp_811_;
}
else
{
lean_object* v_snd_849_; lean_object* v___x_850_; uint8_t v___x_851_; lean_object* v___x_852_; 
lean_dec(v_fst_840_);
v_snd_849_ = lean_ctor_get(v___x_839_, 1);
lean_inc(v_snd_849_);
lean_dec_ref(v___x_839_);
v___x_850_ = lean_box(0);
v___x_851_ = lean_unbox(v_snd_849_);
lean_dec(v_snd_849_);
v___x_852_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_851_, v___x_807_, v___x_850_, v_b_809_);
v___y_812_ = v___x_852_;
goto v___jp_811_;
}
}
}
v___jp_811_:
{
if (lean_obj_tag(v___y_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_825_; 
v_a_813_ = lean_ctor_get(v___y_812_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___y_812_);
if (v_isSharedCheck_825_ == 0)
{
v___x_815_ = v___y_812_;
v_isShared_816_ = v_isSharedCheck_825_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___y_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_825_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
if (lean_obj_tag(v_a_813_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; 
lean_dec(v_a_808_);
lean_dec_ref(v_text_804_);
v_a_817_ = lean_ctor_get(v_a_813_, 0);
lean_inc(v_a_817_);
lean_dec_ref(v_a_813_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v_a_817_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
lean_del_object(v___x_815_);
v_a_821_ = lean_ctor_get(v_a_813_, 0);
lean_inc(v_a_821_);
lean_dec_ref(v_a_813_);
v___x_822_ = lean_unsigned_to_nat(1u);
v___x_823_ = lean_nat_add(v_a_808_, v___x_822_);
lean_dec(v_a_808_);
v_a_808_ = v___x_823_;
v_b_809_ = v_a_821_;
goto _start;
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_a_808_);
lean_dec_ref(v_text_804_);
v_a_826_ = lean_ctor_get(v___y_812_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___y_812_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___y_812_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___y_812_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___boxed(lean_object* v_upperBound_859_, lean_object* v_stack_860_, lean_object* v_text_861_, lean_object* v_ctx_x3f_862_, lean_object* v_requestedPos_863_, lean_object* v___x_864_, lean_object* v_a_865_, lean_object* v_b_866_, lean_object* v___y_867_){
_start:
{
uint8_t v___x_3358__boxed_868_; lean_object* v_res_869_; 
v___x_3358__boxed_868_ = lean_unbox(v___x_864_);
v_res_869_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_859_, v_stack_860_, v_text_861_, v_ctx_x3f_862_, v_requestedPos_863_, v___x_3358__boxed_868_, v_a_865_, v_b_866_);
lean_dec(v_requestedPos_863_);
lean_dec(v_ctx_x3f_862_);
lean_dec_ref(v_stack_860_);
lean_dec(v_upperBound_859_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(size_t v_sz_870_, size_t v_i_871_, lean_object* v_bs_872_){
_start:
{
uint8_t v___x_873_; 
v___x_873_ = lean_usize_dec_lt(v_i_871_, v_sz_870_);
if (v___x_873_ == 0)
{
return v_bs_872_;
}
else
{
lean_object* v_v_874_; lean_object* v_fst_875_; lean_object* v___x_876_; lean_object* v_bs_x27_877_; size_t v___x_878_; size_t v___x_879_; lean_object* v___x_880_; 
v_v_874_ = lean_array_uget_borrowed(v_bs_872_, v_i_871_);
v_fst_875_ = lean_ctor_get(v_v_874_, 0);
lean_inc(v_fst_875_);
v___x_876_ = lean_unsigned_to_nat(0u);
v_bs_x27_877_ = lean_array_uset(v_bs_872_, v_i_871_, v___x_876_);
v___x_878_ = ((size_t)1ULL);
v___x_879_ = lean_usize_add(v_i_871_, v___x_878_);
v___x_880_ = lean_array_uset(v_bs_x27_877_, v_i_871_, v_fst_875_);
v_i_871_ = v___x_879_;
v_bs_872_ = v___x_880_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0___boxed(lean_object* v_sz_882_, lean_object* v_i_883_, lean_object* v_bs_884_){
_start:
{
size_t v_sz_boxed_885_; size_t v_i_boxed_886_; lean_object* v_res_887_; 
v_sz_boxed_885_ = lean_unbox_usize(v_sz_882_);
lean_dec(v_sz_882_);
v_i_boxed_886_ = lean_unbox_usize(v_i_883_);
lean_dec(v_i_883_);
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_sz_boxed_885_, v_i_boxed_886_, v_bs_884_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(lean_object* v_text_891_, lean_object* v_ctx_x3f_892_, lean_object* v_cmdStx_893_, lean_object* v_tree_894_, lean_object* v_requestedPos_895_){
_start:
{
uint8_t v___x_897_; 
lean_inc_ref(v_text_891_);
v___x_897_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_891_, v_requestedPos_895_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___f_899_; uint8_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___f_903_; lean_object* v_stack_x3f_904_; 
v___x_898_ = lean_box(v___x_897_);
v___f_899_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_899_, 0, v___x_898_);
v___x_900_ = 1;
v___x_901_ = lean_box(v___x_900_);
v___x_902_ = lean_box(v___x_897_);
lean_inc(v_requestedPos_895_);
v___f_903_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed), 4, 3);
lean_closure_set(v___f_903_, 0, v___x_901_);
lean_closure_set(v___f_903_, 1, v_requestedPos_895_);
lean_closure_set(v___f_903_, 2, v___x_902_);
v_stack_x3f_904_ = l_Lean_Syntax_findStack_x3f(v_cmdStx_893_, v___f_903_, v___f_899_);
if (lean_obj_tag(v_stack_x3f_904_) == 1)
{
lean_object* v_val_905_; lean_object* v___x_906_; size_t v_sz_907_; size_t v___x_908_; lean_object* v_stack_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v_candidates_912_; lean_object* v___x_913_; 
v_val_905_ = lean_ctor_get(v_stack_x3f_904_, 0);
lean_inc(v_val_905_);
lean_dec_ref(v_stack_x3f_904_);
v___x_906_ = lean_array_mk(v_val_905_);
v_sz_907_ = lean_array_size(v___x_906_);
v___x_908_ = ((size_t)0ULL);
v_stack_909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_sz_907_, v___x_908_, v___x_906_);
v___x_910_ = lean_array_get_size(v_stack_909_);
v___x_911_ = lean_unsigned_to_nat(0u);
v_candidates_912_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0));
v___x_913_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v___x_910_, v_stack_909_, v_text_891_, v_ctx_x3f_892_, v_requestedPos_895_, v___x_897_, v___x_911_, v_candidates_912_);
lean_dec(v_requestedPos_895_);
lean_dec_ref(v_stack_909_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___f_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___y_920_; lean_object* v___x_946_; uint8_t v___x_947_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref(v___x_913_);
v___f_915_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1));
v___x_916_ = lean_array_to_list(v_a_914_);
v___x_917_ = l_List_mergeSort___redArg(v___x_916_, v___f_915_);
v___x_918_ = lean_array_mk(v___x_917_);
v___x_946_ = lean_array_get_size(v___x_918_);
v___x_947_ = lean_nat_dec_lt(v___x_911_, v___x_946_);
if (v___x_947_ == 0)
{
v___y_920_ = v___x_897_;
goto v___jp_919_;
}
else
{
if (v___x_947_ == 0)
{
v___y_920_ = v___x_897_;
goto v___jp_919_;
}
else
{
size_t v___x_948_; uint8_t v___x_949_; 
v___x_948_ = lean_usize_of_nat(v___x_946_);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v___x_918_, v___x_908_, v___x_948_);
v___y_920_ = v___x_949_;
goto v___jp_919_;
}
}
v___jp_919_:
{
lean_object* v___x_921_; lean_object* v___x_922_; size_t v_sz_923_; lean_object* v___x_924_; 
v___x_921_ = lean_box(0);
v___x_922_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0));
v_sz_923_ = lean_array_size(v___x_918_);
v___x_924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v_tree_894_, v___y_920_, v___x_897_, v___x_918_, v_sz_923_, v___x_908_, v___x_922_);
lean_dec_ref(v___x_918_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_937_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_937_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_937_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_937_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_fst_929_; 
v_fst_929_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v_fst_929_);
lean_dec(v_a_925_);
if (lean_obj_tag(v_fst_929_) == 0)
{
lean_object* v___x_931_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_921_);
v___x_931_ = v___x_927_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_921_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
else
{
lean_object* v_val_933_; lean_object* v___x_935_; 
v_val_933_ = lean_ctor_get(v_fst_929_, 0);
lean_inc(v_val_933_);
lean_dec_ref(v_fst_929_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v_val_933_);
v___x_935_ = v___x_927_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_val_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
v_a_938_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_924_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_924_);
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
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v_tree_894_);
v_a_950_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_913_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_913_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v_stack_x3f_904_);
lean_dec(v_requestedPos_895_);
lean_dec_ref(v_tree_894_);
lean_dec_ref(v_text_891_);
v___x_958_ = lean_box(0);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec(v_requestedPos_895_);
lean_dec_ref(v_tree_894_);
lean_dec(v_cmdStx_893_);
lean_dec_ref(v_text_891_);
v___x_960_ = lean_box(0);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___boxed(lean_object* v_text_962_, lean_object* v_ctx_x3f_963_, lean_object* v_cmdStx_964_, lean_object* v_tree_965_, lean_object* v_requestedPos_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(v_text_962_, v_ctx_x3f_963_, v_cmdStx_964_, v_tree_965_, v_requestedPos_966_);
lean_dec(v_ctx_x3f_963_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(lean_object* v_upperBound_969_, lean_object* v_stack_970_, lean_object* v_text_971_, lean_object* v_ctx_x3f_972_, lean_object* v_requestedPos_973_, uint8_t v___x_974_, lean_object* v_inst_975_, lean_object* v_R_976_, lean_object* v_a_977_, lean_object* v_b_978_, lean_object* v_c_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_969_, v_stack_970_, v_text_971_, v_ctx_x3f_972_, v_requestedPos_973_, v___x_974_, v_a_977_, v_b_978_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___boxed(lean_object* v_upperBound_982_, lean_object* v_stack_983_, lean_object* v_text_984_, lean_object* v_ctx_x3f_985_, lean_object* v_requestedPos_986_, lean_object* v___x_987_, lean_object* v_inst_988_, lean_object* v_R_989_, lean_object* v_a_990_, lean_object* v_b_991_, lean_object* v_c_992_, lean_object* v___y_993_){
_start:
{
uint8_t v___x_3605__boxed_994_; lean_object* v_res_995_; 
v___x_3605__boxed_994_ = lean_unbox(v___x_987_);
v_res_995_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(v_upperBound_982_, v_stack_983_, v_text_984_, v_ctx_x3f_985_, v_requestedPos_986_, v___x_3605__boxed_994_, v_inst_988_, v_R_989_, v_a_990_, v_b_991_, v_c_992_);
lean_dec(v_requestedPos_986_);
lean_dec(v_ctx_x3f_985_);
lean_dec_ref(v_stack_983_);
lean_dec(v_upperBound_982_);
return v_res_995_;
}
}
lean_object* runtime_initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileWorker_SignatureHelp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Delaborator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_FileWorker_SignatureHelp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter_Delaborator(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_SignatureHelp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_SignatureHelp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_FileWorker_SignatureHelp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_FileWorker_SignatureHelp(builtin);
}
#ifdef __cplusplus
}
#endif
