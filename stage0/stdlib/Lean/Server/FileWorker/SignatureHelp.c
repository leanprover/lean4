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
lean_dec_ref_known(v___x_77_, 1);
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
lean_dec_ref_known(v___x_91_, 1);
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
lean_dec_ref_known(v___x_145_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(lean_object* v_k_203_){
_start:
{
lean_inc(v_k_203_);
return v_k_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg___boxed(lean_object* v_k_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(v_k_204_);
lean_dec(v_k_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(lean_object* v_motive_206_, lean_object* v_ctorIdx_207_, uint8_t v_t_208_, lean_object* v_h_209_, lean_object* v_k_210_){
_start:
{
lean_inc(v_k_210_);
return v_k_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___boxed(lean_object* v_motive_211_, lean_object* v_ctorIdx_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_k_215_){
_start:
{
uint8_t v_t_boxed_216_; lean_object* v_res_217_; 
v_t_boxed_216_ = lean_unbox(v_t_213_);
v_res_217_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(v_motive_211_, v_ctorIdx_212_, v_t_boxed_216_, v_h_214_, v_k_215_);
lean_dec(v_k_215_);
lean_dec(v_ctorIdx_212_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg(lean_object* v_pipeArg_218_){
_start:
{
lean_inc(v_pipeArg_218_);
return v_pipeArg_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg___boxed(lean_object* v_pipeArg_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg(v_pipeArg_219_);
lean_dec(v_pipeArg_219_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(lean_object* v_motive_221_, uint8_t v_t_222_, lean_object* v_h_223_, lean_object* v_pipeArg_224_){
_start:
{
lean_inc(v_pipeArg_224_);
return v_pipeArg_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___boxed(lean_object* v_motive_225_, lean_object* v_t_226_, lean_object* v_h_227_, lean_object* v_pipeArg_228_){
_start:
{
uint8_t v_t_boxed_229_; lean_object* v_res_230_; 
v_t_boxed_229_ = lean_unbox(v_t_226_);
v_res_230_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(v_motive_225_, v_t_boxed_229_, v_h_227_, v_pipeArg_228_);
lean_dec(v_pipeArg_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(lean_object* v_termArg_231_){
_start:
{
lean_inc(v_termArg_231_);
return v_termArg_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg___boxed(lean_object* v_termArg_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(v_termArg_232_);
lean_dec(v_termArg_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(lean_object* v_motive_234_, uint8_t v_t_235_, lean_object* v_h_236_, lean_object* v_termArg_237_){
_start:
{
lean_inc(v_termArg_237_);
return v_termArg_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___boxed(lean_object* v_motive_238_, lean_object* v_t_239_, lean_object* v_h_240_, lean_object* v_termArg_241_){
_start:
{
uint8_t v_t_boxed_242_; lean_object* v_res_243_; 
v_t_boxed_242_ = lean_unbox(v_t_239_);
v_res_243_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(v_motive_238_, v_t_boxed_242_, v_h_240_, v_termArg_241_);
lean_dec(v_termArg_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(lean_object* v_appArg_244_){
_start:
{
lean_inc(v_appArg_244_);
return v_appArg_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg___boxed(lean_object* v_appArg_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(v_appArg_245_);
lean_dec(v_appArg_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(lean_object* v_motive_247_, uint8_t v_t_248_, lean_object* v_h_249_, lean_object* v_appArg_250_){
_start:
{
lean_inc(v_appArg_250_);
return v_appArg_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___boxed(lean_object* v_motive_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_appArg_254_){
_start:
{
uint8_t v_t_boxed_255_; lean_object* v_res_256_; 
v_t_boxed_255_ = lean_unbox(v_t_252_);
v_res_256_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(v_motive_251_, v_t_boxed_255_, v_h_253_, v_appArg_254_);
lean_dec(v_appArg_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(uint8_t v_x_257_){
_start:
{
switch(v_x_257_)
{
case 0:
{
lean_object* v___x_258_; 
v___x_258_ = lean_unsigned_to_nat(0u);
return v___x_258_;
}
case 1:
{
lean_object* v___x_259_; 
v___x_259_ = lean_unsigned_to_nat(1u);
return v___x_259_;
}
default: 
{
lean_object* v___x_260_; 
v___x_260_ = lean_unsigned_to_nat(2u);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio___boxed(lean_object* v_x_261_){
_start:
{
uint8_t v_x_34__boxed_262_; lean_object* v_res_263_; 
v_x_34__boxed_262_ = lean_unbox(v_x_261_);
v_res_263_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_x_34__boxed_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(uint8_t v_x_264_){
_start:
{
if (v_x_264_ == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_unsigned_to_nat(0u);
return v___x_265_;
}
else
{
lean_object* v___x_266_; 
v___x_266_ = lean_unsigned_to_nat(1u);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___boxed(lean_object* v_x_267_){
_start:
{
uint8_t v_x_boxed_268_; lean_object* v_res_269_; 
v_x_boxed_268_ = lean_unbox(v_x_267_);
v_res_269_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(v_x_boxed_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg(lean_object* v_k_270_){
_start:
{
lean_inc(v_k_270_);
return v_k_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg___boxed(lean_object* v_k_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg(v_k_271_);
lean_dec(v_k_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(lean_object* v_motive_273_, lean_object* v_ctorIdx_274_, uint8_t v_t_275_, lean_object* v_h_276_, lean_object* v_k_277_){
_start:
{
lean_inc(v_k_277_);
return v_k_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___boxed(lean_object* v_motive_278_, lean_object* v_ctorIdx_279_, lean_object* v_t_280_, lean_object* v_h_281_, lean_object* v_k_282_){
_start:
{
uint8_t v_t_boxed_283_; lean_object* v_res_284_; 
v_t_boxed_283_ = lean_unbox(v_t_280_);
v_res_284_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(v_motive_278_, v_ctorIdx_279_, v_t_boxed_283_, v_h_281_, v_k_282_);
lean_dec(v_k_282_);
lean_dec(v_ctorIdx_279_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(lean_object* v_continue_285_){
_start:
{
lean_inc(v_continue_285_);
return v_continue_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg___boxed(lean_object* v_continue_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(v_continue_286_);
lean_dec(v_continue_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(lean_object* v_motive_288_, uint8_t v_t_289_, lean_object* v_h_290_, lean_object* v_continue_291_){
_start:
{
lean_inc(v_continue_291_);
return v_continue_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___boxed(lean_object* v_motive_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_continue_295_){
_start:
{
uint8_t v_t_boxed_296_; lean_object* v_res_297_; 
v_t_boxed_296_ = lean_unbox(v_t_293_);
v_res_297_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(v_motive_292_, v_t_boxed_296_, v_h_294_, v_continue_295_);
lean_dec(v_continue_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(lean_object* v_stop_298_){
_start:
{
lean_inc(v_stop_298_);
return v_stop_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg___boxed(lean_object* v_stop_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(v_stop_299_);
lean_dec(v_stop_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(lean_object* v_motive_301_, uint8_t v_t_302_, lean_object* v_h_303_, lean_object* v_stop_304_){
_start:
{
lean_inc(v_stop_304_);
return v_stop_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___boxed(lean_object* v_motive_305_, lean_object* v_t_306_, lean_object* v_h_307_, lean_object* v_stop_308_){
_start:
{
uint8_t v_t_boxed_309_; lean_object* v_res_310_; 
v_t_boxed_309_ = lean_unbox(v_t_306_);
v_res_310_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(v_motive_305_, v_t_boxed_309_, v_h_307_, v_stop_308_);
lean_dec(v_stop_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(lean_object* v_s_311_, lean_object* v___x_312_, lean_object* v___x_313_, lean_object* v_a_314_, lean_object* v_b_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = lean_box(0);
switch(lean_obj_tag(v_a_314_))
{
case 0:
{
lean_object* v_pos_317_; lean_object* v___x_318_; 
v_pos_317_ = lean_ctor_get(v_a_314_, 0);
lean_inc(v_pos_317_);
lean_dec_ref_known(v_a_314_, 1);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v_pos_317_);
return v___x_318_;
}
case 1:
{
lean_object* v_pos_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_328_; 
v_pos_319_ = lean_ctor_get(v_a_314_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_a_314_);
if (v_isSharedCheck_328_ == 0)
{
v___x_321_ = v_a_314_;
v_isShared_322_ = v_isSharedCheck_328_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_pos_319_);
lean_dec(v_a_314_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_328_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = lean_string_utf8_next_fast(v_s_311_, v_pos_319_);
lean_dec(v_pos_319_);
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 0);
lean_ctor_set(v___x_321_, 0, v___x_323_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_327_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
v_a_314_ = v___x_325_;
v_b_315_ = v___x_316_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_329_; lean_object* v_table_330_; lean_object* v_stackPos_331_; lean_object* v_needlePos_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_383_; 
v_needle_329_ = lean_ctor_get(v_a_314_, 0);
v_table_330_ = lean_ctor_get(v_a_314_, 1);
v_stackPos_331_ = lean_ctor_get(v_a_314_, 2);
v_needlePos_332_ = lean_ctor_get(v_a_314_, 3);
v_isSharedCheck_383_ = !lean_is_exclusive(v_a_314_);
if (v_isSharedCheck_383_ == 0)
{
v___x_334_ = v_a_314_;
v_isShared_335_ = v_isSharedCheck_383_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_needlePos_332_);
lean_inc(v_stackPos_331_);
lean_inc(v_table_330_);
lean_inc(v_needle_329_);
lean_dec(v_a_314_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_383_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_str_336_; lean_object* v_startInclusive_337_; lean_object* v_endExclusive_338_; lean_object* v_basePos_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_str_336_ = lean_ctor_get(v_needle_329_, 0);
v_startInclusive_337_ = lean_ctor_get(v_needle_329_, 1);
v_endExclusive_338_ = lean_ctor_get(v_needle_329_, 2);
v_basePos_339_ = lean_nat_sub(v_stackPos_331_, v_needlePos_332_);
v___x_340_ = lean_nat_sub(v_endExclusive_338_, v_startInclusive_337_);
v___x_341_ = lean_nat_add(v_basePos_339_, v___x_340_);
v___x_342_ = lean_nat_dec_le(v___x_341_, v___x_313_);
lean_dec(v___x_341_);
if (v___x_342_ == 0)
{
uint8_t v___x_343_; 
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_needlePos_332_);
lean_dec(v_stackPos_331_);
lean_dec_ref(v_table_330_);
lean_dec_ref(v_needle_329_);
v___x_343_ = lean_nat_dec_lt(v_basePos_339_, v___x_313_);
lean_dec(v_basePos_339_);
if (v___x_343_ == 0)
{
lean_inc(v_b_315_);
return v_b_315_;
}
else
{
lean_object* v___x_344_; 
v___x_344_ = lean_box(3);
v_a_314_ = v___x_344_;
v_b_315_ = v___x_316_;
goto _start;
}
}
else
{
uint8_t v_stackByte_346_; lean_object* v___x_347_; uint8_t v_patByte_348_; uint8_t v___x_349_; 
lean_dec(v_basePos_339_);
lean_inc(v_stackPos_331_);
v_stackByte_346_ = lean_string_get_byte_fast(v_s_311_, v_stackPos_331_);
v___x_347_ = lean_nat_add(v_startInclusive_337_, v_needlePos_332_);
v_patByte_348_ = lean_string_get_byte_fast(v_str_336_, v___x_347_);
v___x_349_ = lean_uint8_dec_eq(v_stackByte_346_, v_patByte_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; uint8_t v___x_351_; 
lean_dec(v___x_340_);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_nat_dec_eq(v_needlePos_332_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_newNeedlePos_354_; uint8_t v___x_355_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_sub(v_needlePos_332_, v___x_352_);
lean_dec(v_needlePos_332_);
v_newNeedlePos_354_ = lean_array_fget_borrowed(v_table_330_, v___x_353_);
lean_dec(v___x_353_);
v___x_355_ = lean_nat_dec_eq(v_newNeedlePos_354_, v___x_350_);
if (v___x_355_ == 0)
{
lean_object* v___x_357_; 
lean_inc(v_newNeedlePos_354_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 3, v_newNeedlePos_354_);
v___x_357_ = v___x_334_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_needle_329_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_table_330_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_stackPos_331_);
lean_ctor_set(v_reuseFailAlloc_359_, 3, v_newNeedlePos_354_);
v___x_357_ = v_reuseFailAlloc_359_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
v_a_314_ = v___x_357_;
v_b_315_ = v___x_316_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_360_; lean_object* v___x_362_; 
v_nextStackPos_360_ = l_String_Slice_posGE___redArg(v___x_312_, v_stackPos_331_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 3, v___x_350_);
lean_ctor_set(v___x_334_, 2, v_nextStackPos_360_);
v___x_362_ = v___x_334_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_needle_329_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_table_330_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_nextStackPos_360_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v___x_350_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
v_a_314_ = v___x_362_;
v_b_315_ = v___x_316_;
goto _start;
}
}
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_nextStackPos_367_; lean_object* v___x_369_; 
lean_dec(v_needlePos_332_);
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = lean_nat_add(v_stackPos_331_, v___x_365_);
lean_dec(v_stackPos_331_);
v_nextStackPos_367_ = l_String_Slice_posGE___redArg(v___x_312_, v___x_366_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 3, v___x_350_);
lean_ctor_set(v___x_334_, 2, v_nextStackPos_367_);
v___x_369_ = v___x_334_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_needle_329_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_table_330_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_nextStackPos_367_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v___x_350_);
v___x_369_ = v_reuseFailAlloc_371_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
v_a_314_ = v___x_369_;
v_b_315_ = v___x_316_;
goto _start;
}
}
}
else
{
lean_object* v___x_372_; lean_object* v_nextStackPos_373_; lean_object* v_nextNeedlePos_374_; uint8_t v___x_375_; 
v___x_372_ = lean_unsigned_to_nat(1u);
v_nextStackPos_373_ = lean_nat_add(v_stackPos_331_, v___x_372_);
lean_dec(v_stackPos_331_);
v_nextNeedlePos_374_ = lean_nat_add(v_needlePos_332_, v___x_372_);
lean_dec(v_needlePos_332_);
v___x_375_ = lean_nat_dec_eq(v_nextNeedlePos_374_, v___x_340_);
lean_dec(v___x_340_);
if (v___x_375_ == 0)
{
lean_object* v___x_377_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 3, v_nextNeedlePos_374_);
lean_ctor_set(v___x_334_, 2, v_nextStackPos_373_);
v___x_377_ = v___x_334_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_needle_329_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_table_330_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_nextStackPos_373_);
lean_ctor_set(v_reuseFailAlloc_379_, 3, v_nextNeedlePos_374_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
v_a_314_ = v___x_377_;
goto _start;
}
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
lean_del_object(v___x_334_);
lean_dec_ref(v_table_330_);
lean_dec_ref(v_needle_329_);
v___x_380_ = lean_nat_sub(v_nextStackPos_373_, v_nextNeedlePos_374_);
lean_dec(v_nextNeedlePos_374_);
lean_dec(v_nextStackPos_373_);
v___x_381_ = l_String_Slice_pos_x21(v___x_312_, v___x_380_);
lean_dec(v___x_380_);
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
}
}
}
default: 
{
lean_inc(v_b_315_);
return v_b_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg___boxed(lean_object* v_s_384_, lean_object* v___x_385_, lean_object* v___x_386_, lean_object* v_a_387_, lean_object* v_b_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_384_, v___x_385_, v___x_386_, v_a_387_, v_b_388_);
lean_dec(v_b_388_);
lean_dec(v___x_386_);
lean_dec_ref(v___x_385_);
lean_dec_ref(v_s_384_);
return v_res_389_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0));
v___x_392_ = lean_string_utf8_byte_size(v___x_391_);
return v___x_392_;
}
}
static uint8_t _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1);
v___x_395_ = lean_nat_dec_eq(v___x_394_, v___x_393_);
return v___x_395_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_396_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1);
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0));
v___x_399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_397_);
lean_ctor_set(v___x_399_, 2, v___x_396_);
return v___x_399_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3);
v___x_401_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_400_);
return v___x_401_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4);
v___x_404_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3);
v___x_405_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
lean_ctor_set(v___x_405_, 2, v___x_402_);
lean_ctor_set(v___x_405_, 3, v___x_402_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(lean_object* v_s_408_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___y_413_; uint8_t v___x_424_; 
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = lean_string_utf8_byte_size(v_s_408_);
lean_inc_ref(v_s_408_);
v___x_411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_411_, 0, v_s_408_);
lean_ctor_set(v___x_411_, 1, v___x_409_);
lean_ctor_set(v___x_411_, 2, v___x_410_);
v___x_424_ = lean_uint8_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
v___x_425_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5);
v___y_413_ = v___x_425_;
goto v___jp_412_;
}
else
{
lean_object* v___x_426_; 
v___x_426_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__6));
v___y_413_ = v___x_426_;
goto v___jp_412_;
}
v___jp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_box(0);
lean_inc(v___y_413_);
v___x_415_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_408_, v___x_411_, v___x_410_, v___y_413_, v___x_414_);
lean_dec_ref_known(v___x_411_, 3);
lean_dec_ref(v_s_408_);
if (lean_obj_tag(v___x_415_) == 0)
{
return v___x_414_;
}
else
{
lean_object* v_val_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
v_val_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_val_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_val_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(lean_object* v_s_427_, lean_object* v___x_428_, lean_object* v___x_429_, lean_object* v_inst_430_, lean_object* v_R_431_, lean_object* v_a_432_, lean_object* v_b_433_, lean_object* v_c_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_427_, v___x_428_, v___x_429_, v_a_432_, v_b_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___boxed(lean_object* v_s_436_, lean_object* v___x_437_, lean_object* v___x_438_, lean_object* v_inst_439_, lean_object* v_R_440_, lean_object* v_a_441_, lean_object* v_b_442_, lean_object* v_c_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(v_s_436_, v___x_437_, v___x_438_, v_inst_439_, v_R_440_, v_a_441_, v_b_442_, v_c_443_);
lean_dec(v_b_442_);
lean_dec(v___x_438_);
lean_dec_ref(v___x_437_);
lean_dec_ref(v_s_436_);
return v_res_444_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(lean_object* v_text_445_, lean_object* v_pos_446_){
_start:
{
lean_object* v___x_447_; lean_object* v_line_448_; lean_object* v_source_449_; lean_object* v_lineStartPos_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v_lineEndPos_453_; lean_object* v_line_454_; lean_object* v___x_455_; 
lean_inc_ref(v_text_445_);
v___x_447_ = l_Lean_FileMap_toPosition(v_text_445_, v_pos_446_);
v_line_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_line_448_);
lean_dec_ref(v___x_447_);
v_source_449_ = lean_ctor_get(v_text_445_, 0);
lean_inc_ref(v_source_449_);
v_lineStartPos_450_ = l_Lean_FileMap_lineStart(v_text_445_, v_line_448_);
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_nat_add(v_line_448_, v___x_451_);
lean_dec(v_line_448_);
v_lineEndPos_453_ = l_Lean_FileMap_lineStart(v_text_445_, v___x_452_);
lean_dec(v___x_452_);
lean_dec_ref(v_text_445_);
v_line_454_ = lean_string_utf8_extract(v_source_449_, v_lineStartPos_450_, v_lineEndPos_453_);
lean_dec(v_lineEndPos_453_);
lean_dec_ref(v_source_449_);
v___x_455_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(v_line_454_);
if (lean_obj_tag(v___x_455_) == 1)
{
lean_object* v_val_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_val_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_val_456_);
lean_dec_ref_known(v___x_455_, 1);
v___x_457_ = lean_nat_add(v_lineStartPos_450_, v_val_456_);
lean_dec(v_val_456_);
lean_dec(v_lineStartPos_450_);
v___x_458_ = lean_nat_dec_le(v___x_457_, v_pos_446_);
lean_dec(v___x_457_);
return v___x_458_;
}
else
{
uint8_t v___x_459_; 
lean_dec(v___x_455_);
lean_dec(v_lineStartPos_450_);
v___x_459_ = 0;
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment___boxed(lean_object* v_text_460_, lean_object* v_pos_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_460_, v_pos_461_);
lean_dec(v_pos_461_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(lean_object* v_text_520_, lean_object* v_ctx_x3f_521_, lean_object* v_requestedPos_522_, lean_object* v_stx_523_, lean_object* v_parent_524_){
_start:
{
lean_object* v_kind_x3f_526_; uint8_t v___y_625_; uint8_t v___y_626_; uint8_t v___y_627_; uint8_t v___x_629_; lean_object* v___x_630_; 
v___x_629_ = 1;
v___x_630_ = l_Lean_Syntax_getTailPos_x3f(v_stx_523_, v___x_629_);
if (lean_obj_tag(v___x_630_) == 1)
{
lean_object* v_val_631_; uint8_t v___x_632_; uint8_t v___y_634_; uint8_t v___y_635_; uint8_t v___y_642_; 
v_val_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = lean_nat_dec_lt(v_requestedPos_522_, v_val_631_);
if (v___x_632_ == 0)
{
if (lean_obj_tag(v_ctx_x3f_521_) == 0)
{
v___y_642_ = v___x_632_;
goto v___jp_641_;
}
else
{
lean_object* v_val_645_; uint8_t v_triggerKind_646_; 
v_val_645_ = lean_ctor_get(v_ctx_x3f_521_, 0);
v_triggerKind_646_ = lean_ctor_get_uint8(v_val_645_, sizeof(void*)*2);
if (v_triggerKind_646_ == 0)
{
v___y_642_ = v___x_629_;
goto v___jp_641_;
}
else
{
v___y_642_ = v___x_632_;
goto v___jp_641_;
}
}
}
else
{
lean_object* v___x_647_; 
lean_dec(v_val_631_);
lean_dec(v_parent_524_);
lean_dec(v_stx_523_);
lean_dec_ref(v_text_520_);
v___x_647_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23));
return v___x_647_;
}
v___jp_633_:
{
lean_object* v___x_636_; lean_object* v_line_637_; lean_object* v___x_638_; lean_object* v_line_639_; uint8_t v___x_640_; 
lean_inc_ref(v_text_520_);
v___x_636_ = l_Lean_FileMap_toPosition(v_text_520_, v_requestedPos_522_);
v_line_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_line_637_);
lean_dec_ref(v___x_636_);
v___x_638_ = l_Lean_FileMap_toPosition(v_text_520_, v_val_631_);
lean_dec(v_val_631_);
v_line_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_line_639_);
lean_dec_ref(v___x_638_);
v___x_640_ = lean_nat_dec_eq(v_line_637_, v_line_639_);
lean_dec(v_line_639_);
lean_dec(v_line_637_);
if (v___x_640_ == 0)
{
v___y_625_ = v___y_634_;
v___y_626_ = v___y_635_;
v___y_627_ = v___x_629_;
goto v___jp_624_;
}
else
{
v___y_625_ = v___y_634_;
v___y_626_ = v___y_635_;
v___y_627_ = v___x_632_;
goto v___jp_624_;
}
}
v___jp_641_:
{
if (lean_obj_tag(v_ctx_x3f_521_) == 0)
{
v___y_634_ = v___y_642_;
v___y_635_ = v___x_632_;
goto v___jp_633_;
}
else
{
lean_object* v_val_643_; uint8_t v_isRetrigger_644_; 
v_val_643_ = lean_ctor_get(v_ctx_x3f_521_, 0);
v_isRetrigger_644_ = lean_ctor_get_uint8(v_val_643_, sizeof(void*)*2 + 1);
v___y_634_ = v___y_642_;
v___y_635_ = v_isRetrigger_644_;
goto v___jp_633_;
}
}
}
else
{
lean_object* v___x_648_; 
lean_dec(v___x_630_);
lean_dec(v_parent_524_);
lean_dec(v_stx_523_);
lean_dec_ref(v_text_520_);
v___x_648_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22));
return v___x_648_;
}
v___jp_525_:
{
uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_527_ = 0;
v___x_528_ = lean_box(v___x_527_);
lean_inc(v_kind_x3f_526_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_kind_x3f_526_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
return v___x_529_;
}
v___jp_530_:
{
if (lean_obj_tag(v_stx_523_) == 3)
{
lean_object* v___x_531_; uint8_t v___x_532_; 
lean_dec_ref_known(v_stx_523_, 4);
v___x_531_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4));
lean_inc(v_parent_524_);
v___x_532_ = l_Lean_Syntax_isOfKind(v_parent_524_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6));
lean_inc(v_parent_524_);
v___x_534_ = l_Lean_Syntax_isOfKind(v_parent_524_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8));
lean_inc(v_parent_524_);
v___x_536_ = l_Lean_Syntax_isOfKind(v_parent_524_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
lean_dec(v_parent_524_);
v___x_537_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_526_ = v___x_537_;
goto v___jp_525_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = l_Lean_Syntax_getArg(v_parent_524_, v___x_538_);
lean_dec(v_parent_524_);
v___x_540_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_541_ = l_Lean_Syntax_isOfKind(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
v___x_542_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_526_ = v___x_542_;
goto v___jp_525_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = lean_box(0);
v_kind_x3f_526_ = v___x_543_;
goto v___jp_525_;
}
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_544_ = lean_unsigned_to_nat(2u);
v___x_545_ = l_Lean_Syntax_getArg(v_parent_524_, v___x_544_);
lean_dec(v_parent_524_);
v___x_546_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_547_ = l_Lean_Syntax_isOfKind(v___x_545_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
v___x_548_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_526_ = v___x_548_;
goto v___jp_525_;
}
else
{
lean_object* v___x_549_; 
v___x_549_ = lean_box(0);
v_kind_x3f_526_ = v___x_549_;
goto v___jp_525_;
}
}
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_550_ = lean_unsigned_to_nat(2u);
v___x_551_ = l_Lean_Syntax_getArg(v_parent_524_, v___x_550_);
v___x_552_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_553_ = l_Lean_Syntax_isOfKind(v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_dec(v_parent_524_);
v___x_554_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_526_ = v___x_554_;
goto v___jp_525_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = lean_unsigned_to_nat(3u);
v___x_557_ = l_Lean_Syntax_getArg(v_parent_524_, v___x_556_);
lean_dec(v_parent_524_);
v___x_558_ = l_Lean_Syntax_matchesNull(v___x_557_, v___x_555_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_526_ = v___x_559_;
goto v___jp_525_;
}
else
{
lean_object* v___x_560_; 
v___x_560_ = lean_box(0);
v_kind_x3f_526_ = v___x_560_;
goto v___jp_525_;
}
}
}
}
else
{
lean_dec(v_parent_524_);
if (lean_obj_tag(v_stx_523_) == 1)
{
lean_object* v_kind_561_; lean_object* v_args_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_kind_561_ = lean_ctor_get(v_stx_523_, 1);
v_args_562_ = lean_ctor_get(v_stx_523_, 2);
lean_inc_ref(v_args_562_);
v___x_563_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13));
v___x_564_ = lean_name_eq(v_kind_561_, v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15));
v___x_566_ = lean_name_eq(v_kind_561_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_567_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17));
lean_inc_ref(v_stx_523_);
v___x_568_ = l_Lean_Syntax_isOfKind(v_stx_523_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19));
lean_inc_ref(v_stx_523_);
v___x_570_ = l_Lean_Syntax_isOfKind(v_stx_523_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4));
lean_inc_ref(v_stx_523_);
v___x_572_ = l_Lean_Syntax_isOfKind(v_stx_523_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_573_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8));
lean_inc_ref(v_stx_523_);
v___x_574_ = l_Lean_Syntax_isOfKind(v_stx_523_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6));
lean_inc_ref(v_stx_523_);
v___x_576_ = l_Lean_Syntax_isOfKind(v_stx_523_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
lean_dec_ref_known(v_stx_523_, 3);
v___x_577_ = lean_array_get_size(v_args_562_);
lean_dec_ref(v_args_562_);
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_dec_le(v___x_577_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_526_ = v___x_580_;
goto v___jp_525_;
}
else
{
lean_object* v___x_581_; 
v___x_581_ = lean_box(0);
v_kind_x3f_526_ = v___x_581_;
goto v___jp_525_;
}
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_582_ = lean_unsigned_to_nat(2u);
v___x_583_ = l_Lean_Syntax_getArg(v_stx_523_, v___x_582_);
lean_dec_ref_known(v_stx_523_, 3);
v___x_584_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_585_ = l_Lean_Syntax_isOfKind(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = lean_array_get_size(v_args_562_);
lean_dec_ref(v_args_562_);
v___x_588_ = lean_nat_dec_le(v___x_587_, v___x_586_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
v___x_589_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_526_ = v___x_589_;
goto v___jp_525_;
}
else
{
lean_object* v___x_590_; 
v___x_590_ = lean_box(0);
v_kind_x3f_526_ = v___x_590_;
goto v___jp_525_;
}
}
else
{
lean_object* v___x_591_; 
lean_dec_ref(v_args_562_);
v___x_591_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_526_ = v___x_591_;
goto v___jp_525_;
}
}
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = l_Lean_Syntax_getArg(v_stx_523_, v___x_592_);
lean_dec_ref_known(v_stx_523_, 3);
v___x_594_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_595_ = l_Lean_Syntax_isOfKind(v___x_593_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_array_get_size(v_args_562_);
lean_dec_ref(v_args_562_);
v___x_597_ = lean_nat_dec_le(v___x_596_, v___x_592_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
v___x_598_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_526_ = v___x_598_;
goto v___jp_525_;
}
else
{
lean_object* v___x_599_; 
v___x_599_ = lean_box(0);
v_kind_x3f_526_ = v___x_599_;
goto v___jp_525_;
}
}
else
{
lean_object* v___x_600_; 
lean_dec_ref(v_args_562_);
v___x_600_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_526_ = v___x_600_;
goto v___jp_525_;
}
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = lean_unsigned_to_nat(2u);
v___x_603_ = l_Lean_Syntax_getArg(v_stx_523_, v___x_602_);
v___x_604_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_605_ = l_Lean_Syntax_isOfKind(v___x_603_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; uint8_t v___x_607_; 
lean_dec_ref_known(v_stx_523_, 3);
v___x_606_ = lean_array_get_size(v_args_562_);
lean_dec_ref(v_args_562_);
v___x_607_ = lean_nat_dec_le(v___x_606_, v___x_601_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
v___x_608_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_526_ = v___x_608_;
goto v___jp_525_;
}
else
{
lean_object* v___x_609_; 
v___x_609_ = lean_box(0);
v_kind_x3f_526_ = v___x_609_;
goto v___jp_525_;
}
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_unsigned_to_nat(3u);
v___x_612_ = l_Lean_Syntax_getArg(v_stx_523_, v___x_611_);
lean_dec_ref_known(v_stx_523_, 3);
v___x_613_ = l_Lean_Syntax_matchesNull(v___x_612_, v___x_610_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_array_get_size(v_args_562_);
lean_dec_ref(v_args_562_);
v___x_615_ = lean_nat_dec_le(v___x_614_, v___x_601_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
v___x_616_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_526_ = v___x_616_;
goto v___jp_525_;
}
else
{
lean_object* v___x_617_; 
v___x_617_ = lean_box(0);
v_kind_x3f_526_ = v___x_617_;
goto v___jp_525_;
}
}
else
{
lean_object* v___x_618_; 
lean_dec_ref(v_args_562_);
v___x_618_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20));
v_kind_x3f_526_ = v___x_618_;
goto v___jp_525_;
}
}
}
}
else
{
lean_object* v___x_619_; 
lean_dec_ref(v_args_562_);
lean_dec_ref_known(v_stx_523_, 3);
v___x_619_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20));
v_kind_x3f_526_ = v___x_619_;
goto v___jp_525_;
}
}
else
{
lean_object* v___x_620_; 
lean_dec_ref(v_args_562_);
lean_dec_ref_known(v_stx_523_, 3);
v___x_620_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20));
v_kind_x3f_526_ = v___x_620_;
goto v___jp_525_;
}
}
else
{
lean_object* v___x_621_; 
lean_dec_ref(v_args_562_);
lean_dec_ref_known(v_stx_523_, 3);
v___x_621_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21));
v_kind_x3f_526_ = v___x_621_;
goto v___jp_525_;
}
}
else
{
lean_object* v___x_622_; 
lean_dec_ref(v_args_562_);
lean_dec_ref_known(v_stx_523_, 3);
v___x_622_ = lean_box(0);
v_kind_x3f_526_ = v___x_622_;
goto v___jp_525_;
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v_stx_523_);
v___x_623_ = lean_box(0);
v_kind_x3f_526_ = v___x_623_;
goto v___jp_525_;
}
}
}
v___jp_624_:
{
if (v___y_625_ == 0)
{
if (v___y_626_ == 0)
{
if (v___y_627_ == 0)
{
goto v___jp_530_;
}
else
{
lean_object* v___x_628_; 
lean_dec(v_parent_524_);
lean_dec(v_stx_523_);
v___x_628_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22));
return v___x_628_;
}
}
else
{
goto v___jp_530_;
}
}
else
{
goto v___jp_530_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___boxed(lean_object* v_text_649_, lean_object* v_ctx_x3f_650_, lean_object* v_requestedPos_651_, lean_object* v_stx_652_, lean_object* v_parent_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_649_, v_ctx_x3f_650_, v_requestedPos_651_, v_stx_652_, v_parent_653_);
lean_dec(v_requestedPos_651_);
lean_dec(v_ctx_x3f_650_);
return v_res_654_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(uint8_t v___x_655_, lean_object* v_stx_656_){
_start:
{
uint8_t v___x_657_; 
v___x_657_ = l_Lean_Syntax_hasArgs(v_stx_656_);
if (v___x_657_ == 0)
{
uint8_t v___x_658_; 
v___x_658_ = 1;
return v___x_658_;
}
else
{
return v___x_655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed(lean_object* v___x_659_, lean_object* v_stx_660_){
_start:
{
uint8_t v___x_3193__boxed_661_; uint8_t v_res_662_; lean_object* v_r_663_; 
v___x_3193__boxed_661_ = lean_unbox(v___x_659_);
v_res_662_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(v___x_3193__boxed_661_, v_stx_660_);
lean_dec(v_stx_660_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(uint8_t v___x_664_, lean_object* v_requestedPos_665_, uint8_t v___x_666_, lean_object* v_stx_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_667_, v___x_664_);
if (lean_obj_tag(v___x_668_) == 1)
{
lean_object* v_val_669_; uint8_t v___x_670_; 
v_val_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_val_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = l_Lean_Syntax_Range_contains(v_val_669_, v_requestedPos_665_, v___x_664_);
lean_dec(v_val_669_);
return v___x_670_;
}
else
{
lean_dec(v___x_668_);
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed(lean_object* v___x_671_, lean_object* v_requestedPos_672_, lean_object* v___x_673_, lean_object* v_stx_674_){
_start:
{
uint8_t v___x_3200__boxed_675_; uint8_t v___x_3201__boxed_676_; uint8_t v_res_677_; lean_object* v_r_678_; 
v___x_3200__boxed_675_ = lean_unbox(v___x_671_);
v___x_3201__boxed_676_ = lean_unbox(v___x_673_);
v_res_677_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(v___x_3200__boxed_675_, v_requestedPos_672_, v___x_3201__boxed_676_, v_stx_674_);
lean_dec(v_stx_674_);
lean_dec(v_requestedPos_672_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(lean_object* v_c1_679_, lean_object* v_c2_680_){
_start:
{
uint8_t v_kind_681_; uint8_t v_kind_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_kind_681_ = lean_ctor_get_uint8(v_c2_680_, sizeof(void*)*1);
v_kind_682_ = lean_ctor_get_uint8(v_c1_679_, sizeof(void*)*1);
v___x_683_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_681_);
v___x_684_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_682_);
v___x_685_ = lean_nat_dec_le(v___x_683_, v___x_684_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2___boxed(lean_object* v_c1_686_, lean_object* v_c2_687_){
_start:
{
uint8_t v_res_688_; lean_object* v_r_689_; 
v_res_688_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(v_c1_686_, v_c2_687_);
lean_dec_ref(v_c2_687_);
lean_dec_ref(v_c1_686_);
v_r_689_ = lean_box(v_res_688_);
return v_r_689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(lean_object* v_tree_698_, uint8_t v___y_699_, uint8_t v___x_700_, lean_object* v_as_701_, size_t v_sz_702_, size_t v_i_703_, lean_object* v_b_704_){
_start:
{
uint8_t v___x_706_; 
v___x_706_ = lean_usize_dec_lt(v_i_703_, v_sz_702_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
lean_dec_ref(v_tree_698_);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v_b_704_);
return v___x_707_;
}
else
{
lean_object* v_a_708_; uint8_t v_kind_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec_ref(v_b_704_);
v_a_708_ = lean_array_uget_borrowed(v_as_701_, v_i_703_);
v_kind_709_ = lean_ctor_get_uint8(v_a_708_, sizeof(void*)*1);
v___x_710_ = lean_box(0);
v___x_711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0));
if (v_kind_709_ == 1)
{
goto v___jp_736_;
}
else
{
if (v___x_700_ == 0)
{
goto v___jp_712_;
}
else
{
goto v___jp_736_;
}
}
v___jp_712_:
{
lean_object* v_appStx_713_; lean_object* v___x_714_; 
v_appStx_713_ = lean_ctor_get(v_a_708_, 0);
lean_inc(v_appStx_713_);
lean_inc_ref(v_tree_698_);
v___x_714_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_698_, v_appStx_713_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_727_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_727_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_727_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_727_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
if (lean_obj_tag(v_a_715_) == 1)
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
lean_dec_ref(v_tree_698_);
v___x_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_719_, 0, v_a_715_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___x_710_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_720_);
v___x_722_ = v___x_717_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
else
{
size_t v___x_724_; size_t v___x_725_; 
lean_del_object(v___x_717_);
lean_dec(v_a_715_);
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_add(v_i_703_, v___x_724_);
v_i_703_ = v___x_725_;
v_b_704_ = v___x_711_;
goto _start;
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec_ref(v_tree_698_);
v_a_728_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_714_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_714_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
v___jp_736_:
{
if (v___y_699_ == 0)
{
goto v___jp_712_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; 
lean_dec_ref(v_tree_698_);
v___x_737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__2));
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___boxed(lean_object* v_tree_739_, lean_object* v___y_740_, lean_object* v___x_741_, lean_object* v_as_742_, lean_object* v_sz_743_, lean_object* v_i_744_, lean_object* v_b_745_, lean_object* v___y_746_){
_start:
{
uint8_t v___y_3234__boxed_747_; uint8_t v___x_3235__boxed_748_; size_t v_sz_boxed_749_; size_t v_i_boxed_750_; lean_object* v_res_751_; 
v___y_3234__boxed_747_ = lean_unbox(v___y_740_);
v___x_3235__boxed_748_ = lean_unbox(v___x_741_);
v_sz_boxed_749_ = lean_unbox_usize(v_sz_743_);
lean_dec(v_sz_743_);
v_i_boxed_750_ = lean_unbox_usize(v_i_744_);
lean_dec(v_i_744_);
v_res_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v_tree_739_, v___y_3234__boxed_747_, v___x_3235__boxed_748_, v_as_742_, v_sz_boxed_749_, v_i_boxed_750_, v_b_745_);
lean_dec_ref(v_as_742_);
return v_res_751_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0(void){
_start:
{
uint8_t v___x_752_; lean_object* v___x_753_; 
v___x_752_ = 1;
v___x_753_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(lean_object* v_as_754_, size_t v_i_755_, size_t v_stop_756_){
_start:
{
uint8_t v___x_757_; 
v___x_757_ = lean_usize_dec_eq(v_i_755_, v_stop_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; uint8_t v_kind_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_758_ = lean_array_uget_borrowed(v_as_754_, v_i_755_);
v_kind_759_ = lean_ctor_get_uint8(v___x_758_, sizeof(void*)*1);
v___x_760_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0);
v___x_761_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_759_);
v___x_762_ = lean_nat_dec_lt(v___x_760_, v___x_761_);
lean_dec(v___x_761_);
if (v___x_762_ == 0)
{
size_t v___x_763_; size_t v___x_764_; 
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_add(v_i_755_, v___x_763_);
v_i_755_ = v___x_764_;
goto _start;
}
else
{
return v___x_762_;
}
}
else
{
uint8_t v___x_766_; 
v___x_766_ = 0;
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___boxed(lean_object* v_as_767_, lean_object* v_i_768_, lean_object* v_stop_769_){
_start:
{
size_t v_i_boxed_770_; size_t v_stop_boxed_771_; uint8_t v_res_772_; lean_object* v_r_773_; 
v_i_boxed_770_ = lean_unbox_usize(v_i_768_);
lean_dec(v_i_768_);
v_stop_boxed_771_ = lean_unbox_usize(v_stop_769_);
lean_dec(v_stop_769_);
v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v_as_767_, v_i_boxed_770_, v_stop_boxed_771_);
lean_dec_ref(v_as_767_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(uint8_t v_snd_774_, uint8_t v___x_775_, lean_object* v_____r_776_, lean_object* v_candidates_777_){
_start:
{
if (v_snd_774_ == 1)
{
goto v___jp_779_;
}
else
{
if (v___x_775_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_782_, 0, v_candidates_777_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
else
{
goto v___jp_779_;
}
}
v___jp_779_:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v_candidates_777_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0___boxed(lean_object* v_snd_784_, lean_object* v___x_785_, lean_object* v_____r_786_, lean_object* v_candidates_787_, lean_object* v___y_788_){
_start:
{
uint8_t v_snd_3336__boxed_789_; uint8_t v___x_3337__boxed_790_; lean_object* v_res_791_; 
v_snd_3336__boxed_789_ = lean_unbox(v_snd_784_);
v___x_3337__boxed_790_ = lean_unbox(v___x_785_);
v_res_791_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v_snd_3336__boxed_789_, v___x_3337__boxed_790_, v_____r_786_, v_candidates_787_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(lean_object* v_upperBound_792_, lean_object* v_stack_793_, lean_object* v_text_794_, lean_object* v_ctx_x3f_795_, lean_object* v_requestedPos_796_, uint8_t v___x_797_, lean_object* v_a_798_, lean_object* v_b_799_){
_start:
{
lean_object* v___y_802_; uint8_t v___x_824_; 
v___x_824_ = lean_nat_dec_lt(v_a_798_, v_upperBound_792_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
lean_dec(v_a_798_);
lean_dec_ref(v_text_794_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v_b_799_);
return v___x_825_;
}
else
{
lean_object* v___x_826_; lean_object* v___y_828_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_826_ = lean_array_fget_borrowed(v_stack_793_, v_a_798_);
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_nat_add(v_a_798_, v___x_843_);
v___x_845_ = lean_array_get_size(v_stack_793_);
v___x_846_ = lean_nat_dec_lt(v___x_844_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v___y_828_ = v___x_847_;
goto v___jp_827_;
}
else
{
lean_object* v___x_848_; 
v___x_848_ = lean_array_fget_borrowed(v_stack_793_, v___x_844_);
lean_dec(v___x_844_);
lean_inc(v___x_848_);
v___y_828_ = v___x_848_;
goto v___jp_827_;
}
v___jp_827_:
{
lean_object* v___x_829_; lean_object* v_fst_830_; 
lean_inc(v___x_826_);
lean_inc_ref(v_text_794_);
v___x_829_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_794_, v_ctx_x3f_795_, v_requestedPos_796_, v___x_826_, v___y_828_);
v_fst_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_fst_830_);
if (lean_obj_tag(v_fst_830_) == 1)
{
lean_object* v_snd_831_; lean_object* v_val_832_; lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; 
v_snd_831_ = lean_ctor_get(v___x_829_, 1);
lean_inc(v_snd_831_);
lean_dec_ref(v___x_829_);
v_val_832_ = lean_ctor_get(v_fst_830_, 0);
lean_inc(v_val_832_);
lean_dec_ref_known(v_fst_830_, 1);
lean_inc(v___x_826_);
v___x_833_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_833_, 0, v___x_826_);
v___x_834_ = lean_unbox(v_val_832_);
lean_dec(v_val_832_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*1, v___x_834_);
v___x_835_ = lean_array_push(v_b_799_, v___x_833_);
v___x_836_ = lean_box(0);
v___x_837_ = lean_unbox(v_snd_831_);
lean_dec(v_snd_831_);
v___x_838_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_837_, v___x_797_, v___x_836_, v___x_835_);
v___y_802_ = v___x_838_;
goto v___jp_801_;
}
else
{
lean_object* v_snd_839_; lean_object* v___x_840_; uint8_t v___x_841_; lean_object* v___x_842_; 
lean_dec(v_fst_830_);
v_snd_839_ = lean_ctor_get(v___x_829_, 1);
lean_inc(v_snd_839_);
lean_dec_ref(v___x_829_);
v___x_840_ = lean_box(0);
v___x_841_ = lean_unbox(v_snd_839_);
lean_dec(v_snd_839_);
v___x_842_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_841_, v___x_797_, v___x_840_, v_b_799_);
v___y_802_ = v___x_842_;
goto v___jp_801_;
}
}
}
v___jp_801_:
{
if (lean_obj_tag(v___y_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_815_; 
v_a_803_ = lean_ctor_get(v___y_802_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___y_802_);
if (v_isSharedCheck_815_ == 0)
{
v___x_805_ = v___y_802_;
v_isShared_806_ = v_isSharedCheck_815_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___y_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_815_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
if (lean_obj_tag(v_a_803_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_809_; 
lean_dec(v_a_798_);
lean_dec_ref(v_text_794_);
v_a_807_ = lean_ctor_get(v_a_803_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v_a_803_, 1);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v_a_807_);
v___x_809_ = v___x_805_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
lean_del_object(v___x_805_);
v_a_811_ = lean_ctor_get(v_a_803_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v_a_803_, 1);
v___x_812_ = lean_unsigned_to_nat(1u);
v___x_813_ = lean_nat_add(v_a_798_, v___x_812_);
lean_dec(v_a_798_);
v_a_798_ = v___x_813_;
v_b_799_ = v_a_811_;
goto _start;
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec(v_a_798_);
lean_dec_ref(v_text_794_);
v_a_816_ = lean_ctor_get(v___y_802_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___y_802_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___y_802_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___y_802_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___boxed(lean_object* v_upperBound_849_, lean_object* v_stack_850_, lean_object* v_text_851_, lean_object* v_ctx_x3f_852_, lean_object* v_requestedPos_853_, lean_object* v___x_854_, lean_object* v_a_855_, lean_object* v_b_856_, lean_object* v___y_857_){
_start:
{
uint8_t v___x_3359__boxed_858_; lean_object* v_res_859_; 
v___x_3359__boxed_858_ = lean_unbox(v___x_854_);
v_res_859_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_849_, v_stack_850_, v_text_851_, v_ctx_x3f_852_, v_requestedPos_853_, v___x_3359__boxed_858_, v_a_855_, v_b_856_);
lean_dec(v_requestedPos_853_);
lean_dec(v_ctx_x3f_852_);
lean_dec_ref(v_stack_850_);
lean_dec(v_upperBound_849_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(size_t v_sz_860_, size_t v_i_861_, lean_object* v_bs_862_){
_start:
{
uint8_t v___x_863_; 
v___x_863_ = lean_usize_dec_lt(v_i_861_, v_sz_860_);
if (v___x_863_ == 0)
{
return v_bs_862_;
}
else
{
lean_object* v_v_864_; lean_object* v_fst_865_; lean_object* v___x_866_; lean_object* v_bs_x27_867_; size_t v___x_868_; size_t v___x_869_; lean_object* v___x_870_; 
v_v_864_ = lean_array_uget_borrowed(v_bs_862_, v_i_861_);
v_fst_865_ = lean_ctor_get(v_v_864_, 0);
lean_inc(v_fst_865_);
v___x_866_ = lean_unsigned_to_nat(0u);
v_bs_x27_867_ = lean_array_uset(v_bs_862_, v_i_861_, v___x_866_);
v___x_868_ = ((size_t)1ULL);
v___x_869_ = lean_usize_add(v_i_861_, v___x_868_);
v___x_870_ = lean_array_uset(v_bs_x27_867_, v_i_861_, v_fst_865_);
v_i_861_ = v___x_869_;
v_bs_862_ = v___x_870_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0___boxed(lean_object* v_sz_872_, lean_object* v_i_873_, lean_object* v_bs_874_){
_start:
{
size_t v_sz_boxed_875_; size_t v_i_boxed_876_; lean_object* v_res_877_; 
v_sz_boxed_875_ = lean_unbox_usize(v_sz_872_);
lean_dec(v_sz_872_);
v_i_boxed_876_ = lean_unbox_usize(v_i_873_);
lean_dec(v_i_873_);
v_res_877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_sz_boxed_875_, v_i_boxed_876_, v_bs_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(lean_object* v_text_881_, lean_object* v_ctx_x3f_882_, lean_object* v_cmdStx_883_, lean_object* v_tree_884_, lean_object* v_requestedPos_885_){
_start:
{
uint8_t v___x_887_; 
lean_inc_ref(v_text_881_);
v___x_887_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_881_, v_requestedPos_885_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; lean_object* v___f_889_; uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___f_893_; lean_object* v_stack_x3f_894_; 
v___x_888_ = lean_box(v___x_887_);
v___f_889_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_889_, 0, v___x_888_);
v___x_890_ = 1;
v___x_891_ = lean_box(v___x_890_);
v___x_892_ = lean_box(v___x_887_);
lean_inc(v_requestedPos_885_);
v___f_893_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed), 4, 3);
lean_closure_set(v___f_893_, 0, v___x_891_);
lean_closure_set(v___f_893_, 1, v_requestedPos_885_);
lean_closure_set(v___f_893_, 2, v___x_892_);
v_stack_x3f_894_ = l_Lean_Syntax_findStack_x3f(v_cmdStx_883_, v___f_893_, v___f_889_);
if (lean_obj_tag(v_stack_x3f_894_) == 1)
{
lean_object* v_val_895_; lean_object* v___x_896_; size_t v_sz_897_; size_t v___x_898_; lean_object* v_stack_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_candidates_902_; lean_object* v___x_903_; 
v_val_895_ = lean_ctor_get(v_stack_x3f_894_, 0);
lean_inc(v_val_895_);
lean_dec_ref_known(v_stack_x3f_894_, 1);
v___x_896_ = lean_array_mk(v_val_895_);
v_sz_897_ = lean_array_size(v___x_896_);
v___x_898_ = ((size_t)0ULL);
v_stack_899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_sz_897_, v___x_898_, v___x_896_);
v___x_900_ = lean_array_get_size(v_stack_899_);
v___x_901_ = lean_unsigned_to_nat(0u);
v_candidates_902_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0));
v___x_903_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v___x_900_, v_stack_899_, v_text_881_, v_ctx_x3f_882_, v_requestedPos_885_, v___x_887_, v___x_901_, v_candidates_902_);
lean_dec(v_requestedPos_885_);
lean_dec_ref(v_stack_899_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___f_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___y_910_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_903_, 1);
v___f_905_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1));
v___x_906_ = lean_array_to_list(v_a_904_);
v___x_907_ = l_List_mergeSort___redArg(v___x_906_, v___f_905_);
v___x_908_ = lean_array_mk(v___x_907_);
v___x_936_ = lean_array_get_size(v___x_908_);
v___x_937_ = lean_nat_dec_lt(v___x_901_, v___x_936_);
if (v___x_937_ == 0)
{
v___y_910_ = v___x_887_;
goto v___jp_909_;
}
else
{
if (v___x_937_ == 0)
{
v___y_910_ = v___x_887_;
goto v___jp_909_;
}
else
{
size_t v___x_938_; uint8_t v___x_939_; 
v___x_938_ = lean_usize_of_nat(v___x_936_);
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v___x_908_, v___x_898_, v___x_938_);
v___y_910_ = v___x_939_;
goto v___jp_909_;
}
}
v___jp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; size_t v_sz_913_; lean_object* v___x_914_; 
v___x_911_ = lean_box(0);
v___x_912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0));
v_sz_913_ = lean_array_size(v___x_908_);
v___x_914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v_tree_884_, v___y_910_, v___x_887_, v___x_908_, v_sz_913_, v___x_898_, v___x_912_);
lean_dec_ref(v___x_908_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_927_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_927_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_927_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_927_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v_fst_919_; 
v_fst_919_ = lean_ctor_get(v_a_915_, 0);
lean_inc(v_fst_919_);
lean_dec(v_a_915_);
if (lean_obj_tag(v_fst_919_) == 0)
{
lean_object* v___x_921_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_911_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_911_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
else
{
lean_object* v_val_923_; lean_object* v___x_925_; 
v_val_923_ = lean_ctor_get(v_fst_919_, 0);
lean_inc(v_val_923_);
lean_dec_ref_known(v_fst_919_, 1);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v_val_923_);
v___x_925_ = v___x_917_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_val_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_914_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_914_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v_tree_884_);
v_a_940_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_903_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_903_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec(v_stack_x3f_894_);
lean_dec(v_requestedPos_885_);
lean_dec_ref(v_tree_884_);
lean_dec_ref(v_text_881_);
v___x_948_ = lean_box(0);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec(v_requestedPos_885_);
lean_dec_ref(v_tree_884_);
lean_dec(v_cmdStx_883_);
lean_dec_ref(v_text_881_);
v___x_950_ = lean_box(0);
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___boxed(lean_object* v_text_952_, lean_object* v_ctx_x3f_953_, lean_object* v_cmdStx_954_, lean_object* v_tree_955_, lean_object* v_requestedPos_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(v_text_952_, v_ctx_x3f_953_, v_cmdStx_954_, v_tree_955_, v_requestedPos_956_);
lean_dec(v_ctx_x3f_953_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(lean_object* v_upperBound_959_, lean_object* v_stack_960_, lean_object* v_text_961_, lean_object* v_ctx_x3f_962_, lean_object* v_requestedPos_963_, uint8_t v___x_964_, lean_object* v_inst_965_, lean_object* v_R_966_, lean_object* v_a_967_, lean_object* v_b_968_, lean_object* v_c_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_959_, v_stack_960_, v_text_961_, v_ctx_x3f_962_, v_requestedPos_963_, v___x_964_, v_a_967_, v_b_968_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___boxed(lean_object* v_upperBound_972_, lean_object* v_stack_973_, lean_object* v_text_974_, lean_object* v_ctx_x3f_975_, lean_object* v_requestedPos_976_, lean_object* v___x_977_, lean_object* v_inst_978_, lean_object* v_R_979_, lean_object* v_a_980_, lean_object* v_b_981_, lean_object* v_c_982_, lean_object* v___y_983_){
_start:
{
uint8_t v___x_3606__boxed_984_; lean_object* v_res_985_; 
v___x_3606__boxed_984_ = lean_unbox(v___x_977_);
v_res_985_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(v_upperBound_972_, v_stack_973_, v_text_974_, v_ctx_x3f_975_, v_requestedPos_976_, v___x_3606__boxed_984_, v_inst_978_, v_R_979_, v_a_980_, v_b_981_, v_c_982_);
lean_dec(v_requestedPos_976_);
lean_dec(v_ctx_x3f_975_);
lean_dec_ref(v_stack_973_);
lean_dec(v_upperBound_972_);
return v_res_985_;
}
}
lean_object* runtime_initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileWorker_SignatureHelp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
