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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_findStack_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed(lean_object*);
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
static const lean_closure_object l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0_value;
static const lean_array_object l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1_value;
static const lean_closure_object l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__2_value;
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
uint8_t v___x_16_; uint8_t v___x_17_; 
v___x_16_ = l_Lean_Expr_hasMVar(v_e_13_);
v___x_17_ = lean_bool_not(v___x_16_);
if (v___x_17_ == 0)
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
else
{
lean_object* v___x_38_; 
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v_e_13_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_e_39_, v___y_40_);
lean_dec(v___y_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1(lean_object* v_e_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_e_43_, v___y_45_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___boxed(lean_object* v_e_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1(v_e_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_56_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0(lean_object* v_appStx_57_, lean_object* v_x_58_){
_start:
{
if (lean_obj_tag(v_x_58_) == 1)
{
lean_object* v_i_59_; lean_object* v_toElabInfo_60_; lean_object* v_stx_61_; uint8_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v_i_59_ = lean_ctor_get(v_x_58_, 0);
v_toElabInfo_60_ = lean_ctor_get(v_i_59_, 0);
v_stx_61_ = lean_ctor_get(v_toElabInfo_60_, 1);
v___x_62_ = 0;
v___x_63_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_61_, v___x_62_);
v___x_64_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_appStx_57_, v___x_62_);
v___x_65_ = l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(v___x_63_, v___x_64_);
lean_dec(v___x_64_);
lean_dec(v___x_63_);
return v___x_65_;
}
else
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0___boxed(lean_object* v_appStx_67_, lean_object* v_x_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0(v_appStx_67_, v_x_68_);
lean_dec_ref(v_x_68_);
lean_dec(v_appStx_67_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1(lean_object* v_expr_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v___x_78_; 
lean_inc(v___y_76_);
lean_inc_ref(v___y_75_);
lean_inc(v___y_74_);
lean_inc_ref(v___y_73_);
v___x_78_ = lean_infer_type(v_expr_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_80_; lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_122_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_a_79_);
lean_dec_ref_known(v___x_78_, 1);
v___x_80_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_a_79_, v___y_74_);
v_a_81_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_122_ == 0)
{
v___x_83_ = v___x_80_;
v_isShared_84_ = v_isSharedCheck_122_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_122_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
uint8_t v___x_85_; uint8_t v___x_86_; 
v___x_85_ = l_Lean_Expr_isForall(v_a_81_);
v___x_86_ = lean_bool_not(v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
lean_del_object(v___x_83_);
v___x_87_ = lean_box(1);
v___x_88_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___closed__0));
v___x_89_ = l_Lean_PrettyPrinter_delabCore___redArg(v_a_81_, v___x_87_, v___x_88_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v_a_90_; lean_object* v_fst_91_; lean_object* v___x_92_; 
v_a_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_a_90_);
lean_dec_ref_known(v___x_89_, 1);
v_fst_91_ = lean_ctor_get(v_a_90_, 0);
lean_inc(v_fst_91_);
lean_dec(v_a_90_);
v___x_92_ = l_Lean_PrettyPrinter_ppTerm(v_fst_91_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_101_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_101_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_101_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_101_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v_a_93_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_97_);
v___x_99_ = v___x_95_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
v_a_102_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_92_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_92_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
v_a_110_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_89_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_89_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
else
{
lean_object* v___x_118_; lean_object* v___x_120_; 
lean_dec(v_a_81_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
v___x_118_ = lean_box(0);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_118_);
v___x_120_ = v___x_83_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
v_a_123_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_78_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_78_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___boxed(lean_object* v_expr_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1(v_expr_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(lean_object* v_tree_140_, lean_object* v_appStx_141_){
_start:
{
lean_object* v___f_146_; lean_object* v___x_147_; 
v___f_146_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0___boxed), 2, 1);
lean_closure_set(v___f_146_, 0, v_appStx_141_);
v___x_147_ = l_Lean_Elab_InfoTree_smallestInfo_x3f(v___f_146_, v_tree_140_);
if (lean_obj_tag(v___x_147_) == 1)
{
lean_object* v_val_148_; lean_object* v_snd_149_; 
v_val_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_val_148_);
lean_dec_ref_known(v___x_147_, 1);
v_snd_149_ = lean_ctor_get(v_val_148_, 1);
if (lean_obj_tag(v_snd_149_) == 1)
{
lean_object* v_i_150_; lean_object* v_fst_151_; lean_object* v_lctx_152_; lean_object* v_expr_153_; lean_object* v___f_154_; lean_object* v___x_155_; 
v_i_150_ = lean_ctor_get(v_snd_149_, 0);
lean_inc_ref(v_i_150_);
v_fst_151_ = lean_ctor_get(v_val_148_, 0);
lean_inc(v_fst_151_);
lean_dec(v_val_148_);
v_lctx_152_ = lean_ctor_get(v_i_150_, 1);
lean_inc_ref(v_lctx_152_);
v_expr_153_ = lean_ctor_get(v_i_150_, 3);
lean_inc_ref(v_expr_153_);
lean_dec_ref(v_i_150_);
v___f_154_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___boxed), 6, 1);
lean_closure_set(v___f_154_, 0, v_expr_153_);
v___x_155_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_fst_151_, v_lctx_152_, v___f_154_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_185_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_185_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_185_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_185_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
if (lean_obj_tag(v_a_156_) == 1)
{
lean_object* v_val_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_180_; 
v_val_160_ = lean_ctor_get(v_a_156_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_a_156_);
if (v_isSharedCheck_180_ == 0)
{
v___x_162_ = v_a_156_;
v_isShared_163_ = v_isSharedCheck_180_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_val_160_);
lean_dec(v_a_156_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_180_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_164_ = l_Std_Format_defWidth;
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = l_Std_Format_pretty(v_val_160_, v___x_164_, v___x_165_, v___x_165_);
v___x_167_ = lean_box(0);
v___x_168_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
lean_ctor_set(v___x_168_, 2, v___x_167_);
lean_ctor_set(v___x_168_, 3, v___x_167_);
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = lean_mk_empty_array_with_capacity(v___x_169_);
v___x_171_ = lean_array_push(v___x_170_, v___x_168_);
v___x_172_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__0));
v___x_173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
lean_ctor_set(v___x_173_, 2, v___x_167_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_173_);
v___x_175_ = v___x_162_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_177_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_175_);
v___x_177_ = v___x_158_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
else
{
lean_object* v___x_181_; lean_object* v___x_183_; 
lean_dec(v_a_156_);
v___x_181_ = lean_box(0);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_181_);
v___x_183_ = v___x_158_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
v_a_186_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_155_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_155_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
else
{
lean_dec(v_val_148_);
goto v___jp_143_;
}
}
else
{
lean_dec(v___x_147_);
goto v___jp_143_;
}
v___jp_143_:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_box(0);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___boxed(lean_object* v_tree_194_, lean_object* v_appStx_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_194_, v_appStx_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx(uint8_t v_x_198_){
_start:
{
switch(v_x_198_)
{
case 0:
{
lean_object* v___x_199_; 
v___x_199_ = lean_unsigned_to_nat(0u);
return v___x_199_;
}
case 1:
{
lean_object* v___x_200_; 
v___x_200_ = lean_unsigned_to_nat(1u);
return v___x_200_;
}
default: 
{
lean_object* v___x_201_; 
v___x_201_ = lean_unsigned_to_nat(2u);
return v___x_201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___boxed(lean_object* v_x_202_){
_start:
{
uint8_t v_x_boxed_203_; lean_object* v_res_204_; 
v_x_boxed_203_ = lean_unbox(v_x_202_);
v_res_204_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx(v_x_boxed_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx(uint8_t v_x_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx(v_x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx___boxed(lean_object* v_x_207_){
_start:
{
uint8_t v_x_4__boxed_208_; lean_object* v_res_209_; 
v_x_4__boxed_208_ = lean_unbox(v_x_207_);
v_res_209_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx(v_x_4__boxed_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(lean_object* v_k_210_){
_start:
{
lean_inc(v_k_210_);
return v_k_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg___boxed(lean_object* v_k_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(v_k_211_);
lean_dec(v_k_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(lean_object* v_motive_213_, lean_object* v_ctorIdx_214_, uint8_t v_t_215_, lean_object* v_h_216_, lean_object* v_k_217_){
_start:
{
lean_inc(v_k_217_);
return v_k_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___boxed(lean_object* v_motive_218_, lean_object* v_ctorIdx_219_, lean_object* v_t_220_, lean_object* v_h_221_, lean_object* v_k_222_){
_start:
{
uint8_t v_t_boxed_223_; lean_object* v_res_224_; 
v_t_boxed_223_ = lean_unbox(v_t_220_);
v_res_224_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(v_motive_218_, v_ctorIdx_219_, v_t_boxed_223_, v_h_221_, v_k_222_);
lean_dec(v_k_222_);
lean_dec(v_ctorIdx_219_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg(lean_object* v_pipeArg_225_){
_start:
{
lean_inc(v_pipeArg_225_);
return v_pipeArg_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg___boxed(lean_object* v_pipeArg_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg(v_pipeArg_226_);
lean_dec(v_pipeArg_226_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(lean_object* v_motive_228_, uint8_t v_t_229_, lean_object* v_h_230_, lean_object* v_pipeArg_231_){
_start:
{
lean_inc(v_pipeArg_231_);
return v_pipeArg_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___boxed(lean_object* v_motive_232_, lean_object* v_t_233_, lean_object* v_h_234_, lean_object* v_pipeArg_235_){
_start:
{
uint8_t v_t_boxed_236_; lean_object* v_res_237_; 
v_t_boxed_236_ = lean_unbox(v_t_233_);
v_res_237_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(v_motive_232_, v_t_boxed_236_, v_h_234_, v_pipeArg_235_);
lean_dec(v_pipeArg_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(lean_object* v_termArg_238_){
_start:
{
lean_inc(v_termArg_238_);
return v_termArg_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg___boxed(lean_object* v_termArg_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(v_termArg_239_);
lean_dec(v_termArg_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(lean_object* v_motive_241_, uint8_t v_t_242_, lean_object* v_h_243_, lean_object* v_termArg_244_){
_start:
{
lean_inc(v_termArg_244_);
return v_termArg_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___boxed(lean_object* v_motive_245_, lean_object* v_t_246_, lean_object* v_h_247_, lean_object* v_termArg_248_){
_start:
{
uint8_t v_t_boxed_249_; lean_object* v_res_250_; 
v_t_boxed_249_ = lean_unbox(v_t_246_);
v_res_250_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(v_motive_245_, v_t_boxed_249_, v_h_247_, v_termArg_248_);
lean_dec(v_termArg_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(lean_object* v_appArg_251_){
_start:
{
lean_inc(v_appArg_251_);
return v_appArg_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg___boxed(lean_object* v_appArg_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(v_appArg_252_);
lean_dec(v_appArg_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(lean_object* v_motive_254_, uint8_t v_t_255_, lean_object* v_h_256_, lean_object* v_appArg_257_){
_start:
{
lean_inc(v_appArg_257_);
return v_appArg_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___boxed(lean_object* v_motive_258_, lean_object* v_t_259_, lean_object* v_h_260_, lean_object* v_appArg_261_){
_start:
{
uint8_t v_t_boxed_262_; lean_object* v_res_263_; 
v_t_boxed_262_ = lean_unbox(v_t_259_);
v_res_263_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(v_motive_258_, v_t_boxed_262_, v_h_260_, v_appArg_261_);
lean_dec(v_appArg_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(uint8_t v_x_264_){
_start:
{
switch(v_x_264_)
{
case 0:
{
lean_object* v___x_265_; 
v___x_265_ = lean_unsigned_to_nat(0u);
return v___x_265_;
}
case 1:
{
lean_object* v___x_266_; 
v___x_266_ = lean_unsigned_to_nat(1u);
return v___x_266_;
}
default: 
{
lean_object* v___x_267_; 
v___x_267_ = lean_unsigned_to_nat(2u);
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio___boxed(lean_object* v_x_268_){
_start:
{
uint8_t v_x_34__boxed_269_; lean_object* v_res_270_; 
v_x_34__boxed_269_ = lean_unbox(v_x_268_);
v_res_270_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_x_34__boxed_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(uint8_t v_x_271_){
_start:
{
if (v_x_271_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_unsigned_to_nat(0u);
return v___x_272_;
}
else
{
lean_object* v___x_273_; 
v___x_273_ = lean_unsigned_to_nat(1u);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___boxed(lean_object* v_x_274_){
_start:
{
uint8_t v_x_boxed_275_; lean_object* v_res_276_; 
v_x_boxed_275_ = lean_unbox(v_x_274_);
v_res_276_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(v_x_boxed_275_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx(uint8_t v_x_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(v_x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx___boxed(lean_object* v_x_279_){
_start:
{
uint8_t v_x_4__boxed_280_; lean_object* v_res_281_; 
v_x_4__boxed_280_ = lean_unbox(v_x_279_);
v_res_281_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx(v_x_4__boxed_280_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg(lean_object* v_k_282_){
_start:
{
lean_inc(v_k_282_);
return v_k_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg___boxed(lean_object* v_k_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg(v_k_283_);
lean_dec(v_k_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(lean_object* v_motive_285_, lean_object* v_ctorIdx_286_, uint8_t v_t_287_, lean_object* v_h_288_, lean_object* v_k_289_){
_start:
{
lean_inc(v_k_289_);
return v_k_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___boxed(lean_object* v_motive_290_, lean_object* v_ctorIdx_291_, lean_object* v_t_292_, lean_object* v_h_293_, lean_object* v_k_294_){
_start:
{
uint8_t v_t_boxed_295_; lean_object* v_res_296_; 
v_t_boxed_295_ = lean_unbox(v_t_292_);
v_res_296_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(v_motive_290_, v_ctorIdx_291_, v_t_boxed_295_, v_h_293_, v_k_294_);
lean_dec(v_k_294_);
lean_dec(v_ctorIdx_291_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(lean_object* v_continue_297_){
_start:
{
lean_inc(v_continue_297_);
return v_continue_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg___boxed(lean_object* v_continue_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(v_continue_298_);
lean_dec(v_continue_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(lean_object* v_motive_300_, uint8_t v_t_301_, lean_object* v_h_302_, lean_object* v_continue_303_){
_start:
{
lean_inc(v_continue_303_);
return v_continue_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___boxed(lean_object* v_motive_304_, lean_object* v_t_305_, lean_object* v_h_306_, lean_object* v_continue_307_){
_start:
{
uint8_t v_t_boxed_308_; lean_object* v_res_309_; 
v_t_boxed_308_ = lean_unbox(v_t_305_);
v_res_309_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(v_motive_304_, v_t_boxed_308_, v_h_306_, v_continue_307_);
lean_dec(v_continue_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(lean_object* v_stop_310_){
_start:
{
lean_inc(v_stop_310_);
return v_stop_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg___boxed(lean_object* v_stop_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(v_stop_311_);
lean_dec(v_stop_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(lean_object* v_motive_313_, uint8_t v_t_314_, lean_object* v_h_315_, lean_object* v_stop_316_){
_start:
{
lean_inc(v_stop_316_);
return v_stop_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___boxed(lean_object* v_motive_317_, lean_object* v_t_318_, lean_object* v_h_319_, lean_object* v_stop_320_){
_start:
{
uint8_t v_t_boxed_321_; lean_object* v_res_322_; 
v_t_boxed_321_ = lean_unbox(v_t_318_);
v_res_322_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(v_motive_317_, v_t_boxed_321_, v_h_319_, v_stop_320_);
lean_dec(v_stop_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(lean_object* v_s_323_, lean_object* v___x_324_, lean_object* v___x_325_, lean_object* v_a_326_, lean_object* v_b_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_box(0);
switch(lean_obj_tag(v_a_326_))
{
case 0:
{
lean_object* v_pos_329_; lean_object* v___x_330_; 
v_pos_329_ = lean_ctor_get(v_a_326_, 0);
lean_inc(v_pos_329_);
lean_dec_ref_known(v_a_326_, 1);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v_pos_329_);
return v___x_330_;
}
case 1:
{
lean_object* v_pos_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_340_; 
v_pos_331_ = lean_ctor_get(v_a_326_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_a_326_);
if (v_isSharedCheck_340_ == 0)
{
v___x_333_ = v_a_326_;
v_isShared_334_ = v_isSharedCheck_340_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_pos_331_);
lean_dec(v_a_326_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_340_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = lean_string_utf8_next_fast(v_s_323_, v_pos_331_);
lean_dec(v_pos_331_);
if (v_isShared_334_ == 0)
{
lean_ctor_set_tag(v___x_333_, 0);
lean_ctor_set(v___x_333_, 0, v___x_335_);
v___x_337_ = v___x_333_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_339_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
v_a_326_ = v___x_337_;
v_b_327_ = v___x_328_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_341_; lean_object* v_table_342_; lean_object* v_stackPos_343_; lean_object* v_needlePos_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_395_; 
v_needle_341_ = lean_ctor_get(v_a_326_, 0);
v_table_342_ = lean_ctor_get(v_a_326_, 1);
v_stackPos_343_ = lean_ctor_get(v_a_326_, 2);
v_needlePos_344_ = lean_ctor_get(v_a_326_, 3);
v_isSharedCheck_395_ = !lean_is_exclusive(v_a_326_);
if (v_isSharedCheck_395_ == 0)
{
v___x_346_ = v_a_326_;
v_isShared_347_ = v_isSharedCheck_395_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_needlePos_344_);
lean_inc(v_stackPos_343_);
lean_inc(v_table_342_);
lean_inc(v_needle_341_);
lean_dec(v_a_326_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_395_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_str_348_; lean_object* v_startInclusive_349_; lean_object* v_endExclusive_350_; lean_object* v_basePos_351_; lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_str_348_ = lean_ctor_get(v_needle_341_, 0);
v_startInclusive_349_ = lean_ctor_get(v_needle_341_, 1);
v_endExclusive_350_ = lean_ctor_get(v_needle_341_, 2);
v_basePos_351_ = lean_nat_sub(v_stackPos_343_, v_needlePos_344_);
v___x_352_ = lean_nat_sub(v_endExclusive_350_, v_startInclusive_349_);
v___x_353_ = lean_nat_add(v_basePos_351_, v___x_352_);
v___x_354_ = lean_nat_dec_le(v___x_353_, v___x_325_);
lean_dec(v___x_353_);
if (v___x_354_ == 0)
{
uint8_t v___x_355_; 
lean_dec(v___x_352_);
lean_del_object(v___x_346_);
lean_dec(v_needlePos_344_);
lean_dec(v_stackPos_343_);
lean_dec_ref(v_table_342_);
lean_dec_ref(v_needle_341_);
v___x_355_ = lean_nat_dec_lt(v_basePos_351_, v___x_325_);
lean_dec(v_basePos_351_);
if (v___x_355_ == 0)
{
lean_inc(v_b_327_);
return v_b_327_;
}
else
{
lean_object* v___x_356_; 
v___x_356_ = lean_box(3);
v_a_326_ = v___x_356_;
v_b_327_ = v___x_328_;
goto _start;
}
}
else
{
uint8_t v_stackByte_358_; lean_object* v___x_359_; uint8_t v_patByte_360_; uint8_t v___x_361_; 
lean_dec(v_basePos_351_);
lean_inc(v_stackPos_343_);
v_stackByte_358_ = lean_string_get_byte_fast(v_s_323_, v_stackPos_343_);
v___x_359_ = lean_nat_add(v_startInclusive_349_, v_needlePos_344_);
v_patByte_360_ = lean_string_get_byte_fast(v_str_348_, v___x_359_);
v___x_361_ = lean_uint8_dec_eq(v_stackByte_358_, v_patByte_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; uint8_t v___x_363_; 
lean_dec(v___x_352_);
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_nat_dec_eq(v_needlePos_344_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_newNeedlePos_366_; uint8_t v___x_367_; 
v___x_364_ = lean_unsigned_to_nat(1u);
v___x_365_ = lean_nat_sub(v_needlePos_344_, v___x_364_);
lean_dec(v_needlePos_344_);
v_newNeedlePos_366_ = lean_array_fget_borrowed(v_table_342_, v___x_365_);
lean_dec(v___x_365_);
v___x_367_ = lean_nat_dec_eq(v_newNeedlePos_366_, v___x_362_);
if (v___x_367_ == 0)
{
lean_object* v___x_369_; 
lean_inc(v_newNeedlePos_366_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 3, v_newNeedlePos_366_);
v___x_369_ = v___x_346_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_needle_341_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_table_342_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_stackPos_343_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v_newNeedlePos_366_);
v___x_369_ = v_reuseFailAlloc_371_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
v_a_326_ = v___x_369_;
v_b_327_ = v___x_328_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_372_; lean_object* v___x_374_; 
v_nextStackPos_372_ = l_String_Slice_posGE___redArg(v___x_324_, v_stackPos_343_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 3, v___x_362_);
lean_ctor_set(v___x_346_, 2, v_nextStackPos_372_);
v___x_374_ = v___x_346_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_needle_341_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_table_342_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_nextStackPos_372_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v___x_362_);
v___x_374_ = v_reuseFailAlloc_376_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
v_a_326_ = v___x_374_;
v_b_327_ = v___x_328_;
goto _start;
}
}
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_nextStackPos_379_; lean_object* v___x_381_; 
lean_dec(v_needlePos_344_);
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_nat_add(v_stackPos_343_, v___x_377_);
lean_dec(v_stackPos_343_);
v_nextStackPos_379_ = l_String_Slice_posGE___redArg(v___x_324_, v___x_378_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 3, v___x_362_);
lean_ctor_set(v___x_346_, 2, v_nextStackPos_379_);
v___x_381_ = v___x_346_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_needle_341_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_table_342_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v_nextStackPos_379_);
lean_ctor_set(v_reuseFailAlloc_383_, 3, v___x_362_);
v___x_381_ = v_reuseFailAlloc_383_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
v_a_326_ = v___x_381_;
v_b_327_ = v___x_328_;
goto _start;
}
}
}
else
{
lean_object* v___x_384_; lean_object* v_nextStackPos_385_; lean_object* v_nextNeedlePos_386_; uint8_t v___x_387_; 
v___x_384_ = lean_unsigned_to_nat(1u);
v_nextStackPos_385_ = lean_nat_add(v_stackPos_343_, v___x_384_);
lean_dec(v_stackPos_343_);
v_nextNeedlePos_386_ = lean_nat_add(v_needlePos_344_, v___x_384_);
lean_dec(v_needlePos_344_);
v___x_387_ = lean_nat_dec_eq(v_nextNeedlePos_386_, v___x_352_);
lean_dec(v___x_352_);
if (v___x_387_ == 0)
{
lean_object* v___x_389_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 3, v_nextNeedlePos_386_);
lean_ctor_set(v___x_346_, 2, v_nextStackPos_385_);
v___x_389_ = v___x_346_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_needle_341_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_table_342_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v_nextStackPos_385_);
lean_ctor_set(v_reuseFailAlloc_391_, 3, v_nextNeedlePos_386_);
v___x_389_ = v_reuseFailAlloc_391_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
v_a_326_ = v___x_389_;
goto _start;
}
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
lean_del_object(v___x_346_);
lean_dec_ref(v_table_342_);
lean_dec_ref(v_needle_341_);
v___x_392_ = lean_nat_sub(v_nextStackPos_385_, v_nextNeedlePos_386_);
lean_dec(v_nextNeedlePos_386_);
lean_dec(v_nextStackPos_385_);
v___x_393_ = l_String_Slice_pos_x21(v___x_324_, v___x_392_);
lean_dec(v___x_392_);
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
}
}
}
default: 
{
lean_inc(v_b_327_);
return v_b_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg___boxed(lean_object* v_s_396_, lean_object* v___x_397_, lean_object* v___x_398_, lean_object* v_a_399_, lean_object* v_b_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_396_, v___x_397_, v___x_398_, v_a_399_, v_b_400_);
lean_dec(v_b_400_);
lean_dec(v___x_398_);
lean_dec_ref(v___x_397_);
lean_dec_ref(v_s_396_);
return v_res_401_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0));
v___x_404_ = lean_string_utf8_byte_size(v___x_403_);
return v___x_404_;
}
}
static uint8_t _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1);
v___x_407_ = lean_nat_dec_eq(v___x_406_, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_408_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1);
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0));
v___x_411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v___x_409_);
lean_ctor_set(v___x_411_, 2, v___x_408_);
return v___x_411_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3);
v___x_413_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4);
v___x_416_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3);
v___x_417_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_415_);
lean_ctor_set(v___x_417_, 2, v___x_414_);
lean_ctor_set(v___x_417_, 3, v___x_414_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(lean_object* v_s_420_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___y_425_; uint8_t v___x_436_; 
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_string_utf8_byte_size(v_s_420_);
lean_inc_ref(v_s_420_);
v___x_423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_423_, 0, v_s_420_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
lean_ctor_set(v___x_423_, 2, v___x_422_);
v___x_436_ = lean_uint8_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; 
v___x_437_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5);
v___y_425_ = v___x_437_;
goto v___jp_424_;
}
else
{
lean_object* v___x_438_; 
v___x_438_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__6));
v___y_425_ = v___x_438_;
goto v___jp_424_;
}
v___jp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_box(0);
lean_inc(v___y_425_);
v___x_427_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_420_, v___x_423_, v___x_422_, v___y_425_, v___x_426_);
lean_dec_ref_known(v___x_423_, 3);
lean_dec_ref(v_s_420_);
if (lean_obj_tag(v___x_427_) == 0)
{
return v___x_426_;
}
else
{
lean_object* v_val_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
v_val_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_val_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_val_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(lean_object* v_s_439_, lean_object* v___x_440_, lean_object* v___x_441_, lean_object* v_inst_442_, lean_object* v_R_443_, lean_object* v_a_444_, lean_object* v_b_445_, lean_object* v_c_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_439_, v___x_440_, v___x_441_, v_a_444_, v_b_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___boxed(lean_object* v_s_448_, lean_object* v___x_449_, lean_object* v___x_450_, lean_object* v_inst_451_, lean_object* v_R_452_, lean_object* v_a_453_, lean_object* v_b_454_, lean_object* v_c_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(v_s_448_, v___x_449_, v___x_450_, v_inst_451_, v_R_452_, v_a_453_, v_b_454_, v_c_455_);
lean_dec(v_b_454_);
lean_dec(v___x_450_);
lean_dec_ref(v___x_449_);
lean_dec_ref(v_s_448_);
return v_res_456_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(lean_object* v_text_457_, lean_object* v_pos_458_){
_start:
{
lean_object* v___x_459_; lean_object* v_line_460_; lean_object* v_source_461_; lean_object* v_lineStartPos_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v_lineEndPos_465_; lean_object* v_line_466_; lean_object* v___x_467_; 
lean_inc_ref(v_text_457_);
v___x_459_ = l_Lean_FileMap_toPosition(v_text_457_, v_pos_458_);
v_line_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_line_460_);
lean_dec_ref(v___x_459_);
v_source_461_ = lean_ctor_get(v_text_457_, 0);
lean_inc_ref(v_source_461_);
v_lineStartPos_462_ = l_Lean_FileMap_lineStart(v_text_457_, v_line_460_);
v___x_463_ = lean_unsigned_to_nat(1u);
v___x_464_ = lean_nat_add(v_line_460_, v___x_463_);
lean_dec(v_line_460_);
v_lineEndPos_465_ = l_Lean_FileMap_lineStart(v_text_457_, v___x_464_);
lean_dec(v___x_464_);
lean_dec_ref(v_text_457_);
v_line_466_ = lean_string_utf8_extract(v_source_461_, v_lineStartPos_462_, v_lineEndPos_465_);
lean_dec(v_lineEndPos_465_);
lean_dec_ref(v_source_461_);
v___x_467_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(v_line_466_);
if (lean_obj_tag(v___x_467_) == 1)
{
lean_object* v_val_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_val_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_val_468_);
lean_dec_ref_known(v___x_467_, 1);
v___x_469_ = lean_nat_add(v_lineStartPos_462_, v_val_468_);
lean_dec(v_val_468_);
lean_dec(v_lineStartPos_462_);
v___x_470_ = lean_nat_dec_le(v___x_469_, v_pos_458_);
lean_dec(v___x_469_);
return v___x_470_;
}
else
{
uint8_t v___x_471_; 
lean_dec(v___x_467_);
lean_dec(v_lineStartPos_462_);
v___x_471_ = 0;
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment___boxed(lean_object* v_text_472_, lean_object* v_pos_473_){
_start:
{
uint8_t v_res_474_; lean_object* v_r_475_; 
v_res_474_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_472_, v_pos_473_);
lean_dec(v_pos_473_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(lean_object* v_text_532_, lean_object* v_ctx_x3f_533_, lean_object* v_requestedPos_534_, lean_object* v_stx_535_, lean_object* v_parent_536_){
_start:
{
lean_object* v_kind_x3f_538_; uint8_t v___y_637_; uint8_t v___y_638_; uint8_t v___x_640_; lean_object* v___x_641_; 
v___x_640_ = 1;
v___x_641_ = l_Lean_Syntax_getTailPos_x3f(v_stx_535_, v___x_640_);
if (lean_obj_tag(v___x_641_) == 1)
{
lean_object* v_val_642_; uint8_t v___y_644_; uint8_t v___y_645_; uint8_t v___x_654_; uint8_t v___y_656_; 
v_val_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_val_642_);
lean_dec_ref_known(v___x_641_, 1);
v___x_654_ = lean_nat_dec_lt(v_requestedPos_534_, v_val_642_);
if (v___x_654_ == 0)
{
if (lean_obj_tag(v_ctx_x3f_533_) == 0)
{
v___y_656_ = v___x_654_;
goto v___jp_655_;
}
else
{
lean_object* v_val_659_; uint8_t v_triggerKind_660_; 
v_val_659_ = lean_ctor_get(v_ctx_x3f_533_, 0);
v_triggerKind_660_ = lean_ctor_get_uint8(v_val_659_, sizeof(void*)*2);
if (v_triggerKind_660_ == 0)
{
v___y_656_ = v___x_640_;
goto v___jp_655_;
}
else
{
v___y_656_ = v___x_654_;
goto v___jp_655_;
}
}
}
else
{
lean_object* v___x_661_; 
lean_dec(v_val_642_);
lean_dec(v_parent_536_);
lean_dec(v_stx_535_);
lean_dec_ref(v_text_532_);
v___x_661_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23));
return v___x_661_;
}
v___jp_643_:
{
lean_object* v___x_646_; lean_object* v_line_647_; lean_object* v___x_648_; lean_object* v_line_649_; uint8_t v___x_650_; uint8_t v_isCursorAfterTailPosLine_651_; uint8_t v___x_652_; 
lean_inc_ref(v_text_532_);
v___x_646_ = l_Lean_FileMap_toPosition(v_text_532_, v_requestedPos_534_);
v_line_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_line_647_);
lean_dec_ref(v___x_646_);
v___x_648_ = l_Lean_FileMap_toPosition(v_text_532_, v_val_642_);
lean_dec(v_val_642_);
v_line_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_line_649_);
lean_dec_ref(v___x_648_);
v___x_650_ = lean_nat_dec_eq(v_line_647_, v_line_649_);
lean_dec(v_line_649_);
lean_dec(v_line_647_);
v_isCursorAfterTailPosLine_651_ = lean_bool_not(v___x_650_);
v___x_652_ = lean_bool_not(v___y_644_);
if (v___x_652_ == 0)
{
v___y_637_ = v_isCursorAfterTailPosLine_651_;
v___y_638_ = v___x_652_;
goto v___jp_636_;
}
else
{
uint8_t v___x_653_; 
v___x_653_ = lean_bool_not(v___y_645_);
v___y_637_ = v_isCursorAfterTailPosLine_651_;
v___y_638_ = v___x_653_;
goto v___jp_636_;
}
}
v___jp_655_:
{
if (lean_obj_tag(v_ctx_x3f_533_) == 0)
{
v___y_644_ = v___y_656_;
v___y_645_ = v___x_654_;
goto v___jp_643_;
}
else
{
lean_object* v_val_657_; uint8_t v_isRetrigger_658_; 
v_val_657_ = lean_ctor_get(v_ctx_x3f_533_, 0);
v_isRetrigger_658_ = lean_ctor_get_uint8(v_val_657_, sizeof(void*)*2 + 1);
v___y_644_ = v___y_656_;
v___y_645_ = v_isRetrigger_658_;
goto v___jp_643_;
}
}
}
else
{
lean_object* v___x_662_; 
lean_dec(v___x_641_);
lean_dec(v_parent_536_);
lean_dec(v_stx_535_);
lean_dec_ref(v_text_532_);
v___x_662_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22));
return v___x_662_;
}
v___jp_537_:
{
uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = 0;
v___x_540_ = lean_box(v___x_539_);
lean_inc(v_kind_x3f_538_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v_kind_x3f_538_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
return v___x_541_;
}
v___jp_542_:
{
if (lean_obj_tag(v_stx_535_) == 3)
{
lean_object* v___x_543_; uint8_t v___x_544_; 
lean_dec_ref_known(v_stx_535_, 4);
v___x_543_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4));
lean_inc(v_parent_536_);
v___x_544_ = l_Lean_Syntax_isOfKind(v_parent_536_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6));
lean_inc(v_parent_536_);
v___x_546_ = l_Lean_Syntax_isOfKind(v_parent_536_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_547_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8));
lean_inc(v_parent_536_);
v___x_548_ = l_Lean_Syntax_isOfKind(v_parent_536_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; 
lean_dec(v_parent_536_);
v___x_549_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_538_ = v___x_549_;
goto v___jp_537_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = l_Lean_Syntax_getArg(v_parent_536_, v___x_550_);
lean_dec(v_parent_536_);
v___x_552_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_553_ = l_Lean_Syntax_isOfKind(v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
v___x_554_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_538_ = v___x_554_;
goto v___jp_537_;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = lean_box(0);
v_kind_x3f_538_ = v___x_555_;
goto v___jp_537_;
}
}
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_556_ = lean_unsigned_to_nat(2u);
v___x_557_ = l_Lean_Syntax_getArg(v_parent_536_, v___x_556_);
lean_dec(v_parent_536_);
v___x_558_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_559_ = l_Lean_Syntax_isOfKind(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_538_ = v___x_560_;
goto v___jp_537_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = lean_box(0);
v_kind_x3f_538_ = v___x_561_;
goto v___jp_537_;
}
}
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_562_ = lean_unsigned_to_nat(2u);
v___x_563_ = l_Lean_Syntax_getArg(v_parent_536_, v___x_562_);
v___x_564_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_565_ = l_Lean_Syntax_isOfKind(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
lean_dec(v_parent_536_);
v___x_566_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_538_ = v___x_566_;
goto v___jp_537_;
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_unsigned_to_nat(3u);
v___x_569_ = l_Lean_Syntax_getArg(v_parent_536_, v___x_568_);
lean_dec(v_parent_536_);
v___x_570_ = l_Lean_Syntax_matchesNull(v___x_569_, v___x_567_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
v___x_571_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_538_ = v___x_571_;
goto v___jp_537_;
}
else
{
lean_object* v___x_572_; 
v___x_572_ = lean_box(0);
v_kind_x3f_538_ = v___x_572_;
goto v___jp_537_;
}
}
}
}
else
{
lean_dec(v_parent_536_);
if (lean_obj_tag(v_stx_535_) == 1)
{
lean_object* v_kind_573_; lean_object* v_args_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_kind_573_ = lean_ctor_get(v_stx_535_, 1);
v_args_574_ = lean_ctor_get(v_stx_535_, 2);
lean_inc_ref(v_args_574_);
v___x_575_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13));
v___x_576_ = lean_name_eq(v_kind_573_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15));
v___x_578_ = lean_name_eq(v_kind_573_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17));
lean_inc_ref(v_stx_535_);
v___x_580_ = l_Lean_Syntax_isOfKind(v_stx_535_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19));
lean_inc_ref(v_stx_535_);
v___x_582_ = l_Lean_Syntax_isOfKind(v_stx_535_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4));
lean_inc_ref(v_stx_535_);
v___x_584_ = l_Lean_Syntax_isOfKind(v_stx_535_, v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8));
lean_inc_ref(v_stx_535_);
v___x_586_ = l_Lean_Syntax_isOfKind(v_stx_535_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6));
lean_inc_ref(v_stx_535_);
v___x_588_ = l_Lean_Syntax_isOfKind(v_stx_535_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
lean_dec_ref_known(v_stx_535_, 3);
v___x_589_ = lean_array_get_size(v_args_574_);
lean_dec_ref(v_args_574_);
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_nat_dec_le(v___x_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_538_ = v___x_592_;
goto v___jp_537_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = lean_box(0);
v_kind_x3f_538_ = v___x_593_;
goto v___jp_537_;
}
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_594_ = lean_unsigned_to_nat(2u);
v___x_595_ = l_Lean_Syntax_getArg(v_stx_535_, v___x_594_);
lean_dec_ref_known(v_stx_535_, 3);
v___x_596_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_597_ = l_Lean_Syntax_isOfKind(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_array_get_size(v_args_574_);
lean_dec_ref(v_args_574_);
v___x_600_ = lean_nat_dec_le(v___x_599_, v___x_598_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; 
v___x_601_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_538_ = v___x_601_;
goto v___jp_537_;
}
else
{
lean_object* v___x_602_; 
v___x_602_ = lean_box(0);
v_kind_x3f_538_ = v___x_602_;
goto v___jp_537_;
}
}
else
{
lean_object* v___x_603_; 
lean_dec_ref(v_args_574_);
v___x_603_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_538_ = v___x_603_;
goto v___jp_537_;
}
}
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = l_Lean_Syntax_getArg(v_stx_535_, v___x_604_);
lean_dec_ref_known(v_stx_535_, 3);
v___x_606_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_607_ = l_Lean_Syntax_isOfKind(v___x_605_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_array_get_size(v_args_574_);
lean_dec_ref(v_args_574_);
v___x_609_ = lean_nat_dec_le(v___x_608_, v___x_604_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
v___x_610_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_538_ = v___x_610_;
goto v___jp_537_;
}
else
{
lean_object* v___x_611_; 
v___x_611_ = lean_box(0);
v_kind_x3f_538_ = v___x_611_;
goto v___jp_537_;
}
}
else
{
lean_object* v___x_612_; 
lean_dec_ref(v_args_574_);
v___x_612_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_538_ = v___x_612_;
goto v___jp_537_;
}
}
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_unsigned_to_nat(2u);
v___x_615_ = l_Lean_Syntax_getArg(v_stx_535_, v___x_614_);
v___x_616_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11));
v___x_617_ = l_Lean_Syntax_isOfKind(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; uint8_t v___x_619_; 
lean_dec_ref_known(v_stx_535_, 3);
v___x_618_ = lean_array_get_size(v_args_574_);
lean_dec_ref(v_args_574_);
v___x_619_ = lean_nat_dec_le(v___x_618_, v___x_613_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
v___x_620_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_538_ = v___x_620_;
goto v___jp_537_;
}
else
{
lean_object* v___x_621_; 
v___x_621_ = lean_box(0);
v_kind_x3f_538_ = v___x_621_;
goto v___jp_537_;
}
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_unsigned_to_nat(3u);
v___x_624_ = l_Lean_Syntax_getArg(v_stx_535_, v___x_623_);
lean_dec_ref_known(v_stx_535_, 3);
v___x_625_ = l_Lean_Syntax_matchesNull(v___x_624_, v___x_622_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_array_get_size(v_args_574_);
lean_dec_ref(v_args_574_);
v___x_627_ = lean_nat_dec_le(v___x_626_, v___x_613_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
v___x_628_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9));
v_kind_x3f_538_ = v___x_628_;
goto v___jp_537_;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = lean_box(0);
v_kind_x3f_538_ = v___x_629_;
goto v___jp_537_;
}
}
else
{
lean_object* v___x_630_; 
lean_dec_ref(v_args_574_);
v___x_630_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20));
v_kind_x3f_538_ = v___x_630_;
goto v___jp_537_;
}
}
}
}
else
{
lean_object* v___x_631_; 
lean_dec_ref(v_args_574_);
lean_dec_ref_known(v_stx_535_, 3);
v___x_631_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20));
v_kind_x3f_538_ = v___x_631_;
goto v___jp_537_;
}
}
else
{
lean_object* v___x_632_; 
lean_dec_ref(v_args_574_);
lean_dec_ref_known(v_stx_535_, 3);
v___x_632_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20));
v_kind_x3f_538_ = v___x_632_;
goto v___jp_537_;
}
}
else
{
lean_object* v___x_633_; 
lean_dec_ref(v_args_574_);
lean_dec_ref_known(v_stx_535_, 3);
v___x_633_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21));
v_kind_x3f_538_ = v___x_633_;
goto v___jp_537_;
}
}
else
{
lean_object* v___x_634_; 
lean_dec_ref(v_args_574_);
lean_dec_ref_known(v_stx_535_, 3);
v___x_634_ = lean_box(0);
v_kind_x3f_538_ = v___x_634_;
goto v___jp_537_;
}
}
else
{
lean_object* v___x_635_; 
lean_dec(v_stx_535_);
v___x_635_ = lean_box(0);
v_kind_x3f_538_ = v___x_635_;
goto v___jp_537_;
}
}
}
v___jp_636_:
{
if (v___y_638_ == 0)
{
goto v___jp_542_;
}
else
{
if (v___y_637_ == 0)
{
goto v___jp_542_;
}
else
{
lean_object* v___x_639_; 
lean_dec(v_parent_536_);
lean_dec(v_stx_535_);
v___x_639_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22));
return v___x_639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___boxed(lean_object* v_text_663_, lean_object* v_ctx_x3f_664_, lean_object* v_requestedPos_665_, lean_object* v_stx_666_, lean_object* v_parent_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_663_, v_ctx_x3f_664_, v_requestedPos_665_, v_stx_666_, v_parent_667_);
lean_dec(v_requestedPos_665_);
lean_dec(v_ctx_x3f_664_);
return v_res_668_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(lean_object* v_stx_669_){
_start:
{
uint8_t v___x_670_; uint8_t v___x_671_; 
v___x_670_ = l_Lean_Syntax_hasArgs(v_stx_669_);
v___x_671_ = lean_bool_not(v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed(lean_object* v_stx_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(v_stx_672_);
lean_dec(v_stx_672_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(uint8_t v___x_675_, lean_object* v_requestedPos_676_, uint8_t v___x_677_, lean_object* v_stx_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_678_, v___x_675_);
if (lean_obj_tag(v___x_679_) == 1)
{
lean_object* v_val_680_; uint8_t v___x_681_; 
v_val_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_val_680_);
lean_dec_ref_known(v___x_679_, 1);
v___x_681_ = l_Lean_Syntax_Range_contains(v_val_680_, v_requestedPos_676_, v___x_675_);
lean_dec(v_val_680_);
return v___x_681_;
}
else
{
lean_dec(v___x_679_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed(lean_object* v___x_682_, lean_object* v_requestedPos_683_, lean_object* v___x_684_, lean_object* v_stx_685_){
_start:
{
uint8_t v___x_3192__boxed_686_; uint8_t v___x_3193__boxed_687_; uint8_t v_res_688_; lean_object* v_r_689_; 
v___x_3192__boxed_686_ = lean_unbox(v___x_682_);
v___x_3193__boxed_687_ = lean_unbox(v___x_684_);
v_res_688_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(v___x_3192__boxed_686_, v_requestedPos_683_, v___x_3193__boxed_687_, v_stx_685_);
lean_dec(v_stx_685_);
lean_dec(v_requestedPos_683_);
v_r_689_ = lean_box(v_res_688_);
return v_r_689_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(lean_object* v_c1_690_, lean_object* v_c2_691_){
_start:
{
uint8_t v_kind_692_; uint8_t v_kind_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_kind_692_ = lean_ctor_get_uint8(v_c2_691_, sizeof(void*)*1);
v_kind_693_ = lean_ctor_get_uint8(v_c1_690_, sizeof(void*)*1);
v___x_694_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_692_);
v___x_695_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_693_);
v___x_696_ = lean_nat_dec_le(v___x_694_, v___x_695_);
lean_dec(v___x_695_);
lean_dec(v___x_694_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2___boxed(lean_object* v_c1_697_, lean_object* v_c2_698_){
_start:
{
uint8_t v_res_699_; lean_object* v_r_700_; 
v_res_699_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(v_c1_697_, v_c2_698_);
lean_dec_ref(v_c2_698_);
lean_dec_ref(v_c1_697_);
v_r_700_ = lean_box(v_res_699_);
return v_r_700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(lean_object* v_tree_709_, uint8_t v___y_710_, uint8_t v___x_711_, lean_object* v_as_712_, size_t v_sz_713_, size_t v_i_714_, lean_object* v_b_715_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = lean_usize_dec_lt(v_i_714_, v_sz_713_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
lean_dec_ref(v_tree_709_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v_b_715_);
return v___x_718_;
}
else
{
lean_object* v_a_719_; uint8_t v_kind_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec_ref(v_b_715_);
v_a_719_ = lean_array_uget_borrowed(v_as_712_, v_i_714_);
v_kind_720_ = lean_ctor_get_uint8(v_a_719_, sizeof(void*)*1);
v___x_721_ = lean_box(0);
v___x_722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0));
if (v_kind_720_ == 1)
{
goto v___jp_747_;
}
else
{
if (v___x_711_ == 0)
{
goto v___jp_723_;
}
else
{
goto v___jp_747_;
}
}
v___jp_723_:
{
lean_object* v_appStx_724_; lean_object* v___x_725_; 
v_appStx_724_ = lean_ctor_get(v_a_719_, 0);
lean_inc(v_appStx_724_);
lean_inc_ref(v_tree_709_);
v___x_725_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_709_, v_appStx_724_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_738_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_738_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_738_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_738_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
if (lean_obj_tag(v_a_726_) == 1)
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
lean_dec_ref(v_tree_709_);
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v_a_726_);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v___x_721_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_731_);
v___x_733_ = v___x_728_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
else
{
size_t v___x_735_; size_t v___x_736_; 
lean_del_object(v___x_728_);
lean_dec(v_a_726_);
v___x_735_ = ((size_t)1ULL);
v___x_736_ = lean_usize_add(v_i_714_, v___x_735_);
v_i_714_ = v___x_736_;
v_b_715_ = v___x_722_;
goto _start;
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v_tree_709_);
v_a_739_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_725_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_725_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
v___jp_747_:
{
if (v___y_710_ == 0)
{
goto v___jp_723_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec_ref(v_tree_709_);
v___x_748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__2));
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___boxed(lean_object* v_tree_750_, lean_object* v___y_751_, lean_object* v___x_752_, lean_object* v_as_753_, lean_object* v_sz_754_, lean_object* v_i_755_, lean_object* v_b_756_, lean_object* v___y_757_){
_start:
{
uint8_t v___y_3226__boxed_758_; uint8_t v___x_3227__boxed_759_; size_t v_sz_boxed_760_; size_t v_i_boxed_761_; lean_object* v_res_762_; 
v___y_3226__boxed_758_ = lean_unbox(v___y_751_);
v___x_3227__boxed_759_ = lean_unbox(v___x_752_);
v_sz_boxed_760_ = lean_unbox_usize(v_sz_754_);
lean_dec(v_sz_754_);
v_i_boxed_761_ = lean_unbox_usize(v_i_755_);
lean_dec(v_i_755_);
v_res_762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v_tree_750_, v___y_3226__boxed_758_, v___x_3227__boxed_759_, v_as_753_, v_sz_boxed_760_, v_i_boxed_761_, v_b_756_);
lean_dec_ref(v_as_753_);
return v_res_762_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0(void){
_start:
{
uint8_t v___x_763_; lean_object* v___x_764_; 
v___x_763_ = 1;
v___x_764_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(lean_object* v_as_765_, size_t v_i_766_, size_t v_stop_767_){
_start:
{
uint8_t v___x_768_; 
v___x_768_ = lean_usize_dec_eq(v_i_766_, v_stop_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; uint8_t v_kind_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_769_ = lean_array_uget_borrowed(v_as_765_, v_i_766_);
v_kind_770_ = lean_ctor_get_uint8(v___x_769_, sizeof(void*)*1);
v___x_771_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0);
v___x_772_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_770_);
v___x_773_ = lean_nat_dec_lt(v___x_771_, v___x_772_);
lean_dec(v___x_772_);
if (v___x_773_ == 0)
{
size_t v___x_774_; size_t v___x_775_; 
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_766_, v___x_774_);
v_i_766_ = v___x_775_;
goto _start;
}
else
{
return v___x_773_;
}
}
else
{
uint8_t v___x_777_; 
v___x_777_ = 0;
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___boxed(lean_object* v_as_778_, lean_object* v_i_779_, lean_object* v_stop_780_){
_start:
{
size_t v_i_boxed_781_; size_t v_stop_boxed_782_; uint8_t v_res_783_; lean_object* v_r_784_; 
v_i_boxed_781_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_stop_boxed_782_ = lean_unbox_usize(v_stop_780_);
lean_dec(v_stop_780_);
v_res_783_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v_as_778_, v_i_boxed_781_, v_stop_boxed_782_);
lean_dec_ref(v_as_778_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(uint8_t v_snd_785_, uint8_t v___x_786_, lean_object* v_____r_787_, lean_object* v_candidates_788_){
_start:
{
if (v_snd_785_ == 1)
{
goto v___jp_790_;
}
else
{
if (v___x_786_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v_candidates_788_);
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
return v___x_794_;
}
else
{
goto v___jp_790_;
}
}
v___jp_790_:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v_candidates_788_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0___boxed(lean_object* v_snd_795_, lean_object* v___x_796_, lean_object* v_____r_797_, lean_object* v_candidates_798_, lean_object* v___y_799_){
_start:
{
uint8_t v_snd_3328__boxed_800_; uint8_t v___x_3329__boxed_801_; lean_object* v_res_802_; 
v_snd_3328__boxed_800_ = lean_unbox(v_snd_795_);
v___x_3329__boxed_801_ = lean_unbox(v___x_796_);
v_res_802_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v_snd_3328__boxed_800_, v___x_3329__boxed_801_, v_____r_797_, v_candidates_798_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(lean_object* v_upperBound_803_, lean_object* v_stack_804_, lean_object* v_text_805_, lean_object* v_ctx_x3f_806_, lean_object* v_requestedPos_807_, uint8_t v___x_808_, lean_object* v_a_809_, lean_object* v_b_810_){
_start:
{
lean_object* v___y_813_; uint8_t v___x_835_; 
v___x_835_ = lean_nat_dec_lt(v_a_809_, v_upperBound_803_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_dec(v_a_809_);
lean_dec_ref(v_text_805_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v_b_810_);
return v___x_836_;
}
else
{
lean_object* v___x_837_; lean_object* v___y_839_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_837_ = lean_array_fget_borrowed(v_stack_804_, v_a_809_);
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = lean_nat_add(v_a_809_, v___x_854_);
v___x_856_ = lean_array_get_size(v_stack_804_);
v___x_857_ = lean_nat_dec_lt(v___x_855_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; 
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v___y_839_ = v___x_858_;
goto v___jp_838_;
}
else
{
lean_object* v___x_859_; 
v___x_859_ = lean_array_fget_borrowed(v_stack_804_, v___x_855_);
lean_dec(v___x_855_);
lean_inc(v___x_859_);
v___y_839_ = v___x_859_;
goto v___jp_838_;
}
v___jp_838_:
{
lean_object* v___x_840_; lean_object* v_fst_841_; 
lean_inc(v___x_837_);
lean_inc_ref(v_text_805_);
v___x_840_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_805_, v_ctx_x3f_806_, v_requestedPos_807_, v___x_837_, v___y_839_);
v_fst_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_fst_841_);
if (lean_obj_tag(v_fst_841_) == 1)
{
lean_object* v_snd_842_; lean_object* v_val_843_; lean_object* v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___x_849_; 
v_snd_842_ = lean_ctor_get(v___x_840_, 1);
lean_inc(v_snd_842_);
lean_dec_ref(v___x_840_);
v_val_843_ = lean_ctor_get(v_fst_841_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v_fst_841_, 1);
lean_inc(v___x_837_);
v___x_844_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_844_, 0, v___x_837_);
v___x_845_ = lean_unbox(v_val_843_);
lean_dec(v_val_843_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*1, v___x_845_);
v___x_846_ = lean_array_push(v_b_810_, v___x_844_);
v___x_847_ = lean_box(0);
v___x_848_ = lean_unbox(v_snd_842_);
lean_dec(v_snd_842_);
v___x_849_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_848_, v___x_808_, v___x_847_, v___x_846_);
v___y_813_ = v___x_849_;
goto v___jp_812_;
}
else
{
lean_object* v_snd_850_; lean_object* v___x_851_; uint8_t v___x_852_; lean_object* v___x_853_; 
lean_dec(v_fst_841_);
v_snd_850_ = lean_ctor_get(v___x_840_, 1);
lean_inc(v_snd_850_);
lean_dec_ref(v___x_840_);
v___x_851_ = lean_box(0);
v___x_852_ = lean_unbox(v_snd_850_);
lean_dec(v_snd_850_);
v___x_853_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_852_, v___x_808_, v___x_851_, v_b_810_);
v___y_813_ = v___x_853_;
goto v___jp_812_;
}
}
}
v___jp_812_:
{
if (lean_obj_tag(v___y_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_826_; 
v_a_814_ = lean_ctor_get(v___y_813_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___y_813_);
if (v_isSharedCheck_826_ == 0)
{
v___x_816_ = v___y_813_;
v_isShared_817_ = v_isSharedCheck_826_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___y_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_826_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
if (lean_obj_tag(v_a_814_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; 
lean_dec(v_a_809_);
lean_dec_ref(v_text_805_);
v_a_818_ = lean_ctor_get(v_a_814_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v_a_814_, 1);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v_a_818_);
v___x_820_ = v___x_816_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_del_object(v___x_816_);
v_a_822_ = lean_ctor_get(v_a_814_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v_a_814_, 1);
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_nat_add(v_a_809_, v___x_823_);
lean_dec(v_a_809_);
v_a_809_ = v___x_824_;
v_b_810_ = v_a_822_;
goto _start;
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_a_809_);
lean_dec_ref(v_text_805_);
v_a_827_ = lean_ctor_get(v___y_813_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___y_813_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___y_813_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___y_813_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___boxed(lean_object* v_upperBound_860_, lean_object* v_stack_861_, lean_object* v_text_862_, lean_object* v_ctx_x3f_863_, lean_object* v_requestedPos_864_, lean_object* v___x_865_, lean_object* v_a_866_, lean_object* v_b_867_, lean_object* v___y_868_){
_start:
{
uint8_t v___x_3351__boxed_869_; lean_object* v_res_870_; 
v___x_3351__boxed_869_ = lean_unbox(v___x_865_);
v_res_870_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_860_, v_stack_861_, v_text_862_, v_ctx_x3f_863_, v_requestedPos_864_, v___x_3351__boxed_869_, v_a_866_, v_b_867_);
lean_dec(v_requestedPos_864_);
lean_dec(v_ctx_x3f_863_);
lean_dec_ref(v_stack_861_);
lean_dec(v_upperBound_860_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(size_t v_sz_871_, size_t v_i_872_, lean_object* v_bs_873_){
_start:
{
uint8_t v___x_874_; 
v___x_874_ = lean_usize_dec_lt(v_i_872_, v_sz_871_);
if (v___x_874_ == 0)
{
return v_bs_873_;
}
else
{
lean_object* v_v_875_; lean_object* v_fst_876_; lean_object* v___x_877_; lean_object* v_bs_x27_878_; size_t v___x_879_; size_t v___x_880_; lean_object* v___x_881_; 
v_v_875_ = lean_array_uget_borrowed(v_bs_873_, v_i_872_);
v_fst_876_ = lean_ctor_get(v_v_875_, 0);
lean_inc(v_fst_876_);
v___x_877_ = lean_unsigned_to_nat(0u);
v_bs_x27_878_ = lean_array_uset(v_bs_873_, v_i_872_, v___x_877_);
v___x_879_ = ((size_t)1ULL);
v___x_880_ = lean_usize_add(v_i_872_, v___x_879_);
v___x_881_ = lean_array_uset(v_bs_x27_878_, v_i_872_, v_fst_876_);
v_i_872_ = v___x_880_;
v_bs_873_ = v___x_881_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0___boxed(lean_object* v_sz_883_, lean_object* v_i_884_, lean_object* v_bs_885_){
_start:
{
size_t v_sz_boxed_886_; size_t v_i_boxed_887_; lean_object* v_res_888_; 
v_sz_boxed_886_ = lean_unbox_usize(v_sz_883_);
lean_dec(v_sz_883_);
v_i_boxed_887_ = lean_unbox_usize(v_i_884_);
lean_dec(v_i_884_);
v_res_888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_sz_boxed_886_, v_i_boxed_887_, v_bs_885_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(lean_object* v_text_893_, lean_object* v_ctx_x3f_894_, lean_object* v_cmdStx_895_, lean_object* v_tree_896_, lean_object* v_requestedPos_897_){
_start:
{
uint8_t v___x_899_; 
lean_inc_ref(v_text_893_);
v___x_899_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_893_, v_requestedPos_897_);
if (v___x_899_ == 0)
{
lean_object* v___f_900_; uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___f_904_; lean_object* v_stack_x3f_905_; 
v___f_900_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0));
v___x_901_ = 1;
v___x_902_ = lean_box(v___x_901_);
v___x_903_ = lean_box(v___x_899_);
lean_inc(v_requestedPos_897_);
v___f_904_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed), 4, 3);
lean_closure_set(v___f_904_, 0, v___x_902_);
lean_closure_set(v___f_904_, 1, v_requestedPos_897_);
lean_closure_set(v___f_904_, 2, v___x_903_);
v_stack_x3f_905_ = l_Lean_Syntax_findStack_x3f(v_cmdStx_895_, v___f_904_, v___f_900_);
if (lean_obj_tag(v_stack_x3f_905_) == 1)
{
lean_object* v_val_906_; lean_object* v___x_907_; size_t v_sz_908_; size_t v___x_909_; lean_object* v_stack_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_candidates_913_; lean_object* v___x_914_; 
v_val_906_ = lean_ctor_get(v_stack_x3f_905_, 0);
lean_inc(v_val_906_);
lean_dec_ref_known(v_stack_x3f_905_, 1);
v___x_907_ = lean_array_mk(v_val_906_);
v_sz_908_ = lean_array_size(v___x_907_);
v___x_909_ = ((size_t)0ULL);
v_stack_910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_sz_908_, v___x_909_, v___x_907_);
v___x_911_ = lean_array_get_size(v_stack_910_);
v___x_912_ = lean_unsigned_to_nat(0u);
v_candidates_913_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1));
v___x_914_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v___x_911_, v_stack_910_, v_text_893_, v_ctx_x3f_894_, v_requestedPos_897_, v___x_899_, v___x_912_, v_candidates_913_);
lean_dec(v_requestedPos_897_);
lean_dec_ref(v_stack_910_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___f_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___y_921_; lean_object* v___x_947_; uint8_t v___x_948_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
v___f_916_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__2));
v___x_917_ = lean_array_to_list(v_a_915_);
v___x_918_ = l_List_mergeSort___redArg(v___x_917_, v___f_916_);
v___x_919_ = lean_array_mk(v___x_918_);
v___x_947_ = lean_array_get_size(v___x_919_);
v___x_948_ = lean_nat_dec_lt(v___x_912_, v___x_947_);
if (v___x_948_ == 0)
{
v___y_921_ = v___x_899_;
goto v___jp_920_;
}
else
{
if (v___x_948_ == 0)
{
v___y_921_ = v___x_899_;
goto v___jp_920_;
}
else
{
size_t v___x_949_; uint8_t v___x_950_; 
v___x_949_ = lean_usize_of_nat(v___x_947_);
v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v___x_919_, v___x_909_, v___x_949_);
v___y_921_ = v___x_950_;
goto v___jp_920_;
}
}
v___jp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; size_t v_sz_924_; lean_object* v___x_925_; 
v___x_922_ = lean_box(0);
v___x_923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0));
v_sz_924_ = lean_array_size(v___x_919_);
v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v_tree_896_, v___y_921_, v___x_899_, v___x_919_, v_sz_924_, v___x_909_, v___x_923_);
lean_dec_ref(v___x_919_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_938_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_938_ == 0)
{
v___x_928_ = v___x_925_;
v_isShared_929_ = v_isSharedCheck_938_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_938_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_fst_930_; 
v_fst_930_ = lean_ctor_get(v_a_926_, 0);
lean_inc(v_fst_930_);
lean_dec(v_a_926_);
if (lean_obj_tag(v_fst_930_) == 0)
{
lean_object* v___x_932_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_922_);
v___x_932_ = v___x_928_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_922_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
else
{
lean_object* v_val_934_; lean_object* v___x_936_; 
v_val_934_ = lean_ctor_get(v_fst_930_, 0);
lean_inc(v_val_934_);
lean_dec_ref_known(v_fst_930_, 1);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v_val_934_);
v___x_936_ = v___x_928_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_val_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
v_a_939_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_925_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_925_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec_ref(v_tree_896_);
v_a_951_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_914_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_914_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec(v_stack_x3f_905_);
lean_dec(v_requestedPos_897_);
lean_dec_ref(v_tree_896_);
lean_dec_ref(v_text_893_);
v___x_959_ = lean_box(0);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; 
lean_dec(v_requestedPos_897_);
lean_dec_ref(v_tree_896_);
lean_dec(v_cmdStx_895_);
lean_dec_ref(v_text_893_);
v___x_961_ = lean_box(0);
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___boxed(lean_object* v_text_963_, lean_object* v_ctx_x3f_964_, lean_object* v_cmdStx_965_, lean_object* v_tree_966_, lean_object* v_requestedPos_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(v_text_963_, v_ctx_x3f_964_, v_cmdStx_965_, v_tree_966_, v_requestedPos_967_);
lean_dec(v_ctx_x3f_964_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(lean_object* v_upperBound_970_, lean_object* v_stack_971_, lean_object* v_text_972_, lean_object* v_ctx_x3f_973_, lean_object* v_requestedPos_974_, uint8_t v___x_975_, lean_object* v_inst_976_, lean_object* v_R_977_, lean_object* v_a_978_, lean_object* v_b_979_, lean_object* v_c_980_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_970_, v_stack_971_, v_text_972_, v_ctx_x3f_973_, v_requestedPos_974_, v___x_975_, v_a_978_, v_b_979_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___boxed(lean_object* v_upperBound_983_, lean_object* v_stack_984_, lean_object* v_text_985_, lean_object* v_ctx_x3f_986_, lean_object* v_requestedPos_987_, lean_object* v___x_988_, lean_object* v_inst_989_, lean_object* v_R_990_, lean_object* v_a_991_, lean_object* v_b_992_, lean_object* v_c_993_, lean_object* v___y_994_){
_start:
{
uint8_t v___x_3599__boxed_995_; lean_object* v_res_996_; 
v___x_3599__boxed_995_ = lean_unbox(v___x_988_);
v_res_996_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(v_upperBound_983_, v_stack_984_, v_text_985_, v_ctx_x3f_986_, v_requestedPos_987_, v___x_3599__boxed_995_, v_inst_989_, v_R_990_, v_a_991_, v_b_992_, v_c_993_);
lean_dec(v_requestedPos_987_);
lean_dec(v_ctx_x3f_986_);
lean_dec_ref(v_stack_984_);
lean_dec(v_upperBound_983_);
return v_res_996_;
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
