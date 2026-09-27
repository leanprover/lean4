// Lean compiler output
// Module: Lean.Server.FileWorker.SignatureHelp
// Imports: public import Lean.Elab.InfoTree.Util public import Lean.Data.Lsp public import Init.Data.List.Sort.Basic import Lean.PrettyPrinter.Delaborator
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lineStart(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabForallWithSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_findStack_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_mergeSort___redArg(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_value;
static lean_once_cell_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2;
static lean_once_cell_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pipeProj"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5_value),LEAN_SCALAR_PTR_LITERAL(104, 78, 204, 170, 128, 130, 207, 24)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_<|_"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17_value),LEAN_SCALAR_PTR_LITERAL(152, 38, 96, 140, 215, 46, 31, 82)}};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_$__"};
static const lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19 = (const lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19_value),LEAN_SCALAR_PTR_LITERAL(19, 217, 134, 45, 19, 162, 148, 100)}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0_value;
static const lean_array_object l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
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
v___x_33_ = lean_st_ref_put(v___y_14_, v___x_32_);
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
lean_object* v_needle_329_; lean_object* v_table_330_; lean_object* v_stackPos_331_; lean_object* v_needlePos_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_385_; 
v_needle_329_ = lean_ctor_get(v_a_314_, 0);
v_table_330_ = lean_ctor_get(v_a_314_, 1);
v_stackPos_331_ = lean_ctor_get(v_a_314_, 2);
v_needlePos_332_ = lean_ctor_get(v_a_314_, 3);
v_isSharedCheck_385_ = !lean_is_exclusive(v_a_314_);
if (v_isSharedCheck_385_ == 0)
{
v___x_334_ = v_a_314_;
v_isShared_335_ = v_isSharedCheck_385_;
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
v_isShared_335_ = v_isSharedCheck_385_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_str_336_; lean_object* v_startInclusive_337_; lean_object* v_endExclusive_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_str_336_ = lean_ctor_get(v_needle_329_, 0);
v_startInclusive_337_ = lean_ctor_get(v_needle_329_, 1);
v_endExclusive_338_ = lean_ctor_get(v_needle_329_, 2);
v___x_339_ = lean_nat_sub(v_stackPos_331_, v_needlePos_332_);
v___x_340_ = lean_nat_sub(v_endExclusive_338_, v_startInclusive_337_);
v___x_341_ = lean_nat_add(v___x_339_, v___x_340_);
v___x_342_ = lean_nat_dec_le(v___x_341_, v___x_313_);
lean_dec(v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_needlePos_332_);
lean_dec(v_stackPos_331_);
lean_dec_ref(v_table_330_);
lean_dec_ref(v_needle_329_);
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = lean_nat_add(v___x_339_, v___x_343_);
lean_dec(v___x_339_);
v___x_345_ = lean_nat_dec_le(v___x_344_, v___x_313_);
lean_dec(v___x_344_);
if (v___x_345_ == 0)
{
lean_inc(v_b_315_);
return v_b_315_;
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_box(3);
v_a_314_ = v___x_346_;
v_b_315_ = v___x_316_;
goto _start;
}
}
else
{
uint8_t v_stackByte_348_; lean_object* v___x_349_; uint8_t v_patByte_350_; uint8_t v___x_351_; 
lean_dec(v___x_339_);
lean_inc(v_stackPos_331_);
v_stackByte_348_ = lean_string_get_byte_fast(v_s_311_, v_stackPos_331_);
v___x_349_ = lean_nat_add(v_startInclusive_337_, v_needlePos_332_);
v_patByte_350_ = lean_string_get_byte_fast(v_str_336_, v___x_349_);
v___x_351_ = lean_uint8_dec_eq(v_stackByte_348_, v_patByte_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; uint8_t v_decide_353_; 
lean_dec(v___x_340_);
v___x_352_ = lean_unsigned_to_nat(0u);
v_decide_353_ = lean_nat_dec_eq(v_needlePos_332_, v___x_352_);
if (v_decide_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v_newNeedlePos_356_; uint8_t v___x_357_; 
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_nat_sub(v_needlePos_332_, v___x_354_);
lean_dec(v_needlePos_332_);
v_newNeedlePos_356_ = lean_array_fget_borrowed(v_table_330_, v___x_355_);
lean_dec(v___x_355_);
v___x_357_ = lean_nat_dec_eq(v_newNeedlePos_356_, v___x_352_);
if (v___x_357_ == 0)
{
lean_object* v___x_359_; 
lean_inc(v_newNeedlePos_356_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 3, v_newNeedlePos_356_);
v___x_359_ = v___x_334_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_needle_329_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_table_330_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_stackPos_331_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v_newNeedlePos_356_);
v___x_359_ = v_reuseFailAlloc_361_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
v_a_314_ = v___x_359_;
v_b_315_ = v___x_316_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_362_; lean_object* v___x_364_; 
v_nextStackPos_362_ = l_String_Slice_posGE___redArg(v___x_312_, v_stackPos_331_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 3, v___x_352_);
lean_ctor_set(v___x_334_, 2, v_nextStackPos_362_);
v___x_364_ = v___x_334_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_needle_329_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_table_330_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_nextStackPos_362_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v___x_352_);
v___x_364_ = v_reuseFailAlloc_366_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
v_a_314_ = v___x_364_;
v_b_315_ = v___x_316_;
goto _start;
}
}
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_nextStackPos_369_; lean_object* v___x_371_; 
lean_dec(v_needlePos_332_);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_nat_add(v_stackPos_331_, v___x_367_);
lean_dec(v_stackPos_331_);
v_nextStackPos_369_ = l_String_Slice_posGE___redArg(v___x_312_, v___x_368_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 3, v___x_352_);
lean_ctor_set(v___x_334_, 2, v_nextStackPos_369_);
v___x_371_ = v___x_334_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_needle_329_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_table_330_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_nextStackPos_369_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v___x_352_);
v___x_371_ = v_reuseFailAlloc_373_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
v_a_314_ = v___x_371_;
v_b_315_ = v___x_316_;
goto _start;
}
}
}
else
{
lean_object* v___x_374_; lean_object* v_nextStackPos_375_; lean_object* v_nextNeedlePos_376_; uint8_t v_decide_377_; 
v___x_374_ = lean_unsigned_to_nat(1u);
v_nextStackPos_375_ = lean_nat_add(v_stackPos_331_, v___x_374_);
lean_dec(v_stackPos_331_);
v_nextNeedlePos_376_ = lean_nat_add(v_needlePos_332_, v___x_374_);
lean_dec(v_needlePos_332_);
v_decide_377_ = lean_nat_dec_eq(v_nextNeedlePos_376_, v___x_340_);
lean_dec(v___x_340_);
if (v_decide_377_ == 0)
{
lean_object* v___x_379_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 3, v_nextNeedlePos_376_);
lean_ctor_set(v___x_334_, 2, v_nextStackPos_375_);
v___x_379_ = v___x_334_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_needle_329_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_table_330_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_nextStackPos_375_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v_nextNeedlePos_376_);
v___x_379_ = v_reuseFailAlloc_381_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
v_a_314_ = v___x_379_;
goto _start;
}
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
lean_del_object(v___x_334_);
lean_dec_ref(v_table_330_);
lean_dec_ref(v_needle_329_);
v___x_382_ = lean_nat_sub(v_nextStackPos_375_, v_nextNeedlePos_376_);
lean_dec(v_nextNeedlePos_376_);
lean_dec(v_nextStackPos_375_);
v___x_383_ = l_String_Slice_pos_x21(v___x_312_, v___x_382_);
lean_dec(v___x_382_);
v___x_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg___boxed(lean_object* v_s_386_, lean_object* v___x_387_, lean_object* v___x_388_, lean_object* v_a_389_, lean_object* v_b_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_386_, v___x_387_, v___x_388_, v_a_389_, v_b_390_);
lean_dec(v_b_390_);
lean_dec(v___x_388_);
lean_dec_ref(v___x_387_);
lean_dec_ref(v_s_386_);
return v_res_391_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1));
v___x_398_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2);
v___x_401_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1));
v___x_402_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_400_);
lean_ctor_set(v___x_402_, 2, v___x_399_);
lean_ctor_set(v___x_402_, 3, v___x_399_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(lean_object* v_s_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_string_utf8_byte_size(v_s_403_);
lean_inc_ref(v_s_403_);
v___x_406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_406_, 0, v_s_403_);
lean_ctor_set(v___x_406_, 1, v___x_404_);
lean_ctor_set(v___x_406_, 2, v___x_405_);
v___x_407_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3);
v___x_408_ = lean_box(0);
v___x_409_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_403_, v___x_406_, v___x_405_, v___x_407_, v___x_408_);
lean_dec_ref_known(v___x_406_, 3);
lean_dec_ref(v_s_403_);
if (lean_obj_tag(v___x_409_) == 0)
{
return v___x_408_;
}
else
{
lean_object* v_val_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
v_val_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_val_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_val_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(lean_object* v_s_418_, lean_object* v___x_419_, lean_object* v___x_420_, lean_object* v_inst_421_, lean_object* v_R_422_, lean_object* v_a_423_, lean_object* v_b_424_, lean_object* v_c_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_418_, v___x_419_, v___x_420_, v_a_423_, v_b_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___boxed(lean_object* v_s_427_, lean_object* v___x_428_, lean_object* v___x_429_, lean_object* v_inst_430_, lean_object* v_R_431_, lean_object* v_a_432_, lean_object* v_b_433_, lean_object* v_c_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(v_s_427_, v___x_428_, v___x_429_, v_inst_430_, v_R_431_, v_a_432_, v_b_433_, v_c_434_);
lean_dec(v_b_433_);
lean_dec(v___x_429_);
lean_dec_ref(v___x_428_);
lean_dec_ref(v_s_427_);
return v_res_435_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(lean_object* v_text_436_, lean_object* v_pos_437_){
_start:
{
lean_object* v___x_438_; lean_object* v_line_439_; lean_object* v_source_440_; lean_object* v_lineStartPos_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_lineEndPos_444_; lean_object* v_line_445_; lean_object* v___x_446_; 
lean_inc_ref(v_text_436_);
v___x_438_ = l_Lean_FileMap_toPosition(v_text_436_, v_pos_437_);
v_line_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_line_439_);
lean_dec_ref(v___x_438_);
v_source_440_ = lean_ctor_get(v_text_436_, 0);
lean_inc_ref(v_source_440_);
v_lineStartPos_441_ = l_Lean_FileMap_lineStart(v_text_436_, v_line_439_);
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_add(v_line_439_, v___x_442_);
lean_dec(v_line_439_);
v_lineEndPos_444_ = l_Lean_FileMap_lineStart(v_text_436_, v___x_443_);
lean_dec(v___x_443_);
lean_dec_ref(v_text_436_);
v_line_445_ = lean_string_utf8_extract(v_source_440_, v_lineStartPos_441_, v_lineEndPos_444_);
lean_dec(v_lineEndPos_444_);
lean_dec_ref(v_source_440_);
v___x_446_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(v_line_445_);
if (lean_obj_tag(v___x_446_) == 1)
{
lean_object* v_val_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_val_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v___x_446_, 1);
v___x_448_ = lean_nat_add(v_lineStartPos_441_, v_val_447_);
lean_dec(v_val_447_);
lean_dec(v_lineStartPos_441_);
v___x_449_ = lean_nat_dec_le(v___x_448_, v_pos_437_);
lean_dec(v___x_448_);
return v___x_449_;
}
else
{
uint8_t v___x_450_; 
lean_dec(v___x_446_);
lean_dec(v_lineStartPos_441_);
v___x_450_ = 0;
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment___boxed(lean_object* v_text_451_, lean_object* v_pos_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_451_, v_pos_452_);
lean_dec(v_pos_452_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(lean_object* v_text_511_, lean_object* v_ctx_x3f_512_, lean_object* v_requestedPos_513_, lean_object* v_stx_514_, lean_object* v_parent_515_){
_start:
{
lean_object* v_kind_x3f_517_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; uint8_t v___y_542_; uint8_t v___x_625_; lean_object* v___x_626_; 
v___x_625_ = 1;
v___x_626_ = l_Lean_Syntax_getTailPos_x3f(v_stx_514_, v___x_625_);
if (lean_obj_tag(v___x_626_) == 1)
{
lean_object* v_val_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; uint8_t v___y_632_; uint8_t v___y_633_; uint8_t v___y_635_; uint8_t v___y_636_; uint8_t v___y_638_; uint8_t v___y_639_; uint8_t v___y_640_; uint8_t v___y_642_; uint8_t v___y_643_; uint8_t v___y_650_; 
v_val_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_val_627_);
lean_dec_ref_known(v___x_626_, 1);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_add(v_requestedPos_513_, v___x_628_);
v___x_630_ = lean_nat_dec_le(v___x_629_, v_val_627_);
lean_dec(v___x_629_);
if (v___x_630_ == 0)
{
if (lean_obj_tag(v_ctx_x3f_512_) == 0)
{
v___y_650_ = v___x_630_;
goto v___jp_649_;
}
else
{
lean_object* v_val_653_; uint8_t v_triggerKind_654_; 
v_val_653_ = lean_ctor_get(v_ctx_x3f_512_, 0);
v_triggerKind_654_ = lean_ctor_get_uint8(v_val_653_, sizeof(void*)*2);
if (v_triggerKind_654_ == 0)
{
v___y_650_ = v___x_625_;
goto v___jp_649_;
}
else
{
v___y_650_ = v___x_630_;
goto v___jp_649_;
}
}
}
else
{
lean_object* v___x_655_; 
lean_dec(v_val_627_);
lean_dec(v_parent_515_);
lean_dec(v_stx_514_);
lean_dec_ref(v_text_511_);
v___x_655_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23));
return v___x_655_;
}
v___jp_631_:
{
if (v___y_633_ == 0)
{
v___y_542_ = v___x_630_;
goto v___jp_541_;
}
else
{
v___y_542_ = v___y_632_;
goto v___jp_541_;
}
}
v___jp_634_:
{
if (v___y_636_ == 0)
{
v___y_542_ = v___y_635_;
goto v___jp_541_;
}
else
{
v___y_632_ = v___y_635_;
v___y_633_ = v___x_630_;
goto v___jp_631_;
}
}
v___jp_637_:
{
if (v___y_638_ == 0)
{
v___y_635_ = v___y_640_;
v___y_636_ = v___y_639_;
goto v___jp_634_;
}
else
{
if (v___x_630_ == 0)
{
v___y_632_ = v___y_640_;
v___y_633_ = v___x_630_;
goto v___jp_631_;
}
else
{
v___y_635_ = v___y_640_;
v___y_636_ = v___y_639_;
goto v___jp_634_;
}
}
}
v___jp_641_:
{
lean_object* v___x_644_; lean_object* v_line_645_; lean_object* v___x_646_; lean_object* v_line_647_; uint8_t v___x_648_; 
lean_inc_ref(v_text_511_);
v___x_644_ = l_Lean_FileMap_toPosition(v_text_511_, v_requestedPos_513_);
v_line_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_line_645_);
lean_dec_ref(v___x_644_);
v___x_646_ = l_Lean_FileMap_toPosition(v_text_511_, v_val_627_);
lean_dec(v_val_627_);
v_line_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_line_647_);
lean_dec_ref(v___x_646_);
v___x_648_ = lean_nat_dec_eq(v_line_645_, v_line_647_);
lean_dec(v_line_647_);
lean_dec(v_line_645_);
if (v___x_648_ == 0)
{
v___y_638_ = v___y_642_;
v___y_639_ = v___y_643_;
v___y_640_ = v___x_625_;
goto v___jp_637_;
}
else
{
v___y_638_ = v___y_642_;
v___y_639_ = v___y_643_;
v___y_640_ = v___x_630_;
goto v___jp_637_;
}
}
v___jp_649_:
{
if (lean_obj_tag(v_ctx_x3f_512_) == 0)
{
v___y_642_ = v___y_650_;
v___y_643_ = v___x_630_;
goto v___jp_641_;
}
else
{
lean_object* v_val_651_; uint8_t v_isRetrigger_652_; 
v_val_651_ = lean_ctor_get(v_ctx_x3f_512_, 0);
v_isRetrigger_652_ = lean_ctor_get_uint8(v_val_651_, sizeof(void*)*2 + 1);
v___y_642_ = v___y_650_;
v___y_643_ = v_isRetrigger_652_;
goto v___jp_641_;
}
}
}
else
{
lean_object* v___x_656_; 
lean_dec(v___x_626_);
lean_dec(v_parent_515_);
lean_dec(v_stx_514_);
lean_dec_ref(v_text_511_);
v___x_656_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22));
return v___x_656_;
}
v___jp_516_:
{
uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = 0;
v___x_519_ = lean_box(v___x_518_);
lean_inc(v_kind_x3f_517_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_kind_x3f_517_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
return v___x_520_;
}
v___jp_521_:
{
lean_object* v___x_522_; 
v___x_522_ = lean_box(0);
v_kind_x3f_517_ = v___x_522_;
goto v___jp_516_;
}
v___jp_523_:
{
lean_object* v___x_524_; 
v___x_524_ = lean_box(0);
v_kind_x3f_517_ = v___x_524_;
goto v___jp_516_;
}
v___jp_525_:
{
lean_object* v___x_526_; 
v___x_526_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_517_ = v___x_526_;
goto v___jp_516_;
}
v___jp_527_:
{
lean_object* v___x_528_; 
v___x_528_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_517_ = v___x_528_;
goto v___jp_516_;
}
v___jp_529_:
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_533_ = lean_unsigned_to_nat(3u);
v___x_534_ = l_Lean_Syntax_getArg(v_stx_514_, v___x_533_);
lean_dec(v_stx_514_);
v___x_535_ = l_Lean_Syntax_matchesNull(v___x_534_, v___y_531_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_536_ = lean_array_get_size(v___y_532_);
lean_dec_ref(v___y_532_);
v___x_537_ = lean_nat_dec_le(v___x_536_, v___y_530_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
v___x_538_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_517_ = v___x_538_;
goto v___jp_516_;
}
else
{
lean_object* v___x_539_; 
v___x_539_ = lean_box(0);
v_kind_x3f_517_ = v___x_539_;
goto v___jp_516_;
}
}
else
{
lean_object* v___x_540_; 
lean_dec_ref(v___y_532_);
v___x_540_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1));
v_kind_x3f_517_ = v___x_540_;
goto v___jp_516_;
}
}
v___jp_541_:
{
if (v___y_542_ == 0)
{
if (lean_obj_tag(v_stx_514_) == 3)
{
lean_object* v___x_543_; uint8_t v___x_544_; 
lean_dec_ref_known(v_stx_514_, 4);
v___x_543_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6));
lean_inc(v_parent_515_);
v___x_544_ = l_Lean_Syntax_isOfKind(v_parent_515_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8));
lean_inc(v_parent_515_);
v___x_546_ = l_Lean_Syntax_isOfKind(v_parent_515_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_547_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10));
lean_inc(v_parent_515_);
v___x_548_ = l_Lean_Syntax_isOfKind(v_parent_515_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; 
lean_dec(v_parent_515_);
v___x_549_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_517_ = v___x_549_;
goto v___jp_516_;
}
else
{
if (v___x_546_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = l_Lean_Syntax_getArg(v_parent_515_, v___x_550_);
lean_dec(v_parent_515_);
v___x_552_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_553_ = l_Lean_Syntax_isOfKind(v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
v___x_554_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_517_ = v___x_554_;
goto v___jp_516_;
}
else
{
goto v___jp_521_;
}
}
else
{
lean_dec(v_parent_515_);
goto v___jp_521_;
}
}
}
else
{
if (v___x_544_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_555_ = lean_unsigned_to_nat(2u);
v___x_556_ = l_Lean_Syntax_getArg(v_parent_515_, v___x_555_);
lean_dec(v_parent_515_);
v___x_557_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_558_ = l_Lean_Syntax_isOfKind(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_517_ = v___x_559_;
goto v___jp_516_;
}
else
{
goto v___jp_523_;
}
}
else
{
lean_dec(v_parent_515_);
goto v___jp_523_;
}
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_560_ = lean_unsigned_to_nat(2u);
v___x_561_ = l_Lean_Syntax_getArg(v_parent_515_, v___x_560_);
v___x_562_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_563_ = l_Lean_Syntax_isOfKind(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
lean_dec(v_parent_515_);
v___x_564_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_517_ = v___x_564_;
goto v___jp_516_;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_unsigned_to_nat(3u);
v___x_567_ = l_Lean_Syntax_getArg(v_parent_515_, v___x_566_);
lean_dec(v_parent_515_);
v___x_568_ = l_Lean_Syntax_matchesNull(v___x_567_, v___x_565_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
v___x_569_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_517_ = v___x_569_;
goto v___jp_516_;
}
else
{
lean_object* v___x_570_; 
v___x_570_ = lean_box(0);
v_kind_x3f_517_ = v___x_570_;
goto v___jp_516_;
}
}
}
}
else
{
lean_dec(v_parent_515_);
if (lean_obj_tag(v_stx_514_) == 1)
{
lean_object* v_kind_571_; lean_object* v_args_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v_kind_571_ = lean_ctor_get(v_stx_514_, 1);
v_args_572_ = lean_ctor_get(v_stx_514_, 2);
v___x_573_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14));
v___x_574_ = lean_name_eq(v_kind_571_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16));
v___x_576_ = lean_name_eq(v_kind_571_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18));
lean_inc_ref(v_stx_514_);
v___x_578_ = l_Lean_Syntax_isOfKind(v_stx_514_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20));
lean_inc_ref(v_stx_514_);
v___x_580_ = l_Lean_Syntax_isOfKind(v_stx_514_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6));
lean_inc_ref(v_stx_514_);
v___x_582_ = l_Lean_Syntax_isOfKind(v_stx_514_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; uint8_t v___x_584_; 
lean_inc_ref(v_args_572_);
v___x_583_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10));
lean_inc_ref(v_stx_514_);
v___x_584_ = l_Lean_Syntax_isOfKind(v_stx_514_, v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8));
lean_inc_ref(v_stx_514_);
v___x_586_ = l_Lean_Syntax_isOfKind(v_stx_514_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
lean_dec_ref_known(v_stx_514_, 3);
v___x_587_ = lean_array_get_size(v_args_572_);
lean_dec_ref(v_args_572_);
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_nat_dec_le(v___x_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_517_ = v___x_590_;
goto v___jp_516_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = lean_box(0);
v_kind_x3f_517_ = v___x_591_;
goto v___jp_516_;
}
}
else
{
if (v___x_584_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_592_ = lean_unsigned_to_nat(2u);
v___x_593_ = l_Lean_Syntax_getArg(v_stx_514_, v___x_592_);
lean_dec_ref_known(v_stx_514_, 3);
v___x_594_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
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
v___x_599_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_517_ = v___x_599_;
goto v___jp_516_;
}
else
{
lean_object* v___x_600_; 
v___x_600_ = lean_box(0);
v_kind_x3f_517_ = v___x_600_;
goto v___jp_516_;
}
}
else
{
lean_dec_ref(v_args_572_);
goto v___jp_525_;
}
}
else
{
lean_dec_ref(v_args_572_);
lean_dec_ref_known(v_stx_514_, 3);
goto v___jp_525_;
}
}
}
else
{
if (v___x_582_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = l_Lean_Syntax_getArg(v_stx_514_, v___x_601_);
lean_dec_ref_known(v_stx_514_, 3);
v___x_603_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_604_ = l_Lean_Syntax_isOfKind(v___x_602_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = lean_array_get_size(v_args_572_);
lean_dec_ref(v_args_572_);
v___x_606_ = lean_nat_dec_le(v___x_605_, v___x_601_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
v___x_607_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_517_ = v___x_607_;
goto v___jp_516_;
}
else
{
lean_object* v___x_608_; 
v___x_608_ = lean_box(0);
v_kind_x3f_517_ = v___x_608_;
goto v___jp_516_;
}
}
else
{
lean_dec_ref(v_args_572_);
goto v___jp_527_;
}
}
else
{
lean_dec_ref(v_args_572_);
lean_dec_ref_known(v_stx_514_, 3);
goto v___jp_527_;
}
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = lean_unsigned_to_nat(1u);
if (v___x_580_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_611_ = lean_unsigned_to_nat(2u);
v___x_612_ = l_Lean_Syntax_getArg(v_stx_514_, v___x_611_);
v___x_613_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_614_ = l_Lean_Syntax_isOfKind(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; uint8_t v___x_616_; 
lean_inc_ref(v_args_572_);
lean_dec_ref_known(v_stx_514_, 3);
v___x_615_ = lean_array_get_size(v_args_572_);
lean_dec_ref(v_args_572_);
v___x_616_ = lean_nat_dec_le(v___x_615_, v___x_610_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
v___x_617_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_517_ = v___x_617_;
goto v___jp_516_;
}
else
{
lean_object* v___x_618_; 
v___x_618_ = lean_box(0);
v_kind_x3f_517_ = v___x_618_;
goto v___jp_516_;
}
}
else
{
lean_inc_ref(v_args_572_);
v___y_530_ = v___x_610_;
v___y_531_ = v___x_609_;
v___y_532_ = v_args_572_;
goto v___jp_529_;
}
}
else
{
lean_inc_ref(v_args_572_);
v___y_530_ = v___x_610_;
v___y_531_ = v___x_609_;
v___y_532_ = v_args_572_;
goto v___jp_529_;
}
}
}
else
{
lean_object* v___x_619_; 
lean_dec_ref_known(v_stx_514_, 3);
v___x_619_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1));
v_kind_x3f_517_ = v___x_619_;
goto v___jp_516_;
}
}
else
{
lean_object* v___x_620_; 
lean_dec_ref_known(v_stx_514_, 3);
v___x_620_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1));
v_kind_x3f_517_ = v___x_620_;
goto v___jp_516_;
}
}
else
{
lean_object* v___x_621_; 
lean_dec_ref_known(v_stx_514_, 3);
v___x_621_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21));
v_kind_x3f_517_ = v___x_621_;
goto v___jp_516_;
}
}
else
{
lean_object* v___x_622_; 
lean_dec_ref_known(v_stx_514_, 3);
v___x_622_ = lean_box(0);
v_kind_x3f_517_ = v___x_622_;
goto v___jp_516_;
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v_stx_514_);
v___x_623_ = lean_box(0);
v_kind_x3f_517_ = v___x_623_;
goto v___jp_516_;
}
}
}
else
{
lean_object* v___x_624_; 
lean_dec(v_parent_515_);
lean_dec(v_stx_514_);
v___x_624_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22));
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___boxed(lean_object* v_text_657_, lean_object* v_ctx_x3f_658_, lean_object* v_requestedPos_659_, lean_object* v_stx_660_, lean_object* v_parent_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_657_, v_ctx_x3f_658_, v_requestedPos_659_, v_stx_660_, v_parent_661_);
lean_dec(v_requestedPos_659_);
lean_dec(v_ctx_x3f_658_);
return v_res_662_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(uint8_t v___x_663_, lean_object* v_stx_664_){
_start:
{
uint8_t v___x_665_; 
v___x_665_ = l_Lean_Syntax_hasArgs(v_stx_664_);
if (v___x_665_ == 0)
{
uint8_t v___x_666_; 
v___x_666_ = 1;
return v___x_666_;
}
else
{
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed(lean_object* v___x_667_, lean_object* v_stx_668_){
_start:
{
uint8_t v___x_2727__boxed_669_; uint8_t v_res_670_; lean_object* v_r_671_; 
v___x_2727__boxed_669_ = lean_unbox(v___x_667_);
v_res_670_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(v___x_2727__boxed_669_, v_stx_668_);
lean_dec(v_stx_668_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(uint8_t v___x_672_, lean_object* v_requestedPos_673_, uint8_t v___x_674_, lean_object* v_stx_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_675_, v___x_672_);
if (lean_obj_tag(v___x_676_) == 1)
{
lean_object* v_val_677_; uint8_t v___x_678_; 
v_val_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = l_Lean_Syntax_Range_contains(v_val_677_, v_requestedPos_673_, v___x_672_);
lean_dec(v_val_677_);
return v___x_678_;
}
else
{
lean_dec(v___x_676_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed(lean_object* v___x_679_, lean_object* v_requestedPos_680_, lean_object* v___x_681_, lean_object* v_stx_682_){
_start:
{
uint8_t v___x_2734__boxed_683_; uint8_t v___x_2735__boxed_684_; uint8_t v_res_685_; lean_object* v_r_686_; 
v___x_2734__boxed_683_ = lean_unbox(v___x_679_);
v___x_2735__boxed_684_ = lean_unbox(v___x_681_);
v_res_685_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(v___x_2734__boxed_683_, v_requestedPos_680_, v___x_2735__boxed_684_, v_stx_682_);
lean_dec(v_stx_682_);
lean_dec(v_requestedPos_680_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(lean_object* v_c1_687_, lean_object* v_c2_688_){
_start:
{
uint8_t v_kind_689_; uint8_t v_kind_690_; lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v_kind_689_ = lean_ctor_get_uint8(v_c2_688_, sizeof(void*)*1);
v_kind_690_ = lean_ctor_get_uint8(v_c1_687_, sizeof(void*)*1);
v___x_691_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_689_);
v___x_692_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_690_);
v___x_693_ = lean_nat_dec_le(v___x_691_, v___x_692_);
lean_dec(v___x_692_);
lean_dec(v___x_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2___boxed(lean_object* v_c1_694_, lean_object* v_c2_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(v_c1_694_, v_c2_695_);
lean_dec_ref(v_c2_695_);
lean_dec_ref(v_c1_694_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(size_t v_sz_698_, size_t v_i_699_, lean_object* v_bs_700_){
_start:
{
uint8_t v___x_701_; 
v___x_701_ = lean_usize_dec_lt(v_i_699_, v_sz_698_);
if (v___x_701_ == 0)
{
return v_bs_700_;
}
else
{
lean_object* v_v_702_; lean_object* v_fst_703_; lean_object* v___x_704_; lean_object* v_bs_x27_705_; size_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; 
v_v_702_ = lean_array_uget_borrowed(v_bs_700_, v_i_699_);
v_fst_703_ = lean_ctor_get(v_v_702_, 0);
lean_inc(v_fst_703_);
v___x_704_ = lean_unsigned_to_nat(0u);
v_bs_x27_705_ = lean_array_uset(v_bs_700_, v_i_699_, v___x_704_);
v___x_706_ = ((size_t)1ULL);
v___x_707_ = lean_usize_add(v_i_699_, v___x_706_);
v___x_708_ = lean_array_uset(v_bs_x27_705_, v_i_699_, v_fst_703_);
v_i_699_ = v___x_707_;
v_bs_700_ = v___x_708_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___boxed(lean_object* v_sz_710_, lean_object* v_i_711_, lean_object* v_bs_712_){
_start:
{
size_t v_sz_boxed_713_; size_t v_i_boxed_714_; lean_object* v_res_715_; 
v_sz_boxed_713_ = lean_unbox_usize(v_sz_710_);
lean_dec(v_sz_710_);
v_i_boxed_714_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v_sz_boxed_713_, v_i_boxed_714_, v_bs_712_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0(lean_object* v_tree_724_, uint8_t v___y_725_, uint8_t v___x_726_, lean_object* v_as_727_, size_t v_sz_728_, size_t v_i_729_, lean_object* v_b_730_){
_start:
{
uint8_t v___x_732_; 
v___x_732_ = lean_usize_dec_lt(v_i_729_, v_sz_728_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
lean_dec_ref(v_tree_724_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v_b_730_);
return v___x_733_;
}
else
{
lean_object* v_a_734_; uint8_t v_kind_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___y_763_; 
lean_dec_ref(v_b_730_);
v_a_734_ = lean_array_uget_borrowed(v_as_727_, v_i_729_);
v_kind_735_ = lean_ctor_get_uint8(v_a_734_, sizeof(void*)*1);
v___x_736_ = lean_box(0);
v___x_737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__0));
if (v_kind_735_ == 1)
{
v___y_763_ = v___y_725_;
goto v___jp_762_;
}
else
{
if (v___x_726_ == 0)
{
goto v___jp_738_;
}
else
{
v___y_763_ = v___y_725_;
goto v___jp_762_;
}
}
v___jp_738_:
{
lean_object* v_appStx_739_; lean_object* v___x_740_; 
v_appStx_739_ = lean_ctor_get(v_a_734_, 0);
lean_inc(v_appStx_739_);
lean_inc_ref(v_tree_724_);
v___x_740_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_724_, v_appStx_739_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_753_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_753_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_753_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_753_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
if (lean_obj_tag(v_a_741_) == 1)
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
lean_dec_ref(v_tree_724_);
v___x_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_745_, 0, v_a_741_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___x_736_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_746_);
v___x_748_ = v___x_743_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
else
{
size_t v___x_750_; size_t v___x_751_; 
lean_del_object(v___x_743_);
lean_dec(v_a_741_);
v___x_750_ = ((size_t)1ULL);
v___x_751_ = lean_usize_add(v_i_729_, v___x_750_);
v_i_729_ = v___x_751_;
v_b_730_ = v___x_737_;
goto _start;
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v_tree_724_);
v_a_754_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_740_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_740_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
v___jp_762_:
{
if (v___y_763_ == 0)
{
goto v___jp_738_;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; 
lean_dec_ref(v_tree_724_);
v___x_764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__2));
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___boxed(lean_object* v_tree_766_, lean_object* v___y_767_, lean_object* v___x_768_, lean_object* v_as_769_, lean_object* v_sz_770_, lean_object* v_i_771_, lean_object* v_b_772_, lean_object* v___y_773_){
_start:
{
uint8_t v___y_2780__boxed_774_; uint8_t v___x_2781__boxed_775_; size_t v_sz_boxed_776_; size_t v_i_boxed_777_; lean_object* v_res_778_; 
v___y_2780__boxed_774_ = lean_unbox(v___y_767_);
v___x_2781__boxed_775_ = lean_unbox(v___x_768_);
v_sz_boxed_776_ = lean_unbox_usize(v_sz_770_);
lean_dec(v_sz_770_);
v_i_boxed_777_ = lean_unbox_usize(v_i_771_);
lean_dec(v_i_771_);
v_res_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0(v_tree_766_, v___y_2780__boxed_774_, v___x_2781__boxed_775_, v_as_769_, v_sz_boxed_776_, v_i_boxed_777_, v_b_772_);
lean_dec_ref(v_as_769_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(lean_object* v_tree_779_, uint8_t v___y_780_, uint8_t v___x_781_, lean_object* v_as_782_, size_t v_sz_783_, size_t v_i_784_, lean_object* v_b_785_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = lean_usize_dec_lt(v_i_784_, v_sz_783_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
lean_dec_ref(v_tree_779_);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v_b_785_);
return v___x_788_;
}
else
{
lean_object* v_a_789_; uint8_t v_kind_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___y_818_; 
lean_dec_ref(v_b_785_);
v_a_789_ = lean_array_uget_borrowed(v_as_782_, v_i_784_);
v_kind_790_ = lean_ctor_get_uint8(v_a_789_, sizeof(void*)*1);
v___x_791_ = lean_box(0);
v___x_792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__0));
if (v_kind_790_ == 1)
{
v___y_818_ = v___y_780_;
goto v___jp_817_;
}
else
{
if (v___x_781_ == 0)
{
goto v___jp_793_;
}
else
{
v___y_818_ = v___y_780_;
goto v___jp_817_;
}
}
v___jp_793_:
{
lean_object* v_appStx_794_; lean_object* v___x_795_; 
v_appStx_794_ = lean_ctor_get(v_a_789_, 0);
lean_inc(v_appStx_794_);
lean_inc_ref(v_tree_779_);
v___x_795_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_779_, v_appStx_794_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_808_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_808_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_808_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_808_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
if (lean_obj_tag(v_a_796_) == 1)
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
lean_dec_ref(v_tree_779_);
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v_a_796_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v___x_791_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_801_);
v___x_803_ = v___x_798_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
else
{
size_t v___x_805_; size_t v___x_806_; lean_object* v___x_807_; 
lean_del_object(v___x_798_);
lean_dec(v_a_796_);
v___x_805_ = ((size_t)1ULL);
v___x_806_ = lean_usize_add(v_i_784_, v___x_805_);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0(v_tree_779_, v___y_780_, v___x_781_, v_as_782_, v_sz_783_, v___x_806_, v___x_792_);
return v___x_807_;
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_tree_779_);
v_a_809_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_795_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_795_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
v___jp_817_:
{
if (v___y_818_ == 0)
{
goto v___jp_793_;
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec_ref(v_tree_779_);
v___x_819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__2));
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0___boxed(lean_object* v_tree_821_, lean_object* v___y_822_, lean_object* v___x_823_, lean_object* v_as_824_, lean_object* v_sz_825_, lean_object* v_i_826_, lean_object* v_b_827_, lean_object* v___y_828_){
_start:
{
uint8_t v___y_2868__boxed_829_; uint8_t v___x_2869__boxed_830_; size_t v_sz_boxed_831_; size_t v_i_boxed_832_; lean_object* v_res_833_; 
v___y_2868__boxed_829_ = lean_unbox(v___y_822_);
v___x_2869__boxed_830_ = lean_unbox(v___x_823_);
v_sz_boxed_831_ = lean_unbox_usize(v_sz_825_);
lean_dec(v_sz_825_);
v_i_boxed_832_ = lean_unbox_usize(v_i_826_);
lean_dec(v_i_826_);
v_res_833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_tree_821_, v___y_2868__boxed_829_, v___x_2869__boxed_830_, v_as_824_, v_sz_boxed_831_, v_i_boxed_832_, v_b_827_);
lean_dec_ref(v_as_824_);
return v_res_833_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0(void){
_start:
{
uint8_t v___x_834_; lean_object* v___x_835_; 
v___x_834_ = 1;
v___x_835_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(lean_object* v_as_836_, size_t v_i_837_, size_t v_stop_838_){
_start:
{
uint8_t v___x_839_; 
v___x_839_ = lean_usize_dec_eq(v_i_837_, v_stop_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; uint8_t v_kind_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_840_ = lean_array_uget_borrowed(v_as_836_, v_i_837_);
v_kind_841_ = lean_ctor_get_uint8(v___x_840_, sizeof(void*)*1);
v___x_842_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0);
v___x_843_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_841_);
v___x_844_ = lean_nat_dec_lt(v___x_842_, v___x_843_);
lean_dec(v___x_843_);
if (v___x_844_ == 0)
{
size_t v___x_845_; size_t v___x_846_; 
v___x_845_ = ((size_t)1ULL);
v___x_846_ = lean_usize_add(v_i_837_, v___x_845_);
v_i_837_ = v___x_846_;
goto _start;
}
else
{
return v___x_844_;
}
}
else
{
uint8_t v___x_848_; 
v___x_848_ = 0;
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___boxed(lean_object* v_as_849_, lean_object* v_i_850_, lean_object* v_stop_851_){
_start:
{
size_t v_i_boxed_852_; size_t v_stop_boxed_853_; uint8_t v_res_854_; lean_object* v_r_855_; 
v_i_boxed_852_ = lean_unbox_usize(v_i_850_);
lean_dec(v_i_850_);
v_stop_boxed_853_ = lean_unbox_usize(v_stop_851_);
lean_dec(v_stop_851_);
v_res_854_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v_as_849_, v_i_boxed_852_, v_stop_boxed_853_);
lean_dec_ref(v_as_849_);
v_r_855_ = lean_box(v_res_854_);
return v_r_855_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(uint8_t v_snd_856_, uint8_t v___x_857_, lean_object* v_____r_858_, lean_object* v_candidates_859_){
_start:
{
if (v_snd_856_ == 1)
{
goto v___jp_861_;
}
else
{
if (v___x_857_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v_candidates_859_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
else
{
goto v___jp_861_;
}
}
v___jp_861_:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v_candidates_859_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0___boxed(lean_object* v_snd_866_, lean_object* v___x_867_, lean_object* v_____r_868_, lean_object* v_candidates_869_, lean_object* v___y_870_){
_start:
{
uint8_t v_snd_2966__boxed_871_; uint8_t v___x_2967__boxed_872_; lean_object* v_res_873_; 
v_snd_2966__boxed_871_ = lean_unbox(v_snd_866_);
v___x_2967__boxed_872_ = lean_unbox(v___x_867_);
v_res_873_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v_snd_2966__boxed_871_, v___x_2967__boxed_872_, v_____r_868_, v_candidates_869_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(lean_object* v_upperBound_874_, lean_object* v_stack_875_, lean_object* v_text_876_, lean_object* v_ctx_x3f_877_, lean_object* v_requestedPos_878_, uint8_t v___x_879_, lean_object* v_a_880_, lean_object* v_b_881_){
_start:
{
lean_object* v___y_884_; uint8_t v___x_906_; 
v___x_906_ = lean_nat_dec_lt(v_a_880_, v_upperBound_874_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
lean_dec(v_a_880_);
lean_dec_ref(v_text_876_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v_b_881_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; lean_object* v___y_910_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_908_ = lean_array_fget_borrowed(v_stack_875_, v_a_880_);
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_add(v_a_880_, v___x_925_);
v___x_927_ = lean_array_get_size(v_stack_875_);
v___x_928_ = lean_nat_dec_lt(v___x_926_, v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v___y_910_ = v___x_929_;
goto v___jp_909_;
}
else
{
lean_object* v___x_930_; 
v___x_930_ = lean_array_fget_borrowed(v_stack_875_, v___x_926_);
lean_dec(v___x_926_);
lean_inc(v___x_930_);
v___y_910_ = v___x_930_;
goto v___jp_909_;
}
v___jp_909_:
{
lean_object* v___x_911_; lean_object* v_fst_912_; 
lean_inc(v___x_908_);
lean_inc_ref(v_text_876_);
v___x_911_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_876_, v_ctx_x3f_877_, v_requestedPos_878_, v___x_908_, v___y_910_);
v_fst_912_ = lean_ctor_get(v___x_911_, 0);
if (lean_obj_tag(v_fst_912_) == 1)
{
lean_object* v_snd_913_; lean_object* v_val_914_; lean_object* v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; 
lean_inc_ref(v_fst_912_);
v_snd_913_ = lean_ctor_get(v___x_911_, 1);
lean_inc(v_snd_913_);
lean_dec_ref(v___x_911_);
v_val_914_ = lean_ctor_get(v_fst_912_, 0);
lean_inc(v_val_914_);
lean_dec_ref_known(v_fst_912_, 1);
lean_inc(v___x_908_);
v___x_915_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_915_, 0, v___x_908_);
v___x_916_ = lean_unbox(v_val_914_);
lean_dec(v_val_914_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*1, v___x_916_);
v___x_917_ = lean_array_push(v_b_881_, v___x_915_);
v___x_918_ = lean_box(0);
v___x_919_ = lean_unbox(v_snd_913_);
lean_dec(v_snd_913_);
v___x_920_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_919_, v___x_879_, v___x_918_, v___x_917_);
v___y_884_ = v___x_920_;
goto v___jp_883_;
}
else
{
lean_object* v_snd_921_; lean_object* v___x_922_; uint8_t v___x_923_; lean_object* v___x_924_; 
v_snd_921_ = lean_ctor_get(v___x_911_, 1);
lean_inc(v_snd_921_);
lean_dec_ref(v___x_911_);
v___x_922_ = lean_box(0);
v___x_923_ = lean_unbox(v_snd_921_);
lean_dec(v_snd_921_);
v___x_924_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_923_, v___x_879_, v___x_922_, v_b_881_);
v___y_884_ = v___x_924_;
goto v___jp_883_;
}
}
}
v___jp_883_:
{
if (lean_obj_tag(v___y_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_897_; 
v_a_885_ = lean_ctor_get(v___y_884_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___y_884_);
if (v_isSharedCheck_897_ == 0)
{
v___x_887_ = v___y_884_;
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___y_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
if (lean_obj_tag(v_a_885_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; 
lean_dec(v_a_880_);
lean_dec_ref(v_text_876_);
v_a_889_ = lean_ctor_get(v_a_885_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v_a_885_, 1);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v_a_889_);
v___x_891_ = v___x_887_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_del_object(v___x_887_);
v_a_893_ = lean_ctor_get(v_a_885_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v_a_885_, 1);
v___x_894_ = lean_unsigned_to_nat(1u);
v___x_895_ = lean_nat_add(v_a_880_, v___x_894_);
lean_dec(v_a_880_);
v_a_880_ = v___x_895_;
v_b_881_ = v_a_893_;
goto _start;
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec(v_a_880_);
lean_dec_ref(v_text_876_);
v_a_898_ = lean_ctor_get(v___y_884_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___y_884_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___y_884_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___y_884_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___boxed(lean_object* v_upperBound_931_, lean_object* v_stack_932_, lean_object* v_text_933_, lean_object* v_ctx_x3f_934_, lean_object* v_requestedPos_935_, lean_object* v___x_936_, lean_object* v_a_937_, lean_object* v_b_938_, lean_object* v___y_939_){
_start:
{
uint8_t v___x_2989__boxed_940_; lean_object* v_res_941_; 
v___x_2989__boxed_940_ = lean_unbox(v___x_936_);
v_res_941_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_931_, v_stack_932_, v_text_933_, v_ctx_x3f_934_, v_requestedPos_935_, v___x_2989__boxed_940_, v_a_937_, v_b_938_);
lean_dec(v_requestedPos_935_);
lean_dec(v_ctx_x3f_934_);
lean_dec_ref(v_stack_932_);
lean_dec(v_upperBound_931_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(lean_object* v_text_945_, lean_object* v_ctx_x3f_946_, lean_object* v_cmdStx_947_, lean_object* v_tree_948_, lean_object* v_requestedPos_949_){
_start:
{
uint8_t v___x_951_; 
lean_inc_ref(v_text_945_);
v___x_951_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_945_, v_requestedPos_949_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___f_953_; uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___f_957_; lean_object* v_stack_x3f_958_; 
v___x_952_ = lean_box(v___x_951_);
v___f_953_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_953_, 0, v___x_952_);
v___x_954_ = 1;
v___x_955_ = lean_box(v___x_954_);
v___x_956_ = lean_box(v___x_951_);
lean_inc(v_requestedPos_949_);
v___f_957_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed), 4, 3);
lean_closure_set(v___f_957_, 0, v___x_955_);
lean_closure_set(v___f_957_, 1, v_requestedPos_949_);
lean_closure_set(v___f_957_, 2, v___x_956_);
v_stack_x3f_958_ = l_Lean_Syntax_findStack_x3f(v_cmdStx_947_, v___f_957_, v___f_953_);
if (lean_obj_tag(v_stack_x3f_958_) == 1)
{
lean_object* v_val_959_; lean_object* v___f_960_; lean_object* v___x_961_; size_t v_sz_962_; size_t v___x_963_; lean_object* v_stack_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v_candidates_967_; lean_object* v___x_968_; 
v_val_959_ = lean_ctor_get(v_stack_x3f_958_, 0);
lean_inc(v_val_959_);
lean_dec_ref_known(v_stack_x3f_958_, 1);
v___f_960_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0));
v___x_961_ = lean_array_mk(v_val_959_);
v_sz_962_ = lean_array_size(v___x_961_);
v___x_963_ = ((size_t)0ULL);
v_stack_964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v_sz_962_, v___x_963_, v___x_961_);
v___x_965_ = lean_array_get_size(v_stack_964_);
v___x_966_ = lean_unsigned_to_nat(0u);
v_candidates_967_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1));
v___x_968_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v___x_965_, v_stack_964_, v_text_945_, v_ctx_x3f_946_, v_requestedPos_949_, v___x_951_, v___x_966_, v_candidates_967_);
lean_dec(v_requestedPos_949_);
lean_dec_ref(v_stack_964_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___y_974_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = lean_array_to_list(v_a_969_);
v___x_971_ = l_List_mergeSort___redArg(v___x_970_, v___f_960_);
v___x_972_ = lean_array_mk(v___x_971_);
v___x_1000_ = lean_array_get_size(v___x_972_);
v___x_1001_ = lean_nat_dec_lt(v___x_966_, v___x_1000_);
if (v___x_1001_ == 0)
{
v___y_974_ = v___x_1001_;
goto v___jp_973_;
}
else
{
if (v___x_1001_ == 0)
{
v___y_974_ = v___x_1001_;
goto v___jp_973_;
}
else
{
size_t v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = lean_usize_of_nat(v___x_1000_);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v___x_972_, v___x_963_, v___x_1002_);
v___y_974_ = v___x_1003_;
goto v___jp_973_;
}
}
v___jp_973_:
{
lean_object* v___x_975_; lean_object* v___x_976_; size_t v_sz_977_; lean_object* v___x_978_; 
v___x_975_ = lean_box(0);
v___x_976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__0));
v_sz_977_ = lean_array_size(v___x_972_);
v___x_978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_tree_948_, v___y_974_, v___x_951_, v___x_972_, v_sz_977_, v___x_963_, v___x_976_);
lean_dec_ref(v___x_972_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_991_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_991_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_991_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_991_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v_fst_983_; 
v_fst_983_ = lean_ctor_get(v_a_979_, 0);
lean_inc(v_fst_983_);
lean_dec(v_a_979_);
if (lean_obj_tag(v_fst_983_) == 0)
{
lean_object* v___x_985_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_975_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_975_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
else
{
lean_object* v_val_987_; lean_object* v___x_989_; 
v_val_987_ = lean_ctor_get(v_fst_983_, 0);
lean_inc(v_val_987_);
lean_dec_ref_known(v_fst_983_, 1);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v_val_987_);
v___x_989_ = v___x_981_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_val_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
v_a_992_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_978_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_978_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_tree_948_);
v_a_1004_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_968_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_968_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_dec(v_stack_x3f_958_);
lean_dec(v_requestedPos_949_);
lean_dec_ref(v_tree_948_);
lean_dec_ref(v_text_945_);
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec(v_requestedPos_949_);
lean_dec_ref(v_tree_948_);
lean_dec(v_cmdStx_947_);
lean_dec_ref(v_text_945_);
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___boxed(lean_object* v_text_1016_, lean_object* v_ctx_x3f_1017_, lean_object* v_cmdStx_1018_, lean_object* v_tree_1019_, lean_object* v_requestedPos_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(v_text_1016_, v_ctx_x3f_1017_, v_cmdStx_1018_, v_tree_1019_, v_requestedPos_1020_);
lean_dec(v_ctx_x3f_1017_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(lean_object* v_upperBound_1023_, lean_object* v_stack_1024_, lean_object* v_text_1025_, lean_object* v_ctx_x3f_1026_, lean_object* v_requestedPos_1027_, uint8_t v___x_1028_, lean_object* v_inst_1029_, lean_object* v_R_1030_, lean_object* v_a_1031_, lean_object* v_b_1032_, lean_object* v_c_1033_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_1023_, v_stack_1024_, v_text_1025_, v_ctx_x3f_1026_, v_requestedPos_1027_, v___x_1028_, v_a_1031_, v_b_1032_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___boxed(lean_object* v_upperBound_1036_, lean_object* v_stack_1037_, lean_object* v_text_1038_, lean_object* v_ctx_x3f_1039_, lean_object* v_requestedPos_1040_, lean_object* v___x_1041_, lean_object* v_inst_1042_, lean_object* v_R_1043_, lean_object* v_a_1044_, lean_object* v_b_1045_, lean_object* v_c_1046_, lean_object* v___y_1047_){
_start:
{
uint8_t v___x_3224__boxed_1048_; lean_object* v_res_1049_; 
v___x_3224__boxed_1048_ = lean_unbox(v___x_1041_);
v_res_1049_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(v_upperBound_1036_, v_stack_1037_, v_text_1038_, v_ctx_x3f_1039_, v_requestedPos_1040_, v___x_3224__boxed_1048_, v_inst_1042_, v_R_1043_, v_a_1044_, v_b_1045_, v_c_1046_);
lean_dec(v_requestedPos_1040_);
lean_dec(v_ctx_x3f_1039_);
lean_dec_ref(v_stack_1037_);
lean_dec(v_upperBound_1036_);
return v_res_1049_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
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
res = runtime_initialize_Lean_Elab_InfoTree_Util(builtin);
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
lean_object* initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter_Delaborator(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_SignatureHelp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_InfoTree_Util(builtin);
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
