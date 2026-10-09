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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___impl___boxed(lean_object*);
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
uint8_t l_instBEqOption_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_9_;
v_res_9_ = l_instBEqOption_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(v_x_1_, v_x_2_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0___boxed(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_instBEqOption_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(v_x_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec(v_x_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(lean_object* v_e_14_, lean_object* v___y_15_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = l_Lean_Expr_hasMVar(v_e_14_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; 
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v_e_14_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v_mctx_20_; lean_object* v___x_21_; lean_object* v_fst_22_; lean_object* v_snd_23_; lean_object* v___x_24_; lean_object* v_cache_25_; lean_object* v_zetaDeltaFVarIds_26_; lean_object* v_postponed_27_; lean_object* v_diag_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_37_; 
v___x_19_ = lean_st_ref_get(v___y_15_);
v_mctx_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc_ref(v_mctx_20_);
lean_dec(v___x_19_);
v___x_21_ = l_Lean_instantiateMVarsCore(v_mctx_20_, v_e_14_);
v_fst_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_fst_22_);
v_snd_23_ = lean_ctor_get(v___x_21_, 1);
lean_inc(v_snd_23_);
lean_dec_ref(v___x_21_);
v___x_24_ = lean_st_ref_take(v___y_15_);
v_cache_25_ = lean_ctor_get(v___x_24_, 1);
v_zetaDeltaFVarIds_26_ = lean_ctor_get(v___x_24_, 2);
v_postponed_27_ = lean_ctor_get(v___x_24_, 3);
v_diag_28_ = lean_ctor_get(v___x_24_, 4);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_37_ == 0)
{
lean_object* v_unused_38_; 
v_unused_38_ = lean_ctor_get(v___x_24_, 0);
lean_dec(v_unused_38_);
v___x_30_ = v___x_24_;
v_isShared_31_ = v_isSharedCheck_37_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_diag_28_);
lean_inc(v_postponed_27_);
lean_inc(v_zetaDeltaFVarIds_26_);
lean_inc(v_cache_25_);
lean_dec(v___x_24_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_37_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_33_; 
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v_snd_23_);
v___x_33_ = v___x_30_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_snd_23_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v_cache_25_);
lean_ctor_set(v_reuseFailAlloc_36_, 2, v_zetaDeltaFVarIds_26_);
lean_ctor_set(v_reuseFailAlloc_36_, 3, v_postponed_27_);
lean_ctor_set(v_reuseFailAlloc_36_, 4, v_diag_28_);
v___x_33_ = v_reuseFailAlloc_36_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_st_ref_put(v___y_15_, v___x_33_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v_fst_22_);
return v___x_35_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_14_ = stack[0].m_obj;
lean_object* v___y_15_ = stack[1].m_obj;
lean_object* v_res_39_;
v_res_39_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_e_14_, v___y_15_);
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg___boxed(lean_object* v_e_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_e_40_, v___y_41_);
lean_dec(v___y_41_);
return v_res_43_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1(lean_object* v_e_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_e_44_, v___y_46_);
return v___x_50_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_44_ = stack[0].m_obj;
lean_object* v___y_45_ = stack[1].m_obj;
lean_object* v___y_46_ = stack[2].m_obj;
lean_object* v___y_47_ = stack[3].m_obj;
lean_object* v___y_48_ = stack[4].m_obj;
lean_object* v_res_51_;
v_res_51_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1(v_e_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___boxed(lean_object* v_e_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1(v_e_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_58_;
}
}
uint8_t l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0(lean_object* v_appStx_59_, lean_object* v_x_60_){
_start:
{
if (lean_obj_tag(v_x_60_) == 1)
{
lean_object* v_i_61_; lean_object* v_toElabInfo_62_; lean_object* v_stx_63_; uint8_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v_i_61_ = lean_ctor_get(v_x_60_, 0);
v_toElabInfo_62_ = lean_ctor_get(v_i_61_, 0);
v_stx_63_ = lean_ctor_get(v_toElabInfo_62_, 1);
v___x_64_ = 0;
v___x_65_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_63_, v___x_64_);
v___x_66_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_appStx_59_, v___x_64_);
v___x_67_ = l_instBEqOption_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(v___x_65_, v___x_66_);
lean_dec(v___x_66_);
lean_dec(v___x_65_);
return v___x_67_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_appStx_59_ = stack[0].m_obj;
lean_object* v_x_60_ = stack[1].m_obj;
uint8_t v_res_69_;
v_res_69_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0(v_appStx_59_, v_x_60_);
stack->m_num = v_res_69_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0___boxed(lean_object* v_appStx_70_, lean_object* v_x_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0(v_appStx_70_, v_x_71_);
lean_dec_ref(v_x_71_);
lean_dec(v_appStx_70_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1(lean_object* v_expr_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_81_; 
lean_inc(v___y_79_);
lean_inc_ref(v___y_78_);
lean_inc(v___y_77_);
lean_inc_ref(v___y_76_);
v___x_81_ = lean_infer_type(v_expr_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_83_; lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_124_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref_known(v___x_81_, 1);
v___x_83_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_a_82_, v___y_77_);
v_a_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_124_ == 0)
{
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_124_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_124_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
uint8_t v___x_88_; 
v___x_88_ = l_Lean_Expr_isForall(v_a_84_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_91_; 
lean_dec(v_a_84_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
v___x_89_ = lean_box(0);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_89_);
v___x_91_ = v___x_86_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
lean_del_object(v___x_86_);
v___x_93_ = lean_box(1);
v___x_94_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___closed__0));
v___x_95_ = l_Lean_PrettyPrinter_delabCore___redArg(v_a_84_, v___x_93_, v___x_94_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v_fst_97_; lean_object* v___x_98_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_96_);
lean_dec_ref_known(v___x_95_, 1);
v_fst_97_ = lean_ctor_get(v_a_96_, 0);
lean_inc(v_fst_97_);
lean_dec(v_a_96_);
v___x_98_ = l_Lean_PrettyPrinter_ppTerm(v_fst_97_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_107_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_107_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v_a_99_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_103_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
v_a_108_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___x_98_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_98_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
v_a_116_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_95_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_95_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
v_a_125_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_81_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_81_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_75_ = stack[0].m_obj;
lean_object* v___y_76_ = stack[1].m_obj;
lean_object* v___y_77_ = stack[2].m_obj;
lean_object* v___y_78_ = stack[3].m_obj;
lean_object* v___y_79_ = stack[4].m_obj;
lean_object* v_res_133_;
v_res_133_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1(v_expr_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___boxed(lean_object* v_expr_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1(v_expr_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
return v_res_140_;
}
}
lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(lean_object* v_tree_143_, lean_object* v_appStx_144_){
_start:
{
lean_object* v___f_149_; lean_object* v___x_150_; 
v___f_149_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0___boxed), 2, 1);
lean_closure_set(v___f_149_, 0, v_appStx_144_);
v___x_150_ = l_Lean_Elab_InfoTree_smallestInfo_x3f(v___f_149_, v_tree_143_);
if (lean_obj_tag(v___x_150_) == 1)
{
lean_object* v_val_151_; lean_object* v_snd_152_; 
v_val_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_val_151_);
lean_dec_ref_known(v___x_150_, 1);
v_snd_152_ = lean_ctor_get(v_val_151_, 1);
if (lean_obj_tag(v_snd_152_) == 1)
{
lean_object* v_i_153_; lean_object* v_fst_154_; lean_object* v_lctx_155_; lean_object* v_expr_156_; lean_object* v___f_157_; lean_object* v___x_158_; 
v_i_153_ = lean_ctor_get(v_snd_152_, 0);
lean_inc_ref(v_i_153_);
v_fst_154_ = lean_ctor_get(v_val_151_, 0);
lean_inc(v_fst_154_);
lean_dec(v_val_151_);
v_lctx_155_ = lean_ctor_get(v_i_153_, 1);
lean_inc_ref(v_lctx_155_);
v_expr_156_ = lean_ctor_get(v_i_153_, 3);
lean_inc_ref(v_expr_156_);
lean_dec_ref(v_i_153_);
v___f_157_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___boxed), 6, 1);
lean_closure_set(v___f_157_, 0, v_expr_156_);
v___x_158_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_fst_154_, v_lctx_155_, v___f_157_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_188_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_188_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_188_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_188_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
if (lean_obj_tag(v_a_159_) == 1)
{
lean_object* v_val_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_183_; 
v_val_163_ = lean_ctor_get(v_a_159_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_a_159_);
if (v_isSharedCheck_183_ == 0)
{
v___x_165_ = v_a_159_;
v_isShared_166_ = v_isSharedCheck_183_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_val_163_);
lean_dec(v_a_159_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_183_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_167_ = l_Std_Format_defWidth;
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = l_Std_Format_pretty(v_val_163_, v___x_167_, v___x_168_, v___x_168_);
v___x_170_ = lean_box(0);
v___x_171_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
lean_ctor_set(v___x_171_, 2, v___x_170_);
lean_ctor_set(v___x_171_, 3, v___x_170_);
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = lean_mk_empty_array_with_capacity(v___x_172_);
v___x_174_ = lean_array_push(v___x_173_, v___x_171_);
v___x_175_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__0));
v___x_176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
lean_ctor_set(v___x_176_, 2, v___x_170_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_176_);
v___x_178_ = v___x_165_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_176_);
v___x_178_ = v_reuseFailAlloc_182_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_180_; 
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_178_);
v___x_180_ = v___x_161_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
else
{
lean_object* v___x_184_; lean_object* v___x_186_; 
lean_dec(v_a_159_);
v___x_184_ = lean_box(0);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_184_);
v___x_186_ = v___x_161_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
v_a_189_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_158_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_158_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
else
{
lean_dec(v_val_151_);
goto v___jp_146_;
}
}
else
{
lean_dec(v___x_150_);
goto v___jp_146_;
}
v___jp_146_:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_box(0);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_0interp(lean_interpreter_value* stack)
{
lean_object* v_tree_143_ = stack[0].m_obj;
lean_object* v_appStx_144_ = stack[1].m_obj;
lean_object* v_res_197_;
v_res_197_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_143_, v_appStx_144_);
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___boxed(lean_object* v_tree_198_, lean_object* v_appStx_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_198_, v_appStx_199_);
return v_res_201_;
}
}
lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___impl(uint8_t v_x_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_box(v_x_202_);
v___x_204_ = lean_obj_tag_nat(v___x_203_);
lean_dec(v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_202_ = stack[0].m_num;
lean_object* v_res_205_;
v_res_205_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___impl(v_x_202_);
stack->m_obj
 = v_res_205_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___impl___boxed(lean_object* v_x_206_){
_start:
{
uint8_t v_x_4__boxed_207_; lean_object* v_res_208_; 
v_x_4__boxed_207_ = lean_unbox(v_x_206_);
v_res_208_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___impl(v_x_4__boxed_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(lean_object* v_k_209_){
_start:
{
lean_inc(v_k_209_);
return v_k_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg___boxed(lean_object* v_k_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(v_k_210_);
lean_dec(v_k_210_);
return v_res_211_;
}
}
lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(lean_object* v_motive_212_, lean_object* v_ctorIdx_213_, uint8_t v_t_214_, lean_object* v_h_215_, lean_object* v_k_216_){
_start:
{
lean_inc(v_k_216_);
return v_k_216_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_213_ = stack[1].m_obj;
uint8_t v_t_214_ = stack[2].m_num;
lean_object* v_k_216_ = stack[4].m_obj;
lean_object* v_res_217_;
v_res_217_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(lean_box(0), v_ctorIdx_213_, v_t_214_, lean_box(0), v_k_216_);
stack->m_obj
 = v_res_217_;
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
lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(lean_object* v_motive_228_, uint8_t v_t_229_, lean_object* v_h_230_, lean_object* v_pipeArg_231_){
_start:
{
lean_inc(v_pipeArg_231_);
return v_pipeArg_231_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_229_ = stack[1].m_num;
lean_object* v_pipeArg_231_ = stack[3].m_obj;
lean_object* v_res_232_;
v_res_232_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(lean_box(0), v_t_229_, lean_box(0), v_pipeArg_231_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___boxed(lean_object* v_motive_233_, lean_object* v_t_234_, lean_object* v_h_235_, lean_object* v_pipeArg_236_){
_start:
{
uint8_t v_t_boxed_237_; lean_object* v_res_238_; 
v_t_boxed_237_ = lean_unbox(v_t_234_);
v_res_238_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(v_motive_233_, v_t_boxed_237_, v_h_235_, v_pipeArg_236_);
lean_dec(v_pipeArg_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(lean_object* v_termArg_239_){
_start:
{
lean_inc(v_termArg_239_);
return v_termArg_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg___boxed(lean_object* v_termArg_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(v_termArg_240_);
lean_dec(v_termArg_240_);
return v_res_241_;
}
}
lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(lean_object* v_motive_242_, uint8_t v_t_243_, lean_object* v_h_244_, lean_object* v_termArg_245_){
_start:
{
lean_inc(v_termArg_245_);
return v_termArg_245_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_243_ = stack[1].m_num;
lean_object* v_termArg_245_ = stack[3].m_obj;
lean_object* v_res_246_;
v_res_246_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(lean_box(0), v_t_243_, lean_box(0), v_termArg_245_);
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___boxed(lean_object* v_motive_247_, lean_object* v_t_248_, lean_object* v_h_249_, lean_object* v_termArg_250_){
_start:
{
uint8_t v_t_boxed_251_; lean_object* v_res_252_; 
v_t_boxed_251_ = lean_unbox(v_t_248_);
v_res_252_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(v_motive_247_, v_t_boxed_251_, v_h_249_, v_termArg_250_);
lean_dec(v_termArg_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(lean_object* v_appArg_253_){
_start:
{
lean_inc(v_appArg_253_);
return v_appArg_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg___boxed(lean_object* v_appArg_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(v_appArg_254_);
lean_dec(v_appArg_254_);
return v_res_255_;
}
}
lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(lean_object* v_motive_256_, uint8_t v_t_257_, lean_object* v_h_258_, lean_object* v_appArg_259_){
_start:
{
lean_inc(v_appArg_259_);
return v_appArg_259_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_257_ = stack[1].m_num;
lean_object* v_appArg_259_ = stack[3].m_obj;
lean_object* v_res_260_;
v_res_260_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(lean_box(0), v_t_257_, lean_box(0), v_appArg_259_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___boxed(lean_object* v_motive_261_, lean_object* v_t_262_, lean_object* v_h_263_, lean_object* v_appArg_264_){
_start:
{
uint8_t v_t_boxed_265_; lean_object* v_res_266_; 
v_t_boxed_265_ = lean_unbox(v_t_262_);
v_res_266_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(v_motive_261_, v_t_boxed_265_, v_h_263_, v_appArg_264_);
lean_dec(v_appArg_264_);
return v_res_266_;
}
}
lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(uint8_t v_x_267_){
_start:
{
switch(v_x_267_)
{
case 0:
{
lean_object* v___x_268_; 
v___x_268_ = lean_unsigned_to_nat(0u);
return v___x_268_;
}
case 1:
{
lean_object* v___x_269_; 
v___x_269_ = lean_unsigned_to_nat(1u);
return v___x_269_;
}
default: 
{
lean_object* v___x_270_; 
v___x_270_ = lean_unsigned_to_nat(2u);
return v___x_270_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_267_ = stack[0].m_num;
lean_object* v_res_271_;
v_res_271_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_x_267_);
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio___boxed(lean_object* v_x_272_){
_start:
{
uint8_t v_x_34__boxed_273_; lean_object* v_res_274_; 
v_x_34__boxed_273_ = lean_unbox(v_x_272_);
v_res_274_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_x_34__boxed_273_);
return v_res_274_;
}
}
lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___impl(uint8_t v_x_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_box(v_x_275_);
v___x_277_ = lean_obj_tag_nat(v___x_276_);
lean_dec(v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_275_ = stack[0].m_num;
lean_object* v_res_278_;
v_res_278_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___impl(v_x_275_);
stack->m_obj
 = v_res_278_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___impl___boxed(lean_object* v_x_279_){
_start:
{
uint8_t v_x_4__boxed_280_; lean_object* v_res_281_; 
v_x_4__boxed_280_ = lean_unbox(v_x_279_);
v_res_281_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___impl(v_x_4__boxed_280_);
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
lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(lean_object* v_motive_285_, lean_object* v_ctorIdx_286_, uint8_t v_t_287_, lean_object* v_h_288_, lean_object* v_k_289_){
_start:
{
lean_inc(v_k_289_);
return v_k_289_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_286_ = stack[1].m_obj;
uint8_t v_t_287_ = stack[2].m_num;
lean_object* v_k_289_ = stack[4].m_obj;
lean_object* v_res_290_;
v_res_290_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(lean_box(0), v_ctorIdx_286_, v_t_287_, lean_box(0), v_k_289_);
stack->m_obj
 = v_res_290_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___boxed(lean_object* v_motive_291_, lean_object* v_ctorIdx_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_k_295_){
_start:
{
uint8_t v_t_boxed_296_; lean_object* v_res_297_; 
v_t_boxed_296_ = lean_unbox(v_t_293_);
v_res_297_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(v_motive_291_, v_ctorIdx_292_, v_t_boxed_296_, v_h_294_, v_k_295_);
lean_dec(v_k_295_);
lean_dec(v_ctorIdx_292_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(lean_object* v_continue_298_){
_start:
{
lean_inc(v_continue_298_);
return v_continue_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg___boxed(lean_object* v_continue_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(v_continue_299_);
lean_dec(v_continue_299_);
return v_res_300_;
}
}
lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(lean_object* v_motive_301_, uint8_t v_t_302_, lean_object* v_h_303_, lean_object* v_continue_304_){
_start:
{
lean_inc(v_continue_304_);
return v_continue_304_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_302_ = stack[1].m_num;
lean_object* v_continue_304_ = stack[3].m_obj;
lean_object* v_res_305_;
v_res_305_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(lean_box(0), v_t_302_, lean_box(0), v_continue_304_);
stack->m_obj
 = v_res_305_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___boxed(lean_object* v_motive_306_, lean_object* v_t_307_, lean_object* v_h_308_, lean_object* v_continue_309_){
_start:
{
uint8_t v_t_boxed_310_; lean_object* v_res_311_; 
v_t_boxed_310_ = lean_unbox(v_t_307_);
v_res_311_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(v_motive_306_, v_t_boxed_310_, v_h_308_, v_continue_309_);
lean_dec(v_continue_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(lean_object* v_stop_312_){
_start:
{
lean_inc(v_stop_312_);
return v_stop_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg___boxed(lean_object* v_stop_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(v_stop_313_);
lean_dec(v_stop_313_);
return v_res_314_;
}
}
lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(lean_object* v_motive_315_, uint8_t v_t_316_, lean_object* v_h_317_, lean_object* v_stop_318_){
_start:
{
lean_inc(v_stop_318_);
return v_stop_318_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_316_ = stack[1].m_num;
lean_object* v_stop_318_ = stack[3].m_obj;
lean_object* v_res_319_;
v_res_319_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(lean_box(0), v_t_316_, lean_box(0), v_stop_318_);
stack->m_obj
 = v_res_319_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___boxed(lean_object* v_motive_320_, lean_object* v_t_321_, lean_object* v_h_322_, lean_object* v_stop_323_){
_start:
{
uint8_t v_t_boxed_324_; lean_object* v_res_325_; 
v_t_boxed_324_ = lean_unbox(v_t_321_);
v_res_325_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(v_motive_320_, v_t_boxed_324_, v_h_322_, v_stop_323_);
lean_dec(v_stop_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(lean_object* v_s_326_, lean_object* v___x_327_, lean_object* v___x_328_, lean_object* v_a_329_, lean_object* v_b_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = lean_box(0);
switch(lean_obj_tag(v_a_329_))
{
case 0:
{
lean_object* v_pos_332_; lean_object* v___x_333_; 
v_pos_332_ = lean_ctor_get(v_a_329_, 0);
lean_inc(v_pos_332_);
lean_dec_ref_known(v_a_329_, 1);
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v_pos_332_);
return v___x_333_;
}
case 1:
{
lean_object* v_pos_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_343_; 
v_pos_334_ = lean_ctor_get(v_a_329_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v_a_329_);
if (v_isSharedCheck_343_ == 0)
{
v___x_336_ = v_a_329_;
v_isShared_337_ = v_isSharedCheck_343_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_pos_334_);
lean_dec(v_a_329_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_343_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_string_utf8_next_fast(v_s_326_, v_pos_334_);
lean_dec(v_pos_334_);
if (v_isShared_337_ == 0)
{
lean_ctor_set_tag(v___x_336_, 0);
lean_ctor_set(v___x_336_, 0, v___x_338_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_342_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
v_a_329_ = v___x_340_;
v_b_330_ = v___x_331_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_344_; lean_object* v_table_345_; lean_object* v_stackPos_346_; lean_object* v_needlePos_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_400_; 
v_needle_344_ = lean_ctor_get(v_a_329_, 0);
v_table_345_ = lean_ctor_get(v_a_329_, 1);
v_stackPos_346_ = lean_ctor_get(v_a_329_, 2);
v_needlePos_347_ = lean_ctor_get(v_a_329_, 3);
v_isSharedCheck_400_ = !lean_is_exclusive(v_a_329_);
if (v_isSharedCheck_400_ == 0)
{
v___x_349_ = v_a_329_;
v_isShared_350_ = v_isSharedCheck_400_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_needlePos_347_);
lean_inc(v_stackPos_346_);
lean_inc(v_table_345_);
lean_inc(v_needle_344_);
lean_dec(v_a_329_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_400_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v_str_351_; lean_object* v_startInclusive_352_; lean_object* v_endExclusive_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_str_351_ = lean_ctor_get(v_needle_344_, 0);
v_startInclusive_352_ = lean_ctor_get(v_needle_344_, 1);
v_endExclusive_353_ = lean_ctor_get(v_needle_344_, 2);
v___x_354_ = lean_nat_sub(v_stackPos_346_, v_needlePos_347_);
v___x_355_ = lean_nat_sub(v_endExclusive_353_, v_startInclusive_352_);
v___x_356_ = lean_nat_add(v___x_354_, v___x_355_);
v___x_357_ = lean_nat_dec_le(v___x_356_, v___x_328_);
lean_dec(v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
lean_dec(v___x_355_);
lean_del_object(v___x_349_);
lean_dec(v_needlePos_347_);
lean_dec(v_stackPos_346_);
lean_dec_ref(v_table_345_);
lean_dec_ref(v_needle_344_);
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_add(v___x_354_, v___x_358_);
lean_dec(v___x_354_);
v___x_360_ = lean_nat_dec_le(v___x_359_, v___x_328_);
lean_dec(v___x_359_);
if (v___x_360_ == 0)
{
lean_inc(v_b_330_);
return v_b_330_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = lean_box(3);
v_a_329_ = v___x_361_;
v_b_330_ = v___x_331_;
goto _start;
}
}
else
{
uint8_t v_stackByte_363_; lean_object* v___x_364_; uint8_t v_patByte_365_; uint8_t v___x_366_; 
lean_dec(v___x_354_);
lean_inc(v_stackPos_346_);
v_stackByte_363_ = lean_string_get_byte_fast(v_s_326_, v_stackPos_346_);
v___x_364_ = lean_nat_add(v_startInclusive_352_, v_needlePos_347_);
v_patByte_365_ = lean_string_get_byte_fast(v_str_351_, v___x_364_);
v___x_366_ = lean_uint8_dec_eq(v_stackByte_363_, v_patByte_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; uint8_t v_decide_368_; 
lean_dec(v___x_355_);
v___x_367_ = lean_unsigned_to_nat(0u);
v_decide_368_ = lean_nat_dec_eq(v_needlePos_347_, v___x_367_);
if (v_decide_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_newNeedlePos_371_; uint8_t v___x_372_; 
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_sub(v_needlePos_347_, v___x_369_);
lean_dec(v_needlePos_347_);
v_newNeedlePos_371_ = lean_array_fget_borrowed(v_table_345_, v___x_370_);
lean_dec(v___x_370_);
v___x_372_ = lean_nat_dec_eq(v_newNeedlePos_371_, v___x_367_);
if (v___x_372_ == 0)
{
lean_object* v___x_374_; 
lean_inc(v_newNeedlePos_371_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 3, v_newNeedlePos_371_);
v___x_374_ = v___x_349_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_needle_344_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_table_345_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_stackPos_346_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v_newNeedlePos_371_);
v___x_374_ = v_reuseFailAlloc_376_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
v_a_329_ = v___x_374_;
v_b_330_ = v___x_331_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_377_; lean_object* v___x_379_; 
v_nextStackPos_377_ = l_String_Slice_posGE___redArg(v___x_327_, v_stackPos_346_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 3, v___x_367_);
lean_ctor_set(v___x_349_, 2, v_nextStackPos_377_);
v___x_379_ = v___x_349_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_needle_344_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_table_345_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_nextStackPos_377_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v___x_367_);
v___x_379_ = v_reuseFailAlloc_381_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
v_a_329_ = v___x_379_;
v_b_330_ = v___x_331_;
goto _start;
}
}
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_nextStackPos_384_; lean_object* v___x_386_; 
lean_dec(v_needlePos_347_);
v___x_382_ = lean_unsigned_to_nat(1u);
v___x_383_ = lean_nat_add(v_stackPos_346_, v___x_382_);
lean_dec(v_stackPos_346_);
v_nextStackPos_384_ = l_String_Slice_posGE___redArg(v___x_327_, v___x_383_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 3, v___x_367_);
lean_ctor_set(v___x_349_, 2, v_nextStackPos_384_);
v___x_386_ = v___x_349_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_needle_344_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_table_345_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_nextStackPos_384_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v___x_367_);
v___x_386_ = v_reuseFailAlloc_388_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
v_a_329_ = v___x_386_;
v_b_330_ = v___x_331_;
goto _start;
}
}
}
else
{
lean_object* v___x_389_; lean_object* v_nextStackPos_390_; lean_object* v_nextNeedlePos_391_; uint8_t v_decide_392_; 
v___x_389_ = lean_unsigned_to_nat(1u);
v_nextStackPos_390_ = lean_nat_add(v_stackPos_346_, v___x_389_);
lean_dec(v_stackPos_346_);
v_nextNeedlePos_391_ = lean_nat_add(v_needlePos_347_, v___x_389_);
lean_dec(v_needlePos_347_);
v_decide_392_ = lean_nat_dec_eq(v_nextNeedlePos_391_, v___x_355_);
lean_dec(v___x_355_);
if (v_decide_392_ == 0)
{
lean_object* v___x_394_; 
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 3, v_nextNeedlePos_391_);
lean_ctor_set(v___x_349_, 2, v_nextStackPos_390_);
v___x_394_ = v___x_349_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_needle_344_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_table_345_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_nextStackPos_390_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_nextNeedlePos_391_);
v___x_394_ = v_reuseFailAlloc_396_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
v_a_329_ = v___x_394_;
goto _start;
}
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_del_object(v___x_349_);
lean_dec_ref(v_table_345_);
lean_dec_ref(v_needle_344_);
v___x_397_ = lean_nat_sub(v_nextStackPos_390_, v_nextNeedlePos_391_);
lean_dec(v_nextNeedlePos_391_);
lean_dec(v_nextStackPos_390_);
v___x_398_ = l_String_Slice_pos_x21(v___x_327_, v___x_397_);
lean_dec(v___x_397_);
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
}
}
}
default: 
{
lean_inc(v_b_330_);
return v_b_330_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg___boxed(lean_object* v_s_401_, lean_object* v___x_402_, lean_object* v___x_403_, lean_object* v_a_404_, lean_object* v_b_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_401_, v___x_402_, v___x_403_, v_a_404_, v_b_405_);
lean_dec(v_b_405_);
lean_dec(v___x_403_);
lean_dec_ref(v___x_402_);
lean_dec_ref(v_s_401_);
return v_res_406_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1));
v___x_413_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2);
v___x_416_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1));
v___x_417_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_415_);
lean_ctor_set(v___x_417_, 2, v___x_414_);
lean_ctor_set(v___x_417_, 3, v___x_414_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(lean_object* v_s_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_string_utf8_byte_size(v_s_418_);
lean_inc_ref(v_s_418_);
v___x_421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_421_, 0, v_s_418_);
lean_ctor_set(v___x_421_, 1, v___x_419_);
lean_ctor_set(v___x_421_, 2, v___x_420_);
v___x_422_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3);
v___x_423_ = lean_box(0);
v___x_424_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_418_, v___x_421_, v___x_420_, v___x_422_, v___x_423_);
lean_dec_ref_known(v___x_421_, 3);
lean_dec_ref(v_s_418_);
if (lean_obj_tag(v___x_424_) == 0)
{
return v___x_423_;
}
else
{
lean_object* v_val_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
v_val_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_val_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_val_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(lean_object* v_s_433_, lean_object* v___x_434_, lean_object* v___x_435_, lean_object* v_inst_436_, lean_object* v_R_437_, lean_object* v_a_438_, lean_object* v_b_439_, lean_object* v_c_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_433_, v___x_434_, v___x_435_, v_a_438_, v_b_439_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___boxed(lean_object* v_s_442_, lean_object* v___x_443_, lean_object* v___x_444_, lean_object* v_inst_445_, lean_object* v_R_446_, lean_object* v_a_447_, lean_object* v_b_448_, lean_object* v_c_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(v_s_442_, v___x_443_, v___x_444_, v_inst_445_, v_R_446_, v_a_447_, v_b_448_, v_c_449_);
lean_dec(v_b_448_);
lean_dec(v___x_444_);
lean_dec_ref(v___x_443_);
lean_dec_ref(v_s_442_);
return v_res_450_;
}
}
uint8_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(lean_object* v_text_451_, lean_object* v_pos_452_){
_start:
{
lean_object* v___x_453_; lean_object* v_line_454_; lean_object* v_source_455_; lean_object* v_lineStartPos_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v_lineEndPos_459_; lean_object* v_line_460_; lean_object* v___x_461_; 
lean_inc_ref(v_text_451_);
v___x_453_ = l_Lean_FileMap_toPosition(v_text_451_, v_pos_452_);
v_line_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_line_454_);
lean_dec_ref(v___x_453_);
v_source_455_ = lean_ctor_get(v_text_451_, 0);
lean_inc_ref(v_source_455_);
v_lineStartPos_456_ = l_Lean_FileMap_lineStart(v_text_451_, v_line_454_);
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v_line_454_, v___x_457_);
lean_dec(v_line_454_);
v_lineEndPos_459_ = l_Lean_FileMap_lineStart(v_text_451_, v___x_458_);
lean_dec(v___x_458_);
lean_dec_ref(v_text_451_);
v_line_460_ = lean_string_utf8_extract(v_source_455_, v_lineStartPos_456_, v_lineEndPos_459_);
lean_dec(v_lineEndPos_459_);
lean_dec_ref(v_source_455_);
v___x_461_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(v_line_460_);
if (lean_obj_tag(v___x_461_) == 1)
{
lean_object* v_val_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v_val_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_val_462_);
lean_dec_ref_known(v___x_461_, 1);
v___x_463_ = lean_nat_add(v_lineStartPos_456_, v_val_462_);
lean_dec(v_val_462_);
lean_dec(v_lineStartPos_456_);
v___x_464_ = lean_nat_dec_le(v___x_463_, v_pos_452_);
lean_dec(v___x_463_);
return v___x_464_;
}
else
{
uint8_t v___x_465_; 
lean_dec(v___x_461_);
lean_dec(v_lineStartPos_456_);
v___x_465_ = 0;
return v___x_465_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_451_ = stack[0].m_obj;
lean_object* v_pos_452_ = stack[1].m_obj;
uint8_t v_res_466_;
v_res_466_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_451_, v_pos_452_);
stack->m_num = v_res_466_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment___boxed(lean_object* v_text_467_, lean_object* v_pos_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_467_, v_pos_468_);
lean_dec(v_pos_468_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(lean_object* v_text_527_, lean_object* v_ctx_x3f_528_, lean_object* v_requestedPos_529_, lean_object* v_stx_530_, lean_object* v_parent_531_){
_start:
{
lean_object* v_kind_x3f_533_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; uint8_t v___y_558_; uint8_t v___x_641_; lean_object* v___x_642_; 
v___x_641_ = 1;
v___x_642_ = l_Lean_Syntax_getTailPos_x3f(v_stx_530_, v___x_641_);
if (lean_obj_tag(v___x_642_) == 1)
{
lean_object* v_val_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; uint8_t v___y_648_; uint8_t v___y_649_; uint8_t v___y_651_; uint8_t v___y_652_; uint8_t v___y_654_; uint8_t v___y_655_; uint8_t v___y_656_; uint8_t v___y_658_; uint8_t v___y_659_; uint8_t v___y_666_; 
v_val_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_val_643_);
lean_dec_ref_known(v___x_642_, 1);
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_add(v_requestedPos_529_, v___x_644_);
v___x_646_ = lean_nat_dec_le(v___x_645_, v_val_643_);
lean_dec(v___x_645_);
if (v___x_646_ == 0)
{
if (lean_obj_tag(v_ctx_x3f_528_) == 0)
{
v___y_666_ = v___x_646_;
goto v___jp_665_;
}
else
{
lean_object* v_val_669_; uint8_t v_triggerKind_670_; 
v_val_669_ = lean_ctor_get(v_ctx_x3f_528_, 0);
v_triggerKind_670_ = lean_ctor_get_uint8(v_val_669_, sizeof(void*)*2);
if (v_triggerKind_670_ == 0)
{
v___y_666_ = v___x_641_;
goto v___jp_665_;
}
else
{
v___y_666_ = v___x_646_;
goto v___jp_665_;
}
}
}
else
{
lean_object* v___x_671_; 
lean_dec(v_val_643_);
lean_dec(v_parent_531_);
lean_dec(v_stx_530_);
lean_dec_ref(v_text_527_);
v___x_671_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23));
return v___x_671_;
}
v___jp_647_:
{
if (v___y_649_ == 0)
{
v___y_558_ = v___x_646_;
goto v___jp_557_;
}
else
{
v___y_558_ = v___y_648_;
goto v___jp_557_;
}
}
v___jp_650_:
{
if (v___y_652_ == 0)
{
v___y_558_ = v___y_651_;
goto v___jp_557_;
}
else
{
v___y_648_ = v___y_651_;
v___y_649_ = v___x_646_;
goto v___jp_647_;
}
}
v___jp_653_:
{
if (v___y_655_ == 0)
{
v___y_651_ = v___y_656_;
v___y_652_ = v___y_654_;
goto v___jp_650_;
}
else
{
if (v___x_646_ == 0)
{
v___y_648_ = v___y_656_;
v___y_649_ = v___x_646_;
goto v___jp_647_;
}
else
{
v___y_651_ = v___y_656_;
v___y_652_ = v___y_654_;
goto v___jp_650_;
}
}
}
v___jp_657_:
{
lean_object* v___x_660_; lean_object* v_line_661_; lean_object* v___x_662_; lean_object* v_line_663_; uint8_t v___x_664_; 
lean_inc_ref(v_text_527_);
v___x_660_ = l_Lean_FileMap_toPosition(v_text_527_, v_requestedPos_529_);
v_line_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_line_661_);
lean_dec_ref(v___x_660_);
v___x_662_ = l_Lean_FileMap_toPosition(v_text_527_, v_val_643_);
lean_dec(v_val_643_);
v_line_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_line_663_);
lean_dec_ref(v___x_662_);
v___x_664_ = lean_nat_dec_eq(v_line_661_, v_line_663_);
lean_dec(v_line_663_);
lean_dec(v_line_661_);
if (v___x_664_ == 0)
{
v___y_654_ = v___y_659_;
v___y_655_ = v___y_658_;
v___y_656_ = v___x_641_;
goto v___jp_653_;
}
else
{
v___y_654_ = v___y_659_;
v___y_655_ = v___y_658_;
v___y_656_ = v___x_646_;
goto v___jp_653_;
}
}
v___jp_665_:
{
if (lean_obj_tag(v_ctx_x3f_528_) == 0)
{
v___y_658_ = v___y_666_;
v___y_659_ = v___x_646_;
goto v___jp_657_;
}
else
{
lean_object* v_val_667_; uint8_t v_isRetrigger_668_; 
v_val_667_ = lean_ctor_get(v_ctx_x3f_528_, 0);
v_isRetrigger_668_ = lean_ctor_get_uint8(v_val_667_, sizeof(void*)*2 + 1);
v___y_658_ = v___y_666_;
v___y_659_ = v_isRetrigger_668_;
goto v___jp_657_;
}
}
}
else
{
lean_object* v___x_672_; 
lean_dec(v___x_642_);
lean_dec(v_parent_531_);
lean_dec(v_stx_530_);
lean_dec_ref(v_text_527_);
v___x_672_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22));
return v___x_672_;
}
v___jp_532_:
{
uint8_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = 0;
v___x_535_ = lean_box(v___x_534_);
lean_inc(v_kind_x3f_533_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_kind_x3f_533_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
return v___x_536_;
}
v___jp_537_:
{
lean_object* v___x_538_; 
v___x_538_ = lean_box(0);
v_kind_x3f_533_ = v___x_538_;
goto v___jp_532_;
}
v___jp_539_:
{
lean_object* v___x_540_; 
v___x_540_ = lean_box(0);
v_kind_x3f_533_ = v___x_540_;
goto v___jp_532_;
}
v___jp_541_:
{
lean_object* v___x_542_; 
v___x_542_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_533_ = v___x_542_;
goto v___jp_532_;
}
v___jp_543_:
{
lean_object* v___x_544_; 
v___x_544_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_533_ = v___x_544_;
goto v___jp_532_;
}
v___jp_545_:
{
lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_549_ = lean_unsigned_to_nat(3u);
v___x_550_ = l_Lean_Syntax_getArg(v_stx_530_, v___x_549_);
lean_dec(v_stx_530_);
v___x_551_ = l_Lean_Syntax_matchesNull(v___x_550_, v___y_546_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = lean_array_get_size(v___y_547_);
lean_dec_ref(v___y_547_);
v___x_553_ = lean_nat_dec_le(v___x_552_, v___y_548_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
v___x_554_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_533_ = v___x_554_;
goto v___jp_532_;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = lean_box(0);
v_kind_x3f_533_ = v___x_555_;
goto v___jp_532_;
}
}
else
{
lean_object* v___x_556_; 
lean_dec_ref(v___y_547_);
v___x_556_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1));
v_kind_x3f_533_ = v___x_556_;
goto v___jp_532_;
}
}
v___jp_557_:
{
if (v___y_558_ == 0)
{
if (lean_obj_tag(v_stx_530_) == 3)
{
lean_object* v___x_559_; uint8_t v___x_560_; 
lean_dec_ref_known(v_stx_530_, 4);
v___x_559_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6));
lean_inc(v_parent_531_);
v___x_560_ = l_Lean_Syntax_isOfKind(v_parent_531_, v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8));
lean_inc(v_parent_531_);
v___x_562_ = l_Lean_Syntax_isOfKind(v_parent_531_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10));
lean_inc(v_parent_531_);
v___x_564_ = l_Lean_Syntax_isOfKind(v_parent_531_, v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
lean_dec(v_parent_531_);
v___x_565_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_533_ = v___x_565_;
goto v___jp_532_;
}
else
{
if (v___x_562_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = l_Lean_Syntax_getArg(v_parent_531_, v___x_566_);
lean_dec(v_parent_531_);
v___x_568_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_569_ = l_Lean_Syntax_isOfKind(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
v___x_570_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_533_ = v___x_570_;
goto v___jp_532_;
}
else
{
goto v___jp_537_;
}
}
else
{
lean_dec(v_parent_531_);
goto v___jp_537_;
}
}
}
else
{
if (v___x_560_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_571_ = lean_unsigned_to_nat(2u);
v___x_572_ = l_Lean_Syntax_getArg(v_parent_531_, v___x_571_);
lean_dec(v_parent_531_);
v___x_573_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_574_ = l_Lean_Syntax_isOfKind(v___x_572_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
v___x_575_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_533_ = v___x_575_;
goto v___jp_532_;
}
else
{
goto v___jp_539_;
}
}
else
{
lean_dec(v_parent_531_);
goto v___jp_539_;
}
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_576_ = lean_unsigned_to_nat(2u);
v___x_577_ = l_Lean_Syntax_getArg(v_parent_531_, v___x_576_);
v___x_578_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_579_ = l_Lean_Syntax_isOfKind(v___x_577_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
lean_dec(v_parent_531_);
v___x_580_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_533_ = v___x_580_;
goto v___jp_532_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_unsigned_to_nat(3u);
v___x_583_ = l_Lean_Syntax_getArg(v_parent_531_, v___x_582_);
lean_dec(v_parent_531_);
v___x_584_ = l_Lean_Syntax_matchesNull(v___x_583_, v___x_581_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
v___x_585_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_533_ = v___x_585_;
goto v___jp_532_;
}
else
{
lean_object* v___x_586_; 
v___x_586_ = lean_box(0);
v_kind_x3f_533_ = v___x_586_;
goto v___jp_532_;
}
}
}
}
else
{
lean_dec(v_parent_531_);
if (lean_obj_tag(v_stx_530_) == 1)
{
lean_object* v_kind_587_; lean_object* v_args_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v_kind_587_ = lean_ctor_get(v_stx_530_, 1);
v_args_588_ = lean_ctor_get(v_stx_530_, 2);
v___x_589_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14));
v___x_590_ = lean_name_eq(v_kind_587_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16));
v___x_592_ = lean_name_eq(v_kind_587_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18));
lean_inc_ref(v_stx_530_);
v___x_594_ = l_Lean_Syntax_isOfKind(v_stx_530_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20));
lean_inc_ref(v_stx_530_);
v___x_596_ = l_Lean_Syntax_isOfKind(v_stx_530_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6));
lean_inc_ref(v_stx_530_);
v___x_598_ = l_Lean_Syntax_isOfKind(v_stx_530_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; uint8_t v___x_600_; 
lean_inc_ref(v_args_588_);
v___x_599_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10));
lean_inc_ref(v_stx_530_);
v___x_600_ = l_Lean_Syntax_isOfKind(v_stx_530_, v___x_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8));
lean_inc_ref(v_stx_530_);
v___x_602_ = l_Lean_Syntax_isOfKind(v_stx_530_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
lean_dec_ref_known(v_stx_530_, 3);
v___x_603_ = lean_array_get_size(v_args_588_);
lean_dec_ref(v_args_588_);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_dec_le(v___x_603_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; 
v___x_606_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_533_ = v___x_606_;
goto v___jp_532_;
}
else
{
lean_object* v___x_607_; 
v___x_607_ = lean_box(0);
v_kind_x3f_533_ = v___x_607_;
goto v___jp_532_;
}
}
else
{
if (v___x_600_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_608_ = lean_unsigned_to_nat(2u);
v___x_609_ = l_Lean_Syntax_getArg(v_stx_530_, v___x_608_);
lean_dec_ref_known(v_stx_530_, 3);
v___x_610_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_611_ = l_Lean_Syntax_isOfKind(v___x_609_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = lean_array_get_size(v_args_588_);
lean_dec_ref(v_args_588_);
v___x_614_ = lean_nat_dec_le(v___x_613_, v___x_612_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
v___x_615_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_533_ = v___x_615_;
goto v___jp_532_;
}
else
{
lean_object* v___x_616_; 
v___x_616_ = lean_box(0);
v_kind_x3f_533_ = v___x_616_;
goto v___jp_532_;
}
}
else
{
lean_dec_ref(v_args_588_);
goto v___jp_541_;
}
}
else
{
lean_dec_ref(v_args_588_);
lean_dec_ref_known(v_stx_530_, 3);
goto v___jp_541_;
}
}
}
else
{
if (v___x_598_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = l_Lean_Syntax_getArg(v_stx_530_, v___x_617_);
lean_dec_ref_known(v_stx_530_, 3);
v___x_619_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_620_ = l_Lean_Syntax_isOfKind(v___x_618_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = lean_array_get_size(v_args_588_);
lean_dec_ref(v_args_588_);
v___x_622_ = lean_nat_dec_le(v___x_621_, v___x_617_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
v___x_623_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_533_ = v___x_623_;
goto v___jp_532_;
}
else
{
lean_object* v___x_624_; 
v___x_624_ = lean_box(0);
v_kind_x3f_533_ = v___x_624_;
goto v___jp_532_;
}
}
else
{
lean_dec_ref(v_args_588_);
goto v___jp_543_;
}
}
else
{
lean_dec_ref(v_args_588_);
lean_dec_ref_known(v_stx_530_, 3);
goto v___jp_543_;
}
}
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_unsigned_to_nat(1u);
if (v___x_596_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_627_ = lean_unsigned_to_nat(2u);
v___x_628_ = l_Lean_Syntax_getArg(v_stx_530_, v___x_627_);
v___x_629_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_630_ = l_Lean_Syntax_isOfKind(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; uint8_t v___x_632_; 
lean_inc_ref(v_args_588_);
lean_dec_ref_known(v_stx_530_, 3);
v___x_631_ = lean_array_get_size(v_args_588_);
lean_dec_ref(v_args_588_);
v___x_632_ = lean_nat_dec_le(v___x_631_, v___x_626_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
v___x_633_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_533_ = v___x_633_;
goto v___jp_532_;
}
else
{
lean_object* v___x_634_; 
v___x_634_ = lean_box(0);
v_kind_x3f_533_ = v___x_634_;
goto v___jp_532_;
}
}
else
{
lean_inc_ref(v_args_588_);
v___y_546_ = v___x_625_;
v___y_547_ = v_args_588_;
v___y_548_ = v___x_626_;
goto v___jp_545_;
}
}
else
{
lean_inc_ref(v_args_588_);
v___y_546_ = v___x_625_;
v___y_547_ = v_args_588_;
v___y_548_ = v___x_626_;
goto v___jp_545_;
}
}
}
else
{
lean_object* v___x_635_; 
lean_dec_ref_known(v_stx_530_, 3);
v___x_635_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1));
v_kind_x3f_533_ = v___x_635_;
goto v___jp_532_;
}
}
else
{
lean_object* v___x_636_; 
lean_dec_ref_known(v_stx_530_, 3);
v___x_636_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1));
v_kind_x3f_533_ = v___x_636_;
goto v___jp_532_;
}
}
else
{
lean_object* v___x_637_; 
lean_dec_ref_known(v_stx_530_, 3);
v___x_637_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21));
v_kind_x3f_533_ = v___x_637_;
goto v___jp_532_;
}
}
else
{
lean_object* v___x_638_; 
lean_dec_ref_known(v_stx_530_, 3);
v___x_638_ = lean_box(0);
v_kind_x3f_533_ = v___x_638_;
goto v___jp_532_;
}
}
else
{
lean_object* v___x_639_; 
lean_dec(v_stx_530_);
v___x_639_ = lean_box(0);
v_kind_x3f_533_ = v___x_639_;
goto v___jp_532_;
}
}
}
else
{
lean_object* v___x_640_; 
lean_dec(v_parent_531_);
lean_dec(v_stx_530_);
v___x_640_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22));
return v___x_640_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___boxed(lean_object* v_text_673_, lean_object* v_ctx_x3f_674_, lean_object* v_requestedPos_675_, lean_object* v_stx_676_, lean_object* v_parent_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_673_, v_ctx_x3f_674_, v_requestedPos_675_, v_stx_676_, v_parent_677_);
lean_dec(v_requestedPos_675_);
lean_dec(v_ctx_x3f_674_);
return v_res_678_;
}
}
uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(uint8_t v___x_679_, lean_object* v_stx_680_){
_start:
{
uint8_t v___x_681_; 
v___x_681_ = l_Lean_Syntax_hasArgs(v_stx_680_);
if (v___x_681_ == 0)
{
uint8_t v___x_682_; 
v___x_682_ = 1;
return v___x_682_;
}
else
{
return v___x_679_;
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_679_ = stack[0].m_num;
lean_object* v_stx_680_ = stack[1].m_obj;
uint8_t v_res_683_;
v_res_683_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(v___x_679_, v_stx_680_);
stack->m_num = v_res_683_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed(lean_object* v___x_684_, lean_object* v_stx_685_){
_start:
{
uint8_t v___x_2727__boxed_686_; uint8_t v_res_687_; lean_object* v_r_688_; 
v___x_2727__boxed_686_ = lean_unbox(v___x_684_);
v_res_687_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(v___x_2727__boxed_686_, v_stx_685_);
lean_dec(v_stx_685_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(uint8_t v___x_689_, lean_object* v_requestedPos_690_, uint8_t v___x_691_, lean_object* v_stx_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_692_, v___x_689_);
if (lean_obj_tag(v___x_693_) == 1)
{
lean_object* v_val_694_; uint8_t v___x_695_; 
v_val_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_val_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = l_Lean_Syntax_Range_contains(v_val_694_, v_requestedPos_690_, v___x_689_);
lean_dec(v_val_694_);
return v___x_695_;
}
else
{
lean_dec(v___x_693_);
return v___x_691_;
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_689_ = stack[0].m_num;
lean_object* v_requestedPos_690_ = stack[1].m_obj;
uint8_t v___x_691_ = stack[2].m_num;
lean_object* v_stx_692_ = stack[3].m_obj;
uint8_t v_res_696_;
v_res_696_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(v___x_689_, v_requestedPos_690_, v___x_691_, v_stx_692_);
stack->m_num = v_res_696_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed(lean_object* v___x_697_, lean_object* v_requestedPos_698_, lean_object* v___x_699_, lean_object* v_stx_700_){
_start:
{
uint8_t v___x_2738__boxed_701_; uint8_t v___x_2739__boxed_702_; uint8_t v_res_703_; lean_object* v_r_704_; 
v___x_2738__boxed_701_ = lean_unbox(v___x_697_);
v___x_2739__boxed_702_ = lean_unbox(v___x_699_);
v_res_703_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(v___x_2738__boxed_701_, v_requestedPos_698_, v___x_2739__boxed_702_, v_stx_700_);
lean_dec(v_stx_700_);
lean_dec(v_requestedPos_698_);
v_r_704_ = lean_box(v_res_703_);
return v_r_704_;
}
}
uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(lean_object* v_c1_705_, lean_object* v_c2_706_){
_start:
{
uint8_t v_kind_707_; uint8_t v_kind_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_kind_707_ = lean_ctor_get_uint8(v_c2_706_, sizeof(void*)*1);
v_kind_708_ = lean_ctor_get_uint8(v_c1_705_, sizeof(void*)*1);
v___x_709_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_707_);
v___x_710_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_708_);
v___x_711_ = lean_nat_dec_le(v___x_709_, v___x_710_);
lean_dec(v___x_710_);
lean_dec(v___x_709_);
return v___x_711_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_c1_705_ = stack[0].m_obj;
lean_object* v_c2_706_ = stack[1].m_obj;
uint8_t v_res_712_;
v_res_712_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(v_c1_705_, v_c2_706_);
stack->m_num = v_res_712_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2___boxed(lean_object* v_c1_713_, lean_object* v_c2_714_){
_start:
{
uint8_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(v_c1_713_, v_c2_714_);
lean_dec_ref(v_c2_714_);
lean_dec_ref(v_c1_713_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(size_t v_sz_717_, size_t v_i_718_, lean_object* v_bs_719_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = lean_usize_dec_lt(v_i_718_, v_sz_717_);
if (v___x_720_ == 0)
{
return v_bs_719_;
}
else
{
lean_object* v_v_721_; lean_object* v_fst_722_; lean_object* v___x_723_; lean_object* v_bs_x27_724_; size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
v_v_721_ = lean_array_uget_borrowed(v_bs_719_, v_i_718_);
v_fst_722_ = lean_ctor_get(v_v_721_, 0);
lean_inc(v_fst_722_);
v___x_723_ = lean_unsigned_to_nat(0u);
v_bs_x27_724_ = lean_array_uset(v_bs_719_, v_i_718_, v___x_723_);
v___x_725_ = ((size_t)1ULL);
v___x_726_ = lean_usize_add(v_i_718_, v___x_725_);
v___x_727_ = lean_array_uset(v_bs_x27_724_, v_i_718_, v_fst_722_);
v_i_718_ = v___x_726_;
v_bs_719_ = v___x_727_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_717_ = stack[0].m_num;
size_t v_i_718_ = stack[1].m_num;
lean_object* v_bs_719_ = stack[2].m_obj;
lean_object* v_res_729_;
v_res_729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v_sz_717_, v_i_718_, v_bs_719_);
stack->m_obj
 = v_res_729_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___boxed(lean_object* v_sz_730_, lean_object* v_i_731_, lean_object* v_bs_732_){
_start:
{
size_t v_sz_boxed_733_; size_t v_i_boxed_734_; lean_object* v_res_735_; 
v_sz_boxed_733_ = lean_unbox_usize(v_sz_730_);
lean_dec(v_sz_730_);
v_i_boxed_734_ = lean_unbox_usize(v_i_731_);
lean_dec(v_i_731_);
v_res_735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v_sz_boxed_733_, v_i_boxed_734_, v_bs_732_);
return v_res_735_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0(lean_object* v_tree_744_, uint8_t v___y_745_, uint8_t v___x_746_, lean_object* v_as_747_, size_t v_sz_748_, size_t v_i_749_, lean_object* v_b_750_){
_start:
{
uint8_t v___x_752_; 
v___x_752_ = lean_usize_dec_lt(v_i_749_, v_sz_748_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
lean_dec_ref(v_tree_744_);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v_b_750_);
return v___x_753_;
}
else
{
lean_object* v_a_754_; uint8_t v_kind_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___y_783_; 
lean_dec_ref(v_b_750_);
v_a_754_ = lean_array_uget_borrowed(v_as_747_, v_i_749_);
v_kind_755_ = lean_ctor_get_uint8(v_a_754_, sizeof(void*)*1);
v___x_756_ = lean_box(0);
v___x_757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__0));
if (v_kind_755_ == 1)
{
v___y_783_ = v___y_745_;
goto v___jp_782_;
}
else
{
if (v___x_746_ == 0)
{
goto v___jp_758_;
}
else
{
v___y_783_ = v___y_745_;
goto v___jp_782_;
}
}
v___jp_758_:
{
lean_object* v_appStx_759_; lean_object* v___x_760_; 
v_appStx_759_ = lean_ctor_get(v_a_754_, 0);
lean_inc(v_appStx_759_);
lean_inc_ref(v_tree_744_);
v___x_760_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_744_, v_appStx_759_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_773_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_773_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
if (lean_obj_tag(v_a_761_) == 1)
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
lean_dec_ref(v_tree_744_);
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v_a_761_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v___x_756_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_766_);
v___x_768_ = v___x_763_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
else
{
size_t v___x_770_; size_t v___x_771_; 
lean_del_object(v___x_763_);
lean_dec(v_a_761_);
v___x_770_ = ((size_t)1ULL);
v___x_771_ = lean_usize_add(v_i_749_, v___x_770_);
v_i_749_ = v___x_771_;
v_b_750_ = v___x_757_;
goto _start;
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v_tree_744_);
v_a_774_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_760_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_760_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
v___jp_782_:
{
if (v___y_783_ == 0)
{
goto v___jp_758_;
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; 
lean_dec_ref(v_tree_744_);
v___x_784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__2));
v___x_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
return v___x_785_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tree_744_ = stack[0].m_obj;
uint8_t v___y_745_ = stack[1].m_num;
uint8_t v___x_746_ = stack[2].m_num;
lean_object* v_as_747_ = stack[3].m_obj;
size_t v_sz_748_ = stack[4].m_num;
size_t v_i_749_ = stack[5].m_num;
lean_object* v_b_750_ = stack[6].m_obj;
lean_object* v_res_786_;
v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0(v_tree_744_, v___y_745_, v___x_746_, v_as_747_, v_sz_748_, v_i_749_, v_b_750_);
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___boxed(lean_object* v_tree_787_, lean_object* v___y_788_, lean_object* v___x_789_, lean_object* v_as_790_, lean_object* v_sz_791_, lean_object* v_i_792_, lean_object* v_b_793_, lean_object* v___y_794_){
_start:
{
uint8_t v___y_2800__boxed_795_; uint8_t v___x_2801__boxed_796_; size_t v_sz_boxed_797_; size_t v_i_boxed_798_; lean_object* v_res_799_; 
v___y_2800__boxed_795_ = lean_unbox(v___y_788_);
v___x_2801__boxed_796_ = lean_unbox(v___x_789_);
v_sz_boxed_797_ = lean_unbox_usize(v_sz_791_);
lean_dec(v_sz_791_);
v_i_boxed_798_ = lean_unbox_usize(v_i_792_);
lean_dec(v_i_792_);
v_res_799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0(v_tree_787_, v___y_2800__boxed_795_, v___x_2801__boxed_796_, v_as_790_, v_sz_boxed_797_, v_i_boxed_798_, v_b_793_);
lean_dec_ref(v_as_790_);
return v_res_799_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(lean_object* v_tree_800_, uint8_t v___y_801_, uint8_t v___x_802_, lean_object* v_as_803_, size_t v_sz_804_, size_t v_i_805_, lean_object* v_b_806_){
_start:
{
uint8_t v___x_808_; 
v___x_808_ = lean_usize_dec_lt(v_i_805_, v_sz_804_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec_ref(v_tree_800_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v_b_806_);
return v___x_809_;
}
else
{
lean_object* v_a_810_; uint8_t v_kind_811_; lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___y_839_; 
lean_dec_ref(v_b_806_);
v_a_810_ = lean_array_uget_borrowed(v_as_803_, v_i_805_);
v_kind_811_ = lean_ctor_get_uint8(v_a_810_, sizeof(void*)*1);
v___x_812_ = lean_box(0);
v___x_813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__0));
if (v_kind_811_ == 1)
{
v___y_839_ = v___y_801_;
goto v___jp_838_;
}
else
{
if (v___x_802_ == 0)
{
goto v___jp_814_;
}
else
{
v___y_839_ = v___y_801_;
goto v___jp_838_;
}
}
v___jp_814_:
{
lean_object* v_appStx_815_; lean_object* v___x_816_; 
v_appStx_815_ = lean_ctor_get(v_a_810_, 0);
lean_inc(v_appStx_815_);
lean_inc_ref(v_tree_800_);
v___x_816_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_800_, v_appStx_815_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_829_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_829_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_829_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_829_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
if (lean_obj_tag(v_a_817_) == 1)
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
lean_dec_ref(v_tree_800_);
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v_a_817_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___x_812_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_822_);
v___x_824_ = v___x_819_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
else
{
size_t v___x_826_; size_t v___x_827_; lean_object* v___x_828_; 
lean_del_object(v___x_819_);
lean_dec(v_a_817_);
v___x_826_ = ((size_t)1ULL);
v___x_827_ = lean_usize_add(v_i_805_, v___x_826_);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0(v_tree_800_, v___y_801_, v___x_802_, v_as_803_, v_sz_804_, v___x_827_, v___x_813_);
return v___x_828_;
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v_tree_800_);
v_a_830_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_816_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_816_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
v___jp_838_:
{
if (v___y_839_ == 0)
{
goto v___jp_814_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec_ref(v_tree_800_);
v___x_840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__2));
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tree_800_ = stack[0].m_obj;
uint8_t v___y_801_ = stack[1].m_num;
uint8_t v___x_802_ = stack[2].m_num;
lean_object* v_as_803_ = stack[3].m_obj;
size_t v_sz_804_ = stack[4].m_num;
size_t v_i_805_ = stack[5].m_num;
lean_object* v_b_806_ = stack[6].m_obj;
lean_object* v_res_842_;
v_res_842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_tree_800_, v___y_801_, v___x_802_, v_as_803_, v_sz_804_, v_i_805_, v_b_806_);
stack->m_obj
 = v_res_842_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0___boxed(lean_object* v_tree_843_, lean_object* v___y_844_, lean_object* v___x_845_, lean_object* v_as_846_, lean_object* v_sz_847_, lean_object* v_i_848_, lean_object* v_b_849_, lean_object* v___y_850_){
_start:
{
uint8_t v___y_2933__boxed_851_; uint8_t v___x_2934__boxed_852_; size_t v_sz_boxed_853_; size_t v_i_boxed_854_; lean_object* v_res_855_; 
v___y_2933__boxed_851_ = lean_unbox(v___y_844_);
v___x_2934__boxed_852_ = lean_unbox(v___x_845_);
v_sz_boxed_853_ = lean_unbox_usize(v_sz_847_);
lean_dec(v_sz_847_);
v_i_boxed_854_ = lean_unbox_usize(v_i_848_);
lean_dec(v_i_848_);
v_res_855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_tree_843_, v___y_2933__boxed_851_, v___x_2934__boxed_852_, v_as_846_, v_sz_boxed_853_, v_i_boxed_854_, v_b_849_);
lean_dec_ref(v_as_846_);
return v_res_855_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0(void){
_start:
{
uint8_t v___x_856_; lean_object* v___x_857_; 
v___x_856_ = 1;
v___x_857_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v___x_856_);
return v___x_857_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(lean_object* v_as_858_, size_t v_i_859_, size_t v_stop_860_){
_start:
{
uint8_t v___x_861_; 
v___x_861_ = lean_usize_dec_eq(v_i_859_, v_stop_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; uint8_t v_kind_863_; lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_862_ = lean_array_uget_borrowed(v_as_858_, v_i_859_);
v_kind_863_ = lean_ctor_get_uint8(v___x_862_, sizeof(void*)*1);
v___x_864_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0);
v___x_865_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_863_);
v___x_866_ = lean_nat_dec_lt(v___x_864_, v___x_865_);
lean_dec(v___x_865_);
if (v___x_866_ == 0)
{
size_t v___x_867_; size_t v___x_868_; 
v___x_867_ = ((size_t)1ULL);
v___x_868_ = lean_usize_add(v_i_859_, v___x_867_);
v_i_859_ = v___x_868_;
goto _start;
}
else
{
return v___x_866_;
}
}
else
{
uint8_t v___x_870_; 
v___x_870_ = 0;
return v___x_870_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_858_ = stack[0].m_obj;
size_t v_i_859_ = stack[1].m_num;
size_t v_stop_860_ = stack[2].m_num;
uint8_t v_res_871_;
v_res_871_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v_as_858_, v_i_859_, v_stop_860_);
stack->m_num = v_res_871_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___boxed(lean_object* v_as_872_, lean_object* v_i_873_, lean_object* v_stop_874_){
_start:
{
size_t v_i_boxed_875_; size_t v_stop_boxed_876_; uint8_t v_res_877_; lean_object* v_r_878_; 
v_i_boxed_875_ = lean_unbox_usize(v_i_873_);
lean_dec(v_i_873_);
v_stop_boxed_876_ = lean_unbox_usize(v_stop_874_);
lean_dec(v_stop_874_);
v_res_877_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v_as_872_, v_i_boxed_875_, v_stop_boxed_876_);
lean_dec_ref(v_as_872_);
v_r_878_ = lean_box(v_res_877_);
return v_r_878_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(uint8_t v_snd_879_, uint8_t v___x_880_, lean_object* v_____r_881_, lean_object* v_candidates_882_){
_start:
{
if (v_snd_879_ == 1)
{
goto v___jp_884_;
}
else
{
if (v___x_880_ == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v_candidates_882_);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
else
{
goto v___jp_884_;
}
}
v___jp_884_:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v_candidates_882_);
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_snd_879_ = stack[0].m_num;
uint8_t v___x_880_ = stack[1].m_num;
lean_object* v_____r_881_ = stack[2].m_obj;
lean_object* v_candidates_882_ = stack[3].m_obj;
lean_object* v_res_889_;
v_res_889_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v_snd_879_, v___x_880_, v_____r_881_, v_candidates_882_);
stack->m_obj
 = v_res_889_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0___boxed(lean_object* v_snd_890_, lean_object* v___x_891_, lean_object* v_____r_892_, lean_object* v_candidates_893_, lean_object* v___y_894_){
_start:
{
uint8_t v_snd_3079__boxed_895_; uint8_t v___x_3080__boxed_896_; lean_object* v_res_897_; 
v_snd_3079__boxed_895_ = lean_unbox(v_snd_890_);
v___x_3080__boxed_896_ = lean_unbox(v___x_891_);
v_res_897_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v_snd_3079__boxed_895_, v___x_3080__boxed_896_, v_____r_892_, v_candidates_893_);
return v_res_897_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(lean_object* v_upperBound_898_, lean_object* v_stack_899_, lean_object* v_text_900_, lean_object* v_ctx_x3f_901_, lean_object* v_requestedPos_902_, uint8_t v___x_903_, lean_object* v_a_904_, lean_object* v_b_905_){
_start:
{
lean_object* v___y_908_; uint8_t v___x_930_; 
v___x_930_ = lean_nat_dec_lt(v_a_904_, v_upperBound_898_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
lean_dec(v_a_904_);
lean_dec_ref(v_text_900_);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v_b_905_);
return v___x_931_;
}
else
{
lean_object* v___x_932_; lean_object* v___y_934_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_932_ = lean_array_fget_borrowed(v_stack_899_, v_a_904_);
v___x_949_ = lean_unsigned_to_nat(1u);
v___x_950_ = lean_nat_add(v_a_904_, v___x_949_);
v___x_951_ = lean_array_get_size(v_stack_899_);
v___x_952_ = lean_nat_dec_lt(v___x_950_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v___y_934_ = v___x_953_;
goto v___jp_933_;
}
else
{
lean_object* v___x_954_; 
v___x_954_ = lean_array_fget_borrowed(v_stack_899_, v___x_950_);
lean_dec(v___x_950_);
lean_inc(v___x_954_);
v___y_934_ = v___x_954_;
goto v___jp_933_;
}
v___jp_933_:
{
lean_object* v___x_935_; lean_object* v_fst_936_; 
lean_inc(v___x_932_);
lean_inc_ref(v_text_900_);
v___x_935_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_900_, v_ctx_x3f_901_, v_requestedPos_902_, v___x_932_, v___y_934_);
v_fst_936_ = lean_ctor_get(v___x_935_, 0);
if (lean_obj_tag(v_fst_936_) == 1)
{
lean_object* v_snd_937_; lean_object* v_val_938_; lean_object* v___x_939_; uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; lean_object* v___x_944_; 
lean_inc_ref(v_fst_936_);
v_snd_937_ = lean_ctor_get(v___x_935_, 1);
lean_inc(v_snd_937_);
lean_dec_ref(v___x_935_);
v_val_938_ = lean_ctor_get(v_fst_936_, 0);
lean_inc(v_val_938_);
lean_dec_ref_known(v_fst_936_, 1);
lean_inc(v___x_932_);
v___x_939_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_939_, 0, v___x_932_);
v___x_940_ = lean_unbox(v_val_938_);
lean_dec(v_val_938_);
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*1, v___x_940_);
v___x_941_ = lean_array_push(v_b_905_, v___x_939_);
v___x_942_ = lean_box(0);
v___x_943_ = lean_unbox(v_snd_937_);
lean_dec(v_snd_937_);
v___x_944_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_943_, v___x_903_, v___x_942_, v___x_941_);
v___y_908_ = v___x_944_;
goto v___jp_907_;
}
else
{
lean_object* v_snd_945_; lean_object* v___x_946_; uint8_t v___x_947_; lean_object* v___x_948_; 
v_snd_945_ = lean_ctor_get(v___x_935_, 1);
lean_inc(v_snd_945_);
lean_dec_ref(v___x_935_);
v___x_946_ = lean_box(0);
v___x_947_ = lean_unbox(v_snd_945_);
lean_dec(v_snd_945_);
v___x_948_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_947_, v___x_903_, v___x_946_, v_b_905_);
v___y_908_ = v___x_948_;
goto v___jp_907_;
}
}
}
v___jp_907_:
{
if (lean_obj_tag(v___y_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_921_; 
v_a_909_ = lean_ctor_get(v___y_908_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___y_908_);
if (v_isSharedCheck_921_ == 0)
{
v___x_911_ = v___y_908_;
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___y_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
if (lean_obj_tag(v_a_909_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; 
lean_dec(v_a_904_);
lean_dec_ref(v_text_900_);
v_a_913_ = lean_ctor_get(v_a_909_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v_a_909_, 1);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_a_913_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
lean_del_object(v___x_911_);
v_a_917_ = lean_ctor_get(v_a_909_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v_a_909_, 1);
v___x_918_ = lean_unsigned_to_nat(1u);
v___x_919_ = lean_nat_add(v_a_904_, v___x_918_);
lean_dec(v_a_904_);
v_a_904_ = v___x_919_;
v_b_905_ = v_a_917_;
goto _start;
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_a_904_);
lean_dec_ref(v_text_900_);
v_a_922_ = lean_ctor_get(v___y_908_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___y_908_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___y_908_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___y_908_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_898_ = stack[0].m_obj;
lean_object* v_stack_899_ = stack[1].m_obj;
lean_object* v_text_900_ = stack[2].m_obj;
lean_object* v_ctx_x3f_901_ = stack[3].m_obj;
lean_object* v_requestedPos_902_ = stack[4].m_obj;
uint8_t v___x_903_ = stack[5].m_num;
lean_object* v_a_904_ = stack[6].m_obj;
lean_object* v_b_905_ = stack[7].m_obj;
lean_object* v_res_955_;
v_res_955_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_898_, v_stack_899_, v_text_900_, v_ctx_x3f_901_, v_requestedPos_902_, v___x_903_, v_a_904_, v_b_905_);
stack->m_obj
 = v_res_955_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___boxed(lean_object* v_upperBound_956_, lean_object* v_stack_957_, lean_object* v_text_958_, lean_object* v_ctx_x3f_959_, lean_object* v_requestedPos_960_, lean_object* v___x_961_, lean_object* v_a_962_, lean_object* v_b_963_, lean_object* v___y_964_){
_start:
{
uint8_t v___x_3115__boxed_965_; lean_object* v_res_966_; 
v___x_3115__boxed_965_ = lean_unbox(v___x_961_);
v_res_966_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_956_, v_stack_957_, v_text_958_, v_ctx_x3f_959_, v_requestedPos_960_, v___x_3115__boxed_965_, v_a_962_, v_b_963_);
lean_dec(v_requestedPos_960_);
lean_dec(v_ctx_x3f_959_);
lean_dec_ref(v_stack_957_);
lean_dec(v_upperBound_956_);
return v_res_966_;
}
}
lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(lean_object* v_text_970_, lean_object* v_ctx_x3f_971_, lean_object* v_cmdStx_972_, lean_object* v_tree_973_, lean_object* v_requestedPos_974_){
_start:
{
uint8_t v___x_976_; 
lean_inc_ref(v_text_970_);
v___x_976_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_970_, v_requestedPos_974_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; lean_object* v___f_978_; uint8_t v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___f_982_; lean_object* v_stack_x3f_983_; 
v___x_977_ = lean_box(v___x_976_);
v___f_978_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_978_, 0, v___x_977_);
v___x_979_ = 1;
v___x_980_ = lean_box(v___x_979_);
v___x_981_ = lean_box(v___x_976_);
lean_inc(v_requestedPos_974_);
v___f_982_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed), 4, 3);
lean_closure_set(v___f_982_, 0, v___x_980_);
lean_closure_set(v___f_982_, 1, v_requestedPos_974_);
lean_closure_set(v___f_982_, 2, v___x_981_);
v_stack_x3f_983_ = l_Lean_Syntax_findStack_x3f(v_cmdStx_972_, v___f_982_, v___f_978_);
if (lean_obj_tag(v_stack_x3f_983_) == 1)
{
lean_object* v_val_984_; lean_object* v___f_985_; lean_object* v___x_986_; size_t v_sz_987_; size_t v___x_988_; lean_object* v_stack_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v_candidates_992_; lean_object* v___x_993_; 
v_val_984_ = lean_ctor_get(v_stack_x3f_983_, 0);
lean_inc(v_val_984_);
lean_dec_ref_known(v_stack_x3f_983_, 1);
v___f_985_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0));
v___x_986_ = lean_array_mk(v_val_984_);
v_sz_987_ = lean_array_size(v___x_986_);
v___x_988_ = ((size_t)0ULL);
v_stack_989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v_sz_987_, v___x_988_, v___x_986_);
v___x_990_ = lean_array_get_size(v_stack_989_);
v___x_991_ = lean_unsigned_to_nat(0u);
v_candidates_992_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1));
v___x_993_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v___x_990_, v_stack_989_, v_text_970_, v_ctx_x3f_971_, v_requestedPos_974_, v___x_976_, v___x_991_, v_candidates_992_);
lean_dec(v_requestedPos_974_);
lean_dec_ref(v_stack_989_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___y_999_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
v___x_995_ = lean_array_to_list(v_a_994_);
v___x_996_ = l_List_mergeSort___redArg(v___x_995_, v___f_985_);
v___x_997_ = lean_array_mk(v___x_996_);
v___x_1025_ = lean_array_get_size(v___x_997_);
v___x_1026_ = lean_nat_dec_lt(v___x_991_, v___x_1025_);
if (v___x_1026_ == 0)
{
v___y_999_ = v___x_1026_;
goto v___jp_998_;
}
else
{
if (v___x_1026_ == 0)
{
v___y_999_ = v___x_1026_;
goto v___jp_998_;
}
else
{
size_t v___x_1027_; uint8_t v___x_1028_; 
v___x_1027_ = lean_usize_of_nat(v___x_1025_);
v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v___x_997_, v___x_988_, v___x_1027_);
v___y_999_ = v___x_1028_;
goto v___jp_998_;
}
}
v___jp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; size_t v_sz_1002_; lean_object* v___x_1003_; 
v___x_1000_ = lean_box(0);
v___x_1001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__0));
v_sz_1002_ = lean_array_size(v___x_997_);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_tree_973_, v___y_999_, v___x_976_, v___x_997_, v_sz_1002_, v___x_988_, v___x_1001_);
lean_dec_ref(v___x_997_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1016_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1016_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1016_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_fst_1008_; 
v_fst_1008_ = lean_ctor_get(v_a_1004_, 0);
lean_inc(v_fst_1008_);
lean_dec(v_a_1004_);
if (lean_obj_tag(v_fst_1008_) == 0)
{
lean_object* v___x_1010_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1000_);
v___x_1010_ = v___x_1006_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1000_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
else
{
lean_object* v_val_1012_; lean_object* v___x_1014_; 
v_val_1012_ = lean_ctor_get(v_fst_1008_, 0);
lean_inc(v_val_1012_);
lean_dec_ref_known(v_fst_1008_, 1);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v_val_1012_);
v___x_1014_ = v___x_1006_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_val_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_a_1017_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1003_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1003_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v_tree_973_);
v_a_1029_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_993_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_993_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec(v_stack_x3f_983_);
lean_dec(v_requestedPos_974_);
lean_dec_ref(v_tree_973_);
lean_dec_ref(v_text_970_);
v___x_1037_ = lean_box(0);
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
return v___x_1038_;
}
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec(v_requestedPos_974_);
lean_dec_ref(v_tree_973_);
lean_dec(v_cmdStx_972_);
lean_dec_ref(v_text_970_);
v___x_1039_ = lean_box(0);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_970_ = stack[0].m_obj;
lean_object* v_ctx_x3f_971_ = stack[1].m_obj;
lean_object* v_cmdStx_972_ = stack[2].m_obj;
lean_object* v_tree_973_ = stack[3].m_obj;
lean_object* v_requestedPos_974_ = stack[4].m_obj;
lean_object* v_res_1041_;
v_res_1041_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(v_text_970_, v_ctx_x3f_971_, v_cmdStx_972_, v_tree_973_, v_requestedPos_974_);
stack->m_obj
 = v_res_1041_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___boxed(lean_object* v_text_1042_, lean_object* v_ctx_x3f_1043_, lean_object* v_cmdStx_1044_, lean_object* v_tree_1045_, lean_object* v_requestedPos_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(v_text_1042_, v_ctx_x3f_1043_, v_cmdStx_1044_, v_tree_1045_, v_requestedPos_1046_);
lean_dec(v_ctx_x3f_1043_);
return v_res_1048_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(lean_object* v_upperBound_1049_, lean_object* v_stack_1050_, lean_object* v_text_1051_, lean_object* v_ctx_x3f_1052_, lean_object* v_requestedPos_1053_, uint8_t v___x_1054_, lean_object* v_inst_1055_, lean_object* v_R_1056_, lean_object* v_a_1057_, lean_object* v_b_1058_, lean_object* v_c_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_1049_, v_stack_1050_, v_text_1051_, v_ctx_x3f_1052_, v_requestedPos_1053_, v___x_1054_, v_a_1057_, v_b_1058_);
return v___x_1061_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1049_ = stack[0].m_obj;
lean_object* v_stack_1050_ = stack[1].m_obj;
lean_object* v_text_1051_ = stack[2].m_obj;
lean_object* v_ctx_x3f_1052_ = stack[3].m_obj;
lean_object* v_requestedPos_1053_ = stack[4].m_obj;
uint8_t v___x_1054_ = stack[5].m_num;
lean_object* v_a_1057_ = stack[8].m_obj;
lean_object* v_b_1058_ = stack[9].m_obj;
lean_object* v_res_1062_;
v_res_1062_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(v_upperBound_1049_, v_stack_1050_, v_text_1051_, v_ctx_x3f_1052_, v_requestedPos_1053_, v___x_1054_, lean_box(0), lean_box(0), v_a_1057_, v_b_1058_, lean_box(0));
stack->m_obj
 = v_res_1062_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___boxed(lean_object* v_upperBound_1063_, lean_object* v_stack_1064_, lean_object* v_text_1065_, lean_object* v_ctx_x3f_1066_, lean_object* v_requestedPos_1067_, lean_object* v___x_1068_, lean_object* v_inst_1069_, lean_object* v_R_1070_, lean_object* v_a_1071_, lean_object* v_b_1072_, lean_object* v_c_1073_, lean_object* v___y_1074_){
_start:
{
uint8_t v___x_3467__boxed_1075_; lean_object* v_res_1076_; 
v___x_3467__boxed_1075_ = lean_unbox(v___x_1068_);
v_res_1076_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(v_upperBound_1063_, v_stack_1064_, v_text_1065_, v_ctx_x3f_1066_, v_requestedPos_1067_, v___x_3467__boxed_1075_, v_inst_1069_, v_R_1070_, v_a_1071_, v_b_1072_, v_c_1073_);
lean_dec(v_requestedPos_1067_);
lean_dec(v_ctx_x3f_1066_);
lean_dec_ref(v_stack_1064_);
lean_dec(v_upperBound_1063_);
return v_res_1076_;
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
