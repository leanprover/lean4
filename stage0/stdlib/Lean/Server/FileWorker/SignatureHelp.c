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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_instBEqOption_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(v_x_9_, v_x_10_);
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
v___x_64_ = l_instBEqOption_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(v___x_62_, v___x_63_);
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___impl(uint8_t v_x_196_){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_box(v_x_196_);
v___x_198_ = lean_obj_tag_nat(v___x_197_);
lean_dec(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___impl___boxed(lean_object* v_x_199_){
_start:
{
uint8_t v_x_4__boxed_200_; lean_object* v_res_201_; 
v_x_4__boxed_200_ = lean_unbox(v_x_199_);
v_res_201_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___impl(v_x_4__boxed_200_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(lean_object* v_k_202_){
_start:
{
lean_inc(v_k_202_);
return v_k_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg___boxed(lean_object* v_k_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(v_k_203_);
lean_dec(v_k_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(lean_object* v_motive_205_, lean_object* v_ctorIdx_206_, uint8_t v_t_207_, lean_object* v_h_208_, lean_object* v_k_209_){
_start:
{
lean_inc(v_k_209_);
return v_k_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___boxed(lean_object* v_motive_210_, lean_object* v_ctorIdx_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_k_214_){
_start:
{
uint8_t v_t_boxed_215_; lean_object* v_res_216_; 
v_t_boxed_215_ = lean_unbox(v_t_212_);
v_res_216_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(v_motive_210_, v_ctorIdx_211_, v_t_boxed_215_, v_h_213_, v_k_214_);
lean_dec(v_k_214_);
lean_dec(v_ctorIdx_211_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg(lean_object* v_pipeArg_217_){
_start:
{
lean_inc(v_pipeArg_217_);
return v_pipeArg_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg___boxed(lean_object* v_pipeArg_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg(v_pipeArg_218_);
lean_dec(v_pipeArg_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(lean_object* v_motive_220_, uint8_t v_t_221_, lean_object* v_h_222_, lean_object* v_pipeArg_223_){
_start:
{
lean_inc(v_pipeArg_223_);
return v_pipeArg_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___boxed(lean_object* v_motive_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_pipeArg_227_){
_start:
{
uint8_t v_t_boxed_228_; lean_object* v_res_229_; 
v_t_boxed_228_ = lean_unbox(v_t_225_);
v_res_229_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(v_motive_224_, v_t_boxed_228_, v_h_226_, v_pipeArg_227_);
lean_dec(v_pipeArg_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(lean_object* v_termArg_230_){
_start:
{
lean_inc(v_termArg_230_);
return v_termArg_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg___boxed(lean_object* v_termArg_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(v_termArg_231_);
lean_dec(v_termArg_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(lean_object* v_motive_233_, uint8_t v_t_234_, lean_object* v_h_235_, lean_object* v_termArg_236_){
_start:
{
lean_inc(v_termArg_236_);
return v_termArg_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___boxed(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_termArg_240_){
_start:
{
uint8_t v_t_boxed_241_; lean_object* v_res_242_; 
v_t_boxed_241_ = lean_unbox(v_t_238_);
v_res_242_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(v_motive_237_, v_t_boxed_241_, v_h_239_, v_termArg_240_);
lean_dec(v_termArg_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(lean_object* v_appArg_243_){
_start:
{
lean_inc(v_appArg_243_);
return v_appArg_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg___boxed(lean_object* v_appArg_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(v_appArg_244_);
lean_dec(v_appArg_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(lean_object* v_motive_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_appArg_249_){
_start:
{
lean_inc(v_appArg_249_);
return v_appArg_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___boxed(lean_object* v_motive_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_appArg_253_){
_start:
{
uint8_t v_t_boxed_254_; lean_object* v_res_255_; 
v_t_boxed_254_ = lean_unbox(v_t_251_);
v_res_255_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(v_motive_250_, v_t_boxed_254_, v_h_252_, v_appArg_253_);
lean_dec(v_appArg_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(uint8_t v_x_256_){
_start:
{
switch(v_x_256_)
{
case 0:
{
lean_object* v___x_257_; 
v___x_257_ = lean_unsigned_to_nat(0u);
return v___x_257_;
}
case 1:
{
lean_object* v___x_258_; 
v___x_258_ = lean_unsigned_to_nat(1u);
return v___x_258_;
}
default: 
{
lean_object* v___x_259_; 
v___x_259_ = lean_unsigned_to_nat(2u);
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio___boxed(lean_object* v_x_260_){
_start:
{
uint8_t v_x_34__boxed_261_; lean_object* v_res_262_; 
v_x_34__boxed_261_ = lean_unbox(v_x_260_);
v_res_262_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_x_34__boxed_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___impl(uint8_t v_x_263_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_box(v_x_263_);
v___x_265_ = lean_obj_tag_nat(v___x_264_);
lean_dec(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___impl___boxed(lean_object* v_x_266_){
_start:
{
uint8_t v_x_4__boxed_267_; lean_object* v_res_268_; 
v_x_4__boxed_267_ = lean_unbox(v_x_266_);
v_res_268_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___impl(v_x_4__boxed_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg(lean_object* v_k_269_){
_start:
{
lean_inc(v_k_269_);
return v_k_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg___boxed(lean_object* v_k_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg(v_k_270_);
lean_dec(v_k_270_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(lean_object* v_motive_272_, lean_object* v_ctorIdx_273_, uint8_t v_t_274_, lean_object* v_h_275_, lean_object* v_k_276_){
_start:
{
lean_inc(v_k_276_);
return v_k_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___boxed(lean_object* v_motive_277_, lean_object* v_ctorIdx_278_, lean_object* v_t_279_, lean_object* v_h_280_, lean_object* v_k_281_){
_start:
{
uint8_t v_t_boxed_282_; lean_object* v_res_283_; 
v_t_boxed_282_ = lean_unbox(v_t_279_);
v_res_283_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(v_motive_277_, v_ctorIdx_278_, v_t_boxed_282_, v_h_280_, v_k_281_);
lean_dec(v_k_281_);
lean_dec(v_ctorIdx_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(lean_object* v_continue_284_){
_start:
{
lean_inc(v_continue_284_);
return v_continue_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg___boxed(lean_object* v_continue_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(v_continue_285_);
lean_dec(v_continue_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(lean_object* v_motive_287_, uint8_t v_t_288_, lean_object* v_h_289_, lean_object* v_continue_290_){
_start:
{
lean_inc(v_continue_290_);
return v_continue_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___boxed(lean_object* v_motive_291_, lean_object* v_t_292_, lean_object* v_h_293_, lean_object* v_continue_294_){
_start:
{
uint8_t v_t_boxed_295_; lean_object* v_res_296_; 
v_t_boxed_295_ = lean_unbox(v_t_292_);
v_res_296_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(v_motive_291_, v_t_boxed_295_, v_h_293_, v_continue_294_);
lean_dec(v_continue_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(lean_object* v_stop_297_){
_start:
{
lean_inc(v_stop_297_);
return v_stop_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg___boxed(lean_object* v_stop_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(v_stop_298_);
lean_dec(v_stop_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(lean_object* v_motive_300_, uint8_t v_t_301_, lean_object* v_h_302_, lean_object* v_stop_303_){
_start:
{
lean_inc(v_stop_303_);
return v_stop_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___boxed(lean_object* v_motive_304_, lean_object* v_t_305_, lean_object* v_h_306_, lean_object* v_stop_307_){
_start:
{
uint8_t v_t_boxed_308_; lean_object* v_res_309_; 
v_t_boxed_308_ = lean_unbox(v_t_305_);
v_res_309_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(v_motive_304_, v_t_boxed_308_, v_h_306_, v_stop_307_);
lean_dec(v_stop_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(lean_object* v_s_310_, lean_object* v___x_311_, lean_object* v___x_312_, lean_object* v_a_313_, lean_object* v_b_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = lean_box(0);
switch(lean_obj_tag(v_a_313_))
{
case 0:
{
lean_object* v_pos_316_; lean_object* v___x_317_; 
v_pos_316_ = lean_ctor_get(v_a_313_, 0);
lean_inc(v_pos_316_);
lean_dec_ref_known(v_a_313_, 1);
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v_pos_316_);
return v___x_317_;
}
case 1:
{
lean_object* v_pos_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_327_; 
v_pos_318_ = lean_ctor_get(v_a_313_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_a_313_);
if (v_isSharedCheck_327_ == 0)
{
v___x_320_ = v_a_313_;
v_isShared_321_ = v_isSharedCheck_327_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_pos_318_);
lean_dec(v_a_313_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_327_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = lean_string_utf8_next_fast(v_s_310_, v_pos_318_);
lean_dec(v_pos_318_);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 0);
lean_ctor_set(v___x_320_, 0, v___x_322_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_326_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
v_a_313_ = v___x_324_;
v_b_314_ = v___x_315_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_328_; lean_object* v_table_329_; lean_object* v_stackPos_330_; lean_object* v_needlePos_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_384_; 
v_needle_328_ = lean_ctor_get(v_a_313_, 0);
v_table_329_ = lean_ctor_get(v_a_313_, 1);
v_stackPos_330_ = lean_ctor_get(v_a_313_, 2);
v_needlePos_331_ = lean_ctor_get(v_a_313_, 3);
v_isSharedCheck_384_ = !lean_is_exclusive(v_a_313_);
if (v_isSharedCheck_384_ == 0)
{
v___x_333_ = v_a_313_;
v_isShared_334_ = v_isSharedCheck_384_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_needlePos_331_);
lean_inc(v_stackPos_330_);
lean_inc(v_table_329_);
lean_inc(v_needle_328_);
lean_dec(v_a_313_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_384_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_str_335_; lean_object* v_startInclusive_336_; lean_object* v_endExclusive_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v_str_335_ = lean_ctor_get(v_needle_328_, 0);
v_startInclusive_336_ = lean_ctor_get(v_needle_328_, 1);
v_endExclusive_337_ = lean_ctor_get(v_needle_328_, 2);
v___x_338_ = lean_nat_sub(v_stackPos_330_, v_needlePos_331_);
v___x_339_ = lean_nat_sub(v_endExclusive_337_, v_startInclusive_336_);
v___x_340_ = lean_nat_add(v___x_338_, v___x_339_);
v___x_341_ = lean_nat_dec_le(v___x_340_, v___x_312_);
lean_dec(v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
lean_dec(v___x_339_);
lean_del_object(v___x_333_);
lean_dec(v_needlePos_331_);
lean_dec(v_stackPos_330_);
lean_dec_ref(v_table_329_);
lean_dec_ref(v_needle_328_);
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_add(v___x_338_, v___x_342_);
lean_dec(v___x_338_);
v___x_344_ = lean_nat_dec_le(v___x_343_, v___x_312_);
lean_dec(v___x_343_);
if (v___x_344_ == 0)
{
lean_inc(v_b_314_);
return v_b_314_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = lean_box(3);
v_a_313_ = v___x_345_;
v_b_314_ = v___x_315_;
goto _start;
}
}
else
{
uint8_t v_stackByte_347_; lean_object* v___x_348_; uint8_t v_patByte_349_; uint8_t v___x_350_; 
lean_dec(v___x_338_);
lean_inc(v_stackPos_330_);
v_stackByte_347_ = lean_string_get_byte_fast(v_s_310_, v_stackPos_330_);
v___x_348_ = lean_nat_add(v_startInclusive_336_, v_needlePos_331_);
v_patByte_349_ = lean_string_get_byte_fast(v_str_335_, v___x_348_);
v___x_350_ = lean_uint8_dec_eq(v_stackByte_347_, v_patByte_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; uint8_t v_decide_352_; 
lean_dec(v___x_339_);
v___x_351_ = lean_unsigned_to_nat(0u);
v_decide_352_ = lean_nat_dec_eq(v_needlePos_331_, v___x_351_);
if (v_decide_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_newNeedlePos_355_; uint8_t v___x_356_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_nat_sub(v_needlePos_331_, v___x_353_);
lean_dec(v_needlePos_331_);
v_newNeedlePos_355_ = lean_array_fget_borrowed(v_table_329_, v___x_354_);
lean_dec(v___x_354_);
v___x_356_ = lean_nat_dec_eq(v_newNeedlePos_355_, v___x_351_);
if (v___x_356_ == 0)
{
lean_object* v___x_358_; 
lean_inc(v_newNeedlePos_355_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 3, v_newNeedlePos_355_);
v___x_358_ = v___x_333_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_needle_328_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_table_329_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_stackPos_330_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v_newNeedlePos_355_);
v___x_358_ = v_reuseFailAlloc_360_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
v_a_313_ = v___x_358_;
v_b_314_ = v___x_315_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_361_; lean_object* v___x_363_; 
v_nextStackPos_361_ = l_String_Slice_posGE___redArg(v___x_311_, v_stackPos_330_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 3, v___x_351_);
lean_ctor_set(v___x_333_, 2, v_nextStackPos_361_);
v___x_363_ = v___x_333_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_needle_328_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_table_329_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_nextStackPos_361_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v___x_351_);
v___x_363_ = v_reuseFailAlloc_365_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
v_a_313_ = v___x_363_;
v_b_314_ = v___x_315_;
goto _start;
}
}
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_nextStackPos_368_; lean_object* v___x_370_; 
lean_dec(v_needlePos_331_);
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = lean_nat_add(v_stackPos_330_, v___x_366_);
lean_dec(v_stackPos_330_);
v_nextStackPos_368_ = l_String_Slice_posGE___redArg(v___x_311_, v___x_367_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 3, v___x_351_);
lean_ctor_set(v___x_333_, 2, v_nextStackPos_368_);
v___x_370_ = v___x_333_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_needle_328_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_table_329_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_nextStackPos_368_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v___x_351_);
v___x_370_ = v_reuseFailAlloc_372_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
v_a_313_ = v___x_370_;
v_b_314_ = v___x_315_;
goto _start;
}
}
}
else
{
lean_object* v___x_373_; lean_object* v_nextStackPos_374_; lean_object* v_nextNeedlePos_375_; uint8_t v_decide_376_; 
v___x_373_ = lean_unsigned_to_nat(1u);
v_nextStackPos_374_ = lean_nat_add(v_stackPos_330_, v___x_373_);
lean_dec(v_stackPos_330_);
v_nextNeedlePos_375_ = lean_nat_add(v_needlePos_331_, v___x_373_);
lean_dec(v_needlePos_331_);
v_decide_376_ = lean_nat_dec_eq(v_nextNeedlePos_375_, v___x_339_);
lean_dec(v___x_339_);
if (v_decide_376_ == 0)
{
lean_object* v___x_378_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 3, v_nextNeedlePos_375_);
lean_ctor_set(v___x_333_, 2, v_nextStackPos_374_);
v___x_378_ = v___x_333_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_needle_328_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_table_329_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_nextStackPos_374_);
lean_ctor_set(v_reuseFailAlloc_380_, 3, v_nextNeedlePos_375_);
v___x_378_ = v_reuseFailAlloc_380_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
v_a_313_ = v___x_378_;
goto _start;
}
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
lean_del_object(v___x_333_);
lean_dec_ref(v_table_329_);
lean_dec_ref(v_needle_328_);
v___x_381_ = lean_nat_sub(v_nextStackPos_374_, v_nextNeedlePos_375_);
lean_dec(v_nextNeedlePos_375_);
lean_dec(v_nextStackPos_374_);
v___x_382_ = l_String_Slice_pos_x21(v___x_311_, v___x_381_);
lean_dec(v___x_381_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
}
}
}
default: 
{
lean_inc(v_b_314_);
return v_b_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg___boxed(lean_object* v_s_385_, lean_object* v___x_386_, lean_object* v___x_387_, lean_object* v_a_388_, lean_object* v_b_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_385_, v___x_386_, v___x_387_, v_a_388_, v_b_389_);
lean_dec(v_b_389_);
lean_dec(v___x_387_);
lean_dec_ref(v___x_386_);
lean_dec_ref(v_s_385_);
return v_res_390_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1));
v___x_397_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2);
v___x_400_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1));
v___x_401_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_399_);
lean_ctor_set(v___x_401_, 2, v___x_398_);
lean_ctor_set(v___x_401_, 3, v___x_398_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(lean_object* v_s_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_string_utf8_byte_size(v_s_402_);
lean_inc_ref(v_s_402_);
v___x_405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_405_, 0, v_s_402_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
lean_ctor_set(v___x_405_, 2, v___x_404_);
v___x_406_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3, &l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once, _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3);
v___x_407_ = lean_box(0);
v___x_408_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_402_, v___x_405_, v___x_404_, v___x_406_, v___x_407_);
lean_dec_ref_known(v___x_405_, 3);
lean_dec_ref(v_s_402_);
if (lean_obj_tag(v___x_408_) == 0)
{
return v___x_407_;
}
else
{
lean_object* v_val_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
v_val_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_val_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_val_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(lean_object* v_s_417_, lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v_inst_420_, lean_object* v_R_421_, lean_object* v_a_422_, lean_object* v_b_423_, lean_object* v_c_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_417_, v___x_418_, v___x_419_, v_a_422_, v_b_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___boxed(lean_object* v_s_426_, lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v_inst_429_, lean_object* v_R_430_, lean_object* v_a_431_, lean_object* v_b_432_, lean_object* v_c_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(v_s_426_, v___x_427_, v___x_428_, v_inst_429_, v_R_430_, v_a_431_, v_b_432_, v_c_433_);
lean_dec(v_b_432_);
lean_dec(v___x_428_);
lean_dec_ref(v___x_427_);
lean_dec_ref(v_s_426_);
return v_res_434_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(lean_object* v_text_435_, lean_object* v_pos_436_){
_start:
{
lean_object* v___x_437_; lean_object* v_line_438_; lean_object* v_source_439_; lean_object* v_lineStartPos_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_lineEndPos_443_; lean_object* v_line_444_; lean_object* v___x_445_; 
lean_inc_ref(v_text_435_);
v___x_437_ = l_Lean_FileMap_toPosition(v_text_435_, v_pos_436_);
v_line_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_line_438_);
lean_dec_ref(v___x_437_);
v_source_439_ = lean_ctor_get(v_text_435_, 0);
lean_inc_ref(v_source_439_);
v_lineStartPos_440_ = l_Lean_FileMap_lineStart(v_text_435_, v_line_438_);
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = lean_nat_add(v_line_438_, v___x_441_);
lean_dec(v_line_438_);
v_lineEndPos_443_ = l_Lean_FileMap_lineStart(v_text_435_, v___x_442_);
lean_dec(v___x_442_);
lean_dec_ref(v_text_435_);
v_line_444_ = lean_string_utf8_extract(v_source_439_, v_lineStartPos_440_, v_lineEndPos_443_);
lean_dec(v_lineEndPos_443_);
lean_dec_ref(v_source_439_);
v___x_445_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(v_line_444_);
if (lean_obj_tag(v___x_445_) == 1)
{
lean_object* v_val_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v_val_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v___x_445_, 1);
v___x_447_ = lean_nat_add(v_lineStartPos_440_, v_val_446_);
lean_dec(v_val_446_);
lean_dec(v_lineStartPos_440_);
v___x_448_ = lean_nat_dec_le(v___x_447_, v_pos_436_);
lean_dec(v___x_447_);
return v___x_448_;
}
else
{
uint8_t v___x_449_; 
lean_dec(v___x_445_);
lean_dec(v_lineStartPos_440_);
v___x_449_ = 0;
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment___boxed(lean_object* v_text_450_, lean_object* v_pos_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_450_, v_pos_451_);
lean_dec(v_pos_451_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(lean_object* v_text_510_, lean_object* v_ctx_x3f_511_, lean_object* v_requestedPos_512_, lean_object* v_stx_513_, lean_object* v_parent_514_){
_start:
{
lean_object* v_kind_x3f_516_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; uint8_t v___y_541_; uint8_t v___x_624_; lean_object* v___x_625_; 
v___x_624_ = 1;
v___x_625_ = l_Lean_Syntax_getTailPos_x3f(v_stx_513_, v___x_624_);
if (lean_obj_tag(v___x_625_) == 1)
{
lean_object* v_val_626_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; uint8_t v___y_631_; uint8_t v___y_632_; uint8_t v___y_634_; uint8_t v___y_635_; uint8_t v___y_637_; uint8_t v___y_638_; uint8_t v___y_639_; uint8_t v___y_641_; uint8_t v___y_642_; uint8_t v___y_649_; 
v_val_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_val_626_);
lean_dec_ref_known(v___x_625_, 1);
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_nat_add(v_requestedPos_512_, v___x_627_);
v___x_629_ = lean_nat_dec_le(v___x_628_, v_val_626_);
lean_dec(v___x_628_);
if (v___x_629_ == 0)
{
if (lean_obj_tag(v_ctx_x3f_511_) == 0)
{
v___y_649_ = v___x_629_;
goto v___jp_648_;
}
else
{
lean_object* v_val_652_; uint8_t v_triggerKind_653_; 
v_val_652_ = lean_ctor_get(v_ctx_x3f_511_, 0);
v_triggerKind_653_ = lean_ctor_get_uint8(v_val_652_, sizeof(void*)*2);
if (v_triggerKind_653_ == 0)
{
v___y_649_ = v___x_624_;
goto v___jp_648_;
}
else
{
v___y_649_ = v___x_629_;
goto v___jp_648_;
}
}
}
else
{
lean_object* v___x_654_; 
lean_dec(v_val_626_);
lean_dec(v_parent_514_);
lean_dec(v_stx_513_);
lean_dec_ref(v_text_510_);
v___x_654_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23));
return v___x_654_;
}
v___jp_630_:
{
if (v___y_632_ == 0)
{
v___y_541_ = v___x_629_;
goto v___jp_540_;
}
else
{
v___y_541_ = v___y_631_;
goto v___jp_540_;
}
}
v___jp_633_:
{
if (v___y_635_ == 0)
{
v___y_541_ = v___y_634_;
goto v___jp_540_;
}
else
{
v___y_631_ = v___y_634_;
v___y_632_ = v___x_629_;
goto v___jp_630_;
}
}
v___jp_636_:
{
if (v___y_637_ == 0)
{
v___y_634_ = v___y_639_;
v___y_635_ = v___y_638_;
goto v___jp_633_;
}
else
{
if (v___x_629_ == 0)
{
v___y_631_ = v___y_639_;
v___y_632_ = v___x_629_;
goto v___jp_630_;
}
else
{
v___y_634_ = v___y_639_;
v___y_635_ = v___y_638_;
goto v___jp_633_;
}
}
}
v___jp_640_:
{
lean_object* v___x_643_; lean_object* v_line_644_; lean_object* v___x_645_; lean_object* v_line_646_; uint8_t v___x_647_; 
lean_inc_ref(v_text_510_);
v___x_643_ = l_Lean_FileMap_toPosition(v_text_510_, v_requestedPos_512_);
v_line_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_line_644_);
lean_dec_ref(v___x_643_);
v___x_645_ = l_Lean_FileMap_toPosition(v_text_510_, v_val_626_);
lean_dec(v_val_626_);
v_line_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_line_646_);
lean_dec_ref(v___x_645_);
v___x_647_ = lean_nat_dec_eq(v_line_644_, v_line_646_);
lean_dec(v_line_646_);
lean_dec(v_line_644_);
if (v___x_647_ == 0)
{
v___y_637_ = v___y_641_;
v___y_638_ = v___y_642_;
v___y_639_ = v___x_624_;
goto v___jp_636_;
}
else
{
v___y_637_ = v___y_641_;
v___y_638_ = v___y_642_;
v___y_639_ = v___x_629_;
goto v___jp_636_;
}
}
v___jp_648_:
{
if (lean_obj_tag(v_ctx_x3f_511_) == 0)
{
v___y_641_ = v___y_649_;
v___y_642_ = v___x_629_;
goto v___jp_640_;
}
else
{
lean_object* v_val_650_; uint8_t v_isRetrigger_651_; 
v_val_650_ = lean_ctor_get(v_ctx_x3f_511_, 0);
v_isRetrigger_651_ = lean_ctor_get_uint8(v_val_650_, sizeof(void*)*2 + 1);
v___y_641_ = v___y_649_;
v___y_642_ = v_isRetrigger_651_;
goto v___jp_640_;
}
}
}
else
{
lean_object* v___x_655_; 
lean_dec(v___x_625_);
lean_dec(v_parent_514_);
lean_dec(v_stx_513_);
lean_dec_ref(v_text_510_);
v___x_655_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22));
return v___x_655_;
}
v___jp_515_:
{
uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = 0;
v___x_518_ = lean_box(v___x_517_);
lean_inc(v_kind_x3f_516_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v_kind_x3f_516_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
return v___x_519_;
}
v___jp_520_:
{
lean_object* v___x_521_; 
v___x_521_ = lean_box(0);
v_kind_x3f_516_ = v___x_521_;
goto v___jp_515_;
}
v___jp_522_:
{
lean_object* v___x_523_; 
v___x_523_ = lean_box(0);
v_kind_x3f_516_ = v___x_523_;
goto v___jp_515_;
}
v___jp_524_:
{
lean_object* v___x_525_; 
v___x_525_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_516_ = v___x_525_;
goto v___jp_515_;
}
v___jp_526_:
{
lean_object* v___x_527_; 
v___x_527_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_516_ = v___x_527_;
goto v___jp_515_;
}
v___jp_528_:
{
lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_532_ = lean_unsigned_to_nat(3u);
v___x_533_ = l_Lean_Syntax_getArg(v_stx_513_, v___x_532_);
lean_dec(v_stx_513_);
v___x_534_ = l_Lean_Syntax_matchesNull(v___x_533_, v___y_529_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = lean_array_get_size(v___y_530_);
lean_dec_ref(v___y_530_);
v___x_536_ = lean_nat_dec_le(v___x_535_, v___y_531_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
v___x_537_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_516_ = v___x_537_;
goto v___jp_515_;
}
else
{
lean_object* v___x_538_; 
v___x_538_ = lean_box(0);
v_kind_x3f_516_ = v___x_538_;
goto v___jp_515_;
}
}
else
{
lean_object* v___x_539_; 
lean_dec_ref(v___y_530_);
v___x_539_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1));
v_kind_x3f_516_ = v___x_539_;
goto v___jp_515_;
}
}
v___jp_540_:
{
if (v___y_541_ == 0)
{
if (lean_obj_tag(v_stx_513_) == 3)
{
lean_object* v___x_542_; uint8_t v___x_543_; 
lean_dec_ref_known(v_stx_513_, 4);
v___x_542_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6));
lean_inc(v_parent_514_);
v___x_543_ = l_Lean_Syntax_isOfKind(v_parent_514_, v___x_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8));
lean_inc(v_parent_514_);
v___x_545_ = l_Lean_Syntax_isOfKind(v_parent_514_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10));
lean_inc(v_parent_514_);
v___x_547_ = l_Lean_Syntax_isOfKind(v_parent_514_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
lean_dec(v_parent_514_);
v___x_548_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_516_ = v___x_548_;
goto v___jp_515_;
}
else
{
if (v___x_545_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = l_Lean_Syntax_getArg(v_parent_514_, v___x_549_);
lean_dec(v_parent_514_);
v___x_551_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_552_ = l_Lean_Syntax_isOfKind(v___x_550_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
v___x_553_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_516_ = v___x_553_;
goto v___jp_515_;
}
else
{
goto v___jp_520_;
}
}
else
{
lean_dec(v_parent_514_);
goto v___jp_520_;
}
}
}
else
{
if (v___x_543_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_554_ = lean_unsigned_to_nat(2u);
v___x_555_ = l_Lean_Syntax_getArg(v_parent_514_, v___x_554_);
lean_dec(v_parent_514_);
v___x_556_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_557_ = l_Lean_Syntax_isOfKind(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
v___x_558_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_516_ = v___x_558_;
goto v___jp_515_;
}
else
{
goto v___jp_522_;
}
}
else
{
lean_dec(v_parent_514_);
goto v___jp_522_;
}
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_559_ = lean_unsigned_to_nat(2u);
v___x_560_ = l_Lean_Syntax_getArg(v_parent_514_, v___x_559_);
v___x_561_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_562_ = l_Lean_Syntax_isOfKind(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
lean_dec(v_parent_514_);
v___x_563_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_516_ = v___x_563_;
goto v___jp_515_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_unsigned_to_nat(3u);
v___x_566_ = l_Lean_Syntax_getArg(v_parent_514_, v___x_565_);
lean_dec(v_parent_514_);
v___x_567_ = l_Lean_Syntax_matchesNull(v___x_566_, v___x_564_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
v___x_568_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_516_ = v___x_568_;
goto v___jp_515_;
}
else
{
lean_object* v___x_569_; 
v___x_569_ = lean_box(0);
v_kind_x3f_516_ = v___x_569_;
goto v___jp_515_;
}
}
}
}
else
{
lean_dec(v_parent_514_);
if (lean_obj_tag(v_stx_513_) == 1)
{
lean_object* v_kind_570_; lean_object* v_args_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v_kind_570_ = lean_ctor_get(v_stx_513_, 1);
v_args_571_ = lean_ctor_get(v_stx_513_, 2);
v___x_572_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14));
v___x_573_ = lean_name_eq(v_kind_570_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16));
v___x_575_ = lean_name_eq(v_kind_570_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18));
lean_inc_ref(v_stx_513_);
v___x_577_ = l_Lean_Syntax_isOfKind(v_stx_513_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20));
lean_inc_ref(v_stx_513_);
v___x_579_ = l_Lean_Syntax_isOfKind(v_stx_513_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_580_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6));
lean_inc_ref(v_stx_513_);
v___x_581_ = l_Lean_Syntax_isOfKind(v_stx_513_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; uint8_t v___x_583_; 
lean_inc_ref(v_args_571_);
v___x_582_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10));
lean_inc_ref(v_stx_513_);
v___x_583_ = l_Lean_Syntax_isOfKind(v_stx_513_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_584_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8));
lean_inc_ref(v_stx_513_);
v___x_585_ = l_Lean_Syntax_isOfKind(v_stx_513_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
lean_dec_ref_known(v_stx_513_, 3);
v___x_586_ = lean_array_get_size(v_args_571_);
lean_dec_ref(v_args_571_);
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = lean_nat_dec_le(v___x_586_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
v___x_589_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_516_ = v___x_589_;
goto v___jp_515_;
}
else
{
lean_object* v___x_590_; 
v___x_590_ = lean_box(0);
v_kind_x3f_516_ = v___x_590_;
goto v___jp_515_;
}
}
else
{
if (v___x_583_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_591_ = lean_unsigned_to_nat(2u);
v___x_592_ = l_Lean_Syntax_getArg(v_stx_513_, v___x_591_);
lean_dec_ref_known(v_stx_513_, 3);
v___x_593_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_594_ = l_Lean_Syntax_isOfKind(v___x_592_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = lean_array_get_size(v_args_571_);
lean_dec_ref(v_args_571_);
v___x_597_ = lean_nat_dec_le(v___x_596_, v___x_595_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
v___x_598_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_516_ = v___x_598_;
goto v___jp_515_;
}
else
{
lean_object* v___x_599_; 
v___x_599_ = lean_box(0);
v_kind_x3f_516_ = v___x_599_;
goto v___jp_515_;
}
}
else
{
lean_dec_ref(v_args_571_);
goto v___jp_524_;
}
}
else
{
lean_dec_ref(v_args_571_);
lean_dec_ref_known(v_stx_513_, 3);
goto v___jp_524_;
}
}
}
else
{
if (v___x_581_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = l_Lean_Syntax_getArg(v_stx_513_, v___x_600_);
lean_dec_ref_known(v_stx_513_, 3);
v___x_602_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_603_ = l_Lean_Syntax_isOfKind(v___x_601_, v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_array_get_size(v_args_571_);
lean_dec_ref(v_args_571_);
v___x_605_ = lean_nat_dec_le(v___x_604_, v___x_600_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; 
v___x_606_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_516_ = v___x_606_;
goto v___jp_515_;
}
else
{
lean_object* v___x_607_; 
v___x_607_ = lean_box(0);
v_kind_x3f_516_ = v___x_607_;
goto v___jp_515_;
}
}
else
{
lean_dec_ref(v_args_571_);
goto v___jp_526_;
}
}
else
{
lean_dec_ref(v_args_571_);
lean_dec_ref_known(v_stx_513_, 3);
goto v___jp_526_;
}
}
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = lean_unsigned_to_nat(1u);
if (v___x_579_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_610_ = lean_unsigned_to_nat(2u);
v___x_611_ = l_Lean_Syntax_getArg(v_stx_513_, v___x_610_);
v___x_612_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12));
v___x_613_ = l_Lean_Syntax_isOfKind(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; uint8_t v___x_615_; 
lean_inc_ref(v_args_571_);
lean_dec_ref_known(v_stx_513_, 3);
v___x_614_ = lean_array_get_size(v_args_571_);
lean_dec_ref(v_args_571_);
v___x_615_ = lean_nat_dec_le(v___x_614_, v___x_609_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
v___x_616_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0));
v_kind_x3f_516_ = v___x_616_;
goto v___jp_515_;
}
else
{
lean_object* v___x_617_; 
v___x_617_ = lean_box(0);
v_kind_x3f_516_ = v___x_617_;
goto v___jp_515_;
}
}
else
{
lean_inc_ref(v_args_571_);
v___y_529_ = v___x_608_;
v___y_530_ = v_args_571_;
v___y_531_ = v___x_609_;
goto v___jp_528_;
}
}
else
{
lean_inc_ref(v_args_571_);
v___y_529_ = v___x_608_;
v___y_530_ = v_args_571_;
v___y_531_ = v___x_609_;
goto v___jp_528_;
}
}
}
else
{
lean_object* v___x_618_; 
lean_dec_ref_known(v_stx_513_, 3);
v___x_618_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1));
v_kind_x3f_516_ = v___x_618_;
goto v___jp_515_;
}
}
else
{
lean_object* v___x_619_; 
lean_dec_ref_known(v_stx_513_, 3);
v___x_619_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1));
v_kind_x3f_516_ = v___x_619_;
goto v___jp_515_;
}
}
else
{
lean_object* v___x_620_; 
lean_dec_ref_known(v_stx_513_, 3);
v___x_620_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21));
v_kind_x3f_516_ = v___x_620_;
goto v___jp_515_;
}
}
else
{
lean_object* v___x_621_; 
lean_dec_ref_known(v_stx_513_, 3);
v___x_621_ = lean_box(0);
v_kind_x3f_516_ = v___x_621_;
goto v___jp_515_;
}
}
else
{
lean_object* v___x_622_; 
lean_dec(v_stx_513_);
v___x_622_ = lean_box(0);
v_kind_x3f_516_ = v___x_622_;
goto v___jp_515_;
}
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v_parent_514_);
lean_dec(v_stx_513_);
v___x_623_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22));
return v___x_623_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___boxed(lean_object* v_text_656_, lean_object* v_ctx_x3f_657_, lean_object* v_requestedPos_658_, lean_object* v_stx_659_, lean_object* v_parent_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_656_, v_ctx_x3f_657_, v_requestedPos_658_, v_stx_659_, v_parent_660_);
lean_dec(v_requestedPos_658_);
lean_dec(v_ctx_x3f_657_);
return v_res_661_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(uint8_t v___x_662_, lean_object* v_stx_663_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = l_Lean_Syntax_hasArgs(v_stx_663_);
if (v___x_664_ == 0)
{
uint8_t v___x_665_; 
v___x_665_ = 1;
return v___x_665_;
}
else
{
return v___x_662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed(lean_object* v___x_666_, lean_object* v_stx_667_){
_start:
{
uint8_t v___x_2727__boxed_668_; uint8_t v_res_669_; lean_object* v_r_670_; 
v___x_2727__boxed_668_ = lean_unbox(v___x_666_);
v_res_669_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(v___x_2727__boxed_668_, v_stx_667_);
lean_dec(v_stx_667_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(uint8_t v___x_671_, lean_object* v_requestedPos_672_, uint8_t v___x_673_, lean_object* v_stx_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_674_, v___x_671_);
if (lean_obj_tag(v___x_675_) == 1)
{
lean_object* v_val_676_; uint8_t v___x_677_; 
v_val_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_val_676_);
lean_dec_ref_known(v___x_675_, 1);
v___x_677_ = l_Lean_Syntax_Range_contains(v_val_676_, v_requestedPos_672_, v___x_671_);
lean_dec(v_val_676_);
return v___x_677_;
}
else
{
lean_dec(v___x_675_);
return v___x_673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed(lean_object* v___x_678_, lean_object* v_requestedPos_679_, lean_object* v___x_680_, lean_object* v_stx_681_){
_start:
{
uint8_t v___x_2734__boxed_682_; uint8_t v___x_2735__boxed_683_; uint8_t v_res_684_; lean_object* v_r_685_; 
v___x_2734__boxed_682_ = lean_unbox(v___x_678_);
v___x_2735__boxed_683_ = lean_unbox(v___x_680_);
v_res_684_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(v___x_2734__boxed_682_, v_requestedPos_679_, v___x_2735__boxed_683_, v_stx_681_);
lean_dec(v_stx_681_);
lean_dec(v_requestedPos_679_);
v_r_685_ = lean_box(v_res_684_);
return v_r_685_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(lean_object* v_c1_686_, lean_object* v_c2_687_){
_start:
{
uint8_t v_kind_688_; uint8_t v_kind_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_kind_688_ = lean_ctor_get_uint8(v_c2_687_, sizeof(void*)*1);
v_kind_689_ = lean_ctor_get_uint8(v_c1_686_, sizeof(void*)*1);
v___x_690_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_688_);
v___x_691_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_689_);
v___x_692_ = lean_nat_dec_le(v___x_690_, v___x_691_);
lean_dec(v___x_691_);
lean_dec(v___x_690_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2___boxed(lean_object* v_c1_693_, lean_object* v_c2_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(v_c1_693_, v_c2_694_);
lean_dec_ref(v_c2_694_);
lean_dec_ref(v_c1_693_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(size_t v_sz_697_, size_t v_i_698_, lean_object* v_bs_699_){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = lean_usize_dec_lt(v_i_698_, v_sz_697_);
if (v___x_700_ == 0)
{
return v_bs_699_;
}
else
{
lean_object* v_v_701_; lean_object* v_fst_702_; lean_object* v___x_703_; lean_object* v_bs_x27_704_; size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; 
v_v_701_ = lean_array_uget_borrowed(v_bs_699_, v_i_698_);
v_fst_702_ = lean_ctor_get(v_v_701_, 0);
lean_inc(v_fst_702_);
v___x_703_ = lean_unsigned_to_nat(0u);
v_bs_x27_704_ = lean_array_uset(v_bs_699_, v_i_698_, v___x_703_);
v___x_705_ = ((size_t)1ULL);
v___x_706_ = lean_usize_add(v_i_698_, v___x_705_);
v___x_707_ = lean_array_uset(v_bs_x27_704_, v_i_698_, v_fst_702_);
v_i_698_ = v___x_706_;
v_bs_699_ = v___x_707_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___boxed(lean_object* v_sz_709_, lean_object* v_i_710_, lean_object* v_bs_711_){
_start:
{
size_t v_sz_boxed_712_; size_t v_i_boxed_713_; lean_object* v_res_714_; 
v_sz_boxed_712_ = lean_unbox_usize(v_sz_709_);
lean_dec(v_sz_709_);
v_i_boxed_713_ = lean_unbox_usize(v_i_710_);
lean_dec(v_i_710_);
v_res_714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v_sz_boxed_712_, v_i_boxed_713_, v_bs_711_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0(lean_object* v_tree_723_, uint8_t v___y_724_, uint8_t v___x_725_, lean_object* v_as_726_, size_t v_sz_727_, size_t v_i_728_, lean_object* v_b_729_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = lean_usize_dec_lt(v_i_728_, v_sz_727_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
lean_dec_ref(v_tree_723_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v_b_729_);
return v___x_732_;
}
else
{
lean_object* v_a_733_; uint8_t v_kind_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___y_762_; 
lean_dec_ref(v_b_729_);
v_a_733_ = lean_array_uget_borrowed(v_as_726_, v_i_728_);
v_kind_734_ = lean_ctor_get_uint8(v_a_733_, sizeof(void*)*1);
v___x_735_ = lean_box(0);
v___x_736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__0));
if (v_kind_734_ == 1)
{
v___y_762_ = v___y_724_;
goto v___jp_761_;
}
else
{
if (v___x_725_ == 0)
{
goto v___jp_737_;
}
else
{
v___y_762_ = v___y_724_;
goto v___jp_761_;
}
}
v___jp_737_:
{
lean_object* v_appStx_738_; lean_object* v___x_739_; 
v_appStx_738_ = lean_ctor_get(v_a_733_, 0);
lean_inc(v_appStx_738_);
lean_inc_ref(v_tree_723_);
v___x_739_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_723_, v_appStx_738_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_752_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_752_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_752_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_752_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
if (lean_obj_tag(v_a_740_) == 1)
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
lean_dec_ref(v_tree_723_);
v___x_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_744_, 0, v_a_740_);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v___x_735_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_745_);
v___x_747_ = v___x_742_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
else
{
size_t v___x_749_; size_t v___x_750_; 
lean_del_object(v___x_742_);
lean_dec(v_a_740_);
v___x_749_ = ((size_t)1ULL);
v___x_750_ = lean_usize_add(v_i_728_, v___x_749_);
v_i_728_ = v___x_750_;
v_b_729_ = v___x_736_;
goto _start;
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref(v_tree_723_);
v_a_753_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_739_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_739_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
v___jp_761_:
{
if (v___y_762_ == 0)
{
goto v___jp_737_;
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec_ref(v_tree_723_);
v___x_763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__2));
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
return v___x_764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___boxed(lean_object* v_tree_765_, lean_object* v___y_766_, lean_object* v___x_767_, lean_object* v_as_768_, lean_object* v_sz_769_, lean_object* v_i_770_, lean_object* v_b_771_, lean_object* v___y_772_){
_start:
{
uint8_t v___y_2780__boxed_773_; uint8_t v___x_2781__boxed_774_; size_t v_sz_boxed_775_; size_t v_i_boxed_776_; lean_object* v_res_777_; 
v___y_2780__boxed_773_ = lean_unbox(v___y_766_);
v___x_2781__boxed_774_ = lean_unbox(v___x_767_);
v_sz_boxed_775_ = lean_unbox_usize(v_sz_769_);
lean_dec(v_sz_769_);
v_i_boxed_776_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0(v_tree_765_, v___y_2780__boxed_773_, v___x_2781__boxed_774_, v_as_768_, v_sz_boxed_775_, v_i_boxed_776_, v_b_771_);
lean_dec_ref(v_as_768_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(lean_object* v_tree_778_, uint8_t v___y_779_, uint8_t v___x_780_, lean_object* v_as_781_, size_t v_sz_782_, size_t v_i_783_, lean_object* v_b_784_){
_start:
{
uint8_t v___x_786_; 
v___x_786_ = lean_usize_dec_lt(v_i_783_, v_sz_782_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
lean_dec_ref(v_tree_778_);
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v_b_784_);
return v___x_787_;
}
else
{
lean_object* v_a_788_; uint8_t v_kind_789_; lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___y_817_; 
lean_dec_ref(v_b_784_);
v_a_788_ = lean_array_uget_borrowed(v_as_781_, v_i_783_);
v_kind_789_ = lean_ctor_get_uint8(v_a_788_, sizeof(void*)*1);
v___x_790_ = lean_box(0);
v___x_791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__0));
if (v_kind_789_ == 1)
{
v___y_817_ = v___y_779_;
goto v___jp_816_;
}
else
{
if (v___x_780_ == 0)
{
goto v___jp_792_;
}
else
{
v___y_817_ = v___y_779_;
goto v___jp_816_;
}
}
v___jp_792_:
{
lean_object* v_appStx_793_; lean_object* v___x_794_; 
v_appStx_793_ = lean_ctor_get(v_a_788_, 0);
lean_inc(v_appStx_793_);
lean_inc_ref(v_tree_778_);
v___x_794_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_778_, v_appStx_793_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_807_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_807_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_807_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_807_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
if (lean_obj_tag(v_a_795_) == 1)
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
lean_dec_ref(v_tree_778_);
v___x_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_799_, 0, v_a_795_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v___x_790_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_800_);
v___x_802_ = v___x_797_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
else
{
size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
lean_del_object(v___x_797_);
lean_dec(v_a_795_);
v___x_804_ = ((size_t)1ULL);
v___x_805_ = lean_usize_add(v_i_783_, v___x_804_);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0(v_tree_778_, v___y_779_, v___x_780_, v_as_781_, v_sz_782_, v___x_805_, v___x_791_);
return v___x_806_;
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v_tree_778_);
v_a_808_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_794_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_794_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
v___jp_816_:
{
if (v___y_817_ == 0)
{
goto v___jp_792_;
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec_ref(v_tree_778_);
v___x_818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__2));
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0___boxed(lean_object* v_tree_820_, lean_object* v___y_821_, lean_object* v___x_822_, lean_object* v_as_823_, lean_object* v_sz_824_, lean_object* v_i_825_, lean_object* v_b_826_, lean_object* v___y_827_){
_start:
{
uint8_t v___y_2868__boxed_828_; uint8_t v___x_2869__boxed_829_; size_t v_sz_boxed_830_; size_t v_i_boxed_831_; lean_object* v_res_832_; 
v___y_2868__boxed_828_ = lean_unbox(v___y_821_);
v___x_2869__boxed_829_ = lean_unbox(v___x_822_);
v_sz_boxed_830_ = lean_unbox_usize(v_sz_824_);
lean_dec(v_sz_824_);
v_i_boxed_831_ = lean_unbox_usize(v_i_825_);
lean_dec(v_i_825_);
v_res_832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_tree_820_, v___y_2868__boxed_828_, v___x_2869__boxed_829_, v_as_823_, v_sz_boxed_830_, v_i_boxed_831_, v_b_826_);
lean_dec_ref(v_as_823_);
return v_res_832_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0(void){
_start:
{
uint8_t v___x_833_; lean_object* v___x_834_; 
v___x_833_ = 1;
v___x_834_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(lean_object* v_as_835_, size_t v_i_836_, size_t v_stop_837_){
_start:
{
uint8_t v___x_838_; 
v___x_838_ = lean_usize_dec_eq(v_i_836_, v_stop_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; uint8_t v_kind_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_839_ = lean_array_uget_borrowed(v_as_835_, v_i_836_);
v_kind_840_ = lean_ctor_get_uint8(v___x_839_, sizeof(void*)*1);
v___x_841_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0);
v___x_842_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_840_);
v___x_843_ = lean_nat_dec_lt(v___x_841_, v___x_842_);
lean_dec(v___x_842_);
if (v___x_843_ == 0)
{
size_t v___x_844_; size_t v___x_845_; 
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_add(v_i_836_, v___x_844_);
v_i_836_ = v___x_845_;
goto _start;
}
else
{
return v___x_843_;
}
}
else
{
uint8_t v___x_847_; 
v___x_847_ = 0;
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___boxed(lean_object* v_as_848_, lean_object* v_i_849_, lean_object* v_stop_850_){
_start:
{
size_t v_i_boxed_851_; size_t v_stop_boxed_852_; uint8_t v_res_853_; lean_object* v_r_854_; 
v_i_boxed_851_ = lean_unbox_usize(v_i_849_);
lean_dec(v_i_849_);
v_stop_boxed_852_ = lean_unbox_usize(v_stop_850_);
lean_dec(v_stop_850_);
v_res_853_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v_as_848_, v_i_boxed_851_, v_stop_boxed_852_);
lean_dec_ref(v_as_848_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(uint8_t v_snd_855_, uint8_t v___x_856_, lean_object* v_____r_857_, lean_object* v_candidates_858_){
_start:
{
if (v_snd_855_ == 1)
{
goto v___jp_860_;
}
else
{
if (v___x_856_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_863_, 0, v_candidates_858_);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
else
{
goto v___jp_860_;
}
}
v___jp_860_:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v_candidates_858_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0___boxed(lean_object* v_snd_865_, lean_object* v___x_866_, lean_object* v_____r_867_, lean_object* v_candidates_868_, lean_object* v___y_869_){
_start:
{
uint8_t v_snd_2966__boxed_870_; uint8_t v___x_2967__boxed_871_; lean_object* v_res_872_; 
v_snd_2966__boxed_870_ = lean_unbox(v_snd_865_);
v___x_2967__boxed_871_ = lean_unbox(v___x_866_);
v_res_872_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v_snd_2966__boxed_870_, v___x_2967__boxed_871_, v_____r_867_, v_candidates_868_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(lean_object* v_upperBound_873_, lean_object* v_stack_874_, lean_object* v_text_875_, lean_object* v_ctx_x3f_876_, lean_object* v_requestedPos_877_, uint8_t v___x_878_, lean_object* v_a_879_, lean_object* v_b_880_){
_start:
{
lean_object* v___y_883_; uint8_t v___x_905_; 
v___x_905_ = lean_nat_dec_lt(v_a_879_, v_upperBound_873_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
lean_dec(v_a_879_);
lean_dec_ref(v_text_875_);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v_b_880_);
return v___x_906_;
}
else
{
lean_object* v___x_907_; lean_object* v___y_909_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_907_ = lean_array_fget_borrowed(v_stack_874_, v_a_879_);
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_nat_add(v_a_879_, v___x_924_);
v___x_926_ = lean_array_get_size(v_stack_874_);
v___x_927_ = lean_nat_dec_lt(v___x_925_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; 
lean_dec(v___x_925_);
v___x_928_ = lean_box(0);
v___y_909_ = v___x_928_;
goto v___jp_908_;
}
else
{
lean_object* v___x_929_; 
v___x_929_ = lean_array_fget_borrowed(v_stack_874_, v___x_925_);
lean_dec(v___x_925_);
lean_inc(v___x_929_);
v___y_909_ = v___x_929_;
goto v___jp_908_;
}
v___jp_908_:
{
lean_object* v___x_910_; lean_object* v_fst_911_; 
lean_inc(v___x_907_);
lean_inc_ref(v_text_875_);
v___x_910_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_875_, v_ctx_x3f_876_, v_requestedPos_877_, v___x_907_, v___y_909_);
v_fst_911_ = lean_ctor_get(v___x_910_, 0);
if (lean_obj_tag(v_fst_911_) == 1)
{
lean_object* v_snd_912_; lean_object* v_val_913_; lean_object* v___x_914_; uint8_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; lean_object* v___x_919_; 
lean_inc_ref(v_fst_911_);
v_snd_912_ = lean_ctor_get(v___x_910_, 1);
lean_inc(v_snd_912_);
lean_dec_ref(v___x_910_);
v_val_913_ = lean_ctor_get(v_fst_911_, 0);
lean_inc(v_val_913_);
lean_dec_ref_known(v_fst_911_, 1);
lean_inc(v___x_907_);
v___x_914_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_914_, 0, v___x_907_);
v___x_915_ = lean_unbox(v_val_913_);
lean_dec(v_val_913_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*1, v___x_915_);
v___x_916_ = lean_array_push(v_b_880_, v___x_914_);
v___x_917_ = lean_box(0);
v___x_918_ = lean_unbox(v_snd_912_);
lean_dec(v_snd_912_);
v___x_919_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_918_, v___x_878_, v___x_917_, v___x_916_);
v___y_883_ = v___x_919_;
goto v___jp_882_;
}
else
{
lean_object* v_snd_920_; lean_object* v___x_921_; uint8_t v___x_922_; lean_object* v___x_923_; 
v_snd_920_ = lean_ctor_get(v___x_910_, 1);
lean_inc(v_snd_920_);
lean_dec_ref(v___x_910_);
v___x_921_ = lean_box(0);
v___x_922_ = lean_unbox(v_snd_920_);
lean_dec(v_snd_920_);
v___x_923_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_922_, v___x_878_, v___x_921_, v_b_880_);
v___y_883_ = v___x_923_;
goto v___jp_882_;
}
}
}
v___jp_882_:
{
if (lean_obj_tag(v___y_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_896_; 
v_a_884_ = lean_ctor_get(v___y_883_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___y_883_);
if (v_isSharedCheck_896_ == 0)
{
v___x_886_ = v___y_883_;
v_isShared_887_ = v_isSharedCheck_896_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___y_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_896_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
if (lean_obj_tag(v_a_884_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; 
lean_dec(v_a_879_);
lean_dec_ref(v_text_875_);
v_a_888_ = lean_ctor_get(v_a_884_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v_a_884_, 1);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v_a_888_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_del_object(v___x_886_);
v_a_892_ = lean_ctor_get(v_a_884_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v_a_884_, 1);
v___x_893_ = lean_unsigned_to_nat(1u);
v___x_894_ = lean_nat_add(v_a_879_, v___x_893_);
lean_dec(v_a_879_);
v_a_879_ = v___x_894_;
v_b_880_ = v_a_892_;
goto _start;
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec(v_a_879_);
lean_dec_ref(v_text_875_);
v_a_897_ = lean_ctor_get(v___y_883_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___y_883_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___y_883_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___y_883_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___boxed(lean_object* v_upperBound_930_, lean_object* v_stack_931_, lean_object* v_text_932_, lean_object* v_ctx_x3f_933_, lean_object* v_requestedPos_934_, lean_object* v___x_935_, lean_object* v_a_936_, lean_object* v_b_937_, lean_object* v___y_938_){
_start:
{
uint8_t v___x_2989__boxed_939_; lean_object* v_res_940_; 
v___x_2989__boxed_939_ = lean_unbox(v___x_935_);
v_res_940_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_930_, v_stack_931_, v_text_932_, v_ctx_x3f_933_, v_requestedPos_934_, v___x_2989__boxed_939_, v_a_936_, v_b_937_);
lean_dec(v_requestedPos_934_);
lean_dec(v_ctx_x3f_933_);
lean_dec_ref(v_stack_931_);
lean_dec(v_upperBound_930_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(lean_object* v_text_944_, lean_object* v_ctx_x3f_945_, lean_object* v_cmdStx_946_, lean_object* v_tree_947_, lean_object* v_requestedPos_948_){
_start:
{
uint8_t v___x_950_; 
lean_inc_ref(v_text_944_);
v___x_950_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_944_, v_requestedPos_948_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___f_952_; uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___f_956_; lean_object* v_stack_x3f_957_; 
v___x_951_ = lean_box(v___x_950_);
v___f_952_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_952_, 0, v___x_951_);
v___x_953_ = 1;
v___x_954_ = lean_box(v___x_953_);
v___x_955_ = lean_box(v___x_950_);
lean_inc(v_requestedPos_948_);
v___f_956_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed), 4, 3);
lean_closure_set(v___f_956_, 0, v___x_954_);
lean_closure_set(v___f_956_, 1, v_requestedPos_948_);
lean_closure_set(v___f_956_, 2, v___x_955_);
v_stack_x3f_957_ = l_Lean_Syntax_findStack_x3f(v_cmdStx_946_, v___f_956_, v___f_952_);
if (lean_obj_tag(v_stack_x3f_957_) == 1)
{
lean_object* v_val_958_; lean_object* v___f_959_; lean_object* v___x_960_; size_t v_sz_961_; size_t v___x_962_; lean_object* v_stack_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_candidates_966_; lean_object* v___x_967_; 
v_val_958_ = lean_ctor_get(v_stack_x3f_957_, 0);
lean_inc(v_val_958_);
lean_dec_ref_known(v_stack_x3f_957_, 1);
v___f_959_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0));
v___x_960_ = lean_array_mk(v_val_958_);
v_sz_961_ = lean_array_size(v___x_960_);
v___x_962_ = ((size_t)0ULL);
v_stack_963_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v_sz_961_, v___x_962_, v___x_960_);
v___x_964_ = lean_array_get_size(v_stack_963_);
v___x_965_ = lean_unsigned_to_nat(0u);
v_candidates_966_ = ((lean_object*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1));
v___x_967_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v___x_964_, v_stack_963_, v_text_944_, v_ctx_x3f_945_, v_requestedPos_948_, v___x_950_, v___x_965_, v_candidates_966_);
lean_dec(v_requestedPos_948_);
lean_dec_ref(v_stack_963_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___y_973_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = lean_array_to_list(v_a_968_);
v___x_970_ = l_List_mergeSort___redArg(v___x_969_, v___f_959_);
v___x_971_ = lean_array_mk(v___x_970_);
v___x_999_ = lean_array_get_size(v___x_971_);
v___x_1000_ = lean_nat_dec_lt(v___x_965_, v___x_999_);
if (v___x_1000_ == 0)
{
v___y_973_ = v___x_1000_;
goto v___jp_972_;
}
else
{
if (v___x_1000_ == 0)
{
v___y_973_ = v___x_1000_;
goto v___jp_972_;
}
else
{
size_t v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = lean_usize_of_nat(v___x_999_);
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v___x_971_, v___x_962_, v___x_1001_);
v___y_973_ = v___x_1002_;
goto v___jp_972_;
}
}
v___jp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; size_t v_sz_976_; lean_object* v___x_977_; 
v___x_974_ = lean_box(0);
v___x_975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0_spec__0___closed__0));
v_sz_976_ = lean_array_size(v___x_971_);
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_tree_947_, v___y_973_, v___x_950_, v___x_971_, v_sz_976_, v___x_962_, v___x_975_);
lean_dec_ref(v___x_971_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_990_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_990_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_990_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_990_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_fst_982_; 
v_fst_982_ = lean_ctor_get(v_a_978_, 0);
lean_inc(v_fst_982_);
lean_dec(v_a_978_);
if (lean_obj_tag(v_fst_982_) == 0)
{
lean_object* v___x_984_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_974_);
v___x_984_ = v___x_980_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_974_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
else
{
lean_object* v_val_986_; lean_object* v___x_988_; 
v_val_986_ = lean_ctor_get(v_fst_982_, 0);
lean_inc(v_val_986_);
lean_dec_ref_known(v_fst_982_, 1);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v_val_986_);
v___x_988_ = v___x_980_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_val_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_977_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_977_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v_tree_947_);
v_a_1003_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_967_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_967_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec(v_stack_x3f_957_);
lean_dec(v_requestedPos_948_);
lean_dec_ref(v_tree_947_);
lean_dec_ref(v_text_944_);
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec(v_requestedPos_948_);
lean_dec_ref(v_tree_947_);
lean_dec(v_cmdStx_946_);
lean_dec_ref(v_text_944_);
v___x_1013_ = lean_box(0);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___boxed(lean_object* v_text_1015_, lean_object* v_ctx_x3f_1016_, lean_object* v_cmdStx_1017_, lean_object* v_tree_1018_, lean_object* v_requestedPos_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(v_text_1015_, v_ctx_x3f_1016_, v_cmdStx_1017_, v_tree_1018_, v_requestedPos_1019_);
lean_dec(v_ctx_x3f_1016_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(lean_object* v_upperBound_1022_, lean_object* v_stack_1023_, lean_object* v_text_1024_, lean_object* v_ctx_x3f_1025_, lean_object* v_requestedPos_1026_, uint8_t v___x_1027_, lean_object* v_inst_1028_, lean_object* v_R_1029_, lean_object* v_a_1030_, lean_object* v_b_1031_, lean_object* v_c_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_1022_, v_stack_1023_, v_text_1024_, v_ctx_x3f_1025_, v_requestedPos_1026_, v___x_1027_, v_a_1030_, v_b_1031_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___boxed(lean_object* v_upperBound_1035_, lean_object* v_stack_1036_, lean_object* v_text_1037_, lean_object* v_ctx_x3f_1038_, lean_object* v_requestedPos_1039_, lean_object* v___x_1040_, lean_object* v_inst_1041_, lean_object* v_R_1042_, lean_object* v_a_1043_, lean_object* v_b_1044_, lean_object* v_c_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v___x_3224__boxed_1047_; lean_object* v_res_1048_; 
v___x_3224__boxed_1047_ = lean_unbox(v___x_1040_);
v_res_1048_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(v_upperBound_1035_, v_stack_1036_, v_text_1037_, v_ctx_x3f_1038_, v_requestedPos_1039_, v___x_3224__boxed_1047_, v_inst_1041_, v_R_1042_, v_a_1043_, v_b_1044_, v_c_1045_);
lean_dec(v_requestedPos_1039_);
lean_dec(v_ctx_x3f_1038_);
lean_dec_ref(v_stack_1036_);
lean_dec(v_upperBound_1035_);
return v_res_1048_;
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
