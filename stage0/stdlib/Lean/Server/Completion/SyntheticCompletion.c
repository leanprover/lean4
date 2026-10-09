// Lean compiler output
// Module: Lean.Server.Completion.SyntheticCompletion
// Imports: public import Lean.Elab.InfoTree.Util public import Lean.Server.Completion.CompletionUtils
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
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTrailingSize(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lineStart(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Info_pos_x3f(lean_object*);
lean_object* l_Lean_Elab_Info_tailPos_x3f(lean_object*);
lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
uint8_t l_Lean_Elab_Info_isSmaller(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_lctx(lean_object*);
uint8_t l_Lean_LocalContext_isEmpty(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Info_occursInOrOnBoundary(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
lean_object* l_Lean_Elab_Info_stx(lean_object*);
lean_object* l_Lean_Syntax_findStack_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Elab.InfoTree.Util.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.InfoTree.Util"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__2(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1___boxed(lean_object*);
static const lean_string_object l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__0 = (const lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__0_value;
static const lean_ctor_object l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1 = (const lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1_value;
static const lean_string_object l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2 = (const lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value;
static const lean_string_object l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3 = (const lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value;
static const lean_string_object l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__4 = (const lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__4_value;
static const lean_string_object l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "completion"};
static const lean_object* l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__5 = (const lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__5_value;
static const lean_ctor_object l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value_aux_0),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value_aux_1),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value_aux_2),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(231, 49, 5, 252, 150, 235, 247, 237)}};
static const lean_object* l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6 = (const lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(lean_object*);
static const lean_string_object l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__0 = (const lean_object*)&l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__0_value;
static const lean_ctor_object l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value_aux_0),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value_aux_1),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value_aux_2),((lean_object*)&l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1 = (const lean_object*)&l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value;
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_0),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeqBracketed"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__3 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_0),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 80, 121, 250, 245, 54, 71, 145)}};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty___boxed(lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_0),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go___closed__0_value;
static const lean_ctor_object l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0 = (const lean_object*)&l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f(lean_object*);
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_0),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_1),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticFieldCompletion_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_Completion_findSyntheticCompletions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_Completion_findSyntheticCompletions___closed__0 = (const lean_object*)&l_Lean_Server_Completion_findSyntheticCompletions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findSyntheticCompletions(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(lean_object* v_gt_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
if (lean_obj_tag(v_a_2_) == 0)
{
uint8_t v___x_4_; 
lean_dec(v_b_3_);
lean_dec_ref(v_gt_1_);
v___x_4_ = 0;
return v___x_4_;
}
else
{
if (lean_obj_tag(v_b_3_) == 0)
{
uint8_t v___x_5_; 
lean_dec_ref_known(v_a_2_, 1);
lean_dec_ref(v_gt_1_);
v___x_5_ = 1;
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v_val_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v_val_6_ = lean_ctor_get(v_a_2_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_a_2_, 1);
v_val_7_ = lean_ctor_get(v_b_3_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v_b_3_, 1);
v___x_8_ = lean_apply_2(v_gt_1_, v_val_6_, v_val_7_);
v___x_9_ = lean_unbox(v___x_8_);
return v___x_9_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_gt_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_b_3_ = stack[2].m_obj;
uint8_t v_res_10_;
v_res_10_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(v_gt_1_, v_a_2_, v_b_3_);
stack->m_num = v_res_10_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg___boxed(lean_object* v_gt_11_, lean_object* v_a_12_, lean_object* v_b_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(v_gt_11_, v_a_12_, v_b_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter(lean_object* v_00_u03b1_16_, lean_object* v_gt_17_, lean_object* v_a_18_, lean_object* v_b_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(v_gt_17_, v_a_18_, v_b_19_);
return v___x_20_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter_0interp(lean_interpreter_value* stack)
{
lean_object* v_gt_17_ = stack[1].m_obj;
lean_object* v_a_18_ = stack[2].m_obj;
lean_object* v_b_19_ = stack[3].m_obj;
uint8_t v_res_21_;
v_res_21_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter(lean_box(0), v_gt_17_, v_a_18_, v_b_19_);
stack->m_num = v_res_21_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___boxed(lean_object* v_00_u03b1_22_, lean_object* v_gt_23_, lean_object* v_a_24_, lean_object* v_b_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter(v_00_u03b1_22_, v_gt_23_, v_a_24_, v_b_25_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__0___redArg(lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
if (lean_obj_tag(v_a_28_) == 0)
{
lean_object* v___x_30_; 
v___x_30_ = l_List_reverse___redArg(v_a_29_);
return v___x_30_;
}
else
{
lean_object* v_head_31_; lean_object* v_tail_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_44_; 
v_head_31_ = lean_ctor_get(v_a_28_, 0);
v_tail_32_ = lean_ctor_get(v_a_28_, 1);
v_isSharedCheck_44_ = !lean_is_exclusive(v_a_28_);
if (v_isSharedCheck_44_ == 0)
{
v___x_34_ = v_a_28_;
v_isShared_35_ = v_isSharedCheck_44_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_tail_32_);
lean_inc(v_head_31_);
lean_dec(v_a_28_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_44_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___y_37_; 
if (lean_obj_tag(v_head_31_) == 0)
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(0);
v___y_37_ = v___x_42_;
goto v___jp_36_;
}
else
{
lean_object* v_val_43_; 
v_val_43_ = lean_ctor_get(v_head_31_, 0);
lean_inc(v_val_43_);
lean_dec_ref_known(v_head_31_, 1);
v___y_37_ = v_val_43_;
goto v___jp_36_;
}
v___jp_36_:
{
lean_object* v___x_39_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 1, v_a_29_);
lean_ctor_set(v___x_34_, 0, v___y_37_);
v___x_39_ = v___x_34_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___y_37_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v_a_29_);
v___x_39_ = v_reuseFailAlloc_41_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
v_a_28_ = v_tail_32_;
v_a_29_ = v___x_39_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__1___redArg(lean_object* v_gt_45_, lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_47_) == 0)
{
lean_dec_ref(v_gt_45_);
return v_x_46_;
}
else
{
lean_object* v_head_48_; lean_object* v_tail_49_; uint8_t v___x_50_; 
v_head_48_ = lean_ctor_get(v_x_47_, 0);
lean_inc_n(v_head_48_, 2);
v_tail_49_ = lean_ctor_get(v_x_47_, 1);
lean_inc(v_tail_49_);
lean_dec_ref_known(v_x_47_, 2);
lean_inc(v_x_46_);
lean_inc_ref(v_gt_45_);
v___x_50_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(v_gt_45_, v_x_46_, v_head_48_);
if (v___x_50_ == 0)
{
lean_dec(v_x_46_);
v_x_46_ = v_head_48_;
v_x_47_ = v_tail_49_;
goto _start;
}
else
{
lean_dec(v_head_48_);
v_x_47_ = v_tail_49_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose___redArg(lean_object* v_gt_53_, lean_object* v_f_54_, lean_object* v_ctx_55_, lean_object* v_info_56_, lean_object* v_cs_57_, lean_object* v_childValues_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v_bestChildValue_62_; lean_object* v___x_63_; 
v___x_59_ = lean_box(0);
v___x_60_ = lean_box(0);
v___x_61_ = l_List_mapTR_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__0___redArg(v_childValues_58_, v___x_60_);
lean_inc_ref(v_gt_53_);
v_bestChildValue_62_ = l_List_foldl___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__1___redArg(v_gt_53_, v___x_59_, v___x_61_);
v___x_63_ = lean_apply_3(v_f_54_, v_ctx_55_, v_info_56_, v_cs_57_);
if (lean_obj_tag(v___x_63_) == 1)
{
uint8_t v___x_64_; 
lean_inc(v_bestChildValue_62_);
lean_inc_ref(v___x_63_);
v___x_64_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(v_gt_53_, v___x_63_, v_bestChildValue_62_);
if (v___x_64_ == 0)
{
lean_dec_ref_known(v___x_63_, 1);
return v_bestChildValue_62_;
}
else
{
lean_dec(v_bestChildValue_62_);
return v___x_63_;
}
}
else
{
lean_dec(v___x_63_);
lean_dec_ref(v_gt_53_);
return v_bestChildValue_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose(lean_object* v_00_u03b1_65_, lean_object* v_gt_66_, lean_object* v_f_67_, lean_object* v_ctx_68_, lean_object* v_info_69_, lean_object* v_cs_70_, lean_object* v_childValues_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose___redArg(v_gt_66_, v_f_67_, v_ctx_68_, v_info_69_, v_cs_70_, v_childValues_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__0(lean_object* v_00_u03b1_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_List_mapTR_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__0___redArg(v_a_74_, v_a_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__1(lean_object* v_00_u03b1_77_, lean_object* v_gt_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_List_foldl___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__1___redArg(v_gt_78_, v_x_79_, v_x_80_);
return v___x_81_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0(lean_object* v_x_82_, lean_object* v_x_83_, lean_object* v_x_84_){
_start:
{
uint8_t v___x_85_; 
v___x_85_ = 1;
return v___x_85_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_82_ = stack[0].m_obj;
lean_object* v_x_83_ = stack[1].m_obj;
lean_object* v_x_84_ = stack[2].m_obj;
uint8_t v_res_86_;
v_res_86_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0(v_x_82_, v_x_83_, v_x_84_);
stack->m_num = v_res_86_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0___boxed(lean_object* v_x_87_, lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0(v_x_87_, v_x_88_, v_x_89_);
lean_dec_ref(v_x_89_);
lean_dec_ref(v_x_88_);
lean_dec_ref(v_x_87_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(lean_object* v_msg_99_){
_start:
{
lean_object* v___f_100_; lean_object* v___f_101_; lean_object* v___f_102_; lean_object* v___f_103_; lean_object* v___f_104_; lean_object* v___f_105_; lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___f_100_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0));
v___f_101_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1));
v___f_102_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2));
v___f_103_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3));
v___f_104_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4));
v___f_105_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5));
v___f_106_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6));
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v___f_100_);
lean_ctor_set(v___x_107_, 1, v___f_101_);
v___x_108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___f_102_);
lean_ctor_set(v___x_108_, 2, v___f_103_);
lean_ctor_set(v___x_108_, 3, v___f_104_);
lean_ctor_set(v___x_108_, 4, v___f_105_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___f_106_);
v___x_110_ = lean_box(0);
v___x_111_ = l_instInhabitedOfMonad___redArg(v___x_109_, v___x_110_);
v___x_112_ = lean_panic_fn_borrowed(v___x_111_, v_msg_99_);
lean_dec(v___x_111_);
return v___x_112_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_116_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__2));
v___x_117_ = lean_unsigned_to_nat(21u);
v___x_118_ = lean_unsigned_to_nat(65u);
v___x_119_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__1));
v___x_120_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__0));
v___x_121_ = l_mkPanicMessageWithDecl(v___x_120_, v___x_119_, v___x_118_, v___x_117_, v___x_116_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(lean_object* v_preNode_122_, lean_object* v_postNode_123_, lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
switch(lean_obj_tag(v_x_125_))
{
case 0:
{
lean_object* v_i_126_; lean_object* v_t_127_; lean_object* v___x_128_; 
v_i_126_ = lean_ctor_get(v_x_125_, 0);
lean_inc_ref(v_i_126_);
v_t_127_ = lean_ctor_get(v_x_125_, 1);
lean_inc_ref(v_t_127_);
lean_dec_ref_known(v_x_125_, 2);
v___x_128_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_126_, v_x_124_);
v_x_124_ = v___x_128_;
v_x_125_ = v_t_127_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_124_) == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec_ref_known(v_x_125_, 2);
lean_dec(v_postNode_123_);
lean_dec_ref(v_preNode_122_);
v___x_130_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3);
v___x_131_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(v___x_130_);
return v___x_131_;
}
else
{
lean_object* v_i_132_; lean_object* v_children_133_; lean_object* v_val_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_i_132_ = lean_ctor_get(v_x_125_, 0);
lean_inc_ref_n(v_i_132_, 2);
v_children_133_ = lean_ctor_get(v_x_125_, 1);
lean_inc_ref_n(v_children_133_, 2);
lean_dec_ref_known(v_x_125_, 2);
v_val_134_ = lean_ctor_get(v_x_124_, 0);
lean_inc_n(v_val_134_, 2);
lean_inc_ref(v_preNode_122_);
v___x_135_ = lean_apply_3(v_preNode_122_, v_val_134_, v_i_132_, v_children_133_);
v___x_136_ = lean_unbox(v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_145_; 
lean_dec_ref(v_preNode_122_);
v_isSharedCheck_145_ = !lean_is_exclusive(v_x_124_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v_x_124_, 0);
lean_dec(v_unused_146_);
v___x_138_ = v_x_124_;
v_isShared_139_ = v_isSharedCheck_145_;
goto v_resetjp_137_;
}
else
{
lean_dec(v_x_124_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_145_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_140_ = lean_box(0);
v___x_141_ = lean_apply_4(v_postNode_123_, v_val_134_, v_i_132_, v_children_133_, v___x_140_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_141_);
v___x_143_ = v___x_138_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_147_ = l_Lean_Elab_Info_updateContext_x3f(v_x_124_, v_i_132_);
v___x_148_ = l_Lean_PersistentArray_toList___redArg(v_children_133_);
v___x_149_ = lean_box(0);
lean_inc(v_postNode_123_);
v___x_150_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(v_preNode_122_, v_postNode_123_, v___x_147_, v___x_148_, v___x_149_);
v___x_151_ = lean_apply_4(v_postNode_123_, v_val_134_, v_i_132_, v_children_133_, v___x_150_);
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
}
default: 
{
lean_object* v___x_153_; 
lean_dec_ref_known(v_x_125_, 1);
lean_dec(v_x_124_);
lean_dec(v_postNode_123_);
lean_dec_ref(v_preNode_122_);
v___x_153_ = lean_box(0);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(lean_object* v_preNode_154_, lean_object* v_postNode_155_, lean_object* v___x_156_, lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_object* v___x_159_; 
lean_dec(v___x_156_);
lean_dec(v_postNode_155_);
lean_dec_ref(v_preNode_154_);
v___x_159_ = l_List_reverse___redArg(v_x_158_);
return v___x_159_;
}
else
{
lean_object* v_head_160_; lean_object* v_tail_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_170_; 
v_head_160_ = lean_ctor_get(v_x_157_, 0);
v_tail_161_ = lean_ctor_get(v_x_157_, 1);
v_isSharedCheck_170_ = !lean_is_exclusive(v_x_157_);
if (v_isSharedCheck_170_ == 0)
{
v___x_163_ = v_x_157_;
v_isShared_164_ = v_isSharedCheck_170_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_tail_161_);
lean_inc(v_head_160_);
lean_dec(v_x_157_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_170_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_167_; 
lean_inc(v___x_156_);
lean_inc(v_postNode_155_);
lean_inc_ref(v_preNode_154_);
v___x_165_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v_preNode_154_, v_postNode_155_, v___x_156_, v_head_160_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 1, v_x_158_);
lean_ctor_set(v___x_163_, 0, v___x_165_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_x_158_);
v___x_167_ = v_reuseFailAlloc_169_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
v_x_157_ = v_tail_161_;
v_x_158_ = v___x_167_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(lean_object* v_infoTree_172_, lean_object* v_gt_173_, lean_object* v_f_174_){
_start:
{
lean_object* v___f_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___f_175_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___closed__0));
v___x_176_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose), 7, 3);
lean_closure_set(v___x_176_, 0, lean_box(0));
lean_closure_set(v___x_176_, 1, v_gt_173_);
lean_closure_set(v___x_176_, 2, v_f_174_);
v___x_177_ = lean_box(0);
v___x_178_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v___f_175_, v___x_176_, v___x_177_, v_infoTree_172_);
if (lean_obj_tag(v___x_178_) == 0)
{
return v___x_177_;
}
else
{
lean_object* v_val_179_; 
v_val_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_val_179_);
lean_dec_ref_known(v___x_178_, 1);
return v_val_179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f(lean_object* v_00_u03b1_180_, lean_object* v_infoTree_181_, lean_object* v_gt_182_, lean_object* v_f_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(v_infoTree_181_, v_gt_182_, v_f_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0(lean_object* v_00_u03b1_185_, lean_object* v_msg_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(v_msg_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0(lean_object* v_00_u03b1_188_, lean_object* v_preNode_189_, lean_object* v_postNode_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v_preNode_189_, v_postNode_190_, v_x_191_, v_x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1(lean_object* v_00_u03b1_194_, lean_object* v_preNode_195_, lean_object* v_postNode_196_, lean_object* v___x_197_, lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(v_preNode_195_, v_postNode_196_, v___x_197_, v_x_198_, v_x_199_);
return v___x_200_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter(lean_object* v_a_201_, lean_object* v_b_202_){
_start:
{
lean_object* v_snd_203_; lean_object* v_snd_204_; uint8_t v___y_206_; uint8_t v___y_207_; uint8_t v___y_208_; lean_object* v___x_211_; uint8_t v___x_212_; uint8_t v___y_214_; 
v_snd_203_ = lean_ctor_get(v_a_201_, 1);
v_snd_204_ = lean_ctor_get(v_b_202_, 1);
v___x_211_ = l_Lean_Elab_Info_lctx(v_snd_203_);
v___x_212_ = l_Lean_LocalContext_isEmpty(v___x_211_);
lean_dec_ref(v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = l_Lean_Elab_Info_lctx(v_snd_204_);
v___x_219_ = l_Lean_LocalContext_isEmpty(v___x_218_);
lean_dec_ref(v___x_218_);
if (v___x_219_ == 0)
{
v___y_214_ = v___x_219_;
goto v___jp_213_;
}
else
{
return v___x_219_;
}
}
else
{
uint8_t v___x_220_; 
v___x_220_ = 0;
v___y_214_ = v___x_220_;
goto v___jp_213_;
}
v___jp_205_:
{
if (v___y_208_ == 0)
{
uint8_t v___x_209_; 
v___x_209_ = l_Lean_Elab_Info_isSmaller(v_snd_203_, v_snd_204_);
if (v___x_209_ == 0)
{
uint8_t v___x_210_; 
v___x_210_ = l_Lean_Elab_Info_isSmaller(v_snd_204_, v_snd_203_);
if (v___x_210_ == 0)
{
return v___x_210_;
}
else
{
return v___x_209_;
}
}
else
{
return v___y_207_;
}
}
else
{
return v___y_206_;
}
}
v___jp_213_:
{
uint8_t v___x_215_; 
v___x_215_ = 1;
if (v___x_212_ == 0)
{
v___y_206_ = v___y_214_;
v___y_207_ = v___x_215_;
v___y_208_ = v___x_212_;
goto v___jp_205_;
}
else
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = l_Lean_Elab_Info_lctx(v_snd_204_);
v___x_217_ = l_Lean_LocalContext_isEmpty(v___x_216_);
lean_dec_ref(v___x_216_);
if (v___x_217_ == 0)
{
v___y_206_ = v___y_214_;
v___y_207_ = v___x_215_;
v___y_208_ = v___x_212_;
goto v___jp_205_;
}
else
{
v___y_206_ = v___y_214_;
v___y_207_ = v___x_215_;
v___y_208_ = v___y_214_;
goto v___jp_205_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_201_ = stack[0].m_obj;
lean_object* v_b_202_ = stack[1].m_obj;
uint8_t v_res_221_;
v_res_221_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter(v_a_201_, v_b_202_);
stack->m_num = v_res_221_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter___boxed(lean_object* v_a_222_, lean_object* v_b_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter(v_a_222_, v_b_223_);
lean_dec_ref(v_b_223_);
lean_dec_ref(v_a_222_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0(lean_object* v_hoverPos_226_, lean_object* v_ctx_227_, lean_object* v_info_228_, lean_object* v_x_229_){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = l_Lean_Elab_Info_occursInOrOnBoundary(v_info_228_, v_hoverPos_226_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; 
lean_dec_ref(v_info_228_);
lean_dec_ref(v_ctx_227_);
v___x_231_ = lean_box(0);
return v___x_231_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v_ctx_227_);
lean_ctor_set(v___x_232_, 1, v_info_228_);
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0___boxed(lean_object* v_hoverPos_234_, lean_object* v_ctx_235_, lean_object* v_info_236_, lean_object* v_x_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0(v_hoverPos_234_, v_ctx_235_, v_info_236_, v_x_237_);
lean_dec_ref(v_x_237_);
lean_dec(v_hoverPos_234_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f(lean_object* v_hoverPos_240_, lean_object* v_infoTree_241_){
_start:
{
lean_object* v___f_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___f_242_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_242_, 0, v_hoverPos_240_);
v___x_243_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___closed__0));
v___x_244_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(v_infoTree_241_, v___x_243_, v___f_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__2(lean_object* v_msg_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_panic_fn_borrowed(v___x_246_, v_msg_245_);
return v___x_247_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0(lean_object* v_hoverPos_248_, lean_object* v_x_249_){
_start:
{
uint8_t v___x_250_; lean_object* v___x_251_; 
v___x_250_ = 0;
v___x_251_ = l_Lean_Syntax_getRange_x3f(v_x_249_, v___x_250_);
if (lean_obj_tag(v___x_251_) == 0)
{
return v___x_250_;
}
else
{
lean_object* v_val_252_; uint8_t v___x_253_; uint8_t v___x_254_; 
v_val_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_val_252_);
lean_dec_ref_known(v___x_251_, 1);
v___x_253_ = 1;
v___x_254_ = l_Lean_Syntax_Range_contains(v_val_252_, v_hoverPos_248_, v___x_253_);
lean_dec(v_val_252_);
return v___x_254_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_hoverPos_248_ = stack[0].m_obj;
lean_object* v_x_249_ = stack[1].m_obj;
uint8_t v_res_255_;
v_res_255_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0(v_hoverPos_248_, v_x_249_);
stack->m_num = v_res_255_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0___boxed(lean_object* v_hoverPos_256_, lean_object* v_x_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0(v_hoverPos_256_, v_x_257_);
lean_dec(v_x_257_);
lean_dec(v_hoverPos_256_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1(lean_object* v_stx_260_){
_start:
{
uint8_t v___x_261_; 
v___x_261_ = l_Lean_Syntax_hasArgs(v_stx_260_);
if (v___x_261_ == 0)
{
uint8_t v___x_262_; 
v___x_262_ = 1;
return v___x_262_;
}
else
{
uint8_t v___x_263_; 
v___x_263_ = 0;
return v___x_263_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_260_ = stack[0].m_obj;
uint8_t v_res_264_;
v_res_264_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1(v_stx_260_);
stack->m_num = v_res_264_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1___boxed(lean_object* v_stx_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1(v_stx_265_);
lean_dec(v_stx_265_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(lean_object* v_x_280_){
_start:
{
if (lean_obj_tag(v_x_280_) == 0)
{
return v_x_280_;
}
else
{
lean_object* v_head_281_; lean_object* v_tail_282_; uint8_t v___y_284_; lean_object* v_fst_286_; lean_object* v___x_287_; uint8_t v___x_288_; uint8_t v___y_290_; 
v_head_281_ = lean_ctor_get(v_x_280_, 0);
v_tail_282_ = lean_ctor_get(v_x_280_, 1);
v_fst_286_ = lean_ctor_get(v_head_281_, 0);
v___x_287_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
lean_inc(v_fst_286_);
v___x_288_ = l_Lean_Syntax_isOfKind(v_fst_286_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6));
lean_inc(v_fst_286_);
v___x_293_ = l_Lean_Syntax_isOfKind(v_fst_286_, v___x_292_);
if (v___x_293_ == 0)
{
v___y_290_ = v___x_293_;
goto v___jp_289_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = l_Lean_Syntax_getArg(v_fst_286_, v___x_294_);
v___x_296_ = l_Lean_Syntax_isOfKind(v___x_295_, v___x_287_);
if (v___x_296_ == 0)
{
v___y_290_ = v___x_296_;
goto v___jp_289_;
}
else
{
v___y_284_ = v___x_288_;
goto v___jp_283_;
}
}
}
else
{
return v_x_280_;
}
v___jp_283_:
{
if (v___y_284_ == 0)
{
return v_x_280_;
}
else
{
lean_inc(v_tail_282_);
lean_dec_ref_known(v_x_280_, 2);
v_x_280_ = v_tail_282_;
goto _start;
}
}
v___jp_289_:
{
if (v___y_290_ == 0)
{
lean_inc(v_tail_282_);
lean_dec_ref_known(v_x_280_, 2);
v_x_280_ = v_tail_282_;
goto _start;
}
else
{
v___y_284_ = v___x_288_;
goto v___jp_283_;
}
}
}
}
}
uint8_t l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
uint8_t v___x_304_; 
v___x_304_ = 0;
return v___x_304_;
}
else
{
lean_object* v_head_305_; lean_object* v_tail_306_; uint8_t v___y_308_; lean_object* v_fst_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_head_305_ = lean_ctor_get(v_x_303_, 0);
lean_inc(v_head_305_);
v_tail_306_ = lean_ctor_get(v_x_303_, 1);
lean_inc(v_tail_306_);
lean_dec_ref_known(v_x_303_, 2);
v_fst_310_ = lean_ctor_get(v_head_305_, 0);
lean_inc_n(v_fst_310_, 2);
lean_dec(v_head_305_);
v___x_311_ = ((lean_object*)(l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1));
v___x_312_ = l_Lean_Syntax_isOfKind(v_fst_310_, v___x_311_);
if (v___x_312_ == 0)
{
lean_dec(v_fst_310_);
v___y_308_ = v___x_312_;
goto v___jp_307_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_314_ = l_Lean_Syntax_getArg(v_fst_310_, v___x_313_);
lean_dec(v_fst_310_);
v___x_315_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
v___x_316_ = l_Lean_Syntax_isOfKind(v___x_314_, v___x_315_);
v___y_308_ = v___x_316_;
goto v___jp_307_;
}
v___jp_307_:
{
if (v___y_308_ == 0)
{
v_x_303_ = v_tail_306_;
goto _start;
}
else
{
lean_dec(v_tail_306_);
return v___y_308_;
}
}
}
}
}
LEAN_EXPORT void l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_303_ = stack[0].m_obj;
uint8_t v_res_317_;
v_res_317_ = l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(v_x_303_);
stack->m_num = v_res_317_;
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___boxed(lean_object* v_x_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(v_x_318_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_325_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3));
v___x_326_ = lean_unsigned_to_nat(14u);
v___x_327_ = lean_unsigned_to_nat(22u);
v___x_328_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2));
v___x_329_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1));
v___x_330_ = l_mkPanicMessageWithDecl(v___x_329_, v___x_328_, v___x_327_, v___x_326_, v___x_325_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(lean_object* v_hoverPos_331_, lean_object* v_infoTree_332_){
_start:
{
lean_object* v___x_333_; 
lean_inc(v_hoverPos_331_);
v___x_333_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f(v_hoverPos_331_, v_infoTree_332_);
if (lean_obj_tag(v___x_333_) == 1)
{
lean_object* v_val_334_; lean_object* v_fst_335_; lean_object* v_snd_336_; lean_object* v___f_337_; lean_object* v___f_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_val_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_val_334_);
lean_dec_ref_known(v___x_333_, 1);
v_fst_335_ = lean_ctor_get(v_val_334_, 0);
lean_inc(v_fst_335_);
v_snd_336_ = lean_ctor_get(v_val_334_, 1);
lean_inc(v_snd_336_);
lean_dec(v_val_334_);
lean_inc(v_hoverPos_331_);
v___f_337_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_337_, 0, v_hoverPos_331_);
v___f_338_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0));
v___x_339_ = l_Lean_Elab_Info_stx(v_snd_336_);
v___x_340_ = l_Lean_Syntax_findStack_x3f(v___x_339_, v___f_337_, v___f_338_);
if (lean_obj_tag(v___x_340_) == 1)
{
lean_object* v_val_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_397_; 
v_val_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_397_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_397_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_val_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_397_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v_stack_345_; lean_object* v___x_346_; 
v_stack_345_ = l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(v_val_341_);
v___x_346_ = l_List_head_x3f___redArg(v_stack_345_);
if (lean_obj_tag(v___x_346_) == 1)
{
lean_object* v_val_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_395_; 
v_val_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_395_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_395_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_val_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_395_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v_fst_351_; lean_object* v___y_353_; uint8_t v___y_354_; lean_object* v___y_355_; lean_object* v___y_364_; uint8_t v___y_365_; lean_object* v___y_366_; uint8_t v_isDotIdCompletion_375_; lean_object* v_fst_377_; uint8_t v_snd_378_; 
v_fst_351_ = lean_ctor_get(v_val_347_, 0);
lean_inc(v_fst_351_);
lean_dec(v_val_347_);
v_isDotIdCompletion_375_ = l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(v_stack_345_);
if (v_isDotIdCompletion_375_ == 0)
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
lean_inc(v_fst_351_);
v___x_384_ = l_Lean_Syntax_isOfKind(v_fst_351_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6));
lean_inc(v_fst_351_);
v___x_386_ = l_Lean_Syntax_isOfKind(v_fst_351_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
lean_dec(v_fst_351_);
lean_del_object(v___x_349_);
lean_del_object(v___x_343_);
lean_dec(v_snd_336_);
lean_dec(v_fst_335_);
lean_dec(v_hoverPos_331_);
v___x_387_ = lean_box(0);
return v___x_387_;
}
else
{
lean_object* v___x_388_; lean_object* v_id_389_; uint8_t v___x_390_; 
v___x_388_ = lean_unsigned_to_nat(0u);
v_id_389_ = l_Lean_Syntax_getArg(v_fst_351_, v___x_388_);
lean_inc(v_id_389_);
v___x_390_ = l_Lean_Syntax_isOfKind(v_id_389_, v___x_383_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
lean_dec(v_id_389_);
lean_dec(v_fst_351_);
lean_del_object(v___x_349_);
lean_del_object(v___x_343_);
lean_dec(v_snd_336_);
lean_dec(v_fst_335_);
lean_dec(v_hoverPos_331_);
v___x_391_ = lean_box(0);
return v___x_391_;
}
else
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_TSyntax_getId(v_id_389_);
lean_dec(v_id_389_);
v_fst_377_ = v___x_392_;
v_snd_378_ = v___x_390_;
goto v___jp_376_;
}
}
}
else
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_TSyntax_getId(v_fst_351_);
v_fst_377_ = v___x_393_;
v_snd_378_ = v_isDotIdCompletion_375_;
goto v___jp_376_;
}
}
else
{
lean_object* v___x_394_; 
lean_dec(v_fst_351_);
lean_del_object(v___x_349_);
lean_del_object(v___x_343_);
lean_dec(v_snd_336_);
lean_dec(v_fst_335_);
lean_dec(v_hoverPos_331_);
v___x_394_ = lean_box(0);
return v___x_394_;
}
v___jp_352_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_356_ = l_Lean_Elab_Info_lctx(v_snd_336_);
lean_dec(v_snd_336_);
v___x_357_ = lean_box(0);
v___x_358_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_358_, 0, v_fst_351_);
lean_ctor_set(v___x_358_, 1, v___y_353_);
lean_ctor_set(v___x_358_, 2, v___x_356_);
lean_ctor_set(v___x_358_, 3, v___x_357_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*4, v___y_354_);
v___x_359_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_359_, 0, v___y_355_);
lean_ctor_set(v___x_359_, 1, v_fst_335_);
lean_ctor_set(v___x_359_, 2, v___x_358_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_359_);
v___x_361_ = v___x_349_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
v___jp_363_:
{
lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_nat_add(v_hoverPos_331_, v___x_367_);
v___x_369_ = lean_nat_dec_le(v___x_368_, v___y_366_);
lean_dec(v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
lean_dec(v___y_366_);
lean_del_object(v___x_343_);
lean_dec(v_hoverPos_331_);
v___x_370_ = lean_box(0);
v___y_353_ = v___y_364_;
v___y_354_ = v___y_365_;
v___y_355_ = v___x_370_;
goto v___jp_352_;
}
else
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = lean_nat_sub(v___y_366_, v_hoverPos_331_);
lean_dec(v_hoverPos_331_);
lean_dec(v___y_366_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_371_);
v___x_373_ = v___x_343_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
v___y_353_ = v___y_364_;
v___y_354_ = v___y_365_;
v___y_355_ = v___x_373_;
goto v___jp_352_;
}
}
}
v___jp_376_:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Syntax_getTailPos_x3f(v_fst_351_, v_isDotIdCompletion_375_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_obj_once(&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4, &l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_once, _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4);
v___x_381_ = l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__2(v___x_380_);
v___y_364_ = v_fst_377_;
v___y_365_ = v_snd_378_;
v___y_366_ = v___x_381_;
goto v___jp_363_;
}
else
{
lean_object* v_val_382_; 
v_val_382_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_val_382_);
lean_dec_ref_known(v___x_379_, 1);
v___y_364_ = v_fst_377_;
v___y_365_ = v_snd_378_;
v___y_366_ = v_val_382_;
goto v___jp_363_;
}
}
}
}
else
{
lean_object* v___x_396_; 
lean_dec(v___x_346_);
lean_dec(v_stack_345_);
lean_del_object(v___x_343_);
lean_dec(v_snd_336_);
lean_dec(v_fst_335_);
lean_dec(v_hoverPos_331_);
v___x_396_ = lean_box(0);
return v___x_396_;
}
}
}
else
{
lean_object* v___x_398_; 
lean_dec(v___x_340_);
lean_dec(v_snd_336_);
lean_dec(v_fst_335_);
lean_dec(v_hoverPos_331_);
v___x_398_ = lean_box(0);
return v___x_398_;
}
}
else
{
lean_object* v___x_399_; 
lean_dec(v___x_333_);
lean_dec(v_hoverPos_331_);
v___x_399_ = lean_box(0);
return v___x_399_;
}
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(lean_object* v_fileMap_400_, lean_object* v_hoverPos_401_){
_start:
{
lean_object* v_source_402_; uint8_t v___x_403_; 
v_source_402_ = lean_ctor_get(v_fileMap_400_, 0);
v___x_403_ = lean_string_utf8_at_end(v_source_402_, v_hoverPos_401_);
if (v___x_403_ == 0)
{
uint32_t v___x_404_; uint32_t v___x_405_; uint8_t v___x_406_; 
v___x_404_ = lean_string_utf8_get(v_source_402_, v_hoverPos_401_);
v___x_405_ = 32;
v___x_406_ = lean_uint32_dec_eq(v___x_404_, v___x_405_);
if (v___x_406_ == 0)
{
uint32_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = 9;
v___x_408_ = lean_uint32_dec_eq(v___x_404_, v___x_407_);
if (v___x_408_ == 0)
{
uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 13;
v___x_410_ = lean_uint32_dec_eq(v___x_404_, v___x_409_);
if (v___x_410_ == 0)
{
uint32_t v___x_411_; uint8_t v___x_412_; 
v___x_411_ = 10;
v___x_412_ = lean_uint32_dec_eq(v___x_404_, v___x_411_);
return v___x_412_;
}
else
{
return v___x_410_;
}
}
else
{
return v___x_408_;
}
}
else
{
return v___x_406_;
}
}
else
{
return v___x_403_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_400_ = stack[0].m_obj;
lean_object* v_hoverPos_401_ = stack[1].m_obj;
uint8_t v_res_413_;
v_res_413_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_400_, v_hoverPos_401_);
stack->m_num = v_res_413_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace___boxed(lean_object* v_fileMap_414_, lean_object* v_hoverPos_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_414_, v_hoverPos_415_);
lean_dec(v_hoverPos_415_);
lean_dec_ref(v_fileMap_414_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(lean_object* v_fileMap_418_, lean_object* v_hoverPos_419_){
_start:
{
lean_object* v_source_420_; uint8_t v___y_434_; uint8_t v___x_435_; 
v_source_420_ = lean_ctor_get(v_fileMap_418_, 0);
v___x_435_ = lean_string_utf8_at_end(v_source_420_, v_hoverPos_419_);
if (v___x_435_ == 0)
{
uint32_t v___x_436_; uint32_t v___x_437_; uint8_t v___x_438_; 
v___x_436_ = lean_string_utf8_get(v_source_420_, v_hoverPos_419_);
v___x_437_ = 32;
v___x_438_ = lean_uint32_dec_eq(v___x_436_, v___x_437_);
if (v___x_438_ == 0)
{
uint32_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = 9;
v___x_440_ = lean_uint32_dec_eq(v___x_436_, v___x_439_);
if (v___x_440_ == 0)
{
uint32_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 13;
v___x_442_ = lean_uint32_dec_eq(v___x_436_, v___x_441_);
if (v___x_442_ == 0)
{
uint32_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 10;
v___x_444_ = lean_uint32_dec_eq(v___x_436_, v___x_443_);
v___y_434_ = v___x_444_;
goto v___jp_433_;
}
else
{
goto v___jp_421_;
}
}
else
{
goto v___jp_421_;
}
}
else
{
goto v___jp_421_;
}
}
else
{
v___y_434_ = v___x_435_;
goto v___jp_433_;
}
v___jp_421_:
{
lean_object* v___x_422_; lean_object* v___x_423_; uint32_t v___x_424_; uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_sub(v_hoverPos_419_, v___x_422_);
v___x_424_ = lean_string_utf8_get(v_source_420_, v___x_423_);
lean_dec(v___x_423_);
v___x_425_ = 32;
v___x_426_ = lean_uint32_dec_eq(v___x_424_, v___x_425_);
if (v___x_426_ == 0)
{
uint32_t v___x_427_; uint8_t v___x_428_; 
v___x_427_ = 9;
v___x_428_ = lean_uint32_dec_eq(v___x_424_, v___x_427_);
if (v___x_428_ == 0)
{
uint32_t v___x_429_; uint8_t v___x_430_; 
v___x_429_ = 13;
v___x_430_ = lean_uint32_dec_eq(v___x_424_, v___x_429_);
if (v___x_430_ == 0)
{
uint32_t v___x_431_; uint8_t v___x_432_; 
v___x_431_ = 10;
v___x_432_ = lean_uint32_dec_eq(v___x_424_, v___x_431_);
return v___x_432_;
}
else
{
return v___x_430_;
}
}
else
{
return v___x_428_;
}
}
else
{
return v___x_426_;
}
}
v___jp_433_:
{
if (v___y_434_ == 0)
{
return v___y_434_;
}
else
{
goto v___jp_421_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_418_ = stack[0].m_obj;
lean_object* v_hoverPos_419_ = stack[1].m_obj;
uint8_t v_res_445_;
v_res_445_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_418_, v_hoverPos_419_);
stack->m_num = v_res_445_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace___boxed(lean_object* v_fileMap_446_, lean_object* v_hoverPos_447_){
_start:
{
uint8_t v_res_448_; lean_object* v_r_449_; 
v_res_448_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_446_, v_hoverPos_447_);
lean_dec(v_hoverPos_447_);
lean_dec_ref(v_fileMap_446_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(lean_object* v_stx_463_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
lean_inc(v_stx_463_);
v___x_464_ = l_Lean_Syntax_getKind(v_stx_463_);
v___x_465_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2));
v___x_466_ = lean_name_eq(v___x_464_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_468_ = lean_name_eq(v___x_464_, v___x_467_);
lean_dec(v___x_464_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; 
lean_dec(v_stx_463_);
v___x_469_ = lean_box(0);
return v___x_469_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = l_Lean_Syntax_getArg(v_stx_463_, v___x_470_);
lean_dec(v_stx_463_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec(v___x_464_);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = l_Lean_Syntax_getArg(v_stx_463_, v___x_473_);
lean_dec(v_stx_463_);
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(lean_object* v_fileMap_476_, lean_object* v_hoverPos_477_, lean_object* v_hoverFilePos_478_, lean_object* v_stx_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(v_stx_479_);
if (lean_obj_tag(v___x_480_) == 1)
{
lean_object* v_val_481_; uint8_t v___x_482_; lean_object* v___x_483_; 
v_val_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_val_481_);
lean_dec_ref_known(v___x_480_, 1);
v___x_482_ = 0;
v___x_483_ = l_Lean_Syntax_getPos_x3f(v_val_481_, v___x_482_);
lean_dec(v_val_481_);
if (lean_obj_tag(v___x_483_) == 1)
{
lean_object* v_val_484_; lean_object* v___x_485_; lean_object* v_column_486_; lean_object* v_column_487_; uint8_t v___x_488_; 
v_val_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_val_484_);
lean_dec_ref_known(v___x_483_, 1);
lean_inc_ref(v_fileMap_476_);
v___x_485_ = l_Lean_FileMap_toPosition(v_fileMap_476_, v_val_484_);
lean_dec(v_val_484_);
v_column_486_ = lean_ctor_get(v___x_485_, 1);
lean_inc(v_column_486_);
lean_dec_ref(v___x_485_);
v_column_487_ = lean_ctor_get(v_hoverFilePos_478_, 1);
v___x_488_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_476_, v_hoverPos_477_);
lean_dec_ref(v_fileMap_476_);
if (v___x_488_ == 0)
{
lean_dec(v_column_486_);
return v___x_488_;
}
else
{
uint8_t v_isCursorInTacticBlock_489_; 
v_isCursorInTacticBlock_489_ = lean_nat_dec_eq(v_column_487_, v_column_486_);
lean_dec(v_column_486_);
return v_isCursorInTacticBlock_489_;
}
}
else
{
lean_dec(v___x_483_);
lean_dec_ref(v_fileMap_476_);
return v___x_482_;
}
}
else
{
uint8_t v___x_490_; 
lean_dec(v___x_480_);
lean_dec_ref(v_fileMap_476_);
v___x_490_ = 0;
return v___x_490_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_476_ = stack[0].m_obj;
lean_object* v_hoverPos_477_ = stack[1].m_obj;
lean_object* v_hoverFilePos_478_ = stack[2].m_obj;
lean_object* v_stx_479_ = stack[3].m_obj;
uint8_t v_res_491_;
v_res_491_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_476_, v_hoverPos_477_, v_hoverFilePos_478_, v_stx_479_);
stack->m_num = v_res_491_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation___boxed(lean_object* v_fileMap_492_, lean_object* v_hoverPos_493_, lean_object* v_hoverFilePos_494_, lean_object* v_stx_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_492_, v_hoverPos_493_, v_hoverFilePos_494_, v_stx_495_);
lean_dec_ref(v_hoverFilePos_494_);
lean_dec(v_hoverPos_493_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(lean_object* v_hoverPos_499_, lean_object* v_as_500_, size_t v_i_501_, size_t v_stop_502_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_eq(v_i_501_, v_stop_502_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_array_uget_borrowed(v_as_500_, v_i_501_);
v___x_509_ = l_Lean_Syntax_getTailPos_x3f(v___x_508_, v___x_507_);
if (lean_obj_tag(v___x_509_) == 1)
{
lean_object* v_val_510_; uint8_t v___x_511_; uint8_t v___y_513_; lean_object* v___x_517_; uint8_t v___x_518_; 
v_val_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = 1;
v___x_517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___closed__0));
lean_inc(v___x_508_);
v___x_518_ = l_Lean_Syntax_isToken(v___x_517_, v___x_508_);
if (v___x_518_ == 0)
{
v___y_513_ = v___x_518_;
goto v___jp_512_;
}
else
{
uint8_t v___x_519_; 
v___x_519_ = lean_nat_dec_le(v_val_510_, v_hoverPos_499_);
v___y_513_ = v___x_519_;
goto v___jp_512_;
}
v___jp_512_:
{
if (v___y_513_ == 0)
{
lean_dec(v_val_510_);
goto v___jp_503_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_514_ = l_Lean_Syntax_getTrailingSize(v___x_508_);
v___x_515_ = lean_nat_add(v_val_510_, v___x_514_);
lean_dec(v___x_514_);
lean_dec(v_val_510_);
v___x_516_ = lean_nat_dec_le(v_hoverPos_499_, v___x_515_);
lean_dec(v___x_515_);
if (v___x_516_ == 0)
{
goto v___jp_503_;
}
else
{
return v___x_511_;
}
}
}
}
else
{
lean_dec(v___x_509_);
goto v___jp_503_;
}
}
else
{
uint8_t v___x_520_; 
v___x_520_ = 0;
return v___x_520_;
}
v___jp_503_:
{
size_t v___x_504_; size_t v___x_505_; 
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_add(v_i_501_, v___x_504_);
v_i_501_ = v___x_505_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_hoverPos_499_ = stack[0].m_obj;
lean_object* v_as_500_ = stack[1].m_obj;
size_t v_i_501_ = stack[2].m_num;
size_t v_stop_502_ = stack[3].m_num;
uint8_t v_res_521_;
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_499_, v_as_500_, v_i_501_, v_stop_502_);
stack->m_num = v_res_521_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___boxed(lean_object* v_hoverPos_522_, lean_object* v_as_523_, lean_object* v_i_524_, lean_object* v_stop_525_){
_start:
{
size_t v_i_boxed_526_; size_t v_stop_boxed_527_; uint8_t v_res_528_; lean_object* v_r_529_; 
v_i_boxed_526_ = lean_unbox_usize(v_i_524_);
lean_dec(v_i_524_);
v_stop_boxed_527_ = lean_unbox_usize(v_stop_525_);
lean_dec(v_stop_525_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_522_, v_as_523_, v_i_boxed_526_, v_stop_boxed_527_);
lean_dec_ref(v_as_523_);
lean_dec(v_hoverPos_522_);
v_r_529_ = lean_box(v_res_528_);
return v_r_529_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(lean_object* v_fileMap_530_, lean_object* v_hoverPos_531_, lean_object* v_stx_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(v_stx_532_);
if (lean_obj_tag(v___x_533_) == 1)
{
lean_object* v_val_534_; uint8_t v___x_535_; 
v_val_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_val_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_530_, v_hoverPos_531_);
if (v___x_535_ == 0)
{
lean_dec(v_val_534_);
return v___x_535_;
}
else
{
lean_object* v_tactics_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_tactics_536_ = l_Lean_Syntax_getArgs(v_val_534_);
lean_dec(v_val_534_);
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = lean_array_get_size(v_tactics_536_);
v___x_539_ = lean_nat_dec_lt(v___x_537_, v___x_538_);
if (v___x_539_ == 0)
{
lean_dec_ref(v_tactics_536_);
return v___x_539_;
}
else
{
if (v___x_539_ == 0)
{
lean_dec_ref(v_tactics_536_);
return v___x_539_;
}
else
{
size_t v___x_540_; size_t v___x_541_; uint8_t v___x_542_; 
v___x_540_ = ((size_t)0ULL);
v___x_541_ = lean_usize_of_nat(v___x_538_);
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_531_, v_tactics_536_, v___x_540_, v___x_541_);
lean_dec_ref(v_tactics_536_);
return v___x_542_;
}
}
}
}
else
{
uint8_t v___x_543_; 
lean_dec(v___x_533_);
v___x_543_ = 0;
return v___x_543_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_530_ = stack[0].m_obj;
lean_object* v_hoverPos_531_ = stack[1].m_obj;
lean_object* v_stx_532_ = stack[2].m_obj;
uint8_t v_res_544_;
v_res_544_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_530_, v_hoverPos_531_, v_stx_532_);
stack->m_num = v_res_544_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon___boxed(lean_object* v_fileMap_545_, lean_object* v_hoverPos_546_, lean_object* v_stx_547_){
_start:
{
uint8_t v_res_548_; lean_object* v_r_549_; 
v_res_548_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_545_, v_hoverPos_546_, v_stx_547_);
lean_dec(v_hoverPos_546_);
lean_dec_ref(v_fileMap_545_);
v_r_549_ = lean_box(v_res_548_);
return v_r_549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(lean_object* v_fileMap_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_fst_552_; lean_object* v_snd_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_575_; 
v_fst_552_ = lean_ctor_get(v_a_551_, 0);
v_snd_553_ = lean_ctor_get(v_a_551_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_a_551_);
if (v_isSharedCheck_575_ == 0)
{
v___x_555_ = v_a_551_;
v_isShared_556_ = v_isSharedCheck_575_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_snd_553_);
lean_inc(v_fst_552_);
lean_dec(v_a_551_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_575_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v_source_557_; uint8_t v___x_558_; 
v_source_557_ = lean_ctor_get(v_fileMap_550_, 0);
v___x_558_ = lean_string_utf8_at_end(v_source_557_, v_fst_552_);
if (v___x_558_ == 0)
{
uint32_t v___x_559_; uint32_t v___x_560_; uint8_t v___x_561_; 
v___x_559_ = lean_string_utf8_get(v_source_557_, v_fst_552_);
v___x_560_ = 32;
v___x_561_ = lean_uint32_dec_eq(v___x_559_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_563_; 
if (v_isShared_556_ == 0)
{
v___x_563_ = v___x_555_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_fst_552_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_snd_553_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_565_ = lean_string_utf8_next(v_source_557_, v_fst_552_);
lean_dec(v_fst_552_);
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = lean_nat_add(v_snd_553_, v___x_566_);
lean_dec(v_snd_553_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v___x_567_);
lean_ctor_set(v___x_555_, 0, v___x_565_);
v___x_569_ = v___x_555_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_567_);
v___x_569_ = v_reuseFailAlloc_571_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
v_a_551_ = v___x_569_;
goto _start;
}
}
}
else
{
lean_object* v___x_573_; 
if (v_isShared_556_ == 0)
{
v___x_573_ = v___x_555_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_fst_552_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_snd_553_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg___boxed(lean_object* v_fileMap_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_576_, v_a_577_);
lean_dec_ref(v_fileMap_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(lean_object* v_fileMap_579_, lean_object* v_pos_580_){
_start:
{
lean_object* v_n_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v_snd_584_; 
v_n_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v_pos_580_);
lean_ctor_set(v___x_582_, 1, v_n_581_);
v___x_583_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_579_, v___x_582_);
v_snd_584_ = lean_ctor_get(v___x_583_, 1);
lean_inc(v_snd_584_);
lean_dec_ref(v___x_583_);
return v_snd_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces___boxed(lean_object* v_fileMap_585_, lean_object* v_pos_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(v_fileMap_585_, v_pos_586_);
lean_dec_ref(v_fileMap_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(lean_object* v_fileMap_588_, lean_object* v_inst_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_588_, v_a_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___boxed(lean_object* v_fileMap_592_, lean_object* v_inst_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(v_fileMap_592_, v_inst_593_, v_a_594_);
lean_dec_ref(v_fileMap_592_);
return v_res_595_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(lean_object* v_fileMap_596_, lean_object* v_hoverPos_597_, lean_object* v_leadingTokenTailPos_x3f_598_){
_start:
{
if (lean_obj_tag(v_leadingTokenTailPos_x3f_598_) == 1)
{
lean_object* v_val_599_; lean_object* v_hoverFilePos_600_; lean_object* v_line_601_; lean_object* v_column_602_; lean_object* v_tokenTailFilePos_603_; lean_object* v_line_604_; uint8_t v___x_605_; 
v_val_599_ = lean_ctor_get(v_leadingTokenTailPos_x3f_598_, 0);
lean_inc_ref_n(v_fileMap_596_, 2);
v_hoverFilePos_600_ = l_Lean_FileMap_toPosition(v_fileMap_596_, v_hoverPos_597_);
v_line_601_ = lean_ctor_get(v_hoverFilePos_600_, 0);
lean_inc(v_line_601_);
v_column_602_ = lean_ctor_get(v_hoverFilePos_600_, 1);
lean_inc(v_column_602_);
lean_dec_ref(v_hoverFilePos_600_);
v_tokenTailFilePos_603_ = l_Lean_FileMap_toPosition(v_fileMap_596_, v_val_599_);
v_line_604_ = lean_ctor_get(v_tokenTailFilePos_603_, 0);
lean_inc(v_line_604_);
lean_dec_ref(v_tokenTailFilePos_603_);
v___x_605_ = lean_nat_dec_eq(v_line_601_, v_line_604_);
lean_dec(v_line_601_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v_expectedColumn_609_; uint8_t v___x_610_; 
v___x_606_ = l_Lean_FileMap_lineStart(v_fileMap_596_, v_line_604_);
lean_dec(v_line_604_);
v___x_607_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(v_fileMap_596_, v___x_606_);
lean_dec_ref(v_fileMap_596_);
v___x_608_ = lean_unsigned_to_nat(2u);
v_expectedColumn_609_ = lean_nat_add(v___x_607_, v___x_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_nat_dec_eq(v_column_602_, v_expectedColumn_609_);
lean_dec(v_expectedColumn_609_);
lean_dec(v_column_602_);
return v___x_610_;
}
else
{
uint8_t v___x_611_; 
lean_dec(v_line_604_);
lean_dec(v_column_602_);
lean_dec_ref(v_fileMap_596_);
v___x_611_ = lean_nat_dec_le(v_val_599_, v_hoverPos_597_);
return v___x_611_;
}
}
else
{
uint8_t v___x_612_; 
lean_dec_ref(v_fileMap_596_);
v___x_612_ = 1;
return v___x_612_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_596_ = stack[0].m_obj;
lean_object* v_hoverPos_597_ = stack[1].m_obj;
lean_object* v_leadingTokenTailPos_x3f_598_ = stack[2].m_obj;
uint8_t v_res_613_;
v_res_613_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(v_fileMap_596_, v_hoverPos_597_, v_leadingTokenTailPos_x3f_598_);
stack->m_num = v_res_613_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation___boxed(lean_object* v_fileMap_614_, lean_object* v_hoverPos_615_, lean_object* v_leadingTokenTailPos_x3f_616_){
_start:
{
uint8_t v_res_617_; lean_object* v_r_618_; 
v_res_617_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(v_fileMap_614_, v_hoverPos_615_, v_leadingTokenTailPos_x3f_616_);
lean_dec(v_leadingTokenTailPos_x3f_616_);
lean_dec(v_hoverPos_615_);
v_r_618_ = lean_box(v_res_617_);
return v_r_618_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(lean_object* v_a_619_){
_start:
{
switch(lean_obj_tag(v_a_619_))
{
case 0:
{
uint8_t v___x_620_; 
v___x_620_ = 1;
return v___x_620_;
}
case 1:
{
lean_object* v_args_621_; lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_args_621_ = lean_ctor_get(v_a_619_, 2);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_array_get_size(v_args_621_);
v___x_624_ = lean_nat_dec_lt(v___x_622_, v___x_623_);
if (v___x_624_ == 0)
{
uint8_t v___x_625_; 
v___x_625_ = 1;
return v___x_625_;
}
else
{
if (v___x_624_ == 0)
{
return v___x_624_;
}
else
{
size_t v___x_626_; size_t v___x_627_; uint8_t v___x_628_; 
v___x_626_ = ((size_t)0ULL);
v___x_627_ = lean_usize_of_nat(v___x_623_);
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_args_621_, v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
return v___x_624_;
}
else
{
uint8_t v___x_629_; 
v___x_629_ = 0;
return v___x_629_;
}
}
}
}
default: 
{
uint8_t v___x_630_; 
v___x_630_ = 0;
return v___x_630_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_619_ = stack[0].m_obj;
uint8_t v_res_631_;
v_res_631_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_a_619_);
stack->m_num = v_res_631_;
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(lean_object* v_as_632_, size_t v_i_633_, size_t v_stop_634_){
_start:
{
uint8_t v___x_635_; 
v___x_635_ = lean_usize_dec_eq(v_i_633_, v_stop_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = lean_array_uget_borrowed(v_as_632_, v_i_633_);
v___x_637_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v___x_636_);
if (v___x_637_ == 0)
{
uint8_t v___x_638_; 
v___x_638_ = 1;
return v___x_638_;
}
else
{
size_t v___x_639_; size_t v___x_640_; 
v___x_639_ = ((size_t)1ULL);
v___x_640_ = lean_usize_add(v_i_633_, v___x_639_);
v_i_633_ = v___x_640_;
goto _start;
}
}
else
{
uint8_t v___x_642_; 
v___x_642_ = 0;
return v___x_642_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_632_ = stack[0].m_obj;
size_t v_i_633_ = stack[1].m_num;
size_t v_stop_634_ = stack[2].m_num;
uint8_t v_res_643_;
v_res_643_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_as_632_, v_i_633_, v_stop_634_);
stack->m_num = v_res_643_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0___boxed(lean_object* v_as_644_, lean_object* v_i_645_, lean_object* v_stop_646_){
_start:
{
size_t v_i_boxed_647_; size_t v_stop_boxed_648_; uint8_t v_res_649_; lean_object* v_r_650_; 
v_i_boxed_647_ = lean_unbox_usize(v_i_645_);
lean_dec(v_i_645_);
v_stop_boxed_648_ = lean_unbox_usize(v_stop_646_);
lean_dec(v_stop_646_);
v_res_649_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_as_644_, v_i_boxed_647_, v_stop_boxed_648_);
lean_dec_ref(v_as_644_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty___boxed(lean_object* v_a_651_){
_start:
{
uint8_t v_res_652_; lean_object* v_r_653_; 
v_res_652_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_a_651_);
lean_dec(v_a_651_);
v_r_653_ = lean_box(v_res_652_);
return v_r_653_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(lean_object* v_stx_660_){
_start:
{
uint8_t v___y_662_; uint8_t v___y_670_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
lean_inc(v_stx_660_);
v___x_675_ = l_Lean_Syntax_getKind(v_stx_660_);
v___x_676_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1));
v___x_677_ = lean_name_eq(v___x_675_, v___x_676_);
lean_dec(v___x_675_);
if (v___x_677_ == 0)
{
v___y_670_ = v___x_677_;
goto v___jp_669_;
}
else
{
uint8_t v___x_678_; 
v___x_678_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_stx_660_);
v___y_670_ = v___x_678_;
goto v___jp_669_;
}
v___jp_661_:
{
if (v___y_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
lean_inc(v_stx_660_);
v___x_663_ = l_Lean_Syntax_getKind(v_stx_660_);
v___x_664_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_665_ = lean_name_eq(v___x_663_, v___x_664_);
lean_dec(v___x_663_);
if (v___x_665_ == 0)
{
lean_dec(v_stx_660_);
return v___x_665_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = l_Lean_Syntax_getArg(v_stx_660_, v___x_666_);
lean_dec(v_stx_660_);
v___x_668_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v___x_667_);
lean_dec(v___x_667_);
return v___x_668_;
}
}
else
{
lean_dec(v_stx_660_);
return v___y_662_;
}
}
v___jp_669_:
{
if (v___y_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
lean_inc(v_stx_660_);
v___x_671_ = l_Lean_Syntax_getKind(v_stx_660_);
v___x_672_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2));
v___x_673_ = lean_name_eq(v___x_671_, v___x_672_);
lean_dec(v___x_671_);
if (v___x_673_ == 0)
{
v___y_662_ = v___x_673_;
goto v___jp_661_;
}
else
{
uint8_t v___x_674_; 
v___x_674_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_stx_660_);
v___y_662_ = v___x_674_;
goto v___jp_661_;
}
}
else
{
lean_dec(v_stx_660_);
return v___y_670_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_660_ = stack[0].m_obj;
uint8_t v_res_679_;
v_res_679_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_660_);
stack->m_num = v_res_679_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___boxed(lean_object* v_stx_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_680_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(lean_object* v_fileMap_683_, lean_object* v_hoverPos_684_, lean_object* v_stx_685_, lean_object* v_leadingTokenTailPos_x3f_686_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_683_, v_hoverPos_684_);
if (v___x_687_ == 0)
{
lean_dec(v_stx_685_);
lean_dec_ref(v_fileMap_683_);
return v___x_687_;
}
else
{
uint8_t v___x_688_; uint8_t v___x_689_; 
v___x_688_ = 0;
lean_inc(v_stx_685_);
v___x_689_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_685_);
if (v___x_689_ == 0)
{
lean_dec(v_stx_685_);
lean_dec_ref(v_fileMap_683_);
return v___x_688_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
lean_inc(v_stx_685_);
v___x_690_ = l_Lean_Syntax_getKind(v_stx_685_);
v___x_691_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_692_ = lean_name_eq(v___x_690_, v___x_691_);
lean_dec(v___x_690_);
if (v___x_692_ == 0)
{
uint8_t v___x_693_; 
lean_dec(v_stx_685_);
v___x_693_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(v_fileMap_683_, v_hoverPos_684_, v_leadingTokenTailPos_x3f_686_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec_ref(v_fileMap_683_);
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = l_Lean_Syntax_getArg(v_stx_685_, v___x_694_);
v___x_696_ = l_Lean_Syntax_getTailPos_x3f(v___x_695_, v___x_688_);
lean_dec(v___x_695_);
if (lean_obj_tag(v___x_696_) == 1)
{
lean_object* v_val_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_val_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_val_697_);
lean_dec_ref_known(v___x_696_, 1);
v___x_698_ = lean_unsigned_to_nat(2u);
v___x_699_ = l_Lean_Syntax_getArg(v_stx_685_, v___x_698_);
lean_dec(v_stx_685_);
v___x_700_ = l_Lean_Syntax_getPos_x3f(v___x_699_, v___x_688_);
lean_dec(v___x_699_);
if (lean_obj_tag(v___x_700_) == 1)
{
lean_object* v_val_701_; uint8_t v___x_702_; 
v_val_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_val_701_);
lean_dec_ref_known(v___x_700_, 1);
v___x_702_ = lean_nat_dec_le(v_val_697_, v_hoverPos_684_);
lean_dec(v_val_697_);
if (v___x_702_ == 0)
{
lean_dec(v_val_701_);
return v___x_688_;
}
else
{
uint8_t v___x_703_; 
v___x_703_ = lean_nat_dec_le(v_hoverPos_684_, v_val_701_);
lean_dec(v_val_701_);
return v___x_703_;
}
}
else
{
lean_dec(v___x_700_);
lean_dec(v_val_697_);
return v___x_688_;
}
}
else
{
lean_dec(v___x_696_);
lean_dec(v_stx_685_);
return v___x_688_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_683_ = stack[0].m_obj;
lean_object* v_hoverPos_684_ = stack[1].m_obj;
lean_object* v_stx_685_ = stack[2].m_obj;
lean_object* v_leadingTokenTailPos_x3f_686_ = stack[3].m_obj;
uint8_t v_res_704_;
v_res_704_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_683_, v_hoverPos_684_, v_stx_685_, v_leadingTokenTailPos_x3f_686_);
stack->m_num = v_res_704_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock___boxed(lean_object* v_fileMap_705_, lean_object* v_hoverPos_706_, lean_object* v_stx_707_, lean_object* v_leadingTokenTailPos_x3f_708_){
_start:
{
uint8_t v_res_709_; lean_object* v_r_710_; 
v_res_709_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_705_, v_hoverPos_706_, v_stx_707_, v_leadingTokenTailPos_x3f_708_);
lean_dec(v_leadingTokenTailPos_x3f_708_);
lean_dec(v_hoverPos_706_);
v_r_710_ = lean_box(v_res_709_);
return v_r_710_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(lean_object* v_fileMap_711_, lean_object* v_hoverPos_712_, lean_object* v_hoverFilePos_713_, lean_object* v_stx_714_, lean_object* v_leadingWs_715_, lean_object* v_leadingTokenTailPos_x3f_716_){
_start:
{
uint8_t v___x_717_; lean_object* v___x_718_; 
v___x_717_ = 0;
v___x_718_ = l_Lean_Syntax_getPos_x3f(v_stx_714_, v___x_717_);
if (lean_obj_tag(v___x_718_) == 1)
{
lean_object* v_val_719_; lean_object* v___x_720_; 
v_val_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_val_719_);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = l_Lean_Syntax_getTailPos_x3f(v_stx_714_, v___x_717_);
if (lean_obj_tag(v___x_720_) == 1)
{
lean_object* v_val_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_val_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_val_721_);
lean_dec_ref_known(v___x_720_, 1);
v___x_722_ = lean_nat_sub(v_val_719_, v_leadingWs_715_);
lean_dec(v_val_719_);
v___x_723_ = lean_nat_dec_le(v___x_722_, v_hoverPos_712_);
lean_dec(v___x_722_);
if (v___x_723_ == 0)
{
lean_dec(v_val_721_);
lean_dec(v_leadingTokenTailPos_x3f_716_);
lean_dec(v_leadingWs_715_);
lean_dec(v_stx_714_);
lean_dec_ref(v_fileMap_711_);
return v___x_723_;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_724_ = l_Lean_Syntax_getTrailingSize(v_stx_714_);
v___x_725_ = lean_nat_add(v_val_721_, v___x_724_);
lean_dec(v___x_724_);
lean_dec(v_val_721_);
v___x_726_ = lean_nat_dec_le(v_hoverPos_712_, v___x_725_);
if (v___x_726_ == 0)
{
lean_dec(v___x_725_);
lean_dec(v_leadingTokenTailPos_x3f_716_);
lean_dec(v_leadingWs_715_);
lean_dec(v_stx_714_);
lean_dec_ref(v_fileMap_711_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; size_t v_sz_731_; size_t v___x_732_; lean_object* v___x_733_; lean_object* v_fst_734_; 
v___x_727_ = l_Lean_Syntax_getArgs(v_stx_714_);
v___x_728_ = lean_box(0);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v_leadingWs_715_);
lean_ctor_set(v___x_729_, 1, v_leadingTokenTailPos_x3f_716_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v_sz_731_ = lean_array_size(v___x_727_);
v___x_732_ = ((size_t)0ULL);
lean_inc_ref(v_fileMap_711_);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_711_, v_hoverPos_712_, v_hoverFilePos_713_, v_hoverPos_712_, v___x_725_, v___x_727_, v_sz_731_, v___x_732_, v___x_730_);
lean_dec_ref(v___x_727_);
lean_dec(v___x_725_);
v_fst_734_ = lean_ctor_get(v___x_733_, 0);
if (lean_obj_tag(v_fst_734_) == 0)
{
lean_object* v_snd_735_; lean_object* v_snd_736_; uint8_t v___x_737_; 
v_snd_735_ = lean_ctor_get(v___x_733_, 1);
lean_inc(v_snd_735_);
lean_dec_ref(v___x_733_);
v_snd_736_ = lean_ctor_get(v_snd_735_, 1);
lean_inc(v_snd_736_);
lean_dec(v_snd_735_);
lean_inc(v_stx_714_);
lean_inc_ref(v_fileMap_711_);
v___x_737_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_711_, v_hoverPos_712_, v_stx_714_, v_snd_736_);
lean_dec(v_snd_736_);
if (v___x_737_ == 0)
{
uint8_t v___x_738_; 
lean_inc(v_stx_714_);
v___x_738_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_711_, v_hoverPos_712_, v_stx_714_);
if (v___x_738_ == 0)
{
uint8_t v___x_739_; 
v___x_739_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_711_, v_hoverPos_712_, v_hoverFilePos_713_, v_stx_714_);
return v___x_739_;
}
else
{
lean_dec(v_stx_714_);
lean_dec_ref(v_fileMap_711_);
return v___x_726_;
}
}
else
{
lean_dec(v_stx_714_);
lean_dec_ref(v_fileMap_711_);
return v___x_726_;
}
}
else
{
lean_object* v_val_740_; uint8_t v___x_741_; 
lean_inc_ref(v_fst_734_);
lean_dec_ref(v___x_733_);
lean_dec(v_stx_714_);
lean_dec_ref(v_fileMap_711_);
v_val_740_ = lean_ctor_get(v_fst_734_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v_fst_734_, 1);
v___x_741_ = lean_unbox(v_val_740_);
lean_dec(v_val_740_);
return v___x_741_;
}
}
}
}
else
{
uint8_t v___x_742_; 
lean_dec(v___x_720_);
lean_dec(v_val_719_);
lean_dec(v_leadingWs_715_);
v___x_742_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_711_, v_hoverPos_712_, v_stx_714_, v_leadingTokenTailPos_x3f_716_);
lean_dec(v_leadingTokenTailPos_x3f_716_);
return v___x_742_;
}
}
else
{
uint8_t v___x_743_; 
lean_dec(v___x_718_);
lean_dec(v_leadingWs_715_);
v___x_743_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_711_, v_hoverPos_712_, v_stx_714_, v_leadingTokenTailPos_x3f_716_);
lean_dec(v_leadingTokenTailPos_x3f_716_);
return v___x_743_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_711_ = stack[0].m_obj;
lean_object* v_hoverPos_712_ = stack[1].m_obj;
lean_object* v_hoverFilePos_713_ = stack[2].m_obj;
lean_object* v_stx_714_ = stack[3].m_obj;
lean_object* v_leadingWs_715_ = stack[4].m_obj;
lean_object* v_leadingTokenTailPos_x3f_716_ = stack[5].m_obj;
uint8_t v_res_744_;
v_res_744_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_711_, v_hoverPos_712_, v_hoverFilePos_713_, v_stx_714_, v_leadingWs_715_, v_leadingTokenTailPos_x3f_716_);
stack->m_num = v_res_744_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(lean_object* v_fileMap_745_, lean_object* v_hoverPos_746_, lean_object* v_hoverFilePos_747_, lean_object* v___x_748_, lean_object* v___x_749_, lean_object* v_as_750_, size_t v_sz_751_, size_t v_i_752_, lean_object* v_b_753_){
_start:
{
uint8_t v___x_754_; 
v___x_754_ = lean_usize_dec_lt(v_i_752_, v_sz_751_);
if (v___x_754_ == 0)
{
lean_dec_ref(v_fileMap_745_);
return v_b_753_;
}
else
{
lean_object* v_snd_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_790_; 
v_snd_755_ = lean_ctor_get(v_b_753_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_b_753_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v_b_753_, 0);
lean_dec(v_unused_791_);
v___x_757_ = v_b_753_;
v_isShared_758_ = v_isSharedCheck_790_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_snd_755_);
lean_dec(v_b_753_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_790_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v_fst_759_; lean_object* v_snd_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_789_; 
v_fst_759_ = lean_ctor_get(v_snd_755_, 0);
v_snd_760_ = lean_ctor_get(v_snd_755_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_snd_755_);
if (v_isSharedCheck_789_ == 0)
{
v___x_762_ = v_snd_755_;
v_isShared_763_ = v_isSharedCheck_789_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_snd_760_);
lean_inc(v_fst_759_);
lean_dec(v_snd_755_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_789_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_a_764_; uint8_t v___x_765_; 
v_a_764_ = lean_array_uget_borrowed(v_as_750_, v_i_752_);
lean_inc(v_snd_760_);
lean_inc(v_fst_759_);
lean_inc(v_a_764_);
lean_inc_ref(v_fileMap_745_);
v___x_765_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_745_, v_hoverPos_746_, v_hoverFilePos_747_, v_a_764_, v_fst_759_, v_snd_760_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___y_769_; lean_object* v___x_779_; 
lean_dec(v_fst_759_);
v___x_766_ = lean_box(0);
v___x_767_ = l_Lean_Syntax_getTrailingSize(v_a_764_);
v___x_779_ = l_Lean_Syntax_getTailPos_x3f(v_a_764_, v___x_765_);
if (lean_obj_tag(v___x_779_) == 0)
{
v___y_769_ = v_snd_760_;
goto v___jp_768_;
}
else
{
lean_dec(v_snd_760_);
v___y_769_ = v___x_779_;
goto v___jp_768_;
}
v___jp_768_:
{
lean_object* v___x_771_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v___y_769_);
lean_ctor_set(v___x_762_, 0, v___x_767_);
v___x_771_ = v___x_762_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___y_769_);
v___x_771_ = v_reuseFailAlloc_778_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v___x_771_);
lean_ctor_set(v___x_757_, 0, v___x_766_);
v___x_773_ = v___x_757_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_771_);
v___x_773_ = v_reuseFailAlloc_777_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
size_t v___x_774_; size_t v___x_775_; 
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_752_, v___x_774_);
v_i_752_ = v___x_775_;
v_b_753_ = v___x_773_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
lean_dec_ref(v_fileMap_745_);
v___x_780_ = lean_nat_dec_le(v___x_748_, v___x_749_);
v___x_781_ = lean_box(v___x_780_);
v___x_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
if (v_isShared_763_ == 0)
{
v___x_784_ = v___x_762_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_fst_759_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_snd_760_);
v___x_784_ = v_reuseFailAlloc_788_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_786_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v___x_784_);
lean_ctor_set(v___x_757_, 0, v___x_782_);
v___x_786_ = v___x_757_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_745_ = stack[0].m_obj;
lean_object* v_hoverPos_746_ = stack[1].m_obj;
lean_object* v_hoverFilePos_747_ = stack[2].m_obj;
lean_object* v___x_748_ = stack[3].m_obj;
lean_object* v___x_749_ = stack[4].m_obj;
lean_object* v_as_750_ = stack[5].m_obj;
size_t v_sz_751_ = stack[6].m_num;
size_t v_i_752_ = stack[7].m_num;
lean_object* v_b_753_ = stack[8].m_obj;
lean_object* v_res_792_;
v_res_792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_745_, v_hoverPos_746_, v_hoverFilePos_747_, v___x_748_, v___x_749_, v_as_750_, v_sz_751_, v_i_752_, v_b_753_);
stack->m_obj
 = v_res_792_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0___boxed(lean_object* v_fileMap_793_, lean_object* v_hoverPos_794_, lean_object* v_hoverFilePos_795_, lean_object* v___x_796_, lean_object* v___x_797_, lean_object* v_as_798_, lean_object* v_sz_799_, lean_object* v_i_800_, lean_object* v_b_801_){
_start:
{
size_t v_sz_boxed_802_; size_t v_i_boxed_803_; lean_object* v_res_804_; 
v_sz_boxed_802_ = lean_unbox_usize(v_sz_799_);
lean_dec(v_sz_799_);
v_i_boxed_803_ = lean_unbox_usize(v_i_800_);
lean_dec(v_i_800_);
v_res_804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_793_, v_hoverPos_794_, v_hoverFilePos_795_, v___x_796_, v___x_797_, v_as_798_, v_sz_boxed_802_, v_i_boxed_803_, v_b_801_);
lean_dec_ref(v_as_798_);
lean_dec(v___x_797_);
lean_dec(v___x_796_);
lean_dec_ref(v_hoverFilePos_795_);
lean_dec(v_hoverPos_794_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go___boxed(lean_object* v_fileMap_805_, lean_object* v_hoverPos_806_, lean_object* v_hoverFilePos_807_, lean_object* v_stx_808_, lean_object* v_leadingWs_809_, lean_object* v_leadingTokenTailPos_x3f_810_){
_start:
{
uint8_t v_res_811_; lean_object* v_r_812_; 
v_res_811_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_805_, v_hoverPos_806_, v_hoverFilePos_807_, v_stx_808_, v_leadingWs_809_, v_leadingTokenTailPos_x3f_810_);
lean_dec_ref(v_hoverFilePos_807_);
lean_dec(v_hoverPos_806_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(lean_object* v_fileMap_813_, lean_object* v_hoverPos_814_, lean_object* v_cmdStx_815_){
_start:
{
lean_object* v_hoverFilePos_816_; lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
lean_inc_ref(v_fileMap_813_);
v_hoverFilePos_816_ = l_Lean_FileMap_toPosition(v_fileMap_813_, v_hoverPos_814_);
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = lean_box(0);
v___x_819_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_813_, v_hoverPos_814_, v_hoverFilePos_816_, v_cmdStx_815_, v___x_817_, v___x_818_);
lean_dec_ref(v_hoverFilePos_816_);
return v___x_819_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_813_ = stack[0].m_obj;
lean_object* v_hoverPos_814_ = stack[1].m_obj;
lean_object* v_cmdStx_815_ = stack[2].m_obj;
uint8_t v_res_820_;
v_res_820_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_813_, v_hoverPos_814_, v_cmdStx_815_);
stack->m_num = v_res_820_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion___boxed(lean_object* v_fileMap_821_, lean_object* v_hoverPos_822_, lean_object* v_cmdStx_823_){
_start:
{
uint8_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_821_, v_hoverPos_822_, v_cmdStx_823_);
lean_dec(v_hoverPos_822_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(lean_object* v_as_831_, size_t v_sz_832_, size_t v_i_833_, lean_object* v_b_834_){
_start:
{
uint8_t v___x_835_; 
v___x_835_ = lean_usize_dec_lt(v_i_833_, v_sz_832_);
if (v___x_835_ == 0)
{
lean_inc_ref(v_b_834_);
return v_b_834_;
}
else
{
lean_object* v___x_836_; lean_object* v_a_837_; lean_object* v___x_838_; 
v___x_836_ = lean_box(0);
v_a_837_ = lean_array_uget_borrowed(v_as_831_, v_i_833_);
v___x_838_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_a_837_);
if (lean_obj_tag(v___x_838_) == 1)
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v___x_836_);
return v___x_840_;
}
else
{
lean_object* v___x_841_; size_t v___x_842_; size_t v___x_843_; 
lean_dec(v___x_838_);
v___x_841_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v___x_842_ = ((size_t)1ULL);
v___x_843_ = lean_usize_add(v_i_833_, v___x_842_);
v_i_833_ = v___x_843_;
v_b_834_ = v___x_841_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_831_ = stack[0].m_obj;
size_t v_sz_832_ = stack[1].m_num;
size_t v_i_833_ = stack[2].m_num;
lean_object* v_b_834_ = stack[3].m_obj;
lean_object* v_res_845_;
v_res_845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_as_831_, v_sz_832_, v_i_833_, v_b_834_);
stack->m_obj
 = v_res_845_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(lean_object* v_as_846_, size_t v_sz_847_, size_t v_i_848_, lean_object* v_b_849_){
_start:
{
uint8_t v___x_850_; 
v___x_850_ = lean_usize_dec_lt(v_i_848_, v_sz_847_);
if (v___x_850_ == 0)
{
lean_inc_ref(v_b_849_);
return v_b_849_;
}
else
{
lean_object* v___x_851_; lean_object* v_a_852_; lean_object* v___x_853_; 
v___x_851_ = lean_box(0);
v_a_852_ = lean_array_uget_borrowed(v_as_846_, v_i_848_);
lean_inc(v_a_852_);
v___x_853_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_a_852_);
if (lean_obj_tag(v___x_853_) == 1)
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v___x_851_);
return v___x_855_;
}
else
{
lean_object* v___x_856_; size_t v___x_857_; size_t v___x_858_; 
lean_dec(v___x_853_);
v___x_856_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_add(v_i_848_, v___x_857_);
v_i_848_ = v___x_858_;
v_b_849_ = v___x_856_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_846_ = stack[0].m_obj;
size_t v_sz_847_ = stack[1].m_num;
size_t v_i_848_ = stack[2].m_num;
lean_object* v_b_849_ = stack[3].m_obj;
lean_object* v_res_860_;
v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_as_846_, v_sz_847_, v_i_848_, v_b_849_);
stack->m_obj
 = v_res_860_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(lean_object* v_x_861_){
_start:
{
if (lean_obj_tag(v_x_861_) == 0)
{
lean_object* v_cs_862_; lean_object* v___x_863_; lean_object* v___x_864_; size_t v_sz_865_; size_t v___x_866_; lean_object* v___x_867_; lean_object* v_fst_868_; 
v_cs_862_ = lean_ctor_get(v_x_861_, 0);
v___x_863_ = lean_box(0);
v___x_864_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_865_ = lean_array_size(v_cs_862_);
v___x_866_ = ((size_t)0ULL);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_cs_862_, v_sz_865_, v___x_866_, v___x_864_);
v_fst_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_fst_868_);
lean_dec_ref(v___x_867_);
if (lean_obj_tag(v_fst_868_) == 0)
{
return v___x_863_;
}
else
{
lean_object* v_val_869_; 
v_val_869_ = lean_ctor_get(v_fst_868_, 0);
lean_inc(v_val_869_);
lean_dec_ref_known(v_fst_868_, 1);
return v_val_869_;
}
}
else
{
lean_object* v_vs_870_; lean_object* v___x_871_; lean_object* v___x_872_; size_t v_sz_873_; size_t v___x_874_; lean_object* v___x_875_; lean_object* v_fst_876_; 
v_vs_870_ = lean_ctor_get(v_x_861_, 0);
v___x_871_ = lean_box(0);
v___x_872_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_873_ = lean_array_size(v_vs_870_);
v___x_874_ = ((size_t)0ULL);
v___x_875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_vs_870_, v_sz_873_, v___x_874_, v___x_872_);
v_fst_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_fst_876_);
lean_dec_ref(v___x_875_);
if (lean_obj_tag(v_fst_876_) == 0)
{
return v___x_871_;
}
else
{
lean_object* v_val_877_; 
v_val_877_ = lean_ctor_get(v_fst_876_, 0);
lean_inc(v_val_877_);
lean_dec_ref_known(v_fst_876_, 1);
return v_val_877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(lean_object* v_t_878_){
_start:
{
lean_object* v_root_879_; lean_object* v_tail_880_; lean_object* v___x_881_; 
v_root_879_ = lean_ctor_get(v_t_878_, 0);
v_tail_880_ = lean_ctor_get(v_t_878_, 1);
v___x_881_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_root_879_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v___x_882_; size_t v_sz_883_; size_t v___x_884_; lean_object* v___x_885_; lean_object* v_fst_886_; 
v___x_882_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_883_ = lean_array_size(v_tail_880_);
v___x_884_ = ((size_t)0ULL);
v___x_885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_tail_880_, v_sz_883_, v___x_884_, v___x_882_);
v_fst_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_fst_886_);
lean_dec_ref(v___x_885_);
if (lean_obj_tag(v_fst_886_) == 0)
{
return v___x_881_;
}
else
{
lean_object* v_val_887_; 
v_val_887_ = lean_ctor_get(v_fst_886_, 0);
lean_inc(v_val_887_);
lean_dec_ref_known(v_fst_886_, 1);
return v_val_887_;
}
}
else
{
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(lean_object* v_i_888_){
_start:
{
switch(lean_obj_tag(v_i_888_))
{
case 0:
{
lean_object* v_i_889_; 
v_i_889_ = lean_ctor_get(v_i_888_, 0);
lean_inc_ref(v_i_889_);
if (lean_obj_tag(v_i_889_) == 0)
{
lean_object* v_info_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref_known(v_i_888_, 2);
v_info_890_ = lean_ctor_get(v_i_889_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v_i_889_);
if (v_isSharedCheck_900_ == 0)
{
v___x_892_ = v_i_889_;
v_isShared_893_ = v_isSharedCheck_900_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_info_890_);
lean_dec(v_i_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_900_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_894_ = lean_box(0);
v___x_895_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go___closed__0));
v___x_896_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_896_, 0, v_info_890_);
lean_ctor_set(v___x_896_, 1, v___x_894_);
lean_ctor_set(v___x_896_, 2, v___x_895_);
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 1);
lean_ctor_set(v___x_892_, 0, v___x_896_);
v___x_898_ = v___x_892_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
else
{
lean_object* v_t_901_; 
lean_dec_ref(v_i_889_);
v_t_901_ = lean_ctor_get(v_i_888_, 1);
lean_inc_ref(v_t_901_);
lean_dec_ref_known(v_i_888_, 2);
v_i_888_ = v_t_901_;
goto _start;
}
}
case 1:
{
lean_object* v_children_903_; lean_object* v___x_904_; 
v_children_903_ = lean_ctor_get(v_i_888_, 1);
lean_inc_ref(v_children_903_);
lean_dec_ref_known(v_i_888_, 2);
v___x_904_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(v_children_903_);
lean_dec_ref(v_children_903_);
return v___x_904_;
}
default: 
{
lean_object* v___x_905_; 
lean_dec_ref_known(v_i_888_, 1);
v___x_905_ = lean_box(0);
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___boxed(lean_object* v_t_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(v_t_906_);
lean_dec_ref(v_t_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1___boxed(lean_object* v_as_908_, lean_object* v_sz_909_, lean_object* v_i_910_, lean_object* v_b_911_){
_start:
{
size_t v_sz_boxed_912_; size_t v_i_boxed_913_; lean_object* v_res_914_; 
v_sz_boxed_912_ = lean_unbox_usize(v_sz_909_);
lean_dec(v_sz_909_);
v_i_boxed_913_ = lean_unbox_usize(v_i_910_);
lean_dec(v_i_910_);
v_res_914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_as_908_, v_sz_boxed_912_, v_i_boxed_913_, v_b_911_);
lean_dec_ref(v_b_911_);
lean_dec_ref(v_as_908_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1___boxed(lean_object* v_as_915_, lean_object* v_sz_916_, lean_object* v_i_917_, lean_object* v_b_918_){
_start:
{
size_t v_sz_boxed_919_; size_t v_i_boxed_920_; lean_object* v_res_921_; 
v_sz_boxed_919_ = lean_unbox_usize(v_sz_916_);
lean_dec(v_sz_916_);
v_i_boxed_920_ = lean_unbox_usize(v_i_917_);
lean_dec(v_i_917_);
v_res_921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_as_915_, v_sz_boxed_919_, v_i_boxed_920_, v_b_918_);
lean_dec_ref(v_b_918_);
lean_dec_ref(v_as_915_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0___boxed(lean_object* v_x_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_x_922_);
lean_dec_ref(v_x_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f(lean_object* v_i_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_i_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(lean_object* v_fileMap_928_, lean_object* v_hoverPos_929_, lean_object* v_cmdStx_930_, lean_object* v_infoTree_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_infoTree_931_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v___x_933_; 
lean_dec(v_cmdStx_930_);
lean_dec_ref(v_fileMap_928_);
v___x_933_ = lean_box(0);
return v___x_933_;
}
else
{
lean_object* v_val_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_946_; 
v_val_934_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_946_ == 0)
{
v___x_936_ = v___x_932_;
v_isShared_937_ = v_isSharedCheck_946_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_val_934_);
lean_dec(v___x_932_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_946_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
uint8_t v___x_938_; 
v___x_938_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_928_, v_hoverPos_929_, v_cmdStx_930_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; 
lean_del_object(v___x_936_);
lean_dec(v_val_934_);
v___x_939_ = lean_box(0);
return v___x_939_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_940_ = lean_box(0);
v___x_941_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___closed__0));
v___x_942_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v_val_934_);
lean_ctor_set(v___x_942_, 2, v___x_941_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_942_);
v___x_944_ = v___x_936_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___boxed(lean_object* v_fileMap_947_, lean_object* v_hoverPos_948_, lean_object* v_cmdStx_949_, lean_object* v_infoTree_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(v_fileMap_947_, v_hoverPos_948_, v_cmdStx_949_, v_infoTree_950_);
lean_dec(v_hoverPos_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(lean_object* v_msg_952_){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = l_Lean_instInhabitedExpr;
v___x_954_ = lean_panic_fn_borrowed(v___x_953_, v_msg_952_);
return v___x_954_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(lean_object* v_hoverPos_955_, lean_object* v_i_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_Elab_Info_pos_x3f(v_i_956_);
if (lean_obj_tag(v___x_957_) == 1)
{
lean_object* v_val_958_; lean_object* v___x_959_; 
v_val_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_val_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_959_ = l_Lean_Elab_Info_tailPos_x3f(v_i_956_);
if (lean_obj_tag(v___x_959_) == 1)
{
if (lean_obj_tag(v_i_956_) == 1)
{
lean_object* v_i_960_; lean_object* v_expectedType_x3f_961_; 
v_i_960_ = lean_ctor_get(v_i_956_, 0);
v_expectedType_x3f_961_ = lean_ctor_get(v_i_960_, 2);
if (lean_obj_tag(v_expectedType_x3f_961_) == 0)
{
uint8_t v___x_962_; 
lean_dec_ref_known(v___x_959_, 1);
lean_dec(v_val_958_);
v___x_962_ = 0;
return v___x_962_;
}
else
{
lean_object* v_val_963_; uint8_t v___x_964_; 
v_val_963_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_val_963_);
lean_dec_ref_known(v___x_959_, 1);
v___x_964_ = lean_nat_dec_le(v_val_958_, v_hoverPos_955_);
lean_dec(v_val_958_);
if (v___x_964_ == 0)
{
lean_dec(v_val_963_);
return v___x_964_;
}
else
{
uint8_t v___x_965_; 
v___x_965_ = lean_nat_dec_le(v_hoverPos_955_, v_val_963_);
lean_dec(v_val_963_);
return v___x_965_;
}
}
}
else
{
uint8_t v___x_966_; 
lean_dec_ref_known(v___x_959_, 1);
lean_dec(v_val_958_);
v___x_966_ = 0;
return v___x_966_;
}
}
else
{
uint8_t v___x_967_; 
lean_dec(v___x_959_);
lean_dec(v_val_958_);
v___x_967_ = 0;
return v___x_967_;
}
}
else
{
uint8_t v___x_968_; 
lean_dec(v___x_957_);
v___x_968_ = 0;
return v___x_968_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_hoverPos_955_ = stack[0].m_obj;
lean_object* v_i_956_ = stack[1].m_obj;
uint8_t v_res_969_;
v_res_969_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(v_hoverPos_955_, v_i_956_);
stack->m_num = v_res_969_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed(lean_object* v_hoverPos_970_, lean_object* v_i_971_){
_start:
{
uint8_t v_res_972_; lean_object* v_r_973_; 
v_res_972_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(v_hoverPos_970_, v_i_971_);
lean_dec_ref(v_i_971_);
lean_dec(v_hoverPos_970_);
v_r_973_ = lean_box(v_res_972_);
return v_r_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt(lean_object* v_infoTree_974_, lean_object* v_hoverPos_975_){
_start:
{
lean_object* v___f_976_; lean_object* v___x_977_; 
v___f_976_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed), 2, 1);
lean_closure_set(v___f_976_, 0, v_hoverPos_975_);
v___x_977_ = l_Lean_Elab_InfoTree_smallestInfo_x3f(v___f_976_, v_infoTree_974_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v___x_978_; 
v___x_978_ = lean_box(0);
return v___x_978_;
}
else
{
lean_object* v_val_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1003_; 
v_val_979_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_981_ = v___x_977_;
v_isShared_982_ = v_isSharedCheck_1003_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_val_979_);
lean_dec(v___x_977_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1003_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v_fst_983_; lean_object* v_snd_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1002_; 
v_fst_983_ = lean_ctor_get(v_val_979_, 0);
v_snd_984_ = lean_ctor_get(v_val_979_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_val_979_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_986_ = v_val_979_;
v_isShared_987_ = v_isSharedCheck_1002_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_snd_984_);
lean_inc(v_fst_983_);
lean_dec(v_val_979_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1002_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___y_989_; 
if (lean_obj_tag(v_snd_984_) == 1)
{
lean_object* v_i_996_; lean_object* v_expectedType_x3f_997_; 
v_i_996_ = lean_ctor_get(v_snd_984_, 0);
lean_inc_ref(v_i_996_);
lean_dec_ref_known(v_snd_984_, 1);
v_expectedType_x3f_997_ = lean_ctor_get(v_i_996_, 2);
lean_inc(v_expectedType_x3f_997_);
lean_dec_ref(v_i_996_);
if (lean_obj_tag(v_expectedType_x3f_997_) == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_obj_once(&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4, &l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_once, _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4);
v___x_999_ = l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(v___x_998_);
v___y_989_ = v___x_999_;
goto v___jp_988_;
}
else
{
lean_object* v_val_1000_; 
v_val_1000_ = lean_ctor_get(v_expectedType_x3f_997_, 0);
lean_inc(v_val_1000_);
lean_dec_ref_known(v_expectedType_x3f_997_, 1);
v___y_989_ = v_val_1000_;
goto v___jp_988_;
}
}
else
{
lean_object* v___x_1001_; 
lean_del_object(v___x_986_);
lean_dec(v_snd_984_);
lean_dec(v_fst_983_);
lean_del_object(v___x_981_);
v___x_1001_ = lean_box(0);
return v___x_1001_;
}
v___jp_988_:
{
lean_object* v___x_991_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v___y_989_);
v___x_991_ = v___x_986_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_fst_983_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v___y_989_);
v___x_991_ = v_reuseFailAlloc_995_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_991_);
v___x_993_ = v___x_981_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(lean_object* v_f_1004_, lean_object* v_leadingToken_x3f_1005_, lean_object* v_acc_1006_, lean_object* v_stx_1007_){
_start:
{
lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v_acc_1018_; 
v___f_1008_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0));
v___f_1009_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1));
v___f_1010_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2));
v___f_1011_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3));
v___f_1012_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4));
v___f_1013_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5));
v___f_1014_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6));
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___f_1008_);
lean_ctor_set(v___x_1015_, 1, v___f_1009_);
v___x_1016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___f_1010_);
lean_ctor_set(v___x_1016_, 2, v___f_1011_);
lean_ctor_set(v___x_1016_, 3, v___f_1012_);
lean_ctor_set(v___x_1016_, 4, v___f_1013_);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___f_1014_);
lean_inc(v_f_1004_);
lean_inc(v_stx_1007_);
lean_inc(v_leadingToken_x3f_1005_);
v_acc_1018_ = lean_apply_3(v_f_1004_, v_acc_1006_, v_leadingToken_x3f_1005_, v_stx_1007_);
switch(lean_obj_tag(v_stx_1007_))
{
case 0:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec_ref_known(v___x_1017_, 2);
lean_dec(v_leadingToken_x3f_1005_);
lean_dec(v_f_1004_);
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_acc_1018_);
return v___x_1020_;
}
case 1:
{
lean_object* v_args_1021_; lean_object* v___f_1022_; lean_object* v_lastToken_x3f_1023_; lean_object* v___x_1024_; size_t v_sz_1025_; size_t v___x_1026_; lean_object* v___x_1027_; lean_object* v_fst_1028_; lean_object* v_snd_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
v_args_1021_ = lean_ctor_get(v_stx_1007_, 2);
lean_inc_ref(v_args_1021_);
lean_dec_ref_known(v_stx_1007_, 3);
v___f_1022_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1022_, 0, v_f_1004_);
lean_closure_set(v___f_1022_, 1, v_leadingToken_x3f_1005_);
v_lastToken_x3f_1023_ = lean_box(0);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v_acc_1018_);
lean_ctor_set(v___x_1024_, 1, v_lastToken_x3f_1023_);
v_sz_1025_ = lean_array_size(v_args_1021_);
v___x_1026_ = ((size_t)0ULL);
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1017_, v_args_1021_, v___f_1022_, v_sz_1025_, v___x_1026_, v___x_1024_);
v_fst_1028_ = lean_ctor_get(v___x_1027_, 0);
v_snd_1029_ = lean_ctor_get(v___x_1027_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1027_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_snd_1029_);
lean_inc(v_fst_1028_);
lean_dec(v___x_1027_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v_fst_1028_);
lean_ctor_set(v___x_1031_, 0, v_snd_1029_);
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_snd_1029_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_fst_1028_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
default: 
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec_ref_known(v___x_1017_, 2);
lean_dec(v_leadingToken_x3f_1005_);
lean_dec(v_f_1004_);
v___x_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1037_, 0, v_stx_1007_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v_acc_1018_);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0(lean_object* v_f_1039_, lean_object* v_leadingToken_x3f_1040_, lean_object* v_a_1041_, lean_object* v_x_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v_fst_1049_; lean_object* v_snd_1050_; lean_object* v___y_1052_; 
v_fst_1049_ = lean_ctor_get(v___y_1043_, 0);
lean_inc(v_fst_1049_);
v_snd_1050_ = lean_ctor_get(v___y_1043_, 1);
lean_inc(v_snd_1050_);
lean_dec_ref(v___y_1043_);
if (lean_obj_tag(v_snd_1050_) == 0)
{
v___y_1052_ = v_leadingToken_x3f_1040_;
goto v___jp_1051_;
}
else
{
lean_dec(v_leadingToken_x3f_1040_);
lean_inc_ref(v_snd_1050_);
v___y_1052_ = v_snd_1050_;
goto v___jp_1051_;
}
v___jp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___y_1045_);
lean_ctor_set(v___x_1047_, 1, v___y_1046_);
v___x_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
v___jp_1051_:
{
lean_object* v___x_1053_; lean_object* v_fst_1054_; 
v___x_1053_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1039_, v___y_1052_, v_fst_1049_, v_a_1041_);
v_fst_1054_ = lean_ctor_get(v___x_1053_, 0);
if (lean_obj_tag(v_fst_1054_) == 0)
{
lean_object* v_snd_1055_; 
v_snd_1055_ = lean_ctor_get(v___x_1053_, 1);
lean_inc(v_snd_1055_);
lean_dec_ref(v___x_1053_);
v___y_1045_ = v_snd_1055_;
v___y_1046_ = v_snd_1050_;
goto v___jp_1044_;
}
else
{
lean_object* v_snd_1056_; 
lean_inc_ref(v_fst_1054_);
lean_dec(v_snd_1050_);
v_snd_1056_ = lean_ctor_get(v___x_1053_, 1);
lean_inc(v_snd_1056_);
lean_dec_ref(v___x_1053_);
v___y_1045_ = v_snd_1056_;
v___y_1046_ = v_fst_1054_;
goto v___jp_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(lean_object* v_00_u03b1_1057_, lean_object* v_f_1058_, lean_object* v_inst_1059_, lean_object* v_leadingToken_x3f_1060_, lean_object* v_acc_1061_, lean_object* v_stx_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1058_, v_leadingToken_x3f_1060_, v_acc_1061_, v_stx_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___boxed(lean_object* v_00_u03b1_1064_, lean_object* v_f_1065_, lean_object* v_inst_1066_, lean_object* v_leadingToken_x3f_1067_, lean_object* v_acc_1068_, lean_object* v_stx_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(v_00_u03b1_1064_, v_f_1065_, v_inst_1066_, v_leadingToken_x3f_1067_, v_acc_1068_, v_stx_1069_);
lean_dec(v_inst_1066_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(lean_object* v_f_1071_, lean_object* v_init_1072_, lean_object* v_stx_1073_){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_snd_1076_; 
v___x_1074_ = lean_box(0);
v___x_1075_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1071_, v___x_1074_, v_init_1072_, v_stx_1073_);
v_snd_1076_ = lean_ctor_get(v___x_1075_, 1);
lean_inc(v_snd_1076_);
lean_dec_ref(v___x_1075_);
return v_snd_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(lean_object* v_00_u03b1_1077_, lean_object* v_inst_1078_, lean_object* v_f_1079_, lean_object* v_init_1080_, lean_object* v_stx_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(v_f_1079_, v_init_1080_, v_stx_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___boxed(lean_object* v_00_u03b1_1083_, lean_object* v_inst_1084_, lean_object* v_f_1085_, lean_object* v_init_1086_, lean_object* v_stx_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(v_00_u03b1_1083_, v_inst_1084_, v_f_1085_, v_init_1086_, v_stx_1087_);
lean_dec(v_inst_1084_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(lean_object* v_p_1089_, lean_object* v_foundStx_x3f_1090_, lean_object* v_leadingToken_x3f_1091_, lean_object* v_stx_1092_){
_start:
{
if (lean_obj_tag(v_foundStx_x3f_1090_) == 0)
{
lean_object* v___x_1093_; uint8_t v___x_1094_; 
lean_inc(v_stx_1092_);
v___x_1093_ = lean_apply_2(v_p_1089_, v_leadingToken_x3f_1091_, v_stx_1092_);
v___x_1094_ = lean_unbox(v___x_1093_);
if (v___x_1094_ == 0)
{
lean_dec(v_stx_1092_);
return v_foundStx_x3f_1090_;
}
else
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_stx_1092_);
return v___x_1095_;
}
}
else
{
lean_dec(v_stx_1092_);
lean_dec(v_leadingToken_x3f_1091_);
lean_dec_ref(v_p_1089_);
lean_inc_ref(v_foundStx_x3f_1090_);
return v_foundStx_x3f_1090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed(lean_object* v_p_1096_, lean_object* v_foundStx_x3f_1097_, lean_object* v_leadingToken_x3f_1098_, lean_object* v_stx_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(v_p_1096_, v_foundStx_x3f_1097_, v_leadingToken_x3f_1098_, v_stx_1099_);
lean_dec(v_foundStx_x3f_1097_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f(lean_object* v_p_1101_, lean_object* v_stx_1102_){
_start:
{
lean_object* v___f_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___f_1103_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1103_, 0, v_p_1101_);
v___x_1104_ = lean_box(0);
v___x_1105_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(v___f_1103_, v___x_1104_, v_stx_1102_);
return v___x_1105_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(uint8_t v___y_1106_, lean_object* v_hoverPos_1107_, lean_object* v_as_1108_, size_t v_i_1109_, size_t v_stop_1110_){
_start:
{
uint8_t v___x_1115_; 
v___x_1115_ = lean_usize_dec_eq(v_i_1109_, v_stop_1110_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v_fst_1117_; lean_object* v_snd_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; uint8_t v___y_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1116_ = lean_array_uget_borrowed(v_as_1108_, v_i_1109_);
v_fst_1117_ = lean_ctor_get(v___x_1116_, 0);
v_snd_1118_ = lean_ctor_get(v___x_1116_, 1);
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = 1;
v___x_1123_ = lean_unsigned_to_nat(2u);
v___x_1124_ = lean_nat_mod(v_snd_1118_, v___x_1123_);
v___x_1125_ = lean_nat_dec_eq(v___x_1124_, v___x_1119_);
lean_dec(v___x_1124_);
if (v___x_1125_ == 0)
{
uint8_t v___x_1126_; 
v___x_1126_ = l_Lean_Syntax_isAtom(v_fst_1117_);
if (v___x_1126_ == 0)
{
v___y_1122_ = v___y_1106_;
goto v___jp_1121_;
}
else
{
if (v___y_1106_ == 0)
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_Syntax_getTailPos_x3f(v_fst_1117_, v___y_1106_);
if (lean_obj_tag(v___x_1127_) == 1)
{
lean_object* v_val_1128_; uint8_t v___x_1129_; 
v_val_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_val_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___x_1129_ = lean_nat_dec_le(v_val_1128_, v_hoverPos_1107_);
if (v___x_1129_ == 0)
{
lean_dec(v_val_1128_);
goto v___jp_1111_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1130_ = l_Lean_Syntax_getTrailingSize(v_fst_1117_);
v___x_1131_ = lean_nat_add(v_val_1128_, v___x_1130_);
lean_dec(v___x_1130_);
lean_dec(v_val_1128_);
v___x_1132_ = lean_nat_dec_le(v_hoverPos_1107_, v___x_1131_);
lean_dec(v___x_1131_);
v___y_1122_ = v___x_1132_;
goto v___jp_1121_;
}
}
else
{
lean_dec(v___x_1127_);
goto v___jp_1111_;
}
}
else
{
return v___x_1120_;
}
}
}
else
{
v___y_1122_ = v___y_1106_;
goto v___jp_1121_;
}
v___jp_1121_:
{
if (v___y_1122_ == 0)
{
goto v___jp_1111_;
}
else
{
return v___x_1120_;
}
}
}
else
{
uint8_t v___x_1133_; 
v___x_1133_ = 0;
return v___x_1133_;
}
v___jp_1111_:
{
size_t v___x_1112_; size_t v___x_1113_; 
v___x_1112_ = ((size_t)1ULL);
v___x_1113_ = lean_usize_add(v_i_1109_, v___x_1112_);
v_i_1109_ = v___x_1113_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_1106_ = stack[0].m_num;
lean_object* v_hoverPos_1107_ = stack[1].m_obj;
lean_object* v_as_1108_ = stack[2].m_obj;
size_t v_i_1109_ = stack[3].m_num;
size_t v_stop_1110_ = stack[4].m_num;
uint8_t v_res_1134_;
v_res_1134_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(v___y_1106_, v_hoverPos_1107_, v_as_1108_, v_i_1109_, v_stop_1110_);
stack->m_num = v_res_1134_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0___boxed(lean_object* v___y_1135_, lean_object* v_hoverPos_1136_, lean_object* v_as_1137_, lean_object* v_i_1138_, lean_object* v_stop_1139_){
_start:
{
uint8_t v___y_1670__boxed_1140_; size_t v_i_boxed_1141_; size_t v_stop_boxed_1142_; uint8_t v_res_1143_; lean_object* v_r_1144_; 
v___y_1670__boxed_1140_ = lean_unbox(v___y_1135_);
v_i_boxed_1141_ = lean_unbox_usize(v_i_1138_);
lean_dec(v_i_1138_);
v_stop_boxed_1142_ = lean_unbox_usize(v_stop_1139_);
lean_dec(v_stop_1139_);
v_res_1143_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(v___y_1670__boxed_1140_, v_hoverPos_1136_, v_as_1137_, v_i_boxed_1141_, v_stop_boxed_1142_);
lean_dec_ref(v_as_1137_);
lean_dec(v_hoverPos_1136_);
v_r_1144_ = lean_box(v_res_1143_);
return v_r_1144_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(uint8_t v___x_1151_, uint8_t v_isCursorOnWhitespace_1152_, uint8_t v_isCursorInProperWhitespace_1153_, lean_object* v_fileMap_1154_, lean_object* v_hoverFilePos_1155_, lean_object* v_hoverPos_1156_, lean_object* v_leadingToken_x3f_1157_, lean_object* v_stx_1158_){
_start:
{
uint8_t v___y_1160_; 
if (lean_obj_tag(v_leadingToken_x3f_1157_) == 1)
{
lean_object* v_val_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v_val_1167_ = lean_ctor_get(v_leadingToken_x3f_1157_, 0);
lean_inc(v_stx_1158_);
v___x_1168_ = l_Lean_Syntax_getKind(v_stx_1158_);
v___x_1169_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1));
v___x_1170_ = lean_name_eq(v___x_1168_, v___x_1169_);
lean_dec(v___x_1168_);
if (v___x_1170_ == 0)
{
lean_dec(v_stx_1158_);
lean_dec_ref(v_fileMap_1154_);
return v___x_1151_;
}
else
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_Syntax_getTailPos_x3f(v_val_1167_, v_isCursorOnWhitespace_1152_);
if (lean_obj_tag(v___x_1171_) == 1)
{
lean_object* v_val_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v_fieldsAndSeps_1175_; uint8_t v___y_1177_; lean_object* v___y_1185_; lean_object* v___x_1191_; 
v_val_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_val_1172_);
lean_dec_ref_known(v___x_1171_, 1);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = l_Lean_Syntax_getArg(v_stx_1158_, v___x_1173_);
v_fieldsAndSeps_1175_ = l_Lean_Syntax_getArgs(v___x_1174_);
lean_dec(v___x_1174_);
v___x_1191_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1158_, v_isCursorOnWhitespace_1152_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_val_1167_, v_isCursorOnWhitespace_1152_);
v___y_1185_ = v___x_1192_;
goto v___jp_1184_;
}
else
{
v___y_1185_ = v___x_1191_;
goto v___jp_1184_;
}
v___jp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1178_ = l_Array_zipIdx___redArg(v_fieldsAndSeps_1175_, v___x_1173_);
v___x_1179_ = lean_array_get_size(v___x_1178_);
v___x_1180_ = lean_nat_dec_lt(v___x_1173_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_dec_ref(v___x_1178_);
v___y_1160_ = v___x_1180_;
goto v___jp_1159_;
}
else
{
if (v___x_1180_ == 0)
{
lean_dec_ref(v___x_1178_);
v___y_1160_ = v___x_1180_;
goto v___jp_1159_;
}
else
{
size_t v___x_1181_; size_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1181_ = ((size_t)0ULL);
v___x_1182_ = lean_usize_of_nat(v___x_1179_);
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(v___y_1177_, v_hoverPos_1156_, v___x_1178_, v___x_1181_, v___x_1182_);
lean_dec_ref(v___x_1178_);
if (v___x_1183_ == 0)
{
v___y_1160_ = v___x_1183_;
goto v___jp_1159_;
}
else
{
lean_dec(v_stx_1158_);
lean_dec_ref(v_fileMap_1154_);
return v_isCursorOnWhitespace_1152_;
}
}
}
}
v___jp_1184_:
{
if (lean_obj_tag(v___y_1185_) == 1)
{
lean_object* v_val_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v_val_1186_ = lean_ctor_get(v___y_1185_, 0);
lean_inc(v_val_1186_);
lean_dec_ref_known(v___y_1185_, 1);
v___x_1187_ = lean_array_get_size(v_fieldsAndSeps_1175_);
v___x_1188_ = lean_nat_dec_eq(v___x_1187_, v___x_1173_);
if (v___x_1188_ == 0)
{
lean_dec(v_val_1186_);
lean_dec(v_val_1172_);
v___y_1177_ = v___x_1151_;
goto v___jp_1176_;
}
else
{
lean_object* v_outerBounds_1189_; uint8_t v___x_1190_; 
v_outerBounds_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_outerBounds_1189_, 0, v_val_1172_);
lean_ctor_set(v_outerBounds_1189_, 1, v_val_1186_);
v___x_1190_ = l_Lean_Syntax_Range_contains(v_outerBounds_1189_, v_hoverPos_1156_, v_isCursorOnWhitespace_1152_);
lean_dec_ref_known(v_outerBounds_1189_, 2);
if (v___x_1190_ == 0)
{
v___y_1177_ = v___x_1190_;
goto v___jp_1176_;
}
else
{
lean_dec_ref(v_fieldsAndSeps_1175_);
lean_dec(v_stx_1158_);
lean_dec_ref(v_fileMap_1154_);
return v_isCursorOnWhitespace_1152_;
}
}
}
else
{
lean_dec(v___y_1185_);
lean_dec_ref(v_fieldsAndSeps_1175_);
lean_dec(v_val_1172_);
lean_dec(v_stx_1158_);
lean_dec_ref(v_fileMap_1154_);
return v___x_1151_;
}
}
}
else
{
lean_dec(v___x_1171_);
lean_dec(v_stx_1158_);
lean_dec_ref(v_fileMap_1154_);
return v___x_1151_;
}
}
}
else
{
lean_dec(v_stx_1158_);
lean_dec_ref(v_fileMap_1154_);
return v___x_1151_;
}
v___jp_1159_:
{
if (v_isCursorInProperWhitespace_1153_ == 0)
{
lean_dec(v_stx_1158_);
lean_dec_ref(v_fileMap_1154_);
return v___y_1160_;
}
else
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_Syntax_getPos_x3f(v_stx_1158_, v___y_1160_);
lean_dec(v_stx_1158_);
if (lean_obj_tag(v___x_1161_) == 1)
{
lean_object* v_val_1162_; lean_object* v___x_1163_; lean_object* v_column_1164_; lean_object* v_column_1165_; uint8_t v_isCursorInBlock_1166_; 
v_val_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_val_1162_);
lean_dec_ref_known(v___x_1161_, 1);
v___x_1163_ = l_Lean_FileMap_toPosition(v_fileMap_1154_, v_val_1162_);
lean_dec(v_val_1162_);
v_column_1164_ = lean_ctor_get(v___x_1163_, 1);
lean_inc(v_column_1164_);
lean_dec_ref(v___x_1163_);
v_column_1165_ = lean_ctor_get(v_hoverFilePos_1155_, 1);
v_isCursorInBlock_1166_ = lean_nat_dec_eq(v_column_1165_, v_column_1164_);
lean_dec(v_column_1164_);
return v_isCursorInBlock_1166_;
}
else
{
lean_dec(v___x_1161_);
lean_dec_ref(v_fileMap_1154_);
return v___y_1160_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1151_ = stack[0].m_num;
uint8_t v_isCursorOnWhitespace_1152_ = stack[1].m_num;
uint8_t v_isCursorInProperWhitespace_1153_ = stack[2].m_num;
lean_object* v_fileMap_1154_ = stack[3].m_obj;
lean_object* v_hoverFilePos_1155_ = stack[4].m_obj;
lean_object* v_hoverPos_1156_ = stack[5].m_obj;
lean_object* v_leadingToken_x3f_1157_ = stack[6].m_obj;
lean_object* v_stx_1158_ = stack[7].m_obj;
uint8_t v_res_1193_;
v_res_1193_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(v___x_1151_, v_isCursorOnWhitespace_1152_, v_isCursorInProperWhitespace_1153_, v_fileMap_1154_, v_hoverFilePos_1155_, v_hoverPos_1156_, v_leadingToken_x3f_1157_, v_stx_1158_);
stack->m_num = v_res_1193_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___boxed(lean_object* v___x_1194_, lean_object* v_isCursorOnWhitespace_1195_, lean_object* v_isCursorInProperWhitespace_1196_, lean_object* v_fileMap_1197_, lean_object* v_hoverFilePos_1198_, lean_object* v_hoverPos_1199_, lean_object* v_leadingToken_x3f_1200_, lean_object* v_stx_1201_){
_start:
{
uint8_t v___x_1759__boxed_1202_; uint8_t v_isCursorOnWhitespace_boxed_1203_; uint8_t v_isCursorInProperWhitespace_boxed_1204_; uint8_t v_res_1205_; lean_object* v_r_1206_; 
v___x_1759__boxed_1202_ = lean_unbox(v___x_1194_);
v_isCursorOnWhitespace_boxed_1203_ = lean_unbox(v_isCursorOnWhitespace_1195_);
v_isCursorInProperWhitespace_boxed_1204_ = lean_unbox(v_isCursorInProperWhitespace_1196_);
v_res_1205_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(v___x_1759__boxed_1202_, v_isCursorOnWhitespace_boxed_1203_, v_isCursorInProperWhitespace_boxed_1204_, v_fileMap_1197_, v_hoverFilePos_1198_, v_hoverPos_1199_, v_leadingToken_x3f_1200_, v_stx_1201_);
lean_dec(v_leadingToken_x3f_1200_);
lean_dec(v_hoverPos_1199_);
lean_dec_ref(v_hoverFilePos_1198_);
v_r_1206_ = lean_box(v_res_1205_);
return v_r_1206_;
}
}
uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(lean_object* v_fileMap_1207_, lean_object* v_hoverPos_1208_, lean_object* v_cmdStx_1209_){
_start:
{
uint8_t v_isCursorOnWhitespace_1210_; 
v_isCursorOnWhitespace_1210_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_1207_, v_hoverPos_1208_);
if (v_isCursorOnWhitespace_1210_ == 0)
{
lean_dec(v_cmdStx_1209_);
lean_dec(v_hoverPos_1208_);
lean_dec_ref(v_fileMap_1207_);
return v_isCursorOnWhitespace_1210_;
}
else
{
uint8_t v_isCursorInProperWhitespace_1211_; uint8_t v___x_1212_; lean_object* v_hoverFilePos_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; 
v_isCursorInProperWhitespace_1211_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_1207_, v_hoverPos_1208_);
v___x_1212_ = 0;
lean_inc_ref(v_fileMap_1207_);
v_hoverFilePos_1213_ = l_Lean_FileMap_toPosition(v_fileMap_1207_, v_hoverPos_1208_);
v___x_1214_ = lean_box(v___x_1212_);
v___x_1215_ = lean_box(v_isCursorOnWhitespace_1210_);
v___x_1216_ = lean_box(v_isCursorInProperWhitespace_1211_);
v___f_1217_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___boxed), 8, 6);
lean_closure_set(v___f_1217_, 0, v___x_1214_);
lean_closure_set(v___f_1217_, 1, v___x_1215_);
lean_closure_set(v___f_1217_, 2, v___x_1216_);
lean_closure_set(v___f_1217_, 3, v_fileMap_1207_);
lean_closure_set(v___f_1217_, 4, v_hoverFilePos_1213_);
lean_closure_set(v___f_1217_, 5, v_hoverPos_1208_);
v___x_1218_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f(v___f_1217_, v_cmdStx_1209_);
if (lean_obj_tag(v___x_1218_) == 0)
{
return v___x_1212_;
}
else
{
lean_dec_ref_known(v___x_1218_, 1);
return v_isCursorOnWhitespace_1210_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_1207_ = stack[0].m_obj;
lean_object* v_hoverPos_1208_ = stack[1].m_obj;
lean_object* v_cmdStx_1209_ = stack[2].m_obj;
uint8_t v_res_1219_;
v_res_1219_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(v_fileMap_1207_, v_hoverPos_1208_, v_cmdStx_1209_);
stack->m_num = v_res_1219_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___boxed(lean_object* v_fileMap_1220_, lean_object* v_hoverPos_1221_, lean_object* v_cmdStx_1222_){
_start:
{
uint8_t v_res_1223_; lean_object* v_r_1224_; 
v_res_1223_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(v_fileMap_1220_, v_hoverPos_1221_, v_cmdStx_1222_);
v_r_1224_ = lean_box(v_res_1223_);
return v_r_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticFieldCompletion_x3f(lean_object* v_fileMap_1225_, lean_object* v_hoverPos_1226_, lean_object* v_cmdStx_1227_, lean_object* v_infoTree_1228_){
_start:
{
uint8_t v___x_1229_; 
lean_inc(v_hoverPos_1226_);
v___x_1229_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(v_fileMap_1225_, v_hoverPos_1226_, v_cmdStx_1227_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; 
lean_dec_ref(v_infoTree_1228_);
lean_dec(v_hoverPos_1226_);
v___x_1230_ = lean_box(0);
return v___x_1230_;
}
else
{
lean_object* v___x_1231_; 
v___x_1231_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt(v_infoTree_1228_, v_hoverPos_1226_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_box(0);
return v___x_1232_;
}
else
{
lean_object* v_val_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1255_; 
v_val_1233_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1235_ = v___x_1231_;
v_isShared_1236_ = v_isSharedCheck_1255_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_val_1233_);
lean_dec(v___x_1231_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1255_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_fst_1237_; lean_object* v_snd_1238_; lean_object* v___x_1239_; 
v_fst_1237_ = lean_ctor_get(v_val_1233_, 0);
lean_inc(v_fst_1237_);
v_snd_1238_ = lean_ctor_get(v_val_1233_, 1);
lean_inc(v_snd_1238_);
lean_dec(v_val_1233_);
v___x_1239_ = l_Lean_Expr_getAppFn(v_snd_1238_);
lean_dec(v_snd_1238_);
if (lean_obj_tag(v___x_1239_) == 4)
{
lean_object* v_toCommandContextInfo_1240_; lean_object* v_declName_1241_; lean_object* v_env_1242_; uint8_t v___x_1243_; 
v_toCommandContextInfo_1240_ = lean_ctor_get(v_fst_1237_, 0);
v_declName_1241_ = lean_ctor_get(v___x_1239_, 0);
lean_inc_n(v_declName_1241_, 2);
lean_dec_ref_known(v___x_1239_, 2);
v_env_1242_ = lean_ctor_get(v_toCommandContextInfo_1240_, 0);
lean_inc_ref(v_env_1242_);
v___x_1243_ = l_Lean_isStructure(v_env_1242_, v_declName_1241_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
lean_dec(v_declName_1241_);
lean_dec(v_fst_1237_);
lean_del_object(v___x_1235_);
v___x_1244_ = lean_box(0);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_box(0);
v___x_1247_ = lean_box(0);
v___x_1248_ = l_Lean_LocalContext_empty;
v___x_1249_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1246_);
lean_ctor_set(v___x_1249_, 1, v___x_1247_);
lean_ctor_set(v___x_1249_, 2, v___x_1248_);
lean_ctor_set(v___x_1249_, 3, v_declName_1241_);
v___x_1250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1245_);
lean_ctor_set(v___x_1250_, 1, v_fst_1237_);
lean_ctor_set(v___x_1250_, 2, v___x_1249_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1250_);
v___x_1252_ = v___x_1235_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
else
{
lean_object* v___x_1254_; 
lean_dec_ref(v___x_1239_);
lean_dec(v_fst_1237_);
lean_del_object(v___x_1235_);
v___x_1254_ = lean_box(0);
return v___x_1254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findSyntheticCompletions(lean_object* v_fileMap_1258_, lean_object* v_hoverPos_1259_, lean_object* v_cmdStx_1260_, lean_object* v_infoTree_1261_){
_start:
{
lean_object* v___y_1263_; lean_object* v___x_1269_; 
lean_inc_ref(v_infoTree_1261_);
lean_inc(v_cmdStx_1260_);
lean_inc_ref(v_fileMap_1258_);
v___x_1269_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(v_fileMap_1258_, v_hoverPos_1259_, v_cmdStx_1260_, v_infoTree_1261_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v___x_1270_; 
lean_inc_ref(v_infoTree_1261_);
lean_inc(v_hoverPos_1259_);
v___x_1270_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticFieldCompletion_x3f(v_fileMap_1258_, v_hoverPos_1259_, v_cmdStx_1260_, v_infoTree_1261_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(v_hoverPos_1259_, v_infoTree_1261_);
v___y_1263_ = v___x_1271_;
goto v___jp_1262_;
}
else
{
lean_dec_ref(v_infoTree_1261_);
lean_dec(v_hoverPos_1259_);
v___y_1263_ = v___x_1270_;
goto v___jp_1262_;
}
}
else
{
lean_dec_ref(v_infoTree_1261_);
lean_dec(v_cmdStx_1260_);
lean_dec(v_hoverPos_1259_);
lean_dec_ref(v_fileMap_1258_);
v___y_1263_ = v___x_1269_;
goto v___jp_1262_;
}
v___jp_1262_:
{
if (lean_obj_tag(v___y_1263_) == 0)
{
lean_object* v___x_1264_; 
v___x_1264_ = ((lean_object*)(l_Lean_Server_Completion_findSyntheticCompletions___closed__0));
return v___x_1264_;
}
else
{
lean_object* v_val_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v_val_1265_ = lean_ctor_get(v___y_1263_, 0);
lean_inc(v_val_1265_);
lean_dec_ref_known(v___y_1263_, 1);
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_mk_empty_array_with_capacity(v___x_1266_);
v___x_1268_ = lean_array_push(v___x_1267_, v_val_1265_);
return v___x_1268_;
}
}
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Completion_CompletionUtils(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion_SyntheticCompletion(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Completion_CompletionUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Completion_SyntheticCompletion(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
lean_object* initialize_Lean_Server_Completion_CompletionUtils(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_SyntheticCompletion(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Completion_SyntheticCompletion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Completion_SyntheticCompletion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Completion_SyntheticCompletion(builtin);
}
#ifdef __cplusplus
}
#endif
