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
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(lean_object* v_gt_1_, lean_object* v_a_2_, lean_object* v_b_3_){
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg___boxed(lean_object* v_gt_10_, lean_object* v_a_11_, lean_object* v_b_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(v_gt_10_, v_a_11_, v_b_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter(lean_object* v_00_u03b1_15_, lean_object* v_gt_16_, lean_object* v_a_17_, lean_object* v_b_18_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(v_gt_16_, v_a_17_, v_b_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___boxed(lean_object* v_00_u03b1_20_, lean_object* v_gt_21_, lean_object* v_a_22_, lean_object* v_b_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter(v_00_u03b1_20_, v_gt_21_, v_a_22_, v_b_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__0___redArg(lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
if (lean_obj_tag(v_a_26_) == 0)
{
lean_object* v___x_28_; 
v___x_28_ = l_List_reverse___redArg(v_a_27_);
return v___x_28_;
}
else
{
lean_object* v_head_29_; lean_object* v_tail_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_42_; 
v_head_29_ = lean_ctor_get(v_a_26_, 0);
v_tail_30_ = lean_ctor_get(v_a_26_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_a_26_);
if (v_isSharedCheck_42_ == 0)
{
v___x_32_ = v_a_26_;
v_isShared_33_ = v_isSharedCheck_42_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_tail_30_);
lean_inc(v_head_29_);
lean_dec(v_a_26_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_42_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___y_35_; 
if (lean_obj_tag(v_head_29_) == 0)
{
lean_object* v___x_40_; 
v___x_40_ = lean_box(0);
v___y_35_ = v___x_40_;
goto v___jp_34_;
}
else
{
lean_object* v_val_41_; 
v_val_41_ = lean_ctor_get(v_head_29_, 0);
lean_inc(v_val_41_);
lean_dec_ref_known(v_head_29_, 1);
v___y_35_ = v_val_41_;
goto v___jp_34_;
}
v___jp_34_:
{
lean_object* v___x_37_; 
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 1, v_a_27_);
lean_ctor_set(v___x_32_, 0, v___y_35_);
v___x_37_ = v___x_32_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___y_35_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_a_27_);
v___x_37_ = v_reuseFailAlloc_39_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
v_a_26_ = v_tail_30_;
v_a_27_ = v___x_37_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__1___redArg(lean_object* v_gt_43_, lean_object* v_x_44_, lean_object* v_x_45_){
_start:
{
if (lean_obj_tag(v_x_45_) == 0)
{
lean_dec_ref(v_gt_43_);
return v_x_44_;
}
else
{
lean_object* v_head_46_; lean_object* v_tail_47_; uint8_t v___x_48_; 
v_head_46_ = lean_ctor_get(v_x_45_, 0);
lean_inc_n(v_head_46_, 2);
v_tail_47_ = lean_ctor_get(v_x_45_, 1);
lean_inc(v_tail_47_);
lean_dec_ref_known(v_x_45_, 2);
lean_inc(v_x_44_);
lean_inc_ref(v_gt_43_);
v___x_48_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(v_gt_43_, v_x_44_, v_head_46_);
if (v___x_48_ == 0)
{
lean_dec(v_x_44_);
v_x_44_ = v_head_46_;
v_x_45_ = v_tail_47_;
goto _start;
}
else
{
lean_dec(v_head_46_);
v_x_45_ = v_tail_47_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose___redArg(lean_object* v_gt_51_, lean_object* v_f_52_, lean_object* v_ctx_53_, lean_object* v_info_54_, lean_object* v_cs_55_, lean_object* v_childValues_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v_bestChildValue_60_; lean_object* v___x_61_; 
v___x_57_ = lean_box(0);
v___x_58_ = lean_box(0);
v___x_59_ = l_List_mapTR_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__0___redArg(v_childValues_56_, v___x_58_);
lean_inc_ref(v_gt_51_);
v_bestChildValue_60_ = l_List_foldl___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__1___redArg(v_gt_51_, v___x_57_, v___x_59_);
v___x_61_ = lean_apply_3(v_f_52_, v_ctx_53_, v_info_54_, v_cs_55_);
if (lean_obj_tag(v___x_61_) == 1)
{
uint8_t v___x_62_; 
lean_inc(v_bestChildValue_60_);
lean_inc_ref(v___x_61_);
v___x_62_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(v_gt_51_, v___x_61_, v_bestChildValue_60_);
if (v___x_62_ == 0)
{
lean_dec_ref_known(v___x_61_, 1);
return v_bestChildValue_60_;
}
else
{
lean_dec(v_bestChildValue_60_);
return v___x_61_;
}
}
else
{
lean_dec(v___x_61_);
lean_dec_ref(v_gt_51_);
return v_bestChildValue_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose(lean_object* v_00_u03b1_63_, lean_object* v_gt_64_, lean_object* v_f_65_, lean_object* v_ctx_66_, lean_object* v_info_67_, lean_object* v_cs_68_, lean_object* v_childValues_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose___redArg(v_gt_64_, v_f_65_, v_ctx_66_, v_info_67_, v_cs_68_, v_childValues_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__0(lean_object* v_00_u03b1_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_List_mapTR_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__0___redArg(v_a_72_, v_a_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__1(lean_object* v_00_u03b1_75_, lean_object* v_gt_76_, lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_List_foldl___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__1___redArg(v_gt_76_, v_x_77_, v_x_78_);
return v___x_79_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0(lean_object* v_x_80_, lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
uint8_t v___x_83_; 
v___x_83_ = 1;
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0___boxed(lean_object* v_x_84_, lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0(v_x_84_, v_x_85_, v_x_86_);
lean_dec_ref(v_x_86_);
lean_dec_ref(v_x_85_);
lean_dec_ref(v_x_84_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(lean_object* v_msg_96_){
_start:
{
lean_object* v___f_97_; lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___f_101_; lean_object* v___f_102_; lean_object* v___f_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___f_97_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0));
v___f_98_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1));
v___f_99_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2));
v___f_100_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3));
v___f_101_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4));
v___f_102_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5));
v___f_103_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6));
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___f_97_);
lean_ctor_set(v___x_104_, 1, v___f_98_);
v___x_105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___f_99_);
lean_ctor_set(v___x_105_, 2, v___f_100_);
lean_ctor_set(v___x_105_, 3, v___f_101_);
lean_ctor_set(v___x_105_, 4, v___f_102_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___f_103_);
v___x_107_ = lean_box(0);
v___x_108_ = l_instInhabitedOfMonad___redArg(v___x_106_, v___x_107_);
v___x_109_ = lean_panic_fn_borrowed(v___x_108_, v_msg_96_);
lean_dec(v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_113_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__2));
v___x_114_ = lean_unsigned_to_nat(21u);
v___x_115_ = lean_unsigned_to_nat(65u);
v___x_116_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__1));
v___x_117_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__0));
v___x_118_ = l_mkPanicMessageWithDecl(v___x_117_, v___x_116_, v___x_115_, v___x_114_, v___x_113_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(lean_object* v_preNode_119_, lean_object* v_postNode_120_, lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
switch(lean_obj_tag(v_x_122_))
{
case 0:
{
lean_object* v_i_123_; lean_object* v_t_124_; lean_object* v___x_125_; 
v_i_123_ = lean_ctor_get(v_x_122_, 0);
lean_inc_ref(v_i_123_);
v_t_124_ = lean_ctor_get(v_x_122_, 1);
lean_inc_ref(v_t_124_);
lean_dec_ref_known(v_x_122_, 2);
v___x_125_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_123_, v_x_121_);
v_x_121_ = v___x_125_;
v_x_122_ = v_t_124_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_121_) == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec_ref_known(v_x_122_, 2);
lean_dec(v_postNode_120_);
lean_dec_ref(v_preNode_119_);
v___x_127_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3);
v___x_128_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(v___x_127_);
return v___x_128_;
}
else
{
lean_object* v_i_129_; lean_object* v_children_130_; lean_object* v_val_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_i_129_ = lean_ctor_get(v_x_122_, 0);
lean_inc_ref_n(v_i_129_, 2);
v_children_130_ = lean_ctor_get(v_x_122_, 1);
lean_inc_ref_n(v_children_130_, 2);
lean_dec_ref_known(v_x_122_, 2);
v_val_131_ = lean_ctor_get(v_x_121_, 0);
lean_inc_n(v_val_131_, 2);
lean_inc_ref(v_preNode_119_);
v___x_132_ = lean_apply_3(v_preNode_119_, v_val_131_, v_i_129_, v_children_130_);
v___x_133_ = lean_unbox(v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_142_; 
lean_dec_ref(v_preNode_119_);
v_isSharedCheck_142_ = !lean_is_exclusive(v_x_121_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v_x_121_, 0);
lean_dec(v_unused_143_);
v___x_135_ = v_x_121_;
v_isShared_136_ = v_isSharedCheck_142_;
goto v_resetjp_134_;
}
else
{
lean_dec(v_x_121_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_142_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_137_ = lean_box(0);
v___x_138_ = lean_apply_4(v_postNode_120_, v_val_131_, v_i_129_, v_children_130_, v___x_137_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_138_);
v___x_140_ = v___x_135_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
else
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_144_ = l_Lean_Elab_Info_updateContext_x3f(v_x_121_, v_i_129_);
v___x_145_ = l_Lean_PersistentArray_toList___redArg(v_children_130_);
v___x_146_ = lean_box(0);
lean_inc(v_postNode_120_);
v___x_147_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(v_preNode_119_, v_postNode_120_, v___x_144_, v___x_145_, v___x_146_);
v___x_148_ = lean_apply_4(v_postNode_120_, v_val_131_, v_i_129_, v_children_130_, v___x_147_);
v___x_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
}
default: 
{
lean_object* v___x_150_; 
lean_dec_ref_known(v_x_122_, 1);
lean_dec(v_x_121_);
lean_dec(v_postNode_120_);
lean_dec_ref(v_preNode_119_);
v___x_150_ = lean_box(0);
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(lean_object* v_preNode_151_, lean_object* v_postNode_152_, lean_object* v___x_153_, lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
lean_object* v___x_156_; 
lean_dec(v___x_153_);
lean_dec(v_postNode_152_);
lean_dec_ref(v_preNode_151_);
v___x_156_ = l_List_reverse___redArg(v_x_155_);
return v___x_156_;
}
else
{
lean_object* v_head_157_; lean_object* v_tail_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_167_; 
v_head_157_ = lean_ctor_get(v_x_154_, 0);
v_tail_158_ = lean_ctor_get(v_x_154_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_167_ == 0)
{
v___x_160_ = v_x_154_;
v_isShared_161_ = v_isSharedCheck_167_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_tail_158_);
lean_inc(v_head_157_);
lean_dec(v_x_154_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_167_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
lean_inc(v___x_153_);
lean_inc(v_postNode_152_);
lean_inc_ref(v_preNode_151_);
v___x_162_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v_preNode_151_, v_postNode_152_, v___x_153_, v_head_157_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v_x_155_);
lean_ctor_set(v___x_160_, 0, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_x_155_);
v___x_164_ = v_reuseFailAlloc_166_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
v_x_154_ = v_tail_158_;
v_x_155_ = v___x_164_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(lean_object* v_infoTree_169_, lean_object* v_gt_170_, lean_object* v_f_171_){
_start:
{
lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___f_172_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___closed__0));
v___x_173_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose), 7, 3);
lean_closure_set(v___x_173_, 0, lean_box(0));
lean_closure_set(v___x_173_, 1, v_gt_170_);
lean_closure_set(v___x_173_, 2, v_f_171_);
v___x_174_ = lean_box(0);
v___x_175_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v___f_172_, v___x_173_, v___x_174_, v_infoTree_169_);
if (lean_obj_tag(v___x_175_) == 0)
{
return v___x_174_;
}
else
{
lean_object* v_val_176_; 
v_val_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_176_);
lean_dec_ref_known(v___x_175_, 1);
return v_val_176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f(lean_object* v_00_u03b1_177_, lean_object* v_infoTree_178_, lean_object* v_gt_179_, lean_object* v_f_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(v_infoTree_178_, v_gt_179_, v_f_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0(lean_object* v_00_u03b1_182_, lean_object* v_msg_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(v_msg_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0(lean_object* v_00_u03b1_185_, lean_object* v_preNode_186_, lean_object* v_postNode_187_, lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v_preNode_186_, v_postNode_187_, v_x_188_, v_x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1(lean_object* v_00_u03b1_191_, lean_object* v_preNode_192_, lean_object* v_postNode_193_, lean_object* v___x_194_, lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(v_preNode_192_, v_postNode_193_, v___x_194_, v_x_195_, v_x_196_);
return v___x_197_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter(lean_object* v_a_198_, lean_object* v_b_199_){
_start:
{
lean_object* v_snd_200_; lean_object* v_snd_201_; uint8_t v___y_203_; lean_object* v___x_206_; uint8_t v___x_207_; uint8_t v___y_209_; 
v_snd_200_ = lean_ctor_get(v_a_198_, 1);
v_snd_201_ = lean_ctor_get(v_b_199_, 1);
v___x_206_ = l_Lean_Elab_Info_lctx(v_snd_200_);
v___x_207_ = l_Lean_LocalContext_isEmpty(v___x_206_);
lean_dec_ref(v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = l_Lean_Elab_Info_lctx(v_snd_201_);
v___x_214_ = l_Lean_LocalContext_isEmpty(v___x_213_);
lean_dec_ref(v___x_213_);
if (v___x_214_ == 0)
{
v___y_209_ = v___x_214_;
goto v___jp_208_;
}
else
{
return v___x_214_;
}
}
else
{
uint8_t v___x_215_; 
v___x_215_ = 0;
v___y_209_ = v___x_215_;
goto v___jp_208_;
}
v___jp_202_:
{
uint8_t v___x_204_; 
v___x_204_ = l_Lean_Elab_Info_isSmaller(v_snd_200_, v_snd_201_);
if (v___x_204_ == 0)
{
uint8_t v___x_205_; 
v___x_205_ = l_Lean_Elab_Info_isSmaller(v_snd_201_, v_snd_200_);
if (v___x_205_ == 0)
{
return v___x_205_;
}
else
{
return v___x_204_;
}
}
else
{
return v___y_203_;
}
}
v___jp_208_:
{
uint8_t v___x_210_; 
v___x_210_ = 1;
if (v___x_207_ == 0)
{
v___y_203_ = v___x_210_;
goto v___jp_202_;
}
else
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = l_Lean_Elab_Info_lctx(v_snd_201_);
v___x_212_ = l_Lean_LocalContext_isEmpty(v___x_211_);
lean_dec_ref(v___x_211_);
if (v___x_212_ == 0)
{
return v___y_209_;
}
else
{
v___y_203_ = v___x_210_;
goto v___jp_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter___boxed(lean_object* v_a_216_, lean_object* v_b_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter(v_a_216_, v_b_217_);
lean_dec_ref(v_b_217_);
lean_dec_ref(v_a_216_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0(lean_object* v_hoverPos_220_, lean_object* v_ctx_221_, lean_object* v_info_222_, lean_object* v_x_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = l_Lean_Elab_Info_occursInOrOnBoundary(v_info_222_, v_hoverPos_220_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
lean_dec_ref(v_info_222_);
lean_dec_ref(v_ctx_221_);
v___x_225_ = lean_box(0);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_ctx_221_);
lean_ctor_set(v___x_226_, 1, v_info_222_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0___boxed(lean_object* v_hoverPos_228_, lean_object* v_ctx_229_, lean_object* v_info_230_, lean_object* v_x_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0(v_hoverPos_228_, v_ctx_229_, v_info_230_, v_x_231_);
lean_dec_ref(v_x_231_);
lean_dec(v_hoverPos_228_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f(lean_object* v_hoverPos_234_, lean_object* v_infoTree_235_){
_start:
{
lean_object* v___f_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___f_236_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_236_, 0, v_hoverPos_234_);
v___x_237_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___closed__0));
v___x_238_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(v_infoTree_235_, v___x_237_, v___f_236_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__2(lean_object* v_msg_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_panic_fn_borrowed(v___x_240_, v_msg_239_);
return v___x_241_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0(lean_object* v_hoverPos_242_, lean_object* v_x_243_){
_start:
{
uint8_t v___x_244_; lean_object* v___x_245_; 
v___x_244_ = 0;
v___x_245_ = l_Lean_Syntax_getRange_x3f(v_x_243_, v___x_244_);
if (lean_obj_tag(v___x_245_) == 0)
{
return v___x_244_;
}
else
{
lean_object* v_val_246_; uint8_t v___x_247_; uint8_t v___x_248_; 
v_val_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_val_246_);
lean_dec_ref_known(v___x_245_, 1);
v___x_247_ = 1;
v___x_248_ = l_Lean_Syntax_Range_contains(v_val_246_, v_hoverPos_242_, v___x_247_);
lean_dec(v_val_246_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0___boxed(lean_object* v_hoverPos_249_, lean_object* v_x_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0(v_hoverPos_249_, v_x_250_);
lean_dec(v_x_250_);
lean_dec(v_hoverPos_249_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1(lean_object* v_stx_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = l_Lean_Syntax_hasArgs(v_stx_253_);
if (v___x_254_ == 0)
{
uint8_t v___x_255_; 
v___x_255_ = 1;
return v___x_255_;
}
else
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1___boxed(lean_object* v_stx_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1(v_stx_257_);
lean_dec(v_stx_257_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(lean_object* v_x_272_){
_start:
{
if (lean_obj_tag(v_x_272_) == 0)
{
return v_x_272_;
}
else
{
lean_object* v_head_273_; lean_object* v_tail_274_; lean_object* v_fst_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v_head_273_ = lean_ctor_get(v_x_272_, 0);
v_tail_274_ = lean_ctor_get(v_x_272_, 1);
v_fst_275_ = lean_ctor_get(v_head_273_, 0);
v___x_276_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
lean_inc(v_fst_275_);
v___x_277_ = l_Lean_Syntax_isOfKind(v_fst_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6));
lean_inc(v_fst_275_);
v___x_279_ = l_Lean_Syntax_isOfKind(v_fst_275_, v___x_278_);
if (v___x_279_ == 0)
{
lean_inc(v_tail_274_);
lean_dec_ref_known(v_x_272_, 2);
v_x_272_ = v_tail_274_;
goto _start;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = l_Lean_Syntax_getArg(v_fst_275_, v___x_281_);
v___x_283_ = l_Lean_Syntax_isOfKind(v___x_282_, v___x_276_);
if (v___x_283_ == 0)
{
lean_inc(v_tail_274_);
lean_dec_ref_known(v_x_272_, 2);
v_x_272_ = v_tail_274_;
goto _start;
}
else
{
return v_x_272_;
}
}
}
else
{
return v_x_272_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(lean_object* v_x_291_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
uint8_t v___x_292_; 
v___x_292_ = 0;
return v___x_292_;
}
else
{
lean_object* v_head_293_; lean_object* v_tail_294_; lean_object* v_fst_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_head_293_ = lean_ctor_get(v_x_291_, 0);
lean_inc(v_head_293_);
v_tail_294_ = lean_ctor_get(v_x_291_, 1);
lean_inc(v_tail_294_);
lean_dec_ref_known(v_x_291_, 2);
v_fst_295_ = lean_ctor_get(v_head_293_, 0);
lean_inc_n(v_fst_295_, 2);
lean_dec(v_head_293_);
v___x_296_ = ((lean_object*)(l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1));
v___x_297_ = l_Lean_Syntax_isOfKind(v_fst_295_, v___x_296_);
if (v___x_297_ == 0)
{
lean_dec(v_fst_295_);
v_x_291_ = v_tail_294_;
goto _start;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = l_Lean_Syntax_getArg(v_fst_295_, v___x_299_);
lean_dec(v_fst_295_);
v___x_301_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
v___x_302_ = l_Lean_Syntax_isOfKind(v___x_300_, v___x_301_);
if (v___x_302_ == 0)
{
v_x_291_ = v_tail_294_;
goto _start;
}
else
{
lean_dec(v_tail_294_);
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___boxed(lean_object* v_x_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(v_x_304_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_311_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3));
v___x_312_ = lean_unsigned_to_nat(14u);
v___x_313_ = lean_unsigned_to_nat(22u);
v___x_314_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2));
v___x_315_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1));
v___x_316_ = l_mkPanicMessageWithDecl(v___x_315_, v___x_314_, v___x_313_, v___x_312_, v___x_311_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(lean_object* v_hoverPos_317_, lean_object* v_infoTree_318_){
_start:
{
lean_object* v___x_319_; 
lean_inc(v_hoverPos_317_);
v___x_319_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f(v_hoverPos_317_, v_infoTree_318_);
if (lean_obj_tag(v___x_319_) == 1)
{
lean_object* v_val_320_; lean_object* v_fst_321_; lean_object* v_snd_322_; lean_object* v___f_323_; lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_val_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_val_320_);
lean_dec_ref_known(v___x_319_, 1);
v_fst_321_ = lean_ctor_get(v_val_320_, 0);
lean_inc(v_fst_321_);
v_snd_322_ = lean_ctor_get(v_val_320_, 1);
lean_inc(v_snd_322_);
lean_dec(v_val_320_);
lean_inc(v_hoverPos_317_);
v___f_323_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_323_, 0, v_hoverPos_317_);
v___f_324_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0));
v___x_325_ = l_Lean_Elab_Info_stx(v_snd_322_);
v___x_326_ = l_Lean_Syntax_findStack_x3f(v___x_325_, v___f_323_, v___f_324_);
if (lean_obj_tag(v___x_326_) == 1)
{
lean_object* v_val_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_383_; 
v_val_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_383_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_383_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_val_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_383_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v_stack_331_; lean_object* v___x_332_; 
v_stack_331_ = l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(v_val_327_);
v___x_332_ = l_List_head_x3f___redArg(v_stack_331_);
if (lean_obj_tag(v___x_332_) == 1)
{
lean_object* v_val_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_381_; 
v_val_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_381_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_381_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_val_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_381_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v_fst_337_; lean_object* v___y_339_; uint8_t v___y_340_; lean_object* v___y_341_; lean_object* v___y_350_; uint8_t v___y_351_; lean_object* v___y_352_; uint8_t v_isDotIdCompletion_361_; lean_object* v_fst_363_; uint8_t v_snd_364_; 
v_fst_337_ = lean_ctor_get(v_val_333_, 0);
lean_inc(v_fst_337_);
lean_dec(v_val_333_);
v_isDotIdCompletion_361_ = l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(v_stack_331_);
if (v_isDotIdCompletion_361_ == 0)
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
lean_inc(v_fst_337_);
v___x_370_ = l_Lean_Syntax_isOfKind(v_fst_337_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6));
lean_inc(v_fst_337_);
v___x_372_ = l_Lean_Syntax_isOfKind(v_fst_337_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; 
lean_dec(v_fst_337_);
lean_del_object(v___x_335_);
lean_del_object(v___x_329_);
lean_dec(v_snd_322_);
lean_dec(v_fst_321_);
lean_dec(v_hoverPos_317_);
v___x_373_ = lean_box(0);
return v___x_373_;
}
else
{
lean_object* v___x_374_; lean_object* v_id_375_; uint8_t v___x_376_; 
v___x_374_ = lean_unsigned_to_nat(0u);
v_id_375_ = l_Lean_Syntax_getArg(v_fst_337_, v___x_374_);
lean_inc(v_id_375_);
v___x_376_ = l_Lean_Syntax_isOfKind(v_id_375_, v___x_369_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec(v_id_375_);
lean_dec(v_fst_337_);
lean_del_object(v___x_335_);
lean_del_object(v___x_329_);
lean_dec(v_snd_322_);
lean_dec(v_fst_321_);
lean_dec(v_hoverPos_317_);
v___x_377_ = lean_box(0);
return v___x_377_;
}
else
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_TSyntax_getId(v_id_375_);
lean_dec(v_id_375_);
v_fst_363_ = v___x_378_;
v_snd_364_ = v___x_376_;
goto v___jp_362_;
}
}
}
else
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_TSyntax_getId(v_fst_337_);
v_fst_363_ = v___x_379_;
v_snd_364_ = v_isDotIdCompletion_361_;
goto v___jp_362_;
}
}
else
{
lean_object* v___x_380_; 
lean_dec(v_fst_337_);
lean_del_object(v___x_335_);
lean_del_object(v___x_329_);
lean_dec(v_snd_322_);
lean_dec(v_fst_321_);
lean_dec(v_hoverPos_317_);
v___x_380_ = lean_box(0);
return v___x_380_;
}
v___jp_338_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_342_ = l_Lean_Elab_Info_lctx(v_snd_322_);
lean_dec(v_snd_322_);
v___x_343_ = lean_box(0);
v___x_344_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_344_, 0, v_fst_337_);
lean_ctor_set(v___x_344_, 1, v___y_339_);
lean_ctor_set(v___x_344_, 2, v___x_342_);
lean_ctor_set(v___x_344_, 3, v___x_343_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*4, v___y_340_);
v___x_345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_345_, 0, v___y_341_);
lean_ctor_set(v___x_345_, 1, v_fst_321_);
lean_ctor_set(v___x_345_, 2, v___x_344_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_345_);
v___x_347_ = v___x_335_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
v___jp_349_:
{
lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_nat_add(v_hoverPos_317_, v___x_353_);
v___x_355_ = lean_nat_dec_le(v___x_354_, v___y_352_);
lean_dec(v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
lean_dec(v___y_352_);
lean_del_object(v___x_329_);
lean_dec(v_hoverPos_317_);
v___x_356_ = lean_box(0);
v___y_339_ = v___y_350_;
v___y_340_ = v___y_351_;
v___y_341_ = v___x_356_;
goto v___jp_338_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_357_ = lean_nat_sub(v___y_352_, v_hoverPos_317_);
lean_dec(v_hoverPos_317_);
lean_dec(v___y_352_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_357_);
v___x_359_ = v___x_329_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
v___y_339_ = v___y_350_;
v___y_340_ = v___y_351_;
v___y_341_ = v___x_359_;
goto v___jp_338_;
}
}
}
v___jp_362_:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Syntax_getTailPos_x3f(v_fst_337_, v_isDotIdCompletion_361_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_obj_once(&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4, &l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_once, _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4);
v___x_367_ = l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__2(v___x_366_);
v___y_350_ = v_fst_363_;
v___y_351_ = v_snd_364_;
v___y_352_ = v___x_367_;
goto v___jp_349_;
}
else
{
lean_object* v_val_368_; 
v_val_368_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_val_368_);
lean_dec_ref_known(v___x_365_, 1);
v___y_350_ = v_fst_363_;
v___y_351_ = v_snd_364_;
v___y_352_ = v_val_368_;
goto v___jp_349_;
}
}
}
}
else
{
lean_object* v___x_382_; 
lean_dec(v___x_332_);
lean_dec(v_stack_331_);
lean_del_object(v___x_329_);
lean_dec(v_snd_322_);
lean_dec(v_fst_321_);
lean_dec(v_hoverPos_317_);
v___x_382_ = lean_box(0);
return v___x_382_;
}
}
}
else
{
lean_object* v___x_384_; 
lean_dec(v___x_326_);
lean_dec(v_snd_322_);
lean_dec(v_fst_321_);
lean_dec(v_hoverPos_317_);
v___x_384_ = lean_box(0);
return v___x_384_;
}
}
else
{
lean_object* v___x_385_; 
lean_dec(v___x_319_);
lean_dec(v_hoverPos_317_);
v___x_385_ = lean_box(0);
return v___x_385_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(lean_object* v_fileMap_386_, lean_object* v_hoverPos_387_){
_start:
{
lean_object* v_source_388_; uint8_t v___x_389_; 
v_source_388_ = lean_ctor_get(v_fileMap_386_, 0);
v___x_389_ = lean_string_utf8_at_end(v_source_388_, v_hoverPos_387_);
if (v___x_389_ == 0)
{
uint32_t v___x_390_; uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_390_ = lean_string_utf8_get(v_source_388_, v_hoverPos_387_);
v___x_391_ = 32;
v___x_392_ = lean_uint32_dec_eq(v___x_390_, v___x_391_);
if (v___x_392_ == 0)
{
uint32_t v___x_393_; uint8_t v___x_394_; 
v___x_393_ = 9;
v___x_394_ = lean_uint32_dec_eq(v___x_390_, v___x_393_);
if (v___x_394_ == 0)
{
uint32_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = 13;
v___x_396_ = lean_uint32_dec_eq(v___x_390_, v___x_395_);
if (v___x_396_ == 0)
{
uint32_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 10;
v___x_398_ = lean_uint32_dec_eq(v___x_390_, v___x_397_);
return v___x_398_;
}
else
{
return v___x_396_;
}
}
else
{
return v___x_394_;
}
}
else
{
return v___x_392_;
}
}
else
{
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace___boxed(lean_object* v_fileMap_399_, lean_object* v_hoverPos_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_399_, v_hoverPos_400_);
lean_dec(v_hoverPos_400_);
lean_dec_ref(v_fileMap_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(lean_object* v_fileMap_403_, lean_object* v_hoverPos_404_){
_start:
{
lean_object* v_source_405_; uint8_t v___x_418_; 
v_source_405_ = lean_ctor_get(v_fileMap_403_, 0);
v___x_418_ = lean_string_utf8_at_end(v_source_405_, v_hoverPos_404_);
if (v___x_418_ == 0)
{
uint32_t v___x_419_; uint32_t v___x_420_; uint8_t v___x_421_; 
v___x_419_ = lean_string_utf8_get(v_source_405_, v_hoverPos_404_);
v___x_420_ = 32;
v___x_421_ = lean_uint32_dec_eq(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
uint32_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = 9;
v___x_423_ = lean_uint32_dec_eq(v___x_419_, v___x_422_);
if (v___x_423_ == 0)
{
uint32_t v___x_424_; uint8_t v___x_425_; 
v___x_424_ = 13;
v___x_425_ = lean_uint32_dec_eq(v___x_419_, v___x_424_);
if (v___x_425_ == 0)
{
uint32_t v___x_426_; uint8_t v___x_427_; 
v___x_426_ = 10;
v___x_427_ = lean_uint32_dec_eq(v___x_419_, v___x_426_);
if (v___x_427_ == 0)
{
return v___x_427_;
}
else
{
goto v___jp_406_;
}
}
else
{
goto v___jp_406_;
}
}
else
{
goto v___jp_406_;
}
}
else
{
goto v___jp_406_;
}
}
else
{
goto v___jp_406_;
}
v___jp_406_:
{
lean_object* v___x_407_; lean_object* v___x_408_; uint32_t v___x_409_; uint32_t v___x_410_; uint8_t v___x_411_; 
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_nat_sub(v_hoverPos_404_, v___x_407_);
v___x_409_ = lean_string_utf8_get(v_source_405_, v___x_408_);
lean_dec(v___x_408_);
v___x_410_ = 32;
v___x_411_ = lean_uint32_dec_eq(v___x_409_, v___x_410_);
if (v___x_411_ == 0)
{
uint32_t v___x_412_; uint8_t v___x_413_; 
v___x_412_ = 9;
v___x_413_ = lean_uint32_dec_eq(v___x_409_, v___x_412_);
if (v___x_413_ == 0)
{
uint32_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = 13;
v___x_415_ = lean_uint32_dec_eq(v___x_409_, v___x_414_);
if (v___x_415_ == 0)
{
uint32_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = 10;
v___x_417_ = lean_uint32_dec_eq(v___x_409_, v___x_416_);
return v___x_417_;
}
else
{
return v___x_415_;
}
}
else
{
return v___x_413_;
}
}
else
{
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace___boxed(lean_object* v_fileMap_428_, lean_object* v_hoverPos_429_){
_start:
{
uint8_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_428_, v_hoverPos_429_);
lean_dec(v_hoverPos_429_);
lean_dec_ref(v_fileMap_428_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(lean_object* v_stx_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
lean_inc(v_stx_445_);
v___x_446_ = l_Lean_Syntax_getKind(v_stx_445_);
v___x_447_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2));
v___x_448_ = lean_name_eq(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_450_ = lean_name_eq(v___x_446_, v___x_449_);
lean_dec(v___x_446_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
lean_dec(v_stx_445_);
v___x_451_ = lean_box(0);
return v___x_451_;
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_unsigned_to_nat(1u);
v___x_453_ = l_Lean_Syntax_getArg(v_stx_445_, v___x_452_);
lean_dec(v_stx_445_);
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v___x_446_);
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = l_Lean_Syntax_getArg(v_stx_445_, v___x_455_);
lean_dec(v_stx_445_);
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(lean_object* v_fileMap_458_, lean_object* v_hoverPos_459_, lean_object* v_hoverFilePos_460_, lean_object* v_stx_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(v_stx_461_);
if (lean_obj_tag(v___x_462_) == 1)
{
lean_object* v_val_463_; uint8_t v___x_464_; lean_object* v___x_465_; 
v_val_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_val_463_);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = 0;
v___x_465_ = l_Lean_Syntax_getPos_x3f(v_val_463_, v___x_464_);
lean_dec(v_val_463_);
if (lean_obj_tag(v___x_465_) == 1)
{
lean_object* v_val_466_; lean_object* v___x_467_; lean_object* v_column_468_; lean_object* v_column_469_; uint8_t v___x_470_; 
v_val_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_466_);
lean_dec_ref_known(v___x_465_, 1);
lean_inc_ref(v_fileMap_458_);
v___x_467_ = l_Lean_FileMap_toPosition(v_fileMap_458_, v_val_466_);
lean_dec(v_val_466_);
v_column_468_ = lean_ctor_get(v___x_467_, 1);
lean_inc(v_column_468_);
lean_dec_ref(v___x_467_);
v_column_469_ = lean_ctor_get(v_hoverFilePos_460_, 1);
v___x_470_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_458_, v_hoverPos_459_);
lean_dec_ref(v_fileMap_458_);
if (v___x_470_ == 0)
{
lean_dec(v_column_468_);
return v___x_470_;
}
else
{
uint8_t v_isCursorInTacticBlock_471_; 
v_isCursorInTacticBlock_471_ = lean_nat_dec_eq(v_column_469_, v_column_468_);
lean_dec(v_column_468_);
return v_isCursorInTacticBlock_471_;
}
}
else
{
lean_dec(v___x_465_);
lean_dec_ref(v_fileMap_458_);
return v___x_464_;
}
}
else
{
uint8_t v___x_472_; 
lean_dec(v___x_462_);
lean_dec_ref(v_fileMap_458_);
v___x_472_ = 0;
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation___boxed(lean_object* v_fileMap_473_, lean_object* v_hoverPos_474_, lean_object* v_hoverFilePos_475_, lean_object* v_stx_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_473_, v_hoverPos_474_, v_hoverFilePos_475_, v_stx_476_);
lean_dec_ref(v_hoverFilePos_475_);
lean_dec(v_hoverPos_474_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(lean_object* v_hoverPos_480_, lean_object* v_as_481_, size_t v_i_482_, size_t v_stop_483_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = lean_usize_dec_eq(v_i_482_, v_stop_483_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_array_uget_borrowed(v_as_481_, v_i_482_);
v___x_490_ = l_Lean_Syntax_getTailPos_x3f(v___x_489_, v___x_488_);
if (lean_obj_tag(v___x_490_) == 1)
{
lean_object* v_val_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_val_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_val_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___closed__0));
lean_inc(v___x_489_);
v___x_493_ = l_Lean_Syntax_isToken(v___x_492_, v___x_489_);
if (v___x_493_ == 0)
{
lean_dec(v_val_491_);
goto v___jp_484_;
}
else
{
uint8_t v___x_494_; 
v___x_494_ = lean_nat_dec_le(v_val_491_, v_hoverPos_480_);
if (v___x_494_ == 0)
{
lean_dec(v_val_491_);
goto v___jp_484_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_495_ = l_Lean_Syntax_getTrailingSize(v___x_489_);
v___x_496_ = lean_nat_add(v_val_491_, v___x_495_);
lean_dec(v___x_495_);
lean_dec(v_val_491_);
v___x_497_ = lean_nat_dec_le(v_hoverPos_480_, v___x_496_);
lean_dec(v___x_496_);
if (v___x_497_ == 0)
{
goto v___jp_484_;
}
else
{
return v___x_497_;
}
}
}
}
else
{
lean_dec(v___x_490_);
goto v___jp_484_;
}
}
else
{
uint8_t v___x_498_; 
v___x_498_ = 0;
return v___x_498_;
}
v___jp_484_:
{
size_t v___x_485_; size_t v___x_486_; 
v___x_485_ = ((size_t)1ULL);
v___x_486_ = lean_usize_add(v_i_482_, v___x_485_);
v_i_482_ = v___x_486_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___boxed(lean_object* v_hoverPos_499_, lean_object* v_as_500_, lean_object* v_i_501_, lean_object* v_stop_502_){
_start:
{
size_t v_i_boxed_503_; size_t v_stop_boxed_504_; uint8_t v_res_505_; lean_object* v_r_506_; 
v_i_boxed_503_ = lean_unbox_usize(v_i_501_);
lean_dec(v_i_501_);
v_stop_boxed_504_ = lean_unbox_usize(v_stop_502_);
lean_dec(v_stop_502_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_499_, v_as_500_, v_i_boxed_503_, v_stop_boxed_504_);
lean_dec_ref(v_as_500_);
lean_dec(v_hoverPos_499_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(lean_object* v_fileMap_507_, lean_object* v_hoverPos_508_, lean_object* v_stx_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(v_stx_509_);
if (lean_obj_tag(v___x_510_) == 1)
{
lean_object* v_val_511_; uint8_t v___x_512_; 
v_val_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_val_511_);
lean_dec_ref_known(v___x_510_, 1);
v___x_512_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_507_, v_hoverPos_508_);
if (v___x_512_ == 0)
{
lean_dec(v_val_511_);
return v___x_512_;
}
else
{
lean_object* v_tactics_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_tactics_513_ = l_Lean_Syntax_getArgs(v_val_511_);
lean_dec(v_val_511_);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = lean_array_get_size(v_tactics_513_);
v___x_516_ = lean_nat_dec_lt(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
lean_dec_ref(v_tactics_513_);
return v___x_516_;
}
else
{
if (v___x_516_ == 0)
{
lean_dec_ref(v_tactics_513_);
return v___x_516_;
}
else
{
size_t v___x_517_; size_t v___x_518_; uint8_t v___x_519_; 
v___x_517_ = ((size_t)0ULL);
v___x_518_ = lean_usize_of_nat(v___x_515_);
v___x_519_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_508_, v_tactics_513_, v___x_517_, v___x_518_);
lean_dec_ref(v_tactics_513_);
return v___x_519_;
}
}
}
}
else
{
uint8_t v___x_520_; 
lean_dec(v___x_510_);
v___x_520_ = 0;
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon___boxed(lean_object* v_fileMap_521_, lean_object* v_hoverPos_522_, lean_object* v_stx_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_521_, v_hoverPos_522_, v_stx_523_);
lean_dec(v_hoverPos_522_);
lean_dec_ref(v_fileMap_521_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(lean_object* v_fileMap_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_fst_528_; lean_object* v_snd_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_551_; 
v_fst_528_ = lean_ctor_get(v_a_527_, 0);
v_snd_529_ = lean_ctor_get(v_a_527_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_a_527_);
if (v_isSharedCheck_551_ == 0)
{
v___x_531_ = v_a_527_;
v_isShared_532_ = v_isSharedCheck_551_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_snd_529_);
lean_inc(v_fst_528_);
lean_dec(v_a_527_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_551_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_source_533_; uint8_t v___x_534_; 
v_source_533_ = lean_ctor_get(v_fileMap_526_, 0);
v___x_534_ = lean_string_utf8_at_end(v_source_533_, v_fst_528_);
if (v___x_534_ == 0)
{
uint32_t v___x_535_; uint32_t v___x_536_; uint8_t v___x_537_; 
v___x_535_ = lean_string_utf8_get(v_source_533_, v_fst_528_);
v___x_536_ = 32;
v___x_537_ = lean_uint32_dec_eq(v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_539_; 
if (v_isShared_532_ == 0)
{
v___x_539_ = v___x_531_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_fst_528_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_snd_529_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_541_ = lean_string_utf8_next(v_source_533_, v_fst_528_);
lean_dec(v_fst_528_);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_add(v_snd_529_, v___x_542_);
lean_dec(v_snd_529_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 1, v___x_543_);
lean_ctor_set(v___x_531_, 0, v___x_541_);
v___x_545_ = v___x_531_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_543_);
v___x_545_ = v_reuseFailAlloc_547_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
v_a_527_ = v___x_545_;
goto _start;
}
}
}
else
{
lean_object* v___x_549_; 
if (v_isShared_532_ == 0)
{
v___x_549_ = v___x_531_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_fst_528_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_snd_529_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg___boxed(lean_object* v_fileMap_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_552_, v_a_553_);
lean_dec_ref(v_fileMap_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(lean_object* v_fileMap_555_, lean_object* v_pos_556_){
_start:
{
lean_object* v_n_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v_snd_560_; 
v_n_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v_pos_556_);
lean_ctor_set(v___x_558_, 1, v_n_557_);
v___x_559_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_555_, v___x_558_);
v_snd_560_ = lean_ctor_get(v___x_559_, 1);
lean_inc(v_snd_560_);
lean_dec_ref(v___x_559_);
return v_snd_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces___boxed(lean_object* v_fileMap_561_, lean_object* v_pos_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(v_fileMap_561_, v_pos_562_);
lean_dec_ref(v_fileMap_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(lean_object* v_fileMap_564_, lean_object* v_inst_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_564_, v_a_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___boxed(lean_object* v_fileMap_568_, lean_object* v_inst_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(v_fileMap_568_, v_inst_569_, v_a_570_);
lean_dec_ref(v_fileMap_568_);
return v_res_571_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(lean_object* v_fileMap_572_, lean_object* v_hoverPos_573_, lean_object* v_leadingTokenTailPos_x3f_574_){
_start:
{
if (lean_obj_tag(v_leadingTokenTailPos_x3f_574_) == 1)
{
lean_object* v_val_575_; lean_object* v_hoverFilePos_576_; lean_object* v_line_577_; lean_object* v_column_578_; lean_object* v_tokenTailFilePos_579_; lean_object* v_line_580_; uint8_t v___x_581_; 
v_val_575_ = lean_ctor_get(v_leadingTokenTailPos_x3f_574_, 0);
lean_inc_ref_n(v_fileMap_572_, 2);
v_hoverFilePos_576_ = l_Lean_FileMap_toPosition(v_fileMap_572_, v_hoverPos_573_);
v_line_577_ = lean_ctor_get(v_hoverFilePos_576_, 0);
lean_inc(v_line_577_);
v_column_578_ = lean_ctor_get(v_hoverFilePos_576_, 1);
lean_inc(v_column_578_);
lean_dec_ref(v_hoverFilePos_576_);
v_tokenTailFilePos_579_ = l_Lean_FileMap_toPosition(v_fileMap_572_, v_val_575_);
v_line_580_ = lean_ctor_get(v_tokenTailFilePos_579_, 0);
lean_inc(v_line_580_);
lean_dec_ref(v_tokenTailFilePos_579_);
v___x_581_ = lean_nat_dec_eq(v_line_577_, v_line_580_);
lean_dec(v_line_577_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_expectedColumn_585_; uint8_t v___x_586_; 
v___x_582_ = l_Lean_FileMap_lineStart(v_fileMap_572_, v_line_580_);
lean_dec(v_line_580_);
v___x_583_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(v_fileMap_572_, v___x_582_);
lean_dec_ref(v_fileMap_572_);
v___x_584_ = lean_unsigned_to_nat(2u);
v_expectedColumn_585_ = lean_nat_add(v___x_583_, v___x_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_nat_dec_eq(v_column_578_, v_expectedColumn_585_);
lean_dec(v_expectedColumn_585_);
lean_dec(v_column_578_);
return v___x_586_;
}
else
{
uint8_t v___x_587_; 
lean_dec(v_line_580_);
lean_dec(v_column_578_);
lean_dec_ref(v_fileMap_572_);
v___x_587_ = lean_nat_dec_le(v_val_575_, v_hoverPos_573_);
return v___x_587_;
}
}
else
{
uint8_t v___x_588_; 
lean_dec_ref(v_fileMap_572_);
v___x_588_ = 1;
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation___boxed(lean_object* v_fileMap_589_, lean_object* v_hoverPos_590_, lean_object* v_leadingTokenTailPos_x3f_591_){
_start:
{
uint8_t v_res_592_; lean_object* v_r_593_; 
v_res_592_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(v_fileMap_589_, v_hoverPos_590_, v_leadingTokenTailPos_x3f_591_);
lean_dec(v_leadingTokenTailPos_x3f_591_);
lean_dec(v_hoverPos_590_);
v_r_593_ = lean_box(v_res_592_);
return v_r_593_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(lean_object* v_a_594_){
_start:
{
switch(lean_obj_tag(v_a_594_))
{
case 0:
{
uint8_t v___x_595_; 
v___x_595_ = 1;
return v___x_595_;
}
case 1:
{
lean_object* v_args_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_args_596_ = lean_ctor_get(v_a_594_, 2);
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_array_get_size(v_args_596_);
v___x_599_ = lean_nat_dec_lt(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
uint8_t v___x_600_; 
v___x_600_ = 1;
return v___x_600_;
}
else
{
if (v___x_599_ == 0)
{
return v___x_599_;
}
else
{
size_t v___x_601_; size_t v___x_602_; uint8_t v___x_603_; 
v___x_601_ = ((size_t)0ULL);
v___x_602_ = lean_usize_of_nat(v___x_598_);
v___x_603_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_args_596_, v___x_601_, v___x_602_);
if (v___x_603_ == 0)
{
return v___x_599_;
}
else
{
uint8_t v___x_604_; 
v___x_604_ = 0;
return v___x_604_;
}
}
}
}
default: 
{
uint8_t v___x_605_; 
v___x_605_ = 0;
return v___x_605_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(lean_object* v_as_606_, size_t v_i_607_, size_t v_stop_608_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = lean_usize_dec_eq(v_i_607_, v_stop_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_array_uget_borrowed(v_as_606_, v_i_607_);
v___x_611_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v___x_610_);
if (v___x_611_ == 0)
{
uint8_t v___x_612_; 
v___x_612_ = 1;
return v___x_612_;
}
else
{
size_t v___x_613_; size_t v___x_614_; 
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_add(v_i_607_, v___x_613_);
v_i_607_ = v___x_614_;
goto _start;
}
}
else
{
uint8_t v___x_616_; 
v___x_616_ = 0;
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0___boxed(lean_object* v_as_617_, lean_object* v_i_618_, lean_object* v_stop_619_){
_start:
{
size_t v_i_boxed_620_; size_t v_stop_boxed_621_; uint8_t v_res_622_; lean_object* v_r_623_; 
v_i_boxed_620_ = lean_unbox_usize(v_i_618_);
lean_dec(v_i_618_);
v_stop_boxed_621_ = lean_unbox_usize(v_stop_619_);
lean_dec(v_stop_619_);
v_res_622_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_as_617_, v_i_boxed_620_, v_stop_boxed_621_);
lean_dec_ref(v_as_617_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty___boxed(lean_object* v_a_624_){
_start:
{
uint8_t v_res_625_; lean_object* v_r_626_; 
v_res_625_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_a_624_);
lean_dec(v_a_624_);
v_r_626_ = lean_box(v_res_625_);
return v_r_626_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(lean_object* v_stx_633_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
lean_inc(v_stx_633_);
v___x_646_ = l_Lean_Syntax_getKind(v_stx_633_);
v___x_647_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1));
v___x_648_ = lean_name_eq(v___x_646_, v___x_647_);
lean_dec(v___x_646_);
if (v___x_648_ == 0)
{
goto v___jp_641_;
}
else
{
uint8_t v___x_649_; 
v___x_649_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_stx_633_);
if (v___x_649_ == 0)
{
goto v___jp_641_;
}
else
{
lean_dec(v_stx_633_);
return v___x_649_;
}
}
v___jp_634_:
{
lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
lean_inc(v_stx_633_);
v___x_635_ = l_Lean_Syntax_getKind(v_stx_633_);
v___x_636_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_637_ = lean_name_eq(v___x_635_, v___x_636_);
lean_dec(v___x_635_);
if (v___x_637_ == 0)
{
lean_dec(v_stx_633_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = l_Lean_Syntax_getArg(v_stx_633_, v___x_638_);
lean_dec(v_stx_633_);
v___x_640_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v___x_639_);
lean_dec(v___x_639_);
return v___x_640_;
}
}
v___jp_641_:
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
lean_inc(v_stx_633_);
v___x_642_ = l_Lean_Syntax_getKind(v_stx_633_);
v___x_643_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2));
v___x_644_ = lean_name_eq(v___x_642_, v___x_643_);
lean_dec(v___x_642_);
if (v___x_644_ == 0)
{
goto v___jp_634_;
}
else
{
uint8_t v___x_645_; 
v___x_645_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_stx_633_);
if (v___x_645_ == 0)
{
goto v___jp_634_;
}
else
{
lean_dec(v_stx_633_);
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___boxed(lean_object* v_stx_650_){
_start:
{
uint8_t v_res_651_; lean_object* v_r_652_; 
v_res_651_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_650_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(lean_object* v_fileMap_653_, lean_object* v_hoverPos_654_, lean_object* v_stx_655_, lean_object* v_leadingTokenTailPos_x3f_656_){
_start:
{
uint8_t v___x_657_; 
v___x_657_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_653_, v_hoverPos_654_);
if (v___x_657_ == 0)
{
lean_dec(v_stx_655_);
lean_dec_ref(v_fileMap_653_);
return v___x_657_;
}
else
{
uint8_t v___x_658_; uint8_t v___x_659_; 
v___x_658_ = 0;
lean_inc(v_stx_655_);
v___x_659_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_655_);
if (v___x_659_ == 0)
{
lean_dec(v_stx_655_);
lean_dec_ref(v_fileMap_653_);
return v___x_658_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
lean_inc(v_stx_655_);
v___x_660_ = l_Lean_Syntax_getKind(v_stx_655_);
v___x_661_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_662_ = lean_name_eq(v___x_660_, v___x_661_);
lean_dec(v___x_660_);
if (v___x_662_ == 0)
{
uint8_t v___x_663_; 
lean_dec(v_stx_655_);
v___x_663_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(v_fileMap_653_, v_hoverPos_654_, v_leadingTokenTailPos_x3f_656_);
return v___x_663_;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec_ref(v_fileMap_653_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = l_Lean_Syntax_getArg(v_stx_655_, v___x_664_);
v___x_666_ = l_Lean_Syntax_getTailPos_x3f(v___x_665_, v___x_658_);
lean_dec(v___x_665_);
if (lean_obj_tag(v___x_666_) == 1)
{
lean_object* v_val_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_val_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_val_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = lean_unsigned_to_nat(2u);
v___x_669_ = l_Lean_Syntax_getArg(v_stx_655_, v___x_668_);
lean_dec(v_stx_655_);
v___x_670_ = l_Lean_Syntax_getPos_x3f(v___x_669_, v___x_658_);
lean_dec(v___x_669_);
if (lean_obj_tag(v___x_670_) == 1)
{
lean_object* v_val_671_; uint8_t v___x_672_; 
v_val_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = lean_nat_dec_le(v_val_667_, v_hoverPos_654_);
lean_dec(v_val_667_);
if (v___x_672_ == 0)
{
lean_dec(v_val_671_);
return v___x_658_;
}
else
{
uint8_t v___x_673_; 
v___x_673_ = lean_nat_dec_le(v_hoverPos_654_, v_val_671_);
lean_dec(v_val_671_);
return v___x_673_;
}
}
else
{
lean_dec(v___x_670_);
lean_dec(v_val_667_);
return v___x_658_;
}
}
else
{
lean_dec(v___x_666_);
lean_dec(v_stx_655_);
return v___x_658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock___boxed(lean_object* v_fileMap_674_, lean_object* v_hoverPos_675_, lean_object* v_stx_676_, lean_object* v_leadingTokenTailPos_x3f_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_674_, v_hoverPos_675_, v_stx_676_, v_leadingTokenTailPos_x3f_677_);
lean_dec(v_leadingTokenTailPos_x3f_677_);
lean_dec(v_hoverPos_675_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(lean_object* v_fileMap_680_, lean_object* v_hoverPos_681_, lean_object* v_hoverFilePos_682_, lean_object* v_stx_683_, lean_object* v_leadingWs_684_, lean_object* v_leadingTokenTailPos_x3f_685_){
_start:
{
uint8_t v___x_686_; lean_object* v___x_687_; 
v___x_686_ = 0;
v___x_687_ = l_Lean_Syntax_getPos_x3f(v_stx_683_, v___x_686_);
if (lean_obj_tag(v___x_687_) == 1)
{
lean_object* v_val_688_; lean_object* v___x_689_; 
v_val_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v___x_687_, 1);
v___x_689_ = l_Lean_Syntax_getTailPos_x3f(v_stx_683_, v___x_686_);
if (lean_obj_tag(v___x_689_) == 1)
{
lean_object* v_val_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_val_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v___x_689_, 1);
v___x_691_ = lean_nat_sub(v_val_688_, v_leadingWs_684_);
lean_dec(v_val_688_);
v___x_692_ = lean_nat_dec_le(v___x_691_, v_hoverPos_681_);
lean_dec(v___x_691_);
if (v___x_692_ == 0)
{
lean_dec(v_val_690_);
lean_dec(v_leadingTokenTailPos_x3f_685_);
lean_dec(v_leadingWs_684_);
lean_dec(v_stx_683_);
lean_dec_ref(v_fileMap_680_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_693_ = l_Lean_Syntax_getTrailingSize(v_stx_683_);
v___x_694_ = lean_nat_add(v_val_690_, v___x_693_);
lean_dec(v___x_693_);
lean_dec(v_val_690_);
v___x_695_ = lean_nat_dec_le(v_hoverPos_681_, v___x_694_);
if (v___x_695_ == 0)
{
lean_dec(v___x_694_);
lean_dec(v_leadingTokenTailPos_x3f_685_);
lean_dec(v_leadingWs_684_);
lean_dec(v_stx_683_);
lean_dec_ref(v_fileMap_680_);
return v___x_695_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; size_t v_sz_700_; size_t v___x_701_; lean_object* v___x_702_; lean_object* v_fst_703_; 
v___x_696_ = l_Lean_Syntax_getArgs(v_stx_683_);
v___x_697_ = lean_box(0);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v_leadingWs_684_);
lean_ctor_set(v___x_698_, 1, v_leadingTokenTailPos_x3f_685_);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v_sz_700_ = lean_array_size(v___x_696_);
v___x_701_ = ((size_t)0ULL);
lean_inc_ref(v_fileMap_680_);
v___x_702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_680_, v_hoverPos_681_, v_hoverFilePos_682_, v_hoverPos_681_, v___x_694_, v___x_696_, v_sz_700_, v___x_701_, v___x_699_);
lean_dec_ref(v___x_696_);
lean_dec(v___x_694_);
v_fst_703_ = lean_ctor_get(v___x_702_, 0);
if (lean_obj_tag(v_fst_703_) == 0)
{
lean_object* v_snd_704_; lean_object* v_snd_705_; uint8_t v___x_706_; 
v_snd_704_ = lean_ctor_get(v___x_702_, 1);
lean_inc(v_snd_704_);
lean_dec_ref(v___x_702_);
v_snd_705_ = lean_ctor_get(v_snd_704_, 1);
lean_inc(v_snd_705_);
lean_dec(v_snd_704_);
lean_inc(v_stx_683_);
lean_inc_ref(v_fileMap_680_);
v___x_706_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_680_, v_hoverPos_681_, v_stx_683_, v_snd_705_);
lean_dec(v_snd_705_);
if (v___x_706_ == 0)
{
uint8_t v___x_707_; 
lean_inc(v_stx_683_);
v___x_707_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_680_, v_hoverPos_681_, v_stx_683_);
if (v___x_707_ == 0)
{
uint8_t v___x_708_; 
v___x_708_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_680_, v_hoverPos_681_, v_hoverFilePos_682_, v_stx_683_);
return v___x_708_;
}
else
{
lean_dec(v_stx_683_);
lean_dec_ref(v_fileMap_680_);
return v___x_695_;
}
}
else
{
lean_dec(v_stx_683_);
lean_dec_ref(v_fileMap_680_);
return v___x_695_;
}
}
else
{
lean_object* v_val_709_; uint8_t v___x_710_; 
lean_inc_ref(v_fst_703_);
lean_dec_ref(v___x_702_);
lean_dec(v_stx_683_);
lean_dec_ref(v_fileMap_680_);
v_val_709_ = lean_ctor_get(v_fst_703_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v_fst_703_, 1);
v___x_710_ = lean_unbox(v_val_709_);
lean_dec(v_val_709_);
return v___x_710_;
}
}
}
}
else
{
uint8_t v___x_711_; 
lean_dec(v___x_689_);
lean_dec(v_val_688_);
lean_dec(v_leadingWs_684_);
v___x_711_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_680_, v_hoverPos_681_, v_stx_683_, v_leadingTokenTailPos_x3f_685_);
lean_dec(v_leadingTokenTailPos_x3f_685_);
return v___x_711_;
}
}
else
{
uint8_t v___x_712_; 
lean_dec(v___x_687_);
lean_dec(v_leadingWs_684_);
v___x_712_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_680_, v_hoverPos_681_, v_stx_683_, v_leadingTokenTailPos_x3f_685_);
lean_dec(v_leadingTokenTailPos_x3f_685_);
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(lean_object* v_fileMap_713_, lean_object* v_hoverPos_714_, lean_object* v_hoverFilePos_715_, lean_object* v___x_716_, lean_object* v___x_717_, lean_object* v_as_718_, size_t v_sz_719_, size_t v_i_720_, lean_object* v_b_721_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = lean_usize_dec_lt(v_i_720_, v_sz_719_);
if (v___x_722_ == 0)
{
lean_dec_ref(v_fileMap_713_);
return v_b_721_;
}
else
{
lean_object* v_snd_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_758_; 
v_snd_723_ = lean_ctor_get(v_b_721_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_b_721_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v_b_721_, 0);
lean_dec(v_unused_759_);
v___x_725_ = v_b_721_;
v_isShared_726_ = v_isSharedCheck_758_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_snd_723_);
lean_dec(v_b_721_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_758_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v_fst_727_; lean_object* v_snd_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_757_; 
v_fst_727_ = lean_ctor_get(v_snd_723_, 0);
v_snd_728_ = lean_ctor_get(v_snd_723_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v_snd_723_);
if (v_isSharedCheck_757_ == 0)
{
v___x_730_ = v_snd_723_;
v_isShared_731_ = v_isSharedCheck_757_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_snd_728_);
lean_inc(v_fst_727_);
lean_dec(v_snd_723_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_757_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_a_732_; uint8_t v___x_733_; 
v_a_732_ = lean_array_uget_borrowed(v_as_718_, v_i_720_);
lean_inc(v_snd_728_);
lean_inc(v_fst_727_);
lean_inc(v_a_732_);
lean_inc_ref(v_fileMap_713_);
v___x_733_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_713_, v_hoverPos_714_, v_hoverFilePos_715_, v_a_732_, v_fst_727_, v_snd_728_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___y_737_; lean_object* v___x_747_; 
lean_dec(v_fst_727_);
v___x_734_ = lean_box(0);
v___x_735_ = l_Lean_Syntax_getTrailingSize(v_a_732_);
v___x_747_ = l_Lean_Syntax_getTailPos_x3f(v_a_732_, v___x_733_);
if (lean_obj_tag(v___x_747_) == 0)
{
v___y_737_ = v_snd_728_;
goto v___jp_736_;
}
else
{
lean_dec(v_snd_728_);
v___y_737_ = v___x_747_;
goto v___jp_736_;
}
v___jp_736_:
{
lean_object* v___x_739_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___y_737_);
lean_ctor_set(v___x_730_, 0, v___x_735_);
v___x_739_ = v___x_730_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v___y_737_);
v___x_739_ = v_reuseFailAlloc_746_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_741_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v___x_739_);
lean_ctor_set(v___x_725_, 0, v___x_734_);
v___x_741_ = v___x_725_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_739_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
size_t v___x_742_; size_t v___x_743_; 
v___x_742_ = ((size_t)1ULL);
v___x_743_ = lean_usize_add(v_i_720_, v___x_742_);
v_i_720_ = v___x_743_;
v_b_721_ = v___x_741_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
lean_dec_ref(v_fileMap_713_);
v___x_748_ = lean_nat_dec_le(v___x_716_, v___x_717_);
v___x_749_ = lean_box(v___x_748_);
v___x_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
if (v_isShared_731_ == 0)
{
v___x_752_ = v___x_730_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_fst_727_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_snd_728_);
v___x_752_ = v_reuseFailAlloc_756_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v___x_752_);
lean_ctor_set(v___x_725_, 0, v___x_750_);
v___x_754_ = v___x_725_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0___boxed(lean_object* v_fileMap_760_, lean_object* v_hoverPos_761_, lean_object* v_hoverFilePos_762_, lean_object* v___x_763_, lean_object* v___x_764_, lean_object* v_as_765_, lean_object* v_sz_766_, lean_object* v_i_767_, lean_object* v_b_768_){
_start:
{
size_t v_sz_boxed_769_; size_t v_i_boxed_770_; lean_object* v_res_771_; 
v_sz_boxed_769_ = lean_unbox_usize(v_sz_766_);
lean_dec(v_sz_766_);
v_i_boxed_770_ = lean_unbox_usize(v_i_767_);
lean_dec(v_i_767_);
v_res_771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_760_, v_hoverPos_761_, v_hoverFilePos_762_, v___x_763_, v___x_764_, v_as_765_, v_sz_boxed_769_, v_i_boxed_770_, v_b_768_);
lean_dec_ref(v_as_765_);
lean_dec(v___x_764_);
lean_dec(v___x_763_);
lean_dec_ref(v_hoverFilePos_762_);
lean_dec(v_hoverPos_761_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go___boxed(lean_object* v_fileMap_772_, lean_object* v_hoverPos_773_, lean_object* v_hoverFilePos_774_, lean_object* v_stx_775_, lean_object* v_leadingWs_776_, lean_object* v_leadingTokenTailPos_x3f_777_){
_start:
{
uint8_t v_res_778_; lean_object* v_r_779_; 
v_res_778_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_772_, v_hoverPos_773_, v_hoverFilePos_774_, v_stx_775_, v_leadingWs_776_, v_leadingTokenTailPos_x3f_777_);
lean_dec_ref(v_hoverFilePos_774_);
lean_dec(v_hoverPos_773_);
v_r_779_ = lean_box(v_res_778_);
return v_r_779_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(lean_object* v_fileMap_780_, lean_object* v_hoverPos_781_, lean_object* v_cmdStx_782_){
_start:
{
lean_object* v_hoverFilePos_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
lean_inc_ref(v_fileMap_780_);
v_hoverFilePos_783_ = l_Lean_FileMap_toPosition(v_fileMap_780_, v_hoverPos_781_);
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = lean_box(0);
v___x_786_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_780_, v_hoverPos_781_, v_hoverFilePos_783_, v_cmdStx_782_, v___x_784_, v___x_785_);
lean_dec_ref(v_hoverFilePos_783_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion___boxed(lean_object* v_fileMap_787_, lean_object* v_hoverPos_788_, lean_object* v_cmdStx_789_){
_start:
{
uint8_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_787_, v_hoverPos_788_, v_cmdStx_789_);
lean_dec(v_hoverPos_788_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(lean_object* v_as_797_, size_t v_sz_798_, size_t v_i_799_, lean_object* v_b_800_){
_start:
{
uint8_t v___x_801_; 
v___x_801_ = lean_usize_dec_lt(v_i_799_, v_sz_798_);
if (v___x_801_ == 0)
{
lean_inc_ref(v_b_800_);
return v_b_800_;
}
else
{
lean_object* v___x_802_; lean_object* v_a_803_; lean_object* v___x_804_; 
v___x_802_ = lean_box(0);
v_a_803_ = lean_array_uget_borrowed(v_as_797_, v_i_799_);
v___x_804_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_a_803_);
if (lean_obj_tag(v___x_804_) == 1)
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v___x_802_);
return v___x_806_;
}
else
{
lean_object* v___x_807_; size_t v___x_808_; size_t v___x_809_; 
lean_dec(v___x_804_);
v___x_807_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v___x_808_ = ((size_t)1ULL);
v___x_809_ = lean_usize_add(v_i_799_, v___x_808_);
v_i_799_ = v___x_809_;
v_b_800_ = v___x_807_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(lean_object* v_as_811_, size_t v_sz_812_, size_t v_i_813_, lean_object* v_b_814_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = lean_usize_dec_lt(v_i_813_, v_sz_812_);
if (v___x_815_ == 0)
{
lean_inc_ref(v_b_814_);
return v_b_814_;
}
else
{
lean_object* v___x_816_; lean_object* v_a_817_; lean_object* v___x_818_; 
v___x_816_ = lean_box(0);
v_a_817_ = lean_array_uget_borrowed(v_as_811_, v_i_813_);
lean_inc(v_a_817_);
v___x_818_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_a_817_);
if (lean_obj_tag(v___x_818_) == 1)
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v___x_816_);
return v___x_820_;
}
else
{
lean_object* v___x_821_; size_t v___x_822_; size_t v___x_823_; 
lean_dec(v___x_818_);
v___x_821_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v___x_822_ = ((size_t)1ULL);
v___x_823_ = lean_usize_add(v_i_813_, v___x_822_);
v_i_813_ = v___x_823_;
v_b_814_ = v___x_821_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(lean_object* v_x_825_){
_start:
{
if (lean_obj_tag(v_x_825_) == 0)
{
lean_object* v_cs_826_; lean_object* v___x_827_; lean_object* v___x_828_; size_t v_sz_829_; size_t v___x_830_; lean_object* v___x_831_; lean_object* v_fst_832_; 
v_cs_826_ = lean_ctor_get(v_x_825_, 0);
v___x_827_ = lean_box(0);
v___x_828_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_829_ = lean_array_size(v_cs_826_);
v___x_830_ = ((size_t)0ULL);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_cs_826_, v_sz_829_, v___x_830_, v___x_828_);
v_fst_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_fst_832_);
lean_dec_ref(v___x_831_);
if (lean_obj_tag(v_fst_832_) == 0)
{
return v___x_827_;
}
else
{
lean_object* v_val_833_; 
v_val_833_ = lean_ctor_get(v_fst_832_, 0);
lean_inc(v_val_833_);
lean_dec_ref_known(v_fst_832_, 1);
return v_val_833_;
}
}
else
{
lean_object* v_vs_834_; lean_object* v___x_835_; lean_object* v___x_836_; size_t v_sz_837_; size_t v___x_838_; lean_object* v___x_839_; lean_object* v_fst_840_; 
v_vs_834_ = lean_ctor_get(v_x_825_, 0);
v___x_835_ = lean_box(0);
v___x_836_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_837_ = lean_array_size(v_vs_834_);
v___x_838_ = ((size_t)0ULL);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_vs_834_, v_sz_837_, v___x_838_, v___x_836_);
v_fst_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_fst_840_);
lean_dec_ref(v___x_839_);
if (lean_obj_tag(v_fst_840_) == 0)
{
return v___x_835_;
}
else
{
lean_object* v_val_841_; 
v_val_841_ = lean_ctor_get(v_fst_840_, 0);
lean_inc(v_val_841_);
lean_dec_ref_known(v_fst_840_, 1);
return v_val_841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(lean_object* v_t_842_){
_start:
{
lean_object* v_root_843_; lean_object* v_tail_844_; lean_object* v___x_845_; 
v_root_843_ = lean_ctor_get(v_t_842_, 0);
v_tail_844_ = lean_ctor_get(v_t_842_, 1);
v___x_845_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_root_843_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_846_; size_t v_sz_847_; size_t v___x_848_; lean_object* v___x_849_; lean_object* v_fst_850_; 
v___x_846_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_847_ = lean_array_size(v_tail_844_);
v___x_848_ = ((size_t)0ULL);
v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_tail_844_, v_sz_847_, v___x_848_, v___x_846_);
v_fst_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_fst_850_);
lean_dec_ref(v___x_849_);
if (lean_obj_tag(v_fst_850_) == 0)
{
return v___x_845_;
}
else
{
lean_object* v_val_851_; 
v_val_851_ = lean_ctor_get(v_fst_850_, 0);
lean_inc(v_val_851_);
lean_dec_ref_known(v_fst_850_, 1);
return v_val_851_;
}
}
else
{
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(lean_object* v_i_852_){
_start:
{
switch(lean_obj_tag(v_i_852_))
{
case 0:
{
lean_object* v_i_853_; 
v_i_853_ = lean_ctor_get(v_i_852_, 0);
lean_inc_ref(v_i_853_);
if (lean_obj_tag(v_i_853_) == 0)
{
lean_object* v_info_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref_known(v_i_852_, 2);
v_info_854_ = lean_ctor_get(v_i_853_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v_i_853_);
if (v_isSharedCheck_864_ == 0)
{
v___x_856_ = v_i_853_;
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_info_854_);
lean_dec(v_i_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_858_ = lean_box(0);
v___x_859_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go___closed__0));
v___x_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_860_, 0, v_info_854_);
lean_ctor_set(v___x_860_, 1, v___x_858_);
lean_ctor_set(v___x_860_, 2, v___x_859_);
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 1);
lean_ctor_set(v___x_856_, 0, v___x_860_);
v___x_862_ = v___x_856_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
else
{
lean_object* v_t_865_; 
lean_dec_ref(v_i_853_);
v_t_865_ = lean_ctor_get(v_i_852_, 1);
lean_inc_ref(v_t_865_);
lean_dec_ref_known(v_i_852_, 2);
v_i_852_ = v_t_865_;
goto _start;
}
}
case 1:
{
lean_object* v_children_867_; lean_object* v___x_868_; 
v_children_867_ = lean_ctor_get(v_i_852_, 1);
lean_inc_ref(v_children_867_);
lean_dec_ref_known(v_i_852_, 2);
v___x_868_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(v_children_867_);
lean_dec_ref(v_children_867_);
return v___x_868_;
}
default: 
{
lean_object* v___x_869_; 
lean_dec_ref_known(v_i_852_, 1);
v___x_869_ = lean_box(0);
return v___x_869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___boxed(lean_object* v_t_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(v_t_870_);
lean_dec_ref(v_t_870_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1___boxed(lean_object* v_as_872_, lean_object* v_sz_873_, lean_object* v_i_874_, lean_object* v_b_875_){
_start:
{
size_t v_sz_boxed_876_; size_t v_i_boxed_877_; lean_object* v_res_878_; 
v_sz_boxed_876_ = lean_unbox_usize(v_sz_873_);
lean_dec(v_sz_873_);
v_i_boxed_877_ = lean_unbox_usize(v_i_874_);
lean_dec(v_i_874_);
v_res_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_as_872_, v_sz_boxed_876_, v_i_boxed_877_, v_b_875_);
lean_dec_ref(v_b_875_);
lean_dec_ref(v_as_872_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1___boxed(lean_object* v_as_879_, lean_object* v_sz_880_, lean_object* v_i_881_, lean_object* v_b_882_){
_start:
{
size_t v_sz_boxed_883_; size_t v_i_boxed_884_; lean_object* v_res_885_; 
v_sz_boxed_883_ = lean_unbox_usize(v_sz_880_);
lean_dec(v_sz_880_);
v_i_boxed_884_ = lean_unbox_usize(v_i_881_);
lean_dec(v_i_881_);
v_res_885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_as_879_, v_sz_boxed_883_, v_i_boxed_884_, v_b_882_);
lean_dec_ref(v_b_882_);
lean_dec_ref(v_as_879_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0___boxed(lean_object* v_x_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_x_886_);
lean_dec_ref(v_x_886_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f(lean_object* v_i_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_i_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(lean_object* v_fileMap_892_, lean_object* v_hoverPos_893_, lean_object* v_cmdStx_894_, lean_object* v_infoTree_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_infoTree_895_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v___x_897_; 
lean_dec(v_cmdStx_894_);
lean_dec_ref(v_fileMap_892_);
v___x_897_ = lean_box(0);
return v___x_897_;
}
else
{
lean_object* v_val_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_910_; 
v_val_898_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_910_ == 0)
{
v___x_900_ = v___x_896_;
v_isShared_901_ = v_isSharedCheck_910_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_val_898_);
lean_dec(v___x_896_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_910_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
uint8_t v___x_902_; 
v___x_902_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_892_, v_hoverPos_893_, v_cmdStx_894_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
lean_del_object(v___x_900_);
lean_dec(v_val_898_);
v___x_903_ = lean_box(0);
return v___x_903_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_904_ = lean_box(0);
v___x_905_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___closed__0));
v___x_906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v_val_898_);
lean_ctor_set(v___x_906_, 2, v___x_905_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_906_);
v___x_908_ = v___x_900_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___boxed(lean_object* v_fileMap_911_, lean_object* v_hoverPos_912_, lean_object* v_cmdStx_913_, lean_object* v_infoTree_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(v_fileMap_911_, v_hoverPos_912_, v_cmdStx_913_, v_infoTree_914_);
lean_dec(v_hoverPos_912_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(lean_object* v_msg_916_){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = l_Lean_instInhabitedExpr;
v___x_918_ = lean_panic_fn_borrowed(v___x_917_, v_msg_916_);
return v___x_918_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(lean_object* v_hoverPos_919_, lean_object* v_i_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Elab_Info_pos_x3f(v_i_920_);
if (lean_obj_tag(v___x_921_) == 1)
{
lean_object* v_val_922_; lean_object* v___x_923_; 
v_val_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_val_922_);
lean_dec_ref_known(v___x_921_, 1);
v___x_923_ = l_Lean_Elab_Info_tailPos_x3f(v_i_920_);
if (lean_obj_tag(v___x_923_) == 1)
{
if (lean_obj_tag(v_i_920_) == 1)
{
lean_object* v_i_924_; lean_object* v_expectedType_x3f_925_; 
v_i_924_ = lean_ctor_get(v_i_920_, 0);
v_expectedType_x3f_925_ = lean_ctor_get(v_i_924_, 2);
if (lean_obj_tag(v_expectedType_x3f_925_) == 0)
{
uint8_t v___x_926_; 
lean_dec_ref_known(v___x_923_, 1);
lean_dec(v_val_922_);
v___x_926_ = 0;
return v___x_926_;
}
else
{
lean_object* v_val_927_; uint8_t v___x_928_; 
v_val_927_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_val_927_);
lean_dec_ref_known(v___x_923_, 1);
v___x_928_ = lean_nat_dec_le(v_val_922_, v_hoverPos_919_);
lean_dec(v_val_922_);
if (v___x_928_ == 0)
{
lean_dec(v_val_927_);
return v___x_928_;
}
else
{
uint8_t v___x_929_; 
v___x_929_ = lean_nat_dec_le(v_hoverPos_919_, v_val_927_);
lean_dec(v_val_927_);
return v___x_929_;
}
}
}
else
{
uint8_t v___x_930_; 
lean_dec_ref_known(v___x_923_, 1);
lean_dec(v_val_922_);
v___x_930_ = 0;
return v___x_930_;
}
}
else
{
uint8_t v___x_931_; 
lean_dec(v___x_923_);
lean_dec(v_val_922_);
v___x_931_ = 0;
return v___x_931_;
}
}
else
{
uint8_t v___x_932_; 
lean_dec(v___x_921_);
v___x_932_ = 0;
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed(lean_object* v_hoverPos_933_, lean_object* v_i_934_){
_start:
{
uint8_t v_res_935_; lean_object* v_r_936_; 
v_res_935_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(v_hoverPos_933_, v_i_934_);
lean_dec_ref(v_i_934_);
lean_dec(v_hoverPos_933_);
v_r_936_ = lean_box(v_res_935_);
return v_r_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt(lean_object* v_infoTree_937_, lean_object* v_hoverPos_938_){
_start:
{
lean_object* v___f_939_; lean_object* v___x_940_; 
v___f_939_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed), 2, 1);
lean_closure_set(v___f_939_, 0, v_hoverPos_938_);
v___x_940_ = l_Lean_Elab_InfoTree_smallestInfo_x3f(v___f_939_, v_infoTree_937_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v___x_941_; 
v___x_941_ = lean_box(0);
return v___x_941_;
}
else
{
lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_966_; 
v_val_942_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_966_ == 0)
{
v___x_944_ = v___x_940_;
v_isShared_945_ = v_isSharedCheck_966_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_dec(v___x_940_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_966_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_fst_946_; lean_object* v_snd_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_965_; 
v_fst_946_ = lean_ctor_get(v_val_942_, 0);
v_snd_947_ = lean_ctor_get(v_val_942_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_val_942_);
if (v_isSharedCheck_965_ == 0)
{
v___x_949_ = v_val_942_;
v_isShared_950_ = v_isSharedCheck_965_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_snd_947_);
lean_inc(v_fst_946_);
lean_dec(v_val_942_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_965_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___y_952_; 
if (lean_obj_tag(v_snd_947_) == 1)
{
lean_object* v_i_959_; lean_object* v_expectedType_x3f_960_; 
v_i_959_ = lean_ctor_get(v_snd_947_, 0);
lean_inc_ref(v_i_959_);
lean_dec_ref_known(v_snd_947_, 1);
v_expectedType_x3f_960_ = lean_ctor_get(v_i_959_, 2);
lean_inc(v_expectedType_x3f_960_);
lean_dec_ref(v_i_959_);
if (lean_obj_tag(v_expectedType_x3f_960_) == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_obj_once(&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4, &l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_once, _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4);
v___x_962_ = l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(v___x_961_);
v___y_952_ = v___x_962_;
goto v___jp_951_;
}
else
{
lean_object* v_val_963_; 
v_val_963_ = lean_ctor_get(v_expectedType_x3f_960_, 0);
lean_inc(v_val_963_);
lean_dec_ref_known(v_expectedType_x3f_960_, 1);
v___y_952_ = v_val_963_;
goto v___jp_951_;
}
}
else
{
lean_object* v___x_964_; 
lean_del_object(v___x_949_);
lean_dec(v_snd_947_);
lean_dec(v_fst_946_);
lean_del_object(v___x_944_);
v___x_964_ = lean_box(0);
return v___x_964_;
}
v___jp_951_:
{
lean_object* v___x_954_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v___y_952_);
v___x_954_ = v___x_949_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_fst_946_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___y_952_);
v___x_954_ = v_reuseFailAlloc_958_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_956_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_954_);
v___x_956_ = v___x_944_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(lean_object* v_f_967_, lean_object* v_leadingToken_x3f_968_, lean_object* v_acc_969_, lean_object* v_stx_970_){
_start:
{
lean_object* v___f_971_; lean_object* v___f_972_; lean_object* v___f_973_; lean_object* v___f_974_; lean_object* v___f_975_; lean_object* v___f_976_; lean_object* v___f_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_acc_981_; 
v___f_971_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0));
v___f_972_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1));
v___f_973_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2));
v___f_974_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3));
v___f_975_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4));
v___f_976_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5));
v___f_977_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6));
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___f_971_);
lean_ctor_set(v___x_978_, 1, v___f_972_);
v___x_979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v___f_973_);
lean_ctor_set(v___x_979_, 2, v___f_974_);
lean_ctor_set(v___x_979_, 3, v___f_975_);
lean_ctor_set(v___x_979_, 4, v___f_976_);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v___f_977_);
lean_inc(v_f_967_);
lean_inc(v_stx_970_);
lean_inc(v_leadingToken_x3f_968_);
v_acc_981_ = lean_apply_3(v_f_967_, v_acc_969_, v_leadingToken_x3f_968_, v_stx_970_);
switch(lean_obj_tag(v_stx_970_))
{
case 0:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec_ref_known(v___x_980_, 2);
lean_dec(v_leadingToken_x3f_968_);
lean_dec(v_f_967_);
v___x_982_ = lean_box(0);
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v_acc_981_);
return v___x_983_;
}
case 1:
{
lean_object* v_args_984_; lean_object* v___f_985_; lean_object* v_lastToken_x3f_986_; lean_object* v___x_987_; size_t v_sz_988_; size_t v___x_989_; lean_object* v___x_990_; lean_object* v_fst_991_; lean_object* v_snd_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
v_args_984_ = lean_ctor_get(v_stx_970_, 2);
lean_inc_ref(v_args_984_);
lean_dec_ref_known(v_stx_970_, 3);
v___f_985_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0), 5, 2);
lean_closure_set(v___f_985_, 0, v_f_967_);
lean_closure_set(v___f_985_, 1, v_leadingToken_x3f_968_);
v_lastToken_x3f_986_ = lean_box(0);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v_acc_981_);
lean_ctor_set(v___x_987_, 1, v_lastToken_x3f_986_);
v_sz_988_ = lean_array_size(v_args_984_);
v___x_989_ = ((size_t)0ULL);
v___x_990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_980_, v_args_984_, v___f_985_, v_sz_988_, v___x_989_, v___x_987_);
v_fst_991_ = lean_ctor_get(v___x_990_, 0);
v_snd_992_ = lean_ctor_get(v___x_990_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_990_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_snd_992_);
lean_inc(v_fst_991_);
lean_dec(v___x_990_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v_fst_991_);
lean_ctor_set(v___x_994_, 0, v_snd_992_);
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_snd_992_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_fst_991_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
default: 
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec_ref_known(v___x_980_, 2);
lean_dec(v_leadingToken_x3f_968_);
lean_dec(v_f_967_);
v___x_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_stx_970_);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v_acc_981_);
return v___x_1001_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0(lean_object* v_f_1002_, lean_object* v_leadingToken_x3f_1003_, lean_object* v_a_1004_, lean_object* v_x_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v_fst_1012_; lean_object* v_snd_1013_; lean_object* v___y_1015_; 
v_fst_1012_ = lean_ctor_get(v___y_1006_, 0);
lean_inc(v_fst_1012_);
v_snd_1013_ = lean_ctor_get(v___y_1006_, 1);
lean_inc(v_snd_1013_);
lean_dec_ref(v___y_1006_);
if (lean_obj_tag(v_snd_1013_) == 0)
{
v___y_1015_ = v_leadingToken_x3f_1003_;
goto v___jp_1014_;
}
else
{
lean_dec(v_leadingToken_x3f_1003_);
lean_inc_ref(v_snd_1013_);
v___y_1015_ = v_snd_1013_;
goto v___jp_1014_;
}
v___jp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___y_1008_);
lean_ctor_set(v___x_1010_, 1, v___y_1009_);
v___x_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
v___jp_1014_:
{
lean_object* v___x_1016_; lean_object* v_fst_1017_; 
v___x_1016_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1002_, v___y_1015_, v_fst_1012_, v_a_1004_);
v_fst_1017_ = lean_ctor_get(v___x_1016_, 0);
if (lean_obj_tag(v_fst_1017_) == 0)
{
lean_object* v_snd_1018_; 
v_snd_1018_ = lean_ctor_get(v___x_1016_, 1);
lean_inc(v_snd_1018_);
lean_dec_ref(v___x_1016_);
v___y_1008_ = v_snd_1018_;
v___y_1009_ = v_snd_1013_;
goto v___jp_1007_;
}
else
{
lean_object* v_snd_1019_; 
lean_inc_ref(v_fst_1017_);
lean_dec(v_snd_1013_);
v_snd_1019_ = lean_ctor_get(v___x_1016_, 1);
lean_inc(v_snd_1019_);
lean_dec_ref(v___x_1016_);
v___y_1008_ = v_snd_1019_;
v___y_1009_ = v_fst_1017_;
goto v___jp_1007_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(lean_object* v_00_u03b1_1020_, lean_object* v_f_1021_, lean_object* v_inst_1022_, lean_object* v_leadingToken_x3f_1023_, lean_object* v_acc_1024_, lean_object* v_stx_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1021_, v_leadingToken_x3f_1023_, v_acc_1024_, v_stx_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___boxed(lean_object* v_00_u03b1_1027_, lean_object* v_f_1028_, lean_object* v_inst_1029_, lean_object* v_leadingToken_x3f_1030_, lean_object* v_acc_1031_, lean_object* v_stx_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(v_00_u03b1_1027_, v_f_1028_, v_inst_1029_, v_leadingToken_x3f_1030_, v_acc_1031_, v_stx_1032_);
lean_dec(v_inst_1029_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(lean_object* v_f_1034_, lean_object* v_init_1035_, lean_object* v_stx_1036_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v_snd_1039_; 
v___x_1037_ = lean_box(0);
v___x_1038_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1034_, v___x_1037_, v_init_1035_, v_stx_1036_);
v_snd_1039_ = lean_ctor_get(v___x_1038_, 1);
lean_inc(v_snd_1039_);
lean_dec_ref(v___x_1038_);
return v_snd_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(lean_object* v_00_u03b1_1040_, lean_object* v_inst_1041_, lean_object* v_f_1042_, lean_object* v_init_1043_, lean_object* v_stx_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(v_f_1042_, v_init_1043_, v_stx_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___boxed(lean_object* v_00_u03b1_1046_, lean_object* v_inst_1047_, lean_object* v_f_1048_, lean_object* v_init_1049_, lean_object* v_stx_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(v_00_u03b1_1046_, v_inst_1047_, v_f_1048_, v_init_1049_, v_stx_1050_);
lean_dec(v_inst_1047_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(lean_object* v_p_1052_, lean_object* v_foundStx_x3f_1053_, lean_object* v_leadingToken_x3f_1054_, lean_object* v_stx_1055_){
_start:
{
if (lean_obj_tag(v_foundStx_x3f_1053_) == 0)
{
lean_object* v___x_1056_; uint8_t v___x_1057_; 
lean_inc(v_stx_1055_);
v___x_1056_ = lean_apply_2(v_p_1052_, v_leadingToken_x3f_1054_, v_stx_1055_);
v___x_1057_ = lean_unbox(v___x_1056_);
if (v___x_1057_ == 0)
{
lean_dec(v_stx_1055_);
return v_foundStx_x3f_1053_;
}
else
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1058_, 0, v_stx_1055_);
return v___x_1058_;
}
}
else
{
lean_dec(v_stx_1055_);
lean_dec(v_leadingToken_x3f_1054_);
lean_dec_ref(v_p_1052_);
lean_inc_ref(v_foundStx_x3f_1053_);
return v_foundStx_x3f_1053_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed(lean_object* v_p_1059_, lean_object* v_foundStx_x3f_1060_, lean_object* v_leadingToken_x3f_1061_, lean_object* v_stx_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(v_p_1059_, v_foundStx_x3f_1060_, v_leadingToken_x3f_1061_, v_stx_1062_);
lean_dec(v_foundStx_x3f_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f(lean_object* v_p_1064_, lean_object* v_stx_1065_){
_start:
{
lean_object* v___f_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___f_1066_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1066_, 0, v_p_1064_);
v___x_1067_ = lean_box(0);
v___x_1068_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(v___f_1066_, v___x_1067_, v_stx_1065_);
return v___x_1068_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(uint8_t v___y_1069_, lean_object* v_hoverPos_1070_, lean_object* v_as_1071_, size_t v_i_1072_, size_t v_stop_1073_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_usize_dec_eq(v_i_1072_, v_stop_1073_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v_fst_1080_; lean_object* v_snd_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; uint8_t v___y_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1079_ = lean_array_uget_borrowed(v_as_1071_, v_i_1072_);
v_fst_1080_ = lean_ctor_get(v___x_1079_, 0);
v_snd_1081_ = lean_ctor_get(v___x_1079_, 1);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = 1;
v___x_1086_ = lean_unsigned_to_nat(2u);
v___x_1087_ = lean_nat_mod(v_snd_1081_, v___x_1086_);
v___x_1088_ = lean_nat_dec_eq(v___x_1087_, v___x_1082_);
lean_dec(v___x_1087_);
if (v___x_1088_ == 0)
{
uint8_t v___x_1089_; 
v___x_1089_ = l_Lean_Syntax_isAtom(v_fst_1080_);
if (v___x_1089_ == 0)
{
v___y_1085_ = v___y_1069_;
goto v___jp_1084_;
}
else
{
if (v___y_1069_ == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Syntax_getTailPos_x3f(v_fst_1080_, v___y_1069_);
if (lean_obj_tag(v___x_1090_) == 1)
{
lean_object* v_val_1091_; uint8_t v___x_1092_; 
v_val_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_val_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v___x_1092_ = lean_nat_dec_le(v_val_1091_, v_hoverPos_1070_);
if (v___x_1092_ == 0)
{
lean_dec(v_val_1091_);
goto v___jp_1074_;
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1093_ = l_Lean_Syntax_getTrailingSize(v_fst_1080_);
v___x_1094_ = lean_nat_add(v_val_1091_, v___x_1093_);
lean_dec(v___x_1093_);
lean_dec(v_val_1091_);
v___x_1095_ = lean_nat_dec_le(v_hoverPos_1070_, v___x_1094_);
lean_dec(v___x_1094_);
v___y_1085_ = v___x_1095_;
goto v___jp_1084_;
}
}
else
{
lean_dec(v___x_1090_);
goto v___jp_1074_;
}
}
else
{
return v___x_1083_;
}
}
}
else
{
v___y_1085_ = v___y_1069_;
goto v___jp_1084_;
}
v___jp_1084_:
{
if (v___y_1085_ == 0)
{
goto v___jp_1074_;
}
else
{
return v___x_1083_;
}
}
}
else
{
uint8_t v___x_1096_; 
v___x_1096_ = 0;
return v___x_1096_;
}
v___jp_1074_:
{
size_t v___x_1075_; size_t v___x_1076_; 
v___x_1075_ = ((size_t)1ULL);
v___x_1076_ = lean_usize_add(v_i_1072_, v___x_1075_);
v_i_1072_ = v___x_1076_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0___boxed(lean_object* v___y_1097_, lean_object* v_hoverPos_1098_, lean_object* v_as_1099_, lean_object* v_i_1100_, lean_object* v_stop_1101_){
_start:
{
uint8_t v___y_1680__boxed_1102_; size_t v_i_boxed_1103_; size_t v_stop_boxed_1104_; uint8_t v_res_1105_; lean_object* v_r_1106_; 
v___y_1680__boxed_1102_ = lean_unbox(v___y_1097_);
v_i_boxed_1103_ = lean_unbox_usize(v_i_1100_);
lean_dec(v_i_1100_);
v_stop_boxed_1104_ = lean_unbox_usize(v_stop_1101_);
lean_dec(v_stop_1101_);
v_res_1105_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(v___y_1680__boxed_1102_, v_hoverPos_1098_, v_as_1099_, v_i_boxed_1103_, v_stop_boxed_1104_);
lean_dec_ref(v_as_1099_);
lean_dec(v_hoverPos_1098_);
v_r_1106_ = lean_box(v_res_1105_);
return v_r_1106_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(uint8_t v___x_1113_, uint8_t v_isCursorOnWhitespace_1114_, uint8_t v_isCursorInProperWhitespace_1115_, lean_object* v_fileMap_1116_, lean_object* v_hoverFilePos_1117_, lean_object* v_hoverPos_1118_, lean_object* v_leadingToken_x3f_1119_, lean_object* v_stx_1120_){
_start:
{
uint8_t v___y_1122_; 
if (lean_obj_tag(v_leadingToken_x3f_1119_) == 1)
{
lean_object* v_val_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_val_1129_ = lean_ctor_get(v_leadingToken_x3f_1119_, 0);
lean_inc(v_stx_1120_);
v___x_1130_ = l_Lean_Syntax_getKind(v_stx_1120_);
v___x_1131_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1));
v___x_1132_ = lean_name_eq(v___x_1130_, v___x_1131_);
lean_dec(v___x_1130_);
if (v___x_1132_ == 0)
{
lean_dec(v_stx_1120_);
lean_dec_ref(v_fileMap_1116_);
return v___x_1113_;
}
else
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_Syntax_getTailPos_x3f(v_val_1129_, v_isCursorOnWhitespace_1114_);
if (lean_obj_tag(v___x_1133_) == 1)
{
lean_object* v_val_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v_fieldsAndSeps_1137_; uint8_t v___y_1139_; lean_object* v_val_1147_; lean_object* v___x_1152_; 
v_val_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_val_1134_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = l_Lean_Syntax_getArg(v_stx_1120_, v___x_1135_);
v_fieldsAndSeps_1137_ = l_Lean_Syntax_getArgs(v___x_1136_);
lean_dec(v___x_1136_);
v___x_1152_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1120_, v_isCursorOnWhitespace_1114_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_val_1129_, v_isCursorOnWhitespace_1114_);
if (lean_obj_tag(v___x_1153_) == 1)
{
lean_object* v_val_1154_; 
v_val_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_val_1154_);
lean_dec_ref_known(v___x_1153_, 1);
v_val_1147_ = v_val_1154_;
goto v___jp_1146_;
}
else
{
lean_dec(v___x_1153_);
lean_dec_ref(v_fieldsAndSeps_1137_);
lean_dec(v_val_1134_);
lean_dec(v_stx_1120_);
lean_dec_ref(v_fileMap_1116_);
return v___x_1113_;
}
}
else
{
lean_object* v_val_1155_; 
v_val_1155_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_val_1155_);
lean_dec_ref_known(v___x_1152_, 1);
v_val_1147_ = v_val_1155_;
goto v___jp_1146_;
}
v___jp_1138_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1140_ = l_Array_zipIdx___redArg(v_fieldsAndSeps_1137_, v___x_1135_);
v___x_1141_ = lean_array_get_size(v___x_1140_);
v___x_1142_ = lean_nat_dec_lt(v___x_1135_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_dec_ref(v___x_1140_);
v___y_1122_ = v___x_1142_;
goto v___jp_1121_;
}
else
{
if (v___x_1142_ == 0)
{
lean_dec_ref(v___x_1140_);
v___y_1122_ = v___x_1142_;
goto v___jp_1121_;
}
else
{
size_t v___x_1143_; size_t v___x_1144_; uint8_t v___x_1145_; 
v___x_1143_ = ((size_t)0ULL);
v___x_1144_ = lean_usize_of_nat(v___x_1141_);
v___x_1145_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(v___y_1139_, v_hoverPos_1118_, v___x_1140_, v___x_1143_, v___x_1144_);
lean_dec_ref(v___x_1140_);
if (v___x_1145_ == 0)
{
v___y_1122_ = v___x_1145_;
goto v___jp_1121_;
}
else
{
lean_dec(v_stx_1120_);
lean_dec_ref(v_fileMap_1116_);
return v_isCursorOnWhitespace_1114_;
}
}
}
}
v___jp_1146_:
{
lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = lean_array_get_size(v_fieldsAndSeps_1137_);
v___x_1149_ = lean_nat_dec_eq(v___x_1148_, v___x_1135_);
if (v___x_1149_ == 0)
{
lean_dec(v_val_1147_);
lean_dec(v_val_1134_);
v___y_1139_ = v___x_1113_;
goto v___jp_1138_;
}
else
{
lean_object* v_outerBounds_1150_; uint8_t v___x_1151_; 
v_outerBounds_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_outerBounds_1150_, 0, v_val_1134_);
lean_ctor_set(v_outerBounds_1150_, 1, v_val_1147_);
v___x_1151_ = l_Lean_Syntax_Range_contains(v_outerBounds_1150_, v_hoverPos_1118_, v_isCursorOnWhitespace_1114_);
lean_dec_ref_known(v_outerBounds_1150_, 2);
if (v___x_1151_ == 0)
{
v___y_1139_ = v___x_1151_;
goto v___jp_1138_;
}
else
{
lean_dec_ref(v_fieldsAndSeps_1137_);
lean_dec(v_stx_1120_);
lean_dec_ref(v_fileMap_1116_);
return v_isCursorOnWhitespace_1114_;
}
}
}
}
else
{
lean_dec(v___x_1133_);
lean_dec(v_stx_1120_);
lean_dec_ref(v_fileMap_1116_);
return v___x_1113_;
}
}
}
else
{
lean_dec(v_stx_1120_);
lean_dec_ref(v_fileMap_1116_);
return v___x_1113_;
}
v___jp_1121_:
{
if (v_isCursorInProperWhitespace_1115_ == 0)
{
lean_dec(v_stx_1120_);
lean_dec_ref(v_fileMap_1116_);
return v___y_1122_;
}
else
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_Syntax_getPos_x3f(v_stx_1120_, v___y_1122_);
lean_dec(v_stx_1120_);
if (lean_obj_tag(v___x_1123_) == 1)
{
lean_object* v_val_1124_; lean_object* v___x_1125_; lean_object* v_column_1126_; lean_object* v_column_1127_; uint8_t v_isCursorInBlock_1128_; 
v_val_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_val_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v___x_1125_ = l_Lean_FileMap_toPosition(v_fileMap_1116_, v_val_1124_);
lean_dec(v_val_1124_);
v_column_1126_ = lean_ctor_get(v___x_1125_, 1);
lean_inc(v_column_1126_);
lean_dec_ref(v___x_1125_);
v_column_1127_ = lean_ctor_get(v_hoverFilePos_1117_, 1);
v_isCursorInBlock_1128_ = lean_nat_dec_eq(v_column_1127_, v_column_1126_);
lean_dec(v_column_1126_);
return v_isCursorInBlock_1128_;
}
else
{
lean_dec(v___x_1123_);
lean_dec_ref(v_fileMap_1116_);
return v___y_1122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___boxed(lean_object* v___x_1156_, lean_object* v_isCursorOnWhitespace_1157_, lean_object* v_isCursorInProperWhitespace_1158_, lean_object* v_fileMap_1159_, lean_object* v_hoverFilePos_1160_, lean_object* v_hoverPos_1161_, lean_object* v_leadingToken_x3f_1162_, lean_object* v_stx_1163_){
_start:
{
uint8_t v___x_1744__boxed_1164_; uint8_t v_isCursorOnWhitespace_boxed_1165_; uint8_t v_isCursorInProperWhitespace_boxed_1166_; uint8_t v_res_1167_; lean_object* v_r_1168_; 
v___x_1744__boxed_1164_ = lean_unbox(v___x_1156_);
v_isCursorOnWhitespace_boxed_1165_ = lean_unbox(v_isCursorOnWhitespace_1157_);
v_isCursorInProperWhitespace_boxed_1166_ = lean_unbox(v_isCursorInProperWhitespace_1158_);
v_res_1167_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(v___x_1744__boxed_1164_, v_isCursorOnWhitespace_boxed_1165_, v_isCursorInProperWhitespace_boxed_1166_, v_fileMap_1159_, v_hoverFilePos_1160_, v_hoverPos_1161_, v_leadingToken_x3f_1162_, v_stx_1163_);
lean_dec(v_leadingToken_x3f_1162_);
lean_dec(v_hoverPos_1161_);
lean_dec_ref(v_hoverFilePos_1160_);
v_r_1168_ = lean_box(v_res_1167_);
return v_r_1168_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(lean_object* v_fileMap_1169_, lean_object* v_hoverPos_1170_, lean_object* v_cmdStx_1171_){
_start:
{
uint8_t v_isCursorOnWhitespace_1172_; 
v_isCursorOnWhitespace_1172_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_1169_, v_hoverPos_1170_);
if (v_isCursorOnWhitespace_1172_ == 0)
{
lean_dec(v_cmdStx_1171_);
lean_dec(v_hoverPos_1170_);
lean_dec_ref(v_fileMap_1169_);
return v_isCursorOnWhitespace_1172_;
}
else
{
uint8_t v_isCursorInProperWhitespace_1173_; uint8_t v___x_1174_; lean_object* v_hoverFilePos_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___f_1179_; lean_object* v___x_1180_; 
v_isCursorInProperWhitespace_1173_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_1169_, v_hoverPos_1170_);
v___x_1174_ = 0;
lean_inc_ref(v_fileMap_1169_);
v_hoverFilePos_1175_ = l_Lean_FileMap_toPosition(v_fileMap_1169_, v_hoverPos_1170_);
v___x_1176_ = lean_box(v___x_1174_);
v___x_1177_ = lean_box(v_isCursorOnWhitespace_1172_);
v___x_1178_ = lean_box(v_isCursorInProperWhitespace_1173_);
v___f_1179_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___boxed), 8, 6);
lean_closure_set(v___f_1179_, 0, v___x_1176_);
lean_closure_set(v___f_1179_, 1, v___x_1177_);
lean_closure_set(v___f_1179_, 2, v___x_1178_);
lean_closure_set(v___f_1179_, 3, v_fileMap_1169_);
lean_closure_set(v___f_1179_, 4, v_hoverFilePos_1175_);
lean_closure_set(v___f_1179_, 5, v_hoverPos_1170_);
v___x_1180_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f(v___f_1179_, v_cmdStx_1171_);
if (lean_obj_tag(v___x_1180_) == 0)
{
return v___x_1174_;
}
else
{
lean_dec_ref_known(v___x_1180_, 1);
return v_isCursorOnWhitespace_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___boxed(lean_object* v_fileMap_1181_, lean_object* v_hoverPos_1182_, lean_object* v_cmdStx_1183_){
_start:
{
uint8_t v_res_1184_; lean_object* v_r_1185_; 
v_res_1184_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(v_fileMap_1181_, v_hoverPos_1182_, v_cmdStx_1183_);
v_r_1185_ = lean_box(v_res_1184_);
return v_r_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticFieldCompletion_x3f(lean_object* v_fileMap_1186_, lean_object* v_hoverPos_1187_, lean_object* v_cmdStx_1188_, lean_object* v_infoTree_1189_){
_start:
{
uint8_t v___x_1190_; 
lean_inc(v_hoverPos_1187_);
v___x_1190_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(v_fileMap_1186_, v_hoverPos_1187_, v_cmdStx_1188_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; 
lean_dec_ref(v_infoTree_1189_);
lean_dec(v_hoverPos_1187_);
v___x_1191_ = lean_box(0);
return v___x_1191_;
}
else
{
lean_object* v___x_1192_; 
v___x_1192_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt(v_infoTree_1189_, v_hoverPos_1187_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_box(0);
return v___x_1193_;
}
else
{
lean_object* v_val_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1216_; 
v_val_1194_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1196_ = v___x_1192_;
v_isShared_1197_ = v_isSharedCheck_1216_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_val_1194_);
lean_dec(v___x_1192_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1216_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_fst_1198_; lean_object* v_snd_1199_; lean_object* v___x_1200_; 
v_fst_1198_ = lean_ctor_get(v_val_1194_, 0);
lean_inc(v_fst_1198_);
v_snd_1199_ = lean_ctor_get(v_val_1194_, 1);
lean_inc(v_snd_1199_);
lean_dec(v_val_1194_);
v___x_1200_ = l_Lean_Expr_getAppFn(v_snd_1199_);
lean_dec(v_snd_1199_);
if (lean_obj_tag(v___x_1200_) == 4)
{
lean_object* v_toCommandContextInfo_1201_; lean_object* v_declName_1202_; lean_object* v_env_1203_; uint8_t v___x_1204_; 
v_toCommandContextInfo_1201_ = lean_ctor_get(v_fst_1198_, 0);
v_declName_1202_ = lean_ctor_get(v___x_1200_, 0);
lean_inc_n(v_declName_1202_, 2);
lean_dec_ref_known(v___x_1200_, 2);
v_env_1203_ = lean_ctor_get(v_toCommandContextInfo_1201_, 0);
lean_inc_ref(v_env_1203_);
v___x_1204_ = l_Lean_isStructure(v_env_1203_, v_declName_1202_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
lean_dec(v_declName_1202_);
lean_dec(v_fst_1198_);
lean_del_object(v___x_1196_);
v___x_1205_ = lean_box(0);
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1206_ = lean_box(0);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_box(0);
v___x_1209_ = l_Lean_LocalContext_empty;
v___x_1210_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1207_);
lean_ctor_set(v___x_1210_, 1, v___x_1208_);
lean_ctor_set(v___x_1210_, 2, v___x_1209_);
lean_ctor_set(v___x_1210_, 3, v_declName_1202_);
v___x_1211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1206_);
lean_ctor_set(v___x_1211_, 1, v_fst_1198_);
lean_ctor_set(v___x_1211_, 2, v___x_1210_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1211_);
v___x_1213_ = v___x_1196_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
else
{
lean_object* v___x_1215_; 
lean_dec_ref(v___x_1200_);
lean_dec(v_fst_1198_);
lean_del_object(v___x_1196_);
v___x_1215_ = lean_box(0);
return v___x_1215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findSyntheticCompletions(lean_object* v_fileMap_1219_, lean_object* v_hoverPos_1220_, lean_object* v_cmdStx_1221_, lean_object* v_infoTree_1222_){
_start:
{
lean_object* v_val_1224_; lean_object* v___x_1228_; 
lean_inc_ref(v_infoTree_1222_);
lean_inc(v_cmdStx_1221_);
lean_inc_ref(v_fileMap_1219_);
v___x_1228_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(v_fileMap_1219_, v_hoverPos_1220_, v_cmdStx_1221_, v_infoTree_1222_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1229_; 
lean_inc_ref(v_infoTree_1222_);
lean_inc(v_hoverPos_1220_);
v___x_1229_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticFieldCompletion_x3f(v_fileMap_1219_, v_hoverPos_1220_, v_cmdStx_1221_, v_infoTree_1222_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; 
v___x_1230_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(v_hoverPos_1220_, v_infoTree_1222_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v___x_1231_; 
v___x_1231_ = ((lean_object*)(l_Lean_Server_Completion_findSyntheticCompletions___closed__0));
return v___x_1231_;
}
else
{
lean_object* v_val_1232_; 
v_val_1232_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_val_1232_);
lean_dec_ref_known(v___x_1230_, 1);
v_val_1224_ = v_val_1232_;
goto v___jp_1223_;
}
}
else
{
lean_object* v_val_1233_; 
lean_dec_ref(v_infoTree_1222_);
lean_dec(v_hoverPos_1220_);
v_val_1233_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_val_1233_);
lean_dec_ref_known(v___x_1229_, 1);
v_val_1224_ = v_val_1233_;
goto v___jp_1223_;
}
}
else
{
lean_object* v_val_1234_; 
lean_dec_ref(v_infoTree_1222_);
lean_dec(v_cmdStx_1221_);
lean_dec(v_hoverPos_1220_);
lean_dec_ref(v_fileMap_1219_);
v_val_1234_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_val_1234_);
lean_dec_ref_known(v___x_1228_, 1);
v_val_1224_ = v_val_1234_;
goto v___jp_1223_;
}
v___jp_1223_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_unsigned_to_nat(1u);
v___x_1226_ = lean_mk_empty_array_with_capacity(v___x_1225_);
v___x_1227_ = lean_array_push(v___x_1226_, v_val_1224_);
return v___x_1227_;
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
