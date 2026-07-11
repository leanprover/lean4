// Lean compiler output
// Module: Lean.Server.Completion.SyntheticCompletion
// Imports: public import Lean.Server.InfoUtils public import Lean.Server.Completion.CompletionUtils
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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lineStart(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTrailingSize(lean_object*);
uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Info_pos_x3f(lean_object*);
lean_object* l_Lean_Elab_Info_tailPos_x3f(lean_object*);
lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
uint8_t l_Lean_Elab_Info_isSmaller(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_lctx(lean_object*);
uint8_t lean_local_ctx_is_empty(lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Server.InfoUtils.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.InfoUtils"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_0),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_1),((lean_object*)&l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(lean_object* v_msg_96_){
_start:
{
lean_object* v___f_97_; lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___f_101_; lean_object* v___f_102_; lean_object* v___f_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___f_97_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0));
v___f_98_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1));
v___f_99_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2));
v___f_100_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3));
v___f_101_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4));
v___f_102_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5));
v___f_103_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6));
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
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_113_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__2));
v___x_114_ = lean_unsigned_to_nat(21u);
v___x_115_ = lean_unsigned_to_nat(65u);
v___x_116_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__1));
v___x_117_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__0));
v___x_118_ = l_mkPanicMessageWithDecl(v___x_117_, v___x_116_, v___x_115_, v___x_114_, v___x_113_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(lean_object* v_preNode_119_, lean_object* v_postNode_120_, lean_object* v_x_121_, lean_object* v_x_122_){
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
v___x_127_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3);
v___x_128_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(v___x_127_);
return v___x_128_;
}
else
{
lean_object* v_i_129_; lean_object* v_children_130_; lean_object* v_val_131_; lean_object* v___x_132_; uint8_t v___x_133_; uint8_t v___x_134_; 
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
v___x_134_ = lean_bool_not(v___x_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_135_ = l_Lean_Elab_Info_updateContext_x3f(v_x_121_, v_i_129_);
v___x_136_ = l_Lean_PersistentArray_toList___redArg(v_children_130_);
v___x_137_ = lean_box(0);
lean_inc(v_postNode_120_);
v___x_138_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(v_preNode_119_, v_postNode_120_, v___x_135_, v___x_136_, v___x_137_);
v___x_139_ = lean_apply_4(v_postNode_120_, v_val_131_, v_i_129_, v_children_130_, v___x_138_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
else
{
lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_149_; 
lean_dec_ref(v_preNode_119_);
v_isSharedCheck_149_ = !lean_is_exclusive(v_x_121_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; 
v_unused_150_ = lean_ctor_get(v_x_121_, 0);
lean_dec(v_unused_150_);
v___x_142_ = v_x_121_;
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
else
{
lean_dec(v_x_121_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_144_ = lean_box(0);
v___x_145_ = lean_apply_4(v_postNode_120_, v_val_131_, v_i_129_, v_children_130_, v___x_144_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_145_);
v___x_147_ = v___x_142_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
default: 
{
lean_object* v___x_151_; 
lean_dec_ref_known(v_x_122_, 1);
lean_dec(v_x_121_);
lean_dec(v_postNode_120_);
lean_dec_ref(v_preNode_119_);
v___x_151_ = lean_box(0);
return v___x_151_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(lean_object* v_preNode_152_, lean_object* v_postNode_153_, lean_object* v___x_154_, lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
lean_object* v___x_157_; 
lean_dec(v___x_154_);
lean_dec(v_postNode_153_);
lean_dec_ref(v_preNode_152_);
v___x_157_ = l_List_reverse___redArg(v_x_156_);
return v___x_157_;
}
else
{
lean_object* v_head_158_; lean_object* v_tail_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_168_; 
v_head_158_ = lean_ctor_get(v_x_155_, 0);
v_tail_159_ = lean_ctor_get(v_x_155_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_x_155_);
if (v_isSharedCheck_168_ == 0)
{
v___x_161_ = v_x_155_;
v_isShared_162_ = v_isSharedCheck_168_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_tail_159_);
lean_inc(v_head_158_);
lean_dec(v_x_155_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_168_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
lean_inc(v___x_154_);
lean_inc(v_postNode_153_);
lean_inc_ref(v_preNode_152_);
v___x_163_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v_preNode_152_, v_postNode_153_, v___x_154_, v_head_158_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v_x_156_);
lean_ctor_set(v___x_161_, 0, v___x_163_);
v___x_165_ = v___x_161_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_x_156_);
v___x_165_ = v_reuseFailAlloc_167_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
v_x_155_ = v_tail_159_;
v_x_156_ = v___x_165_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(lean_object* v_infoTree_170_, lean_object* v_gt_171_, lean_object* v_f_172_){
_start:
{
lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___f_173_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___closed__0));
v___x_174_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose), 7, 3);
lean_closure_set(v___x_174_, 0, lean_box(0));
lean_closure_set(v___x_174_, 1, v_gt_171_);
lean_closure_set(v___x_174_, 2, v_f_172_);
v___x_175_ = lean_box(0);
v___x_176_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v___f_173_, v___x_174_, v___x_175_, v_infoTree_170_);
if (lean_obj_tag(v___x_176_) == 0)
{
return v___x_175_;
}
else
{
lean_object* v_val_177_; 
v_val_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_val_177_);
lean_dec_ref_known(v___x_176_, 1);
return v_val_177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f(lean_object* v_00_u03b1_178_, lean_object* v_infoTree_179_, lean_object* v_gt_180_, lean_object* v_f_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(v_infoTree_179_, v_gt_180_, v_f_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0(lean_object* v_00_u03b1_183_, lean_object* v_msg_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(v_msg_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0(lean_object* v_00_u03b1_186_, lean_object* v_preNode_187_, lean_object* v_postNode_188_, lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v_preNode_187_, v_postNode_188_, v_x_189_, v_x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1(lean_object* v_00_u03b1_192_, lean_object* v_preNode_193_, lean_object* v_postNode_194_, lean_object* v___x_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(v_preNode_193_, v_postNode_194_, v___x_195_, v_x_196_, v_x_197_);
return v___x_198_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter(lean_object* v_a_199_, lean_object* v_b_200_){
_start:
{
lean_object* v_snd_201_; lean_object* v_snd_202_; uint8_t v___y_204_; uint8_t v___y_205_; uint8_t v___y_206_; lean_object* v___x_209_; uint8_t v___x_210_; uint8_t v___y_212_; uint8_t v___x_217_; 
v_snd_201_ = lean_ctor_get(v_a_199_, 1);
v_snd_202_ = lean_ctor_get(v_b_200_, 1);
v___x_209_ = l_Lean_Elab_Info_lctx(v_snd_201_);
v___x_210_ = lean_local_ctx_is_empty(v___x_209_);
v___x_217_ = lean_bool_not(v___x_210_);
if (v___x_217_ == 0)
{
v___y_212_ = v___x_217_;
goto v___jp_211_;
}
else
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = l_Lean_Elab_Info_lctx(v_snd_202_);
v___x_219_ = lean_local_ctx_is_empty(v___x_218_);
v___y_212_ = v___x_219_;
goto v___jp_211_;
}
v___jp_203_:
{
if (v___y_206_ == 0)
{
uint8_t v___x_207_; 
v___x_207_ = l_Lean_Elab_Info_isSmaller(v_snd_201_, v_snd_202_);
if (v___x_207_ == 0)
{
uint8_t v___x_208_; 
v___x_208_ = l_Lean_Elab_Info_isSmaller(v_snd_202_, v_snd_201_);
if (v___x_208_ == 0)
{
return v___x_208_;
}
else
{
return v___x_207_;
}
}
else
{
return v___y_205_;
}
}
else
{
return v___y_204_;
}
}
v___jp_211_:
{
uint8_t v___x_213_; 
v___x_213_ = 1;
if (v___y_212_ == 0)
{
if (v___x_210_ == 0)
{
v___y_204_ = v___y_212_;
v___y_205_ = v___x_213_;
v___y_206_ = v___x_210_;
goto v___jp_203_;
}
else
{
lean_object* v___x_214_; uint8_t v___x_215_; uint8_t v___x_216_; 
v___x_214_ = l_Lean_Elab_Info_lctx(v_snd_202_);
v___x_215_ = lean_local_ctx_is_empty(v___x_214_);
v___x_216_ = lean_bool_not(v___x_215_);
v___y_204_ = v___y_212_;
v___y_205_ = v___x_213_;
v___y_206_ = v___x_216_;
goto v___jp_203_;
}
}
else
{
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter___boxed(lean_object* v_a_220_, lean_object* v_b_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter(v_a_220_, v_b_221_);
lean_dec_ref(v_b_221_);
lean_dec_ref(v_a_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0(lean_object* v_hoverPos_224_, lean_object* v_ctx_225_, lean_object* v_info_226_, lean_object* v_x_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = l_Lean_Elab_Info_occursInOrOnBoundary(v_info_226_, v_hoverPos_224_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
lean_dec_ref(v_info_226_);
lean_dec_ref(v_ctx_225_);
v___x_229_ = lean_box(0);
return v___x_229_;
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v_ctx_225_);
lean_ctor_set(v___x_230_, 1, v_info_226_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0___boxed(lean_object* v_hoverPos_232_, lean_object* v_ctx_233_, lean_object* v_info_234_, lean_object* v_x_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0(v_hoverPos_232_, v_ctx_233_, v_info_234_, v_x_235_);
lean_dec_ref(v_x_235_);
lean_dec(v_hoverPos_232_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f(lean_object* v_hoverPos_238_, lean_object* v_infoTree_239_){
_start:
{
lean_object* v___f_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___f_240_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_240_, 0, v_hoverPos_238_);
v___x_241_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___closed__0));
v___x_242_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(v_infoTree_239_, v___x_241_, v___f_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__2(lean_object* v_msg_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_panic_fn_borrowed(v___x_244_, v_msg_243_);
return v___x_245_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0(lean_object* v_hoverPos_246_, lean_object* v_x_247_){
_start:
{
uint8_t v___x_248_; lean_object* v___x_249_; 
v___x_248_ = 0;
v___x_249_ = l_Lean_Syntax_getRange_x3f(v_x_247_, v___x_248_);
if (lean_obj_tag(v___x_249_) == 0)
{
return v___x_248_;
}
else
{
lean_object* v_val_250_; uint8_t v___x_251_; uint8_t v___x_252_; 
v_val_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_val_250_);
lean_dec_ref_known(v___x_249_, 1);
v___x_251_ = 1;
v___x_252_ = l_Lean_Syntax_Range_contains(v_val_250_, v_hoverPos_246_, v___x_251_);
lean_dec(v_val_250_);
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0___boxed(lean_object* v_hoverPos_253_, lean_object* v_x_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0(v_hoverPos_253_, v_x_254_);
lean_dec(v_x_254_);
lean_dec(v_hoverPos_253_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1(lean_object* v_stx_257_){
_start:
{
uint8_t v___x_258_; uint8_t v___x_259_; 
v___x_258_ = l_Lean_Syntax_hasArgs(v_stx_257_);
v___x_259_ = lean_bool_not(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1___boxed(lean_object* v_stx_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1(v_stx_260_);
lean_dec(v_stx_260_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
return v_x_275_;
}
else
{
lean_object* v_head_276_; lean_object* v_tail_277_; uint8_t v___y_279_; lean_object* v_fst_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_head_276_ = lean_ctor_get(v_x_275_, 0);
v_tail_277_ = lean_ctor_get(v_x_275_, 1);
v_fst_281_ = lean_ctor_get(v_head_276_, 0);
v___x_282_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
lean_inc(v_fst_281_);
v___x_283_ = l_Lean_Syntax_isOfKind(v_fst_281_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6));
lean_inc(v_fst_281_);
v___x_285_ = l_Lean_Syntax_isOfKind(v_fst_281_, v___x_284_);
if (v___x_285_ == 0)
{
uint8_t v___x_286_; 
v___x_286_ = lean_bool_not(v___x_283_);
v___y_279_ = v___x_286_;
goto v___jp_278_;
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; uint8_t v___x_290_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = l_Lean_Syntax_getArg(v_fst_281_, v___x_287_);
v___x_289_ = l_Lean_Syntax_isOfKind(v___x_288_, v___x_282_);
v___x_290_ = lean_bool_not(v___x_289_);
v___y_279_ = v___x_290_;
goto v___jp_278_;
}
}
else
{
uint8_t v___x_291_; 
v___x_291_ = lean_bool_not(v___x_283_);
v___y_279_ = v___x_291_;
goto v___jp_278_;
}
v___jp_278_:
{
if (v___y_279_ == 0)
{
return v_x_275_;
}
else
{
lean_inc(v_tail_277_);
lean_dec_ref_known(v_x_275_, 2);
v_x_275_ = v_tail_277_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(lean_object* v_x_298_){
_start:
{
if (lean_obj_tag(v_x_298_) == 0)
{
uint8_t v___x_299_; 
v___x_299_ = 0;
return v___x_299_;
}
else
{
lean_object* v_head_300_; lean_object* v_tail_301_; uint8_t v___y_303_; lean_object* v_fst_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_head_300_ = lean_ctor_get(v_x_298_, 0);
lean_inc(v_head_300_);
v_tail_301_ = lean_ctor_get(v_x_298_, 1);
lean_inc(v_tail_301_);
lean_dec_ref_known(v_x_298_, 2);
v_fst_305_ = lean_ctor_get(v_head_300_, 0);
lean_inc_n(v_fst_305_, 2);
lean_dec(v_head_300_);
v___x_306_ = ((lean_object*)(l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1));
v___x_307_ = l_Lean_Syntax_isOfKind(v_fst_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_dec(v_fst_305_);
v___y_303_ = v___x_307_;
goto v___jp_302_;
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = l_Lean_Syntax_getArg(v_fst_305_, v___x_308_);
lean_dec(v_fst_305_);
v___x_310_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
v___x_311_ = l_Lean_Syntax_isOfKind(v___x_309_, v___x_310_);
v___y_303_ = v___x_311_;
goto v___jp_302_;
}
v___jp_302_:
{
if (v___y_303_ == 0)
{
v_x_298_ = v_tail_301_;
goto _start;
}
else
{
lean_dec(v_tail_301_);
return v___y_303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___boxed(lean_object* v_x_312_){
_start:
{
uint8_t v_res_313_; lean_object* v_r_314_; 
v_res_313_ = l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(v_x_312_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_319_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3));
v___x_320_ = lean_unsigned_to_nat(14u);
v___x_321_ = lean_unsigned_to_nat(22u);
v___x_322_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2));
v___x_323_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1));
v___x_324_ = l_mkPanicMessageWithDecl(v___x_323_, v___x_322_, v___x_321_, v___x_320_, v___x_319_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(lean_object* v_hoverPos_325_, lean_object* v_infoTree_326_){
_start:
{
lean_object* v___x_327_; 
lean_inc(v_hoverPos_325_);
v___x_327_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f(v_hoverPos_325_, v_infoTree_326_);
if (lean_obj_tag(v___x_327_) == 1)
{
lean_object* v_val_328_; lean_object* v_fst_329_; lean_object* v_snd_330_; lean_object* v___f_331_; lean_object* v___f_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_val_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_val_328_);
lean_dec_ref_known(v___x_327_, 1);
v_fst_329_ = lean_ctor_get(v_val_328_, 0);
lean_inc(v_fst_329_);
v_snd_330_ = lean_ctor_get(v_val_328_, 1);
lean_inc(v_snd_330_);
lean_dec(v_val_328_);
lean_inc(v_hoverPos_325_);
v___f_331_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_331_, 0, v_hoverPos_325_);
v___f_332_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0));
v___x_333_ = l_Lean_Elab_Info_stx(v_snd_330_);
v___x_334_ = l_Lean_Syntax_findStack_x3f(v___x_333_, v___f_331_, v___f_332_);
if (lean_obj_tag(v___x_334_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_389_; 
v_val_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_389_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_389_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_val_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_389_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v_stack_339_; lean_object* v___x_340_; 
v_stack_339_ = l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(v_val_335_);
v___x_340_ = l_List_head_x3f___redArg(v_stack_339_);
if (lean_obj_tag(v___x_340_) == 1)
{
lean_object* v_val_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_387_; 
v_val_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_387_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_387_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_val_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_387_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v_fst_345_; lean_object* v___y_347_; uint8_t v___y_348_; lean_object* v___y_349_; lean_object* v___y_358_; uint8_t v___y_359_; lean_object* v___y_360_; uint8_t v_isDotIdCompletion_367_; lean_object* v_fst_369_; uint8_t v_snd_370_; 
v_fst_345_ = lean_ctor_get(v_val_341_, 0);
lean_inc(v_fst_345_);
lean_dec(v_val_341_);
v_isDotIdCompletion_367_ = l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(v_stack_339_);
if (v_isDotIdCompletion_367_ == 0)
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
lean_inc(v_fst_345_);
v___x_376_ = l_Lean_Syntax_isOfKind(v_fst_345_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_377_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6));
lean_inc(v_fst_345_);
v___x_378_ = l_Lean_Syntax_isOfKind(v_fst_345_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_dec(v_fst_345_);
lean_del_object(v___x_343_);
lean_del_object(v___x_337_);
lean_dec(v_snd_330_);
lean_dec(v_fst_329_);
lean_dec(v_hoverPos_325_);
v___x_379_ = lean_box(0);
return v___x_379_;
}
else
{
lean_object* v___x_380_; lean_object* v_id_381_; uint8_t v___x_382_; 
v___x_380_ = lean_unsigned_to_nat(0u);
v_id_381_ = l_Lean_Syntax_getArg(v_fst_345_, v___x_380_);
lean_inc(v_id_381_);
v___x_382_ = l_Lean_Syntax_isOfKind(v_id_381_, v___x_375_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec(v_id_381_);
lean_dec(v_fst_345_);
lean_del_object(v___x_343_);
lean_del_object(v___x_337_);
lean_dec(v_snd_330_);
lean_dec(v_fst_329_);
lean_dec(v_hoverPos_325_);
v___x_383_ = lean_box(0);
return v___x_383_;
}
else
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_TSyntax_getId(v_id_381_);
lean_dec(v_id_381_);
v_fst_369_ = v___x_384_;
v_snd_370_ = v___x_382_;
goto v___jp_368_;
}
}
}
else
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_TSyntax_getId(v_fst_345_);
v_fst_369_ = v___x_385_;
v_snd_370_ = v_isDotIdCompletion_367_;
goto v___jp_368_;
}
}
else
{
lean_object* v___x_386_; 
lean_dec(v_fst_345_);
lean_del_object(v___x_343_);
lean_del_object(v___x_337_);
lean_dec(v_snd_330_);
lean_dec(v_fst_329_);
lean_dec(v_hoverPos_325_);
v___x_386_ = lean_box(0);
return v___x_386_;
}
v___jp_346_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_350_ = l_Lean_Elab_Info_lctx(v_snd_330_);
lean_dec(v_snd_330_);
v___x_351_ = lean_box(0);
v___x_352_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_352_, 0, v_fst_345_);
lean_ctor_set(v___x_352_, 1, v___y_347_);
lean_ctor_set(v___x_352_, 2, v___x_350_);
lean_ctor_set(v___x_352_, 3, v___x_351_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*4, v___y_348_);
v___x_353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_353_, 0, v___y_349_);
lean_ctor_set(v___x_353_, 1, v_fst_329_);
lean_ctor_set(v___x_353_, 2, v___x_352_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_353_);
v___x_355_ = v___x_343_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
v___jp_357_:
{
uint8_t v___x_361_; 
v___x_361_ = lean_nat_dec_lt(v_hoverPos_325_, v___y_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
lean_dec(v___y_360_);
lean_del_object(v___x_337_);
lean_dec(v_hoverPos_325_);
v___x_362_ = lean_box(0);
v___y_347_ = v___y_358_;
v___y_348_ = v___y_359_;
v___y_349_ = v___x_362_;
goto v___jp_346_;
}
else
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_nat_sub(v___y_360_, v_hoverPos_325_);
lean_dec(v_hoverPos_325_);
lean_dec(v___y_360_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_363_);
v___x_365_ = v___x_337_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
v___y_347_ = v___y_358_;
v___y_348_ = v___y_359_;
v___y_349_ = v___x_365_;
goto v___jp_346_;
}
}
}
v___jp_368_:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Syntax_getTailPos_x3f(v_fst_345_, v_isDotIdCompletion_367_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_obj_once(&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4, &l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_once, _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4);
v___x_373_ = l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__2(v___x_372_);
v___y_358_ = v_fst_369_;
v___y_359_ = v_snd_370_;
v___y_360_ = v___x_373_;
goto v___jp_357_;
}
else
{
lean_object* v_val_374_; 
v_val_374_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v___x_371_, 1);
v___y_358_ = v_fst_369_;
v___y_359_ = v_snd_370_;
v___y_360_ = v_val_374_;
goto v___jp_357_;
}
}
}
}
else
{
lean_object* v___x_388_; 
lean_dec(v___x_340_);
lean_dec(v_stack_339_);
lean_del_object(v___x_337_);
lean_dec(v_snd_330_);
lean_dec(v_fst_329_);
lean_dec(v_hoverPos_325_);
v___x_388_ = lean_box(0);
return v___x_388_;
}
}
}
else
{
lean_object* v___x_390_; 
lean_dec(v___x_334_);
lean_dec(v_snd_330_);
lean_dec(v_fst_329_);
lean_dec(v_hoverPos_325_);
v___x_390_ = lean_box(0);
return v___x_390_;
}
}
else
{
lean_object* v___x_391_; 
lean_dec(v___x_327_);
lean_dec(v_hoverPos_325_);
v___x_391_ = lean_box(0);
return v___x_391_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(lean_object* v_fileMap_392_, lean_object* v_hoverPos_393_){
_start:
{
lean_object* v_source_394_; uint8_t v___x_395_; 
v_source_394_ = lean_ctor_get(v_fileMap_392_, 0);
v___x_395_ = lean_string_utf8_at_end(v_source_394_, v_hoverPos_393_);
if (v___x_395_ == 0)
{
uint32_t v___x_396_; uint8_t v___y_398_; uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_396_ = lean_string_utf8_get(v_source_394_, v_hoverPos_393_);
v___x_403_ = 32;
v___x_404_ = lean_uint32_dec_eq(v___x_396_, v___x_403_);
if (v___x_404_ == 0)
{
uint32_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 9;
v___x_406_ = lean_uint32_dec_eq(v___x_396_, v___x_405_);
v___y_398_ = v___x_406_;
goto v___jp_397_;
}
else
{
v___y_398_ = v___x_404_;
goto v___jp_397_;
}
v___jp_397_:
{
if (v___y_398_ == 0)
{
uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_399_ = 13;
v___x_400_ = lean_uint32_dec_eq(v___x_396_, v___x_399_);
if (v___x_400_ == 0)
{
uint32_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = 10;
v___x_402_ = lean_uint32_dec_eq(v___x_396_, v___x_401_);
return v___x_402_;
}
else
{
return v___x_400_;
}
}
else
{
return v___y_398_;
}
}
}
else
{
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace___boxed(lean_object* v_fileMap_407_, lean_object* v_hoverPos_408_){
_start:
{
uint8_t v_res_409_; lean_object* v_r_410_; 
v_res_409_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_407_, v_hoverPos_408_);
lean_dec(v_hoverPos_408_);
lean_dec_ref(v_fileMap_407_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(lean_object* v_fileMap_411_, lean_object* v_hoverPos_412_){
_start:
{
uint32_t v___y_414_; uint8_t v___y_415_; lean_object* v_source_420_; uint8_t v___y_430_; uint8_t v___x_431_; 
v_source_420_ = lean_ctor_get(v_fileMap_411_, 0);
v___x_431_ = lean_string_utf8_at_end(v_source_420_, v_hoverPos_412_);
if (v___x_431_ == 0)
{
uint32_t v___x_432_; uint8_t v___y_434_; uint32_t v___x_439_; uint8_t v___x_440_; 
v___x_432_ = lean_string_utf8_get(v_source_420_, v_hoverPos_412_);
v___x_439_ = 32;
v___x_440_ = lean_uint32_dec_eq(v___x_432_, v___x_439_);
if (v___x_440_ == 0)
{
uint32_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 9;
v___x_442_ = lean_uint32_dec_eq(v___x_432_, v___x_441_);
v___y_434_ = v___x_442_;
goto v___jp_433_;
}
else
{
v___y_434_ = v___x_440_;
goto v___jp_433_;
}
v___jp_433_:
{
if (v___y_434_ == 0)
{
uint32_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = 13;
v___x_436_ = lean_uint32_dec_eq(v___x_432_, v___x_435_);
if (v___x_436_ == 0)
{
uint32_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = 10;
v___x_438_ = lean_uint32_dec_eq(v___x_432_, v___x_437_);
v___y_430_ = v___x_438_;
goto v___jp_429_;
}
else
{
v___y_430_ = v___x_436_;
goto v___jp_429_;
}
}
else
{
goto v___jp_421_;
}
}
}
else
{
v___y_430_ = v___x_431_;
goto v___jp_429_;
}
v___jp_413_:
{
if (v___y_415_ == 0)
{
uint32_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = 13;
v___x_417_ = lean_uint32_dec_eq(v___y_414_, v___x_416_);
if (v___x_417_ == 0)
{
uint32_t v___x_418_; uint8_t v___x_419_; 
v___x_418_ = 10;
v___x_419_ = lean_uint32_dec_eq(v___y_414_, v___x_418_);
return v___x_419_;
}
else
{
return v___x_417_;
}
}
else
{
return v___y_415_;
}
}
v___jp_421_:
{
lean_object* v___x_422_; lean_object* v___x_423_; uint32_t v___x_424_; uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_sub(v_hoverPos_412_, v___x_422_);
v___x_424_ = lean_string_utf8_get(v_source_420_, v___x_423_);
lean_dec(v___x_423_);
v___x_425_ = 32;
v___x_426_ = lean_uint32_dec_eq(v___x_424_, v___x_425_);
if (v___x_426_ == 0)
{
uint32_t v___x_427_; uint8_t v___x_428_; 
v___x_427_ = 9;
v___x_428_ = lean_uint32_dec_eq(v___x_424_, v___x_427_);
v___y_414_ = v___x_424_;
v___y_415_ = v___x_428_;
goto v___jp_413_;
}
else
{
v___y_414_ = v___x_424_;
v___y_415_ = v___x_426_;
goto v___jp_413_;
}
}
v___jp_429_:
{
if (v___y_430_ == 0)
{
return v___y_430_;
}
else
{
goto v___jp_421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace___boxed(lean_object* v_fileMap_443_, lean_object* v_hoverPos_444_){
_start:
{
uint8_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_443_, v_hoverPos_444_);
lean_dec(v_hoverPos_444_);
lean_dec_ref(v_fileMap_443_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(lean_object* v_stx_460_){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
lean_inc(v_stx_460_);
v___x_461_ = l_Lean_Syntax_getKind(v_stx_460_);
v___x_462_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2));
v___x_463_ = lean_name_eq(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_465_ = lean_name_eq(v___x_461_, v___x_464_);
lean_dec(v___x_461_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
lean_dec(v_stx_460_);
v___x_466_ = lean_box(0);
return v___x_466_;
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = l_Lean_Syntax_getArg(v_stx_460_, v___x_467_);
lean_dec(v_stx_460_);
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec(v___x_461_);
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = l_Lean_Syntax_getArg(v_stx_460_, v___x_470_);
lean_dec(v_stx_460_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(lean_object* v_fileMap_473_, lean_object* v_hoverPos_474_, lean_object* v_hoverFilePos_475_, lean_object* v_stx_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(v_stx_476_);
if (lean_obj_tag(v___x_477_) == 1)
{
lean_object* v_val_478_; uint8_t v___x_479_; lean_object* v___x_480_; 
v_val_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_val_478_);
lean_dec_ref_known(v___x_477_, 1);
v___x_479_ = 0;
v___x_480_ = l_Lean_Syntax_getPos_x3f(v_val_478_, v___x_479_);
lean_dec(v_val_478_);
if (lean_obj_tag(v___x_480_) == 1)
{
lean_object* v_val_481_; lean_object* v___x_482_; lean_object* v_column_483_; lean_object* v_column_484_; uint8_t v___x_485_; 
v_val_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_val_481_);
lean_dec_ref_known(v___x_480_, 1);
lean_inc_ref(v_fileMap_473_);
v___x_482_ = l_Lean_FileMap_toPosition(v_fileMap_473_, v_val_481_);
lean_dec(v_val_481_);
v_column_483_ = lean_ctor_get(v___x_482_, 1);
lean_inc(v_column_483_);
lean_dec_ref(v___x_482_);
v_column_484_ = lean_ctor_get(v_hoverFilePos_475_, 1);
v___x_485_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_473_, v_hoverPos_474_);
lean_dec_ref(v_fileMap_473_);
if (v___x_485_ == 0)
{
lean_dec(v_column_483_);
return v___x_485_;
}
else
{
uint8_t v_isCursorInTacticBlock_486_; 
v_isCursorInTacticBlock_486_ = lean_nat_dec_eq(v_column_484_, v_column_483_);
lean_dec(v_column_483_);
return v_isCursorInTacticBlock_486_;
}
}
else
{
lean_dec(v___x_480_);
lean_dec_ref(v_fileMap_473_);
return v___x_479_;
}
}
else
{
uint8_t v___x_487_; 
lean_dec(v___x_477_);
lean_dec_ref(v_fileMap_473_);
v___x_487_ = 0;
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation___boxed(lean_object* v_fileMap_488_, lean_object* v_hoverPos_489_, lean_object* v_hoverFilePos_490_, lean_object* v_stx_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_488_, v_hoverPos_489_, v_hoverFilePos_490_, v_stx_491_);
lean_dec_ref(v_hoverFilePos_490_);
lean_dec(v_hoverPos_489_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(lean_object* v_hoverPos_495_, lean_object* v_as_496_, size_t v_i_497_, size_t v_stop_498_){
_start:
{
uint8_t v___x_503_; 
v___x_503_ = lean_usize_dec_eq(v_i_497_, v_stop_498_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; uint8_t v___y_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_504_ = 1;
v___x_507_ = lean_array_uget_borrowed(v_as_496_, v_i_497_);
v___x_508_ = l_Lean_Syntax_getTailPos_x3f(v___x_507_, v___x_503_);
if (lean_obj_tag(v___x_508_) == 1)
{
lean_object* v_val_509_; uint8_t v___y_511_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_val_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_val_509_);
lean_dec_ref_known(v___x_508_, 1);
v___x_515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___closed__0));
lean_inc(v___x_507_);
v___x_516_ = l_Lean_Syntax_isToken(v___x_515_, v___x_507_);
if (v___x_516_ == 0)
{
v___y_511_ = v___x_516_;
goto v___jp_510_;
}
else
{
uint8_t v___x_517_; 
v___x_517_ = lean_nat_dec_le(v_val_509_, v_hoverPos_495_);
v___y_511_ = v___x_517_;
goto v___jp_510_;
}
v___jp_510_:
{
if (v___y_511_ == 0)
{
lean_dec(v_val_509_);
goto v___jp_499_;
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_512_ = l_Lean_Syntax_getTrailingSize(v___x_507_);
v___x_513_ = lean_nat_add(v_val_509_, v___x_512_);
lean_dec(v___x_512_);
lean_dec(v_val_509_);
v___x_514_ = lean_nat_dec_le(v_hoverPos_495_, v___x_513_);
lean_dec(v___x_513_);
v___y_506_ = v___x_514_;
goto v___jp_505_;
}
}
}
else
{
lean_dec(v___x_508_);
v___y_506_ = v___x_503_;
goto v___jp_505_;
}
v___jp_505_:
{
if (v___y_506_ == 0)
{
goto v___jp_499_;
}
else
{
return v___x_504_;
}
}
}
else
{
uint8_t v___x_518_; 
v___x_518_ = 0;
return v___x_518_;
}
v___jp_499_:
{
size_t v___x_500_; size_t v___x_501_; 
v___x_500_ = ((size_t)1ULL);
v___x_501_ = lean_usize_add(v_i_497_, v___x_500_);
v_i_497_ = v___x_501_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___boxed(lean_object* v_hoverPos_519_, lean_object* v_as_520_, lean_object* v_i_521_, lean_object* v_stop_522_){
_start:
{
size_t v_i_boxed_523_; size_t v_stop_boxed_524_; uint8_t v_res_525_; lean_object* v_r_526_; 
v_i_boxed_523_ = lean_unbox_usize(v_i_521_);
lean_dec(v_i_521_);
v_stop_boxed_524_ = lean_unbox_usize(v_stop_522_);
lean_dec(v_stop_522_);
v_res_525_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_519_, v_as_520_, v_i_boxed_523_, v_stop_boxed_524_);
lean_dec_ref(v_as_520_);
lean_dec(v_hoverPos_519_);
v_r_526_ = lean_box(v_res_525_);
return v_r_526_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(lean_object* v_fileMap_527_, lean_object* v_hoverPos_528_, lean_object* v_stx_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(v_stx_529_);
if (lean_obj_tag(v___x_530_) == 1)
{
lean_object* v_val_531_; uint8_t v___x_532_; 
v_val_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_val_531_);
lean_dec_ref_known(v___x_530_, 1);
v___x_532_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_527_, v_hoverPos_528_);
if (v___x_532_ == 0)
{
lean_dec(v_val_531_);
return v___x_532_;
}
else
{
lean_object* v_tactics_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v_tactics_533_ = l_Lean_Syntax_getArgs(v_val_531_);
lean_dec(v_val_531_);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = lean_array_get_size(v_tactics_533_);
v___x_536_ = lean_nat_dec_lt(v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
lean_dec_ref(v_tactics_533_);
return v___x_536_;
}
else
{
if (v___x_536_ == 0)
{
lean_dec_ref(v_tactics_533_);
return v___x_536_;
}
else
{
size_t v___x_537_; size_t v___x_538_; uint8_t v___x_539_; 
v___x_537_ = ((size_t)0ULL);
v___x_538_ = lean_usize_of_nat(v___x_535_);
v___x_539_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_528_, v_tactics_533_, v___x_537_, v___x_538_);
lean_dec_ref(v_tactics_533_);
return v___x_539_;
}
}
}
}
else
{
uint8_t v___x_540_; 
lean_dec(v___x_530_);
v___x_540_ = 0;
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon___boxed(lean_object* v_fileMap_541_, lean_object* v_hoverPos_542_, lean_object* v_stx_543_){
_start:
{
uint8_t v_res_544_; lean_object* v_r_545_; 
v_res_544_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_541_, v_hoverPos_542_, v_stx_543_);
lean_dec(v_hoverPos_542_);
lean_dec_ref(v_fileMap_541_);
v_r_545_ = lean_box(v_res_544_);
return v_r_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(lean_object* v_fileMap_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_fst_548_; lean_object* v_snd_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_573_; 
v_fst_548_ = lean_ctor_get(v_a_547_, 0);
v_snd_549_ = lean_ctor_get(v_a_547_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_a_547_);
if (v_isSharedCheck_573_ == 0)
{
v___x_551_ = v_a_547_;
v_isShared_552_ = v_isSharedCheck_573_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_snd_549_);
lean_inc(v_fst_548_);
lean_dec(v_a_547_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_573_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v_source_553_; uint8_t v___x_554_; uint8_t v___x_555_; 
v_source_553_ = lean_ctor_get(v_fileMap_546_, 0);
v___x_554_ = lean_string_utf8_at_end(v_source_553_, v_fst_548_);
v___x_555_ = lean_bool_not(v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_557_; 
if (v_isShared_552_ == 0)
{
v___x_557_ = v___x_551_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_fst_548_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_snd_549_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
else
{
uint32_t v___x_559_; uint32_t v___x_560_; uint8_t v___x_561_; uint8_t v___x_562_; 
v___x_559_ = lean_string_utf8_get(v_source_553_, v_fst_548_);
v___x_560_ = 32;
v___x_561_ = lean_uint32_dec_eq(v___x_559_, v___x_560_);
v___x_562_ = lean_bool_not(v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_563_ = lean_string_utf8_next(v_source_553_, v_fst_548_);
lean_dec(v_fst_548_);
v___x_564_ = lean_unsigned_to_nat(1u);
v___x_565_ = lean_nat_add(v_snd_549_, v___x_564_);
lean_dec(v_snd_549_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v___x_565_);
lean_ctor_set(v___x_551_, 0, v___x_563_);
v___x_567_ = v___x_551_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v___x_565_);
v___x_567_ = v_reuseFailAlloc_569_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
v_a_547_ = v___x_567_;
goto _start;
}
}
else
{
lean_object* v___x_571_; 
if (v_isShared_552_ == 0)
{
v___x_571_ = v___x_551_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_fst_548_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_snd_549_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg___boxed(lean_object* v_fileMap_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_574_, v_a_575_);
lean_dec_ref(v_fileMap_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(lean_object* v_fileMap_577_, lean_object* v_pos_578_){
_start:
{
lean_object* v_n_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v_snd_582_; 
v_n_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_pos_578_);
lean_ctor_set(v___x_580_, 1, v_n_579_);
v___x_581_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_577_, v___x_580_);
v_snd_582_ = lean_ctor_get(v___x_581_, 1);
lean_inc(v_snd_582_);
lean_dec_ref(v___x_581_);
return v_snd_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces___boxed(lean_object* v_fileMap_583_, lean_object* v_pos_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(v_fileMap_583_, v_pos_584_);
lean_dec_ref(v_fileMap_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(lean_object* v_fileMap_586_, lean_object* v_inst_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_586_, v_a_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___boxed(lean_object* v_fileMap_590_, lean_object* v_inst_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(v_fileMap_590_, v_inst_591_, v_a_592_);
lean_dec_ref(v_fileMap_590_);
return v_res_593_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(lean_object* v_fileMap_594_, lean_object* v_hoverPos_595_, lean_object* v_leadingTokenTailPos_x3f_596_){
_start:
{
if (lean_obj_tag(v_leadingTokenTailPos_x3f_596_) == 1)
{
lean_object* v_val_597_; lean_object* v_hoverFilePos_598_; lean_object* v_line_599_; lean_object* v_column_600_; lean_object* v_tokenTailFilePos_601_; lean_object* v_line_602_; uint8_t v___x_603_; 
v_val_597_ = lean_ctor_get(v_leadingTokenTailPos_x3f_596_, 0);
lean_inc_ref_n(v_fileMap_594_, 2);
v_hoverFilePos_598_ = l_Lean_FileMap_toPosition(v_fileMap_594_, v_hoverPos_595_);
v_line_599_ = lean_ctor_get(v_hoverFilePos_598_, 0);
lean_inc(v_line_599_);
v_column_600_ = lean_ctor_get(v_hoverFilePos_598_, 1);
lean_inc(v_column_600_);
lean_dec_ref(v_hoverFilePos_598_);
v_tokenTailFilePos_601_ = l_Lean_FileMap_toPosition(v_fileMap_594_, v_val_597_);
v_line_602_ = lean_ctor_get(v_tokenTailFilePos_601_, 0);
lean_inc(v_line_602_);
lean_dec_ref(v_tokenTailFilePos_601_);
v___x_603_ = lean_nat_dec_eq(v_line_599_, v_line_602_);
lean_dec(v_line_599_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v_expectedColumn_607_; uint8_t v___x_608_; 
v___x_604_ = l_Lean_FileMap_lineStart(v_fileMap_594_, v_line_602_);
lean_dec(v_line_602_);
v___x_605_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(v_fileMap_594_, v___x_604_);
lean_dec_ref(v_fileMap_594_);
v___x_606_ = lean_unsigned_to_nat(2u);
v_expectedColumn_607_ = lean_nat_add(v___x_605_, v___x_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_nat_dec_eq(v_column_600_, v_expectedColumn_607_);
lean_dec(v_expectedColumn_607_);
lean_dec(v_column_600_);
return v___x_608_;
}
else
{
uint8_t v___x_609_; 
lean_dec(v_line_602_);
lean_dec(v_column_600_);
lean_dec_ref(v_fileMap_594_);
v___x_609_ = lean_nat_dec_le(v_val_597_, v_hoverPos_595_);
return v___x_609_;
}
}
else
{
uint8_t v___x_610_; 
lean_dec_ref(v_fileMap_594_);
v___x_610_ = 1;
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation___boxed(lean_object* v_fileMap_611_, lean_object* v_hoverPos_612_, lean_object* v_leadingTokenTailPos_x3f_613_){
_start:
{
uint8_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(v_fileMap_611_, v_hoverPos_612_, v_leadingTokenTailPos_x3f_613_);
lean_dec(v_leadingTokenTailPos_x3f_613_);
lean_dec(v_hoverPos_612_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(lean_object* v_a_616_){
_start:
{
switch(lean_obj_tag(v_a_616_))
{
case 0:
{
uint8_t v___x_617_; 
v___x_617_ = 1;
return v___x_617_;
}
case 1:
{
lean_object* v_args_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_args_618_ = lean_ctor_get(v_a_616_, 2);
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_array_get_size(v_args_618_);
v___x_621_ = lean_nat_dec_lt(v___x_619_, v___x_620_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; 
v___x_622_ = lean_bool_not(v___x_621_);
return v___x_622_;
}
else
{
if (v___x_621_ == 0)
{
uint8_t v___x_623_; 
v___x_623_ = lean_bool_not(v___x_621_);
return v___x_623_;
}
else
{
size_t v___x_624_; size_t v___x_625_; uint8_t v___x_626_; uint8_t v___x_627_; 
v___x_624_ = ((size_t)0ULL);
v___x_625_ = lean_usize_of_nat(v___x_620_);
v___x_626_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_args_618_, v___x_624_, v___x_625_);
v___x_627_ = lean_bool_not(v___x_626_);
return v___x_627_;
}
}
}
default: 
{
uint8_t v___x_628_; 
v___x_628_ = 0;
return v___x_628_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(lean_object* v_as_629_, size_t v_i_630_, size_t v_stop_631_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = lean_usize_dec_eq(v_i_630_, v_stop_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; uint8_t v___x_634_; uint8_t v___x_635_; 
v___x_633_ = lean_array_uget_borrowed(v_as_629_, v_i_630_);
v___x_634_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v___x_633_);
v___x_635_ = lean_bool_not(v___x_634_);
if (v___x_635_ == 0)
{
size_t v___x_636_; size_t v___x_637_; 
v___x_636_ = ((size_t)1ULL);
v___x_637_ = lean_usize_add(v_i_630_, v___x_636_);
v_i_630_ = v___x_637_;
goto _start;
}
else
{
return v___x_635_;
}
}
else
{
uint8_t v___x_639_; 
v___x_639_ = 0;
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0___boxed(lean_object* v_as_640_, lean_object* v_i_641_, lean_object* v_stop_642_){
_start:
{
size_t v_i_boxed_643_; size_t v_stop_boxed_644_; uint8_t v_res_645_; lean_object* v_r_646_; 
v_i_boxed_643_ = lean_unbox_usize(v_i_641_);
lean_dec(v_i_641_);
v_stop_boxed_644_ = lean_unbox_usize(v_stop_642_);
lean_dec(v_stop_642_);
v_res_645_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_as_640_, v_i_boxed_643_, v_stop_boxed_644_);
lean_dec_ref(v_as_640_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty___boxed(lean_object* v_a_647_){
_start:
{
uint8_t v_res_648_; lean_object* v_r_649_; 
v_res_648_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_a_647_);
lean_dec(v_a_647_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(lean_object* v_stx_656_){
_start:
{
uint8_t v___y_658_; uint8_t v___y_666_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
lean_inc(v_stx_656_);
v___x_671_ = l_Lean_Syntax_getKind(v_stx_656_);
v___x_672_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1));
v___x_673_ = lean_name_eq(v___x_671_, v___x_672_);
lean_dec(v___x_671_);
if (v___x_673_ == 0)
{
v___y_666_ = v___x_673_;
goto v___jp_665_;
}
else
{
uint8_t v___x_674_; 
v___x_674_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_stx_656_);
v___y_666_ = v___x_674_;
goto v___jp_665_;
}
v___jp_657_:
{
if (v___y_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
lean_inc(v_stx_656_);
v___x_659_ = l_Lean_Syntax_getKind(v_stx_656_);
v___x_660_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_661_ = lean_name_eq(v___x_659_, v___x_660_);
lean_dec(v___x_659_);
if (v___x_661_ == 0)
{
lean_dec(v_stx_656_);
return v___x_661_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = lean_unsigned_to_nat(1u);
v___x_663_ = l_Lean_Syntax_getArg(v_stx_656_, v___x_662_);
lean_dec(v_stx_656_);
v___x_664_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v___x_663_);
lean_dec(v___x_663_);
return v___x_664_;
}
}
else
{
lean_dec(v_stx_656_);
return v___y_658_;
}
}
v___jp_665_:
{
if (v___y_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
lean_inc(v_stx_656_);
v___x_667_ = l_Lean_Syntax_getKind(v_stx_656_);
v___x_668_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2));
v___x_669_ = lean_name_eq(v___x_667_, v___x_668_);
lean_dec(v___x_667_);
if (v___x_669_ == 0)
{
v___y_658_ = v___x_669_;
goto v___jp_657_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_stx_656_);
v___y_658_ = v___x_670_;
goto v___jp_657_;
}
}
else
{
lean_dec(v_stx_656_);
return v___y_666_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___boxed(lean_object* v_stx_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_675_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(lean_object* v_fileMap_678_, lean_object* v_hoverPos_679_, lean_object* v_stx_680_, lean_object* v_leadingTokenTailPos_x3f_681_){
_start:
{
uint8_t v___x_682_; uint8_t v___x_683_; 
v___x_682_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_678_, v_hoverPos_679_);
v___x_683_ = lean_bool_not(v___x_682_);
if (v___x_683_ == 0)
{
uint8_t v___x_684_; uint8_t v___x_685_; 
lean_inc(v_stx_680_);
v___x_684_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_680_);
v___x_685_ = lean_bool_not(v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
lean_inc(v_stx_680_);
v___x_686_ = l_Lean_Syntax_getKind(v_stx_680_);
v___x_687_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_688_ = lean_name_eq(v___x_686_, v___x_687_);
lean_dec(v___x_686_);
if (v___x_688_ == 0)
{
uint8_t v___x_689_; 
lean_dec(v_stx_680_);
v___x_689_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(v_fileMap_678_, v_hoverPos_679_, v_leadingTokenTailPos_x3f_681_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec_ref(v_fileMap_678_);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = l_Lean_Syntax_getArg(v_stx_680_, v___x_690_);
v___x_692_ = l_Lean_Syntax_getTailPos_x3f(v___x_691_, v___x_685_);
lean_dec(v___x_691_);
if (lean_obj_tag(v___x_692_) == 1)
{
lean_object* v_val_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_val_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_val_693_);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = lean_unsigned_to_nat(2u);
v___x_695_ = l_Lean_Syntax_getArg(v_stx_680_, v___x_694_);
lean_dec(v_stx_680_);
v___x_696_ = l_Lean_Syntax_getPos_x3f(v___x_695_, v___x_685_);
lean_dec(v___x_695_);
if (lean_obj_tag(v___x_696_) == 1)
{
lean_object* v_val_697_; uint8_t v___x_698_; 
v_val_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_val_697_);
lean_dec_ref_known(v___x_696_, 1);
v___x_698_ = lean_nat_dec_le(v_val_693_, v_hoverPos_679_);
lean_dec(v_val_693_);
if (v___x_698_ == 0)
{
lean_dec(v_val_697_);
return v___x_698_;
}
else
{
uint8_t v___x_699_; 
v___x_699_ = lean_nat_dec_le(v_hoverPos_679_, v_val_697_);
lean_dec(v_val_697_);
return v___x_699_;
}
}
else
{
lean_dec(v___x_696_);
lean_dec(v_val_693_);
return v___x_685_;
}
}
else
{
lean_dec(v___x_692_);
lean_dec(v_stx_680_);
return v___x_685_;
}
}
}
else
{
lean_dec(v_stx_680_);
lean_dec_ref(v_fileMap_678_);
return v___x_683_;
}
}
else
{
uint8_t v___x_700_; 
lean_dec(v_stx_680_);
lean_dec_ref(v_fileMap_678_);
v___x_700_ = 0;
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock___boxed(lean_object* v_fileMap_701_, lean_object* v_hoverPos_702_, lean_object* v_stx_703_, lean_object* v_leadingTokenTailPos_x3f_704_){
_start:
{
uint8_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_701_, v_hoverPos_702_, v_stx_703_, v_leadingTokenTailPos_x3f_704_);
lean_dec(v_leadingTokenTailPos_x3f_704_);
lean_dec(v_hoverPos_702_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(lean_object* v_fileMap_707_, lean_object* v_hoverPos_708_, lean_object* v_hoverFilePos_709_, lean_object* v_stx_710_, lean_object* v_leadingWs_711_, lean_object* v_leadingTokenTailPos_x3f_712_){
_start:
{
uint8_t v___y_714_; uint8_t v___x_733_; lean_object* v___x_734_; 
v___x_733_ = 0;
v___x_734_ = l_Lean_Syntax_getPos_x3f(v_stx_710_, v___x_733_);
if (lean_obj_tag(v___x_734_) == 1)
{
lean_object* v_val_735_; lean_object* v___x_736_; 
v_val_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_val_735_);
lean_dec_ref_known(v___x_734_, 1);
v___x_736_ = l_Lean_Syntax_getTailPos_x3f(v_stx_710_, v___x_733_);
if (lean_obj_tag(v___x_736_) == 1)
{
lean_object* v_val_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_val_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_val_737_);
lean_dec_ref_known(v___x_736_, 1);
v___x_738_ = lean_nat_sub(v_val_735_, v_leadingWs_711_);
lean_dec(v_val_735_);
v___x_739_ = lean_nat_dec_le(v___x_738_, v_hoverPos_708_);
lean_dec(v___x_738_);
if (v___x_739_ == 0)
{
lean_dec(v_val_737_);
v___y_714_ = v___x_739_;
goto v___jp_713_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_740_ = l_Lean_Syntax_getTrailingSize(v_stx_710_);
v___x_741_ = lean_nat_add(v_val_737_, v___x_740_);
lean_dec(v___x_740_);
lean_dec(v_val_737_);
v___x_742_ = lean_nat_dec_le(v_hoverPos_708_, v___x_741_);
lean_dec(v___x_741_);
v___y_714_ = v___x_742_;
goto v___jp_713_;
}
}
else
{
uint8_t v___x_743_; 
lean_dec(v___x_736_);
lean_dec(v_val_735_);
lean_dec(v_leadingWs_711_);
v___x_743_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_707_, v_hoverPos_708_, v_stx_710_, v_leadingTokenTailPos_x3f_712_);
lean_dec(v_leadingTokenTailPos_x3f_712_);
return v___x_743_;
}
}
else
{
uint8_t v___x_744_; 
lean_dec(v___x_734_);
lean_dec(v_leadingWs_711_);
v___x_744_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_707_, v_hoverPos_708_, v_stx_710_, v_leadingTokenTailPos_x3f_712_);
lean_dec(v_leadingTokenTailPos_x3f_712_);
return v___x_744_;
}
v___jp_713_:
{
uint8_t v___x_715_; 
v___x_715_ = lean_bool_not(v___y_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; size_t v_sz_720_; size_t v___x_721_; lean_object* v___x_722_; lean_object* v_fst_723_; 
v___x_716_ = l_Lean_Syntax_getArgs(v_stx_710_);
v___x_717_ = lean_box(0);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v_leadingWs_711_);
lean_ctor_set(v___x_718_, 1, v_leadingTokenTailPos_x3f_712_);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v_sz_720_ = lean_array_size(v___x_716_);
v___x_721_ = ((size_t)0ULL);
lean_inc_ref(v_fileMap_707_);
v___x_722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_707_, v_hoverPos_708_, v_hoverFilePos_709_, v___x_716_, v_sz_720_, v___x_721_, v___x_719_);
lean_dec_ref(v___x_716_);
v_fst_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_fst_723_);
if (lean_obj_tag(v_fst_723_) == 0)
{
lean_object* v_snd_724_; lean_object* v_snd_725_; uint8_t v___x_726_; uint8_t v___x_727_; 
v_snd_724_ = lean_ctor_get(v___x_722_, 1);
lean_inc(v_snd_724_);
lean_dec_ref(v___x_722_);
v_snd_725_ = lean_ctor_get(v_snd_724_, 1);
lean_inc(v_snd_725_);
lean_dec(v_snd_724_);
v___x_726_ = 1;
lean_inc(v_stx_710_);
lean_inc_ref(v_fileMap_707_);
v___x_727_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_707_, v_hoverPos_708_, v_stx_710_, v_snd_725_);
lean_dec(v_snd_725_);
if (v___x_727_ == 0)
{
uint8_t v___x_728_; 
lean_inc(v_stx_710_);
v___x_728_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_707_, v_hoverPos_708_, v_stx_710_);
if (v___x_728_ == 0)
{
uint8_t v___x_729_; 
v___x_729_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_707_, v_hoverPos_708_, v_hoverFilePos_709_, v_stx_710_);
return v___x_729_;
}
else
{
lean_dec(v_stx_710_);
lean_dec_ref(v_fileMap_707_);
return v___x_726_;
}
}
else
{
lean_dec(v_stx_710_);
lean_dec_ref(v_fileMap_707_);
return v___x_726_;
}
}
else
{
lean_object* v_val_730_; uint8_t v___x_731_; 
lean_dec_ref(v___x_722_);
lean_dec(v_stx_710_);
lean_dec_ref(v_fileMap_707_);
v_val_730_ = lean_ctor_get(v_fst_723_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v_fst_723_, 1);
v___x_731_ = lean_unbox(v_val_730_);
lean_dec(v_val_730_);
return v___x_731_;
}
}
else
{
uint8_t v___x_732_; 
lean_dec(v_leadingTokenTailPos_x3f_712_);
lean_dec(v_leadingWs_711_);
lean_dec(v_stx_710_);
lean_dec_ref(v_fileMap_707_);
v___x_732_ = 0;
return v___x_732_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(lean_object* v_fileMap_745_, lean_object* v_hoverPos_746_, lean_object* v_hoverFilePos_747_, lean_object* v_as_748_, size_t v_sz_749_, size_t v_i_750_, lean_object* v_b_751_){
_start:
{
uint8_t v___x_752_; 
v___x_752_ = lean_usize_dec_lt(v_i_750_, v_sz_749_);
if (v___x_752_ == 0)
{
lean_dec_ref(v_fileMap_745_);
return v_b_751_;
}
else
{
lean_object* v_snd_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_787_; 
v_snd_753_ = lean_ctor_get(v_b_751_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_b_751_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v_b_751_, 0);
lean_dec(v_unused_788_);
v___x_755_ = v_b_751_;
v_isShared_756_ = v_isSharedCheck_787_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_snd_753_);
lean_dec(v_b_751_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_787_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_fst_757_; lean_object* v_snd_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_786_; 
v_fst_757_ = lean_ctor_get(v_snd_753_, 0);
v_snd_758_ = lean_ctor_get(v_snd_753_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v_snd_753_);
if (v_isSharedCheck_786_ == 0)
{
v___x_760_ = v_snd_753_;
v_isShared_761_ = v_isSharedCheck_786_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_snd_758_);
lean_inc(v_fst_757_);
lean_dec(v_snd_753_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_786_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_a_762_; uint8_t v___x_763_; 
v_a_762_ = lean_array_uget_borrowed(v_as_748_, v_i_750_);
lean_inc(v_snd_758_);
lean_inc(v_fst_757_);
lean_inc(v_a_762_);
lean_inc_ref(v_fileMap_745_);
v___x_763_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_745_, v_hoverPos_746_, v_hoverFilePos_747_, v_a_762_, v_fst_757_, v_snd_758_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___y_767_; lean_object* v___x_777_; 
lean_dec(v_fst_757_);
v___x_764_ = lean_box(0);
v___x_765_ = l_Lean_Syntax_getTrailingSize(v_a_762_);
v___x_777_ = l_Lean_Syntax_getTailPos_x3f(v_a_762_, v___x_763_);
if (lean_obj_tag(v___x_777_) == 0)
{
v___y_767_ = v_snd_758_;
goto v___jp_766_;
}
else
{
lean_dec(v_snd_758_);
v___y_767_ = v___x_777_;
goto v___jp_766_;
}
v___jp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v___y_767_);
lean_ctor_set(v___x_760_, 0, v___x_765_);
v___x_769_ = v___x_760_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___y_767_);
v___x_769_ = v_reuseFailAlloc_776_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_771_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v___x_769_);
lean_ctor_set(v___x_755_, 0, v___x_764_);
v___x_771_ = v___x_755_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
size_t v___x_772_; size_t v___x_773_; 
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_add(v_i_750_, v___x_772_);
v_i_750_ = v___x_773_;
v_b_751_ = v___x_771_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
lean_dec_ref(v_fileMap_745_);
v___x_778_ = lean_box(v___x_763_);
v___x_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
if (v_isShared_761_ == 0)
{
v___x_781_ = v___x_760_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_fst_757_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_snd_758_);
v___x_781_ = v_reuseFailAlloc_785_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v___x_781_);
lean_ctor_set(v___x_755_, 0, v___x_779_);
v___x_783_ = v___x_755_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0___boxed(lean_object* v_fileMap_789_, lean_object* v_hoverPos_790_, lean_object* v_hoverFilePos_791_, lean_object* v_as_792_, lean_object* v_sz_793_, lean_object* v_i_794_, lean_object* v_b_795_){
_start:
{
size_t v_sz_boxed_796_; size_t v_i_boxed_797_; lean_object* v_res_798_; 
v_sz_boxed_796_ = lean_unbox_usize(v_sz_793_);
lean_dec(v_sz_793_);
v_i_boxed_797_ = lean_unbox_usize(v_i_794_);
lean_dec(v_i_794_);
v_res_798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_789_, v_hoverPos_790_, v_hoverFilePos_791_, v_as_792_, v_sz_boxed_796_, v_i_boxed_797_, v_b_795_);
lean_dec_ref(v_as_792_);
lean_dec_ref(v_hoverFilePos_791_);
lean_dec(v_hoverPos_790_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go___boxed(lean_object* v_fileMap_799_, lean_object* v_hoverPos_800_, lean_object* v_hoverFilePos_801_, lean_object* v_stx_802_, lean_object* v_leadingWs_803_, lean_object* v_leadingTokenTailPos_x3f_804_){
_start:
{
uint8_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_799_, v_hoverPos_800_, v_hoverFilePos_801_, v_stx_802_, v_leadingWs_803_, v_leadingTokenTailPos_x3f_804_);
lean_dec_ref(v_hoverFilePos_801_);
lean_dec(v_hoverPos_800_);
v_r_806_ = lean_box(v_res_805_);
return v_r_806_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(lean_object* v_fileMap_807_, lean_object* v_hoverPos_808_, lean_object* v_cmdStx_809_){
_start:
{
lean_object* v_hoverFilePos_810_; lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
lean_inc_ref(v_fileMap_807_);
v_hoverFilePos_810_ = l_Lean_FileMap_toPosition(v_fileMap_807_, v_hoverPos_808_);
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = lean_box(0);
v___x_813_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_807_, v_hoverPos_808_, v_hoverFilePos_810_, v_cmdStx_809_, v___x_811_, v___x_812_);
lean_dec_ref(v_hoverFilePos_810_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion___boxed(lean_object* v_fileMap_814_, lean_object* v_hoverPos_815_, lean_object* v_cmdStx_816_){
_start:
{
uint8_t v_res_817_; lean_object* v_r_818_; 
v_res_817_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_814_, v_hoverPos_815_, v_cmdStx_816_);
lean_dec(v_hoverPos_815_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(lean_object* v_as_824_, size_t v_sz_825_, size_t v_i_826_, lean_object* v_b_827_){
_start:
{
uint8_t v___x_828_; 
v___x_828_ = lean_usize_dec_lt(v_i_826_, v_sz_825_);
if (v___x_828_ == 0)
{
lean_inc_ref(v_b_827_);
return v_b_827_;
}
else
{
lean_object* v___x_829_; lean_object* v_a_830_; lean_object* v___x_831_; 
v___x_829_ = lean_box(0);
v_a_830_ = lean_array_uget_borrowed(v_as_824_, v_i_826_);
v___x_831_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_a_830_);
if (lean_obj_tag(v___x_831_) == 1)
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___x_829_);
return v___x_833_;
}
else
{
lean_object* v___x_834_; size_t v___x_835_; size_t v___x_836_; 
lean_dec(v___x_831_);
v___x_834_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v___x_835_ = ((size_t)1ULL);
v___x_836_ = lean_usize_add(v_i_826_, v___x_835_);
v_i_826_ = v___x_836_;
v_b_827_ = v___x_834_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(lean_object* v_as_838_, size_t v_sz_839_, size_t v_i_840_, lean_object* v_b_841_){
_start:
{
uint8_t v___x_842_; 
v___x_842_ = lean_usize_dec_lt(v_i_840_, v_sz_839_);
if (v___x_842_ == 0)
{
lean_inc_ref(v_b_841_);
return v_b_841_;
}
else
{
lean_object* v___x_843_; lean_object* v_a_844_; lean_object* v___x_845_; 
v___x_843_ = lean_box(0);
v_a_844_ = lean_array_uget_borrowed(v_as_838_, v_i_840_);
lean_inc(v_a_844_);
v___x_845_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_a_844_);
if (lean_obj_tag(v___x_845_) == 1)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v___x_843_);
return v___x_847_;
}
else
{
lean_object* v___x_848_; size_t v___x_849_; size_t v___x_850_; 
lean_dec(v___x_845_);
v___x_848_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v___x_849_ = ((size_t)1ULL);
v___x_850_ = lean_usize_add(v_i_840_, v___x_849_);
v_i_840_ = v___x_850_;
v_b_841_ = v___x_848_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(lean_object* v_x_852_){
_start:
{
if (lean_obj_tag(v_x_852_) == 0)
{
lean_object* v_cs_853_; lean_object* v___x_854_; lean_object* v___x_855_; size_t v_sz_856_; size_t v___x_857_; lean_object* v___x_858_; lean_object* v_fst_859_; 
v_cs_853_ = lean_ctor_get(v_x_852_, 0);
v___x_854_ = lean_box(0);
v___x_855_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_856_ = lean_array_size(v_cs_853_);
v___x_857_ = ((size_t)0ULL);
v___x_858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_cs_853_, v_sz_856_, v___x_857_, v___x_855_);
v_fst_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_fst_859_);
lean_dec_ref(v___x_858_);
if (lean_obj_tag(v_fst_859_) == 0)
{
return v___x_854_;
}
else
{
lean_object* v_val_860_; 
v_val_860_ = lean_ctor_get(v_fst_859_, 0);
lean_inc(v_val_860_);
lean_dec_ref_known(v_fst_859_, 1);
return v_val_860_;
}
}
else
{
lean_object* v_vs_861_; lean_object* v___x_862_; lean_object* v___x_863_; size_t v_sz_864_; size_t v___x_865_; lean_object* v___x_866_; lean_object* v_fst_867_; 
v_vs_861_ = lean_ctor_get(v_x_852_, 0);
v___x_862_ = lean_box(0);
v___x_863_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_864_ = lean_array_size(v_vs_861_);
v___x_865_ = ((size_t)0ULL);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_vs_861_, v_sz_864_, v___x_865_, v___x_863_);
v_fst_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_fst_867_);
lean_dec_ref(v___x_866_);
if (lean_obj_tag(v_fst_867_) == 0)
{
return v___x_862_;
}
else
{
lean_object* v_val_868_; 
v_val_868_ = lean_ctor_get(v_fst_867_, 0);
lean_inc(v_val_868_);
lean_dec_ref_known(v_fst_867_, 1);
return v_val_868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(lean_object* v_t_869_){
_start:
{
lean_object* v_root_870_; lean_object* v_tail_871_; lean_object* v___x_872_; 
v_root_870_ = lean_ctor_get(v_t_869_, 0);
v_tail_871_ = lean_ctor_get(v_t_869_, 1);
v___x_872_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_root_870_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v___x_873_; size_t v_sz_874_; size_t v___x_875_; lean_object* v___x_876_; lean_object* v_fst_877_; 
v___x_873_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_874_ = lean_array_size(v_tail_871_);
v___x_875_ = ((size_t)0ULL);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_tail_871_, v_sz_874_, v___x_875_, v___x_873_);
v_fst_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_fst_877_);
lean_dec_ref(v___x_876_);
if (lean_obj_tag(v_fst_877_) == 0)
{
return v___x_872_;
}
else
{
lean_object* v_val_878_; 
v_val_878_ = lean_ctor_get(v_fst_877_, 0);
lean_inc(v_val_878_);
lean_dec_ref_known(v_fst_877_, 1);
return v_val_878_;
}
}
else
{
return v___x_872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(lean_object* v_i_879_){
_start:
{
switch(lean_obj_tag(v_i_879_))
{
case 0:
{
lean_object* v_i_880_; 
v_i_880_ = lean_ctor_get(v_i_879_, 0);
lean_inc_ref(v_i_880_);
if (lean_obj_tag(v_i_880_) == 0)
{
lean_object* v_info_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref_known(v_i_879_, 2);
v_info_881_ = lean_ctor_get(v_i_880_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v_i_880_);
if (v_isSharedCheck_891_ == 0)
{
v___x_883_ = v_i_880_;
v_isShared_884_ = v_isSharedCheck_891_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_info_881_);
lean_dec(v_i_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_891_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_885_ = lean_box(0);
v___x_886_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go___closed__0));
v___x_887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_887_, 0, v_info_881_);
lean_ctor_set(v___x_887_, 1, v___x_885_);
lean_ctor_set(v___x_887_, 2, v___x_886_);
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 1);
lean_ctor_set(v___x_883_, 0, v___x_887_);
v___x_889_ = v___x_883_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
else
{
lean_object* v_t_892_; 
lean_dec_ref(v_i_880_);
v_t_892_ = lean_ctor_get(v_i_879_, 1);
lean_inc_ref(v_t_892_);
lean_dec_ref_known(v_i_879_, 2);
v_i_879_ = v_t_892_;
goto _start;
}
}
case 1:
{
lean_object* v_children_894_; lean_object* v___x_895_; 
v_children_894_ = lean_ctor_get(v_i_879_, 1);
lean_inc_ref(v_children_894_);
lean_dec_ref_known(v_i_879_, 2);
v___x_895_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(v_children_894_);
lean_dec_ref(v_children_894_);
return v___x_895_;
}
default: 
{
lean_object* v___x_896_; 
lean_dec_ref_known(v_i_879_, 1);
v___x_896_ = lean_box(0);
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___boxed(lean_object* v_t_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(v_t_897_);
lean_dec_ref(v_t_897_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1___boxed(lean_object* v_as_899_, lean_object* v_sz_900_, lean_object* v_i_901_, lean_object* v_b_902_){
_start:
{
size_t v_sz_boxed_903_; size_t v_i_boxed_904_; lean_object* v_res_905_; 
v_sz_boxed_903_ = lean_unbox_usize(v_sz_900_);
lean_dec(v_sz_900_);
v_i_boxed_904_ = lean_unbox_usize(v_i_901_);
lean_dec(v_i_901_);
v_res_905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_as_899_, v_sz_boxed_903_, v_i_boxed_904_, v_b_902_);
lean_dec_ref(v_b_902_);
lean_dec_ref(v_as_899_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1___boxed(lean_object* v_as_906_, lean_object* v_sz_907_, lean_object* v_i_908_, lean_object* v_b_909_){
_start:
{
size_t v_sz_boxed_910_; size_t v_i_boxed_911_; lean_object* v_res_912_; 
v_sz_boxed_910_ = lean_unbox_usize(v_sz_907_);
lean_dec(v_sz_907_);
v_i_boxed_911_ = lean_unbox_usize(v_i_908_);
lean_dec(v_i_908_);
v_res_912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_as_906_, v_sz_boxed_910_, v_i_boxed_911_, v_b_909_);
lean_dec_ref(v_b_909_);
lean_dec_ref(v_as_906_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0___boxed(lean_object* v_x_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_x_913_);
lean_dec_ref(v_x_913_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f(lean_object* v_i_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_i_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(lean_object* v_fileMap_919_, lean_object* v_hoverPos_920_, lean_object* v_cmdStx_921_, lean_object* v_infoTree_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_infoTree_922_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v___x_924_; 
lean_dec(v_cmdStx_921_);
lean_dec_ref(v_fileMap_919_);
v___x_924_ = lean_box(0);
return v___x_924_;
}
else
{
lean_object* v_val_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_938_; 
v_val_925_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_938_ == 0)
{
v___x_927_ = v___x_923_;
v_isShared_928_ = v_isSharedCheck_938_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_val_925_);
lean_dec(v___x_923_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_938_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
uint8_t v___x_929_; uint8_t v___x_930_; 
v___x_929_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_919_, v_hoverPos_920_, v_cmdStx_921_);
v___x_930_ = lean_bool_not(v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_931_ = lean_box(0);
v___x_932_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___closed__0));
v___x_933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v_val_925_);
lean_ctor_set(v___x_933_, 2, v___x_932_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_933_);
v___x_935_ = v___x_927_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
else
{
lean_object* v___x_937_; 
lean_del_object(v___x_927_);
lean_dec(v_val_925_);
v___x_937_ = lean_box(0);
return v___x_937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___boxed(lean_object* v_fileMap_939_, lean_object* v_hoverPos_940_, lean_object* v_cmdStx_941_, lean_object* v_infoTree_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(v_fileMap_939_, v_hoverPos_940_, v_cmdStx_941_, v_infoTree_942_);
lean_dec(v_hoverPos_940_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(lean_object* v_msg_944_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = l_Lean_instInhabitedExpr;
v___x_946_ = lean_panic_fn_borrowed(v___x_945_, v_msg_944_);
return v___x_946_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(lean_object* v_hoverPos_947_, lean_object* v_i_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_Elab_Info_pos_x3f(v_i_948_);
if (lean_obj_tag(v___x_949_) == 1)
{
lean_object* v_val_950_; lean_object* v___x_951_; 
v_val_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_val_950_);
lean_dec_ref_known(v___x_949_, 1);
v___x_951_ = l_Lean_Elab_Info_tailPos_x3f(v_i_948_);
if (lean_obj_tag(v___x_951_) == 1)
{
if (lean_obj_tag(v_i_948_) == 1)
{
lean_object* v_i_952_; lean_object* v_expectedType_x3f_953_; 
v_i_952_ = lean_ctor_get(v_i_948_, 0);
v_expectedType_x3f_953_ = lean_ctor_get(v_i_952_, 2);
if (lean_obj_tag(v_expectedType_x3f_953_) == 0)
{
uint8_t v___x_954_; 
lean_dec_ref_known(v___x_951_, 1);
lean_dec(v_val_950_);
v___x_954_ = 0;
return v___x_954_;
}
else
{
lean_object* v_val_955_; uint8_t v___x_956_; 
v_val_955_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_val_955_);
lean_dec_ref_known(v___x_951_, 1);
v___x_956_ = lean_nat_dec_le(v_val_950_, v_hoverPos_947_);
lean_dec(v_val_950_);
if (v___x_956_ == 0)
{
lean_dec(v_val_955_);
return v___x_956_;
}
else
{
uint8_t v___x_957_; 
v___x_957_ = lean_nat_dec_le(v_hoverPos_947_, v_val_955_);
lean_dec(v_val_955_);
return v___x_957_;
}
}
}
else
{
uint8_t v___x_958_; 
lean_dec_ref_known(v___x_951_, 1);
lean_dec(v_val_950_);
v___x_958_ = 0;
return v___x_958_;
}
}
else
{
uint8_t v___x_959_; 
lean_dec(v___x_951_);
lean_dec(v_val_950_);
v___x_959_ = 0;
return v___x_959_;
}
}
else
{
uint8_t v___x_960_; 
lean_dec(v___x_949_);
v___x_960_ = 0;
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed(lean_object* v_hoverPos_961_, lean_object* v_i_962_){
_start:
{
uint8_t v_res_963_; lean_object* v_r_964_; 
v_res_963_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(v_hoverPos_961_, v_i_962_);
lean_dec_ref(v_i_962_);
lean_dec(v_hoverPos_961_);
v_r_964_ = lean_box(v_res_963_);
return v_r_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt(lean_object* v_infoTree_965_, lean_object* v_hoverPos_966_){
_start:
{
lean_object* v___f_967_; lean_object* v___x_968_; 
v___f_967_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed), 2, 1);
lean_closure_set(v___f_967_, 0, v_hoverPos_966_);
v___x_968_ = l_Lean_Elab_InfoTree_smallestInfo_x3f(v___f_967_, v_infoTree_965_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v___x_969_; 
v___x_969_ = lean_box(0);
return v___x_969_;
}
else
{
lean_object* v_val_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_994_; 
v_val_970_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_994_ == 0)
{
v___x_972_ = v___x_968_;
v_isShared_973_ = v_isSharedCheck_994_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_val_970_);
lean_dec(v___x_968_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_994_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v_fst_974_; lean_object* v_snd_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_993_; 
v_fst_974_ = lean_ctor_get(v_val_970_, 0);
v_snd_975_ = lean_ctor_get(v_val_970_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v_val_970_);
if (v_isSharedCheck_993_ == 0)
{
v___x_977_ = v_val_970_;
v_isShared_978_ = v_isSharedCheck_993_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_snd_975_);
lean_inc(v_fst_974_);
lean_dec(v_val_970_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_993_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___y_980_; 
if (lean_obj_tag(v_snd_975_) == 1)
{
lean_object* v_i_987_; lean_object* v_expectedType_x3f_988_; 
v_i_987_ = lean_ctor_get(v_snd_975_, 0);
lean_inc_ref(v_i_987_);
lean_dec_ref_known(v_snd_975_, 1);
v_expectedType_x3f_988_ = lean_ctor_get(v_i_987_, 2);
lean_inc(v_expectedType_x3f_988_);
lean_dec_ref(v_i_987_);
if (lean_obj_tag(v_expectedType_x3f_988_) == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_obj_once(&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4, &l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_once, _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4);
v___x_990_ = l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(v___x_989_);
v___y_980_ = v___x_990_;
goto v___jp_979_;
}
else
{
lean_object* v_val_991_; 
v_val_991_ = lean_ctor_get(v_expectedType_x3f_988_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v_expectedType_x3f_988_, 1);
v___y_980_ = v_val_991_;
goto v___jp_979_;
}
}
else
{
lean_object* v___x_992_; 
lean_del_object(v___x_977_);
lean_dec(v_snd_975_);
lean_dec(v_fst_974_);
lean_del_object(v___x_972_);
v___x_992_ = lean_box(0);
return v___x_992_;
}
v___jp_979_:
{
lean_object* v___x_982_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 1, v___y_980_);
v___x_982_ = v___x_977_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_fst_974_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___y_980_);
v___x_982_ = v_reuseFailAlloc_986_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_984_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_982_);
v___x_984_ = v___x_972_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(lean_object* v_f_995_, lean_object* v_leadingToken_x3f_996_, lean_object* v_acc_997_, lean_object* v_stx_998_){
_start:
{
lean_object* v___f_999_; lean_object* v___f_1000_; lean_object* v___f_1001_; lean_object* v___f_1002_; lean_object* v___f_1003_; lean_object* v___f_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_acc_1009_; 
v___f_999_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0));
v___f_1000_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1));
v___f_1001_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2));
v___f_1002_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3));
v___f_1003_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4));
v___f_1004_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5));
v___f_1005_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6));
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___f_999_);
lean_ctor_set(v___x_1006_, 1, v___f_1000_);
v___x_1007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___f_1001_);
lean_ctor_set(v___x_1007_, 2, v___f_1002_);
lean_ctor_set(v___x_1007_, 3, v___f_1003_);
lean_ctor_set(v___x_1007_, 4, v___f_1004_);
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___f_1005_);
lean_inc(v_f_995_);
lean_inc(v_stx_998_);
lean_inc(v_leadingToken_x3f_996_);
v_acc_1009_ = lean_apply_3(v_f_995_, v_acc_997_, v_leadingToken_x3f_996_, v_stx_998_);
switch(lean_obj_tag(v_stx_998_))
{
case 0:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec_ref_known(v___x_1008_, 2);
lean_dec(v_leadingToken_x3f_996_);
lean_dec(v_f_995_);
v___x_1010_ = lean_box(0);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v_acc_1009_);
return v___x_1011_;
}
case 1:
{
lean_object* v_args_1012_; lean_object* v___f_1013_; lean_object* v_lastToken_x3f_1014_; lean_object* v___x_1015_; size_t v_sz_1016_; size_t v___x_1017_; lean_object* v___x_1018_; lean_object* v_fst_1019_; lean_object* v_snd_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
v_args_1012_ = lean_ctor_get(v_stx_998_, 2);
lean_inc_ref(v_args_1012_);
lean_dec_ref_known(v_stx_998_, 3);
v___f_1013_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1013_, 0, v_f_995_);
lean_closure_set(v___f_1013_, 1, v_leadingToken_x3f_996_);
v_lastToken_x3f_1014_ = lean_box(0);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_acc_1009_);
lean_ctor_set(v___x_1015_, 1, v_lastToken_x3f_1014_);
v_sz_1016_ = lean_array_size(v_args_1012_);
v___x_1017_ = ((size_t)0ULL);
v___x_1018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1008_, v_args_1012_, v___f_1013_, v_sz_1016_, v___x_1017_, v___x_1015_);
v_fst_1019_ = lean_ctor_get(v___x_1018_, 0);
v_snd_1020_ = lean_ctor_get(v___x_1018_, 1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1018_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_snd_1020_);
lean_inc(v_fst_1019_);
lean_dec(v___x_1018_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 1, v_fst_1019_);
lean_ctor_set(v___x_1022_, 0, v_snd_1020_);
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_snd_1020_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_fst_1019_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
default: 
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec_ref_known(v___x_1008_, 2);
lean_dec(v_leadingToken_x3f_996_);
lean_dec(v_f_995_);
v___x_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1028_, 0, v_stx_998_);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v_acc_1009_);
return v___x_1029_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0(lean_object* v_f_1030_, lean_object* v_leadingToken_x3f_1031_, lean_object* v_a_1032_, lean_object* v_x_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v_fst_1040_; lean_object* v_snd_1041_; lean_object* v___y_1043_; 
v_fst_1040_ = lean_ctor_get(v___y_1034_, 0);
lean_inc(v_fst_1040_);
v_snd_1041_ = lean_ctor_get(v___y_1034_, 1);
lean_inc(v_snd_1041_);
lean_dec_ref(v___y_1034_);
if (lean_obj_tag(v_snd_1041_) == 0)
{
v___y_1043_ = v_leadingToken_x3f_1031_;
goto v___jp_1042_;
}
else
{
lean_dec(v_leadingToken_x3f_1031_);
lean_inc_ref(v_snd_1041_);
v___y_1043_ = v_snd_1041_;
goto v___jp_1042_;
}
v___jp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___y_1036_);
lean_ctor_set(v___x_1038_, 1, v___y_1037_);
v___x_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
v___jp_1042_:
{
lean_object* v___x_1044_; lean_object* v_fst_1045_; 
v___x_1044_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1030_, v___y_1043_, v_fst_1040_, v_a_1032_);
v_fst_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_fst_1045_);
if (lean_obj_tag(v_fst_1045_) == 0)
{
lean_object* v_snd_1046_; 
v_snd_1046_ = lean_ctor_get(v___x_1044_, 1);
lean_inc(v_snd_1046_);
lean_dec_ref(v___x_1044_);
v___y_1036_ = v_snd_1046_;
v___y_1037_ = v_snd_1041_;
goto v___jp_1035_;
}
else
{
lean_object* v_snd_1047_; 
lean_dec(v_snd_1041_);
v_snd_1047_ = lean_ctor_get(v___x_1044_, 1);
lean_inc(v_snd_1047_);
lean_dec_ref(v___x_1044_);
v___y_1036_ = v_snd_1047_;
v___y_1037_ = v_fst_1045_;
goto v___jp_1035_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(lean_object* v_00_u03b1_1048_, lean_object* v_f_1049_, lean_object* v_inst_1050_, lean_object* v_leadingToken_x3f_1051_, lean_object* v_acc_1052_, lean_object* v_stx_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1049_, v_leadingToken_x3f_1051_, v_acc_1052_, v_stx_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___boxed(lean_object* v_00_u03b1_1055_, lean_object* v_f_1056_, lean_object* v_inst_1057_, lean_object* v_leadingToken_x3f_1058_, lean_object* v_acc_1059_, lean_object* v_stx_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(v_00_u03b1_1055_, v_f_1056_, v_inst_1057_, v_leadingToken_x3f_1058_, v_acc_1059_, v_stx_1060_);
lean_dec(v_inst_1057_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(lean_object* v_f_1062_, lean_object* v_init_1063_, lean_object* v_stx_1064_){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v_snd_1067_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1062_, v___x_1065_, v_init_1063_, v_stx_1064_);
v_snd_1067_ = lean_ctor_get(v___x_1066_, 1);
lean_inc(v_snd_1067_);
lean_dec_ref(v___x_1066_);
return v_snd_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(lean_object* v_00_u03b1_1068_, lean_object* v_inst_1069_, lean_object* v_f_1070_, lean_object* v_init_1071_, lean_object* v_stx_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(v_f_1070_, v_init_1071_, v_stx_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___boxed(lean_object* v_00_u03b1_1074_, lean_object* v_inst_1075_, lean_object* v_f_1076_, lean_object* v_init_1077_, lean_object* v_stx_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(v_00_u03b1_1074_, v_inst_1075_, v_f_1076_, v_init_1077_, v_stx_1078_);
lean_dec(v_inst_1075_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(lean_object* v_p_1080_, lean_object* v_foundStx_x3f_1081_, lean_object* v_leadingToken_x3f_1082_, lean_object* v_stx_1083_){
_start:
{
if (lean_obj_tag(v_foundStx_x3f_1081_) == 0)
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
lean_inc(v_stx_1083_);
v___x_1084_ = lean_apply_2(v_p_1080_, v_leadingToken_x3f_1082_, v_stx_1083_);
v___x_1085_ = lean_unbox(v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec(v_stx_1083_);
return v_foundStx_x3f_1081_;
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_stx_1083_);
return v___x_1086_;
}
}
else
{
lean_dec(v_stx_1083_);
lean_dec(v_leadingToken_x3f_1082_);
lean_dec_ref(v_p_1080_);
lean_inc_ref(v_foundStx_x3f_1081_);
return v_foundStx_x3f_1081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed(lean_object* v_p_1087_, lean_object* v_foundStx_x3f_1088_, lean_object* v_leadingToken_x3f_1089_, lean_object* v_stx_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(v_p_1087_, v_foundStx_x3f_1088_, v_leadingToken_x3f_1089_, v_stx_1090_);
lean_dec(v_foundStx_x3f_1088_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f(lean_object* v_p_1092_, lean_object* v_stx_1093_){
_start:
{
lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___f_1094_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1094_, 0, v_p_1092_);
v___x_1095_ = lean_box(0);
v___x_1096_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(v___f_1094_, v___x_1095_, v_stx_1093_);
return v___x_1096_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(lean_object* v_hoverPos_1097_, uint8_t v___y_1098_, lean_object* v_as_1099_, size_t v_i_1100_, size_t v_stop_1101_){
_start:
{
uint8_t v___x_1102_; 
v___x_1102_ = lean_usize_dec_eq(v_i_1100_, v_stop_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v_fst_1104_; lean_object* v_snd_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; uint8_t v___y_1109_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1103_ = lean_array_uget_borrowed(v_as_1099_, v_i_1100_);
v_fst_1104_ = lean_ctor_get(v___x_1103_, 0);
v_snd_1105_ = lean_ctor_get(v___x_1103_, 1);
v___x_1106_ = lean_unsigned_to_nat(0u);
v___x_1107_ = 1;
v___x_1113_ = lean_unsigned_to_nat(2u);
v___x_1114_ = lean_nat_mod(v_snd_1105_, v___x_1113_);
v___x_1115_ = lean_nat_dec_eq(v___x_1114_, v___x_1106_);
lean_dec(v___x_1114_);
if (v___x_1115_ == 0)
{
uint8_t v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = l_Lean_Syntax_isAtom(v_fst_1104_);
v___x_1117_ = lean_bool_not(v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_Syntax_getTailPos_x3f(v_fst_1104_, v___x_1117_);
if (lean_obj_tag(v___x_1118_) == 1)
{
lean_object* v_val_1119_; uint8_t v___x_1120_; 
v_val_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_val_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v___x_1120_ = lean_nat_dec_le(v_val_1119_, v_hoverPos_1097_);
if (v___x_1120_ == 0)
{
lean_dec(v_val_1119_);
v___y_1109_ = v___x_1120_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1121_ = l_Lean_Syntax_getTrailingSize(v_fst_1104_);
v___x_1122_ = lean_nat_add(v_val_1119_, v___x_1121_);
lean_dec(v___x_1121_);
lean_dec(v_val_1119_);
v___x_1123_ = lean_nat_dec_le(v_hoverPos_1097_, v___x_1122_);
lean_dec(v___x_1122_);
v___y_1109_ = v___x_1123_;
goto v___jp_1108_;
}
}
else
{
lean_dec(v___x_1118_);
v___y_1109_ = v___x_1117_;
goto v___jp_1108_;
}
}
else
{
v___y_1109_ = v___y_1098_;
goto v___jp_1108_;
}
}
else
{
v___y_1109_ = v___y_1098_;
goto v___jp_1108_;
}
v___jp_1108_:
{
if (v___y_1109_ == 0)
{
size_t v___x_1110_; size_t v___x_1111_; 
v___x_1110_ = ((size_t)1ULL);
v___x_1111_ = lean_usize_add(v_i_1100_, v___x_1110_);
v_i_1100_ = v___x_1111_;
goto _start;
}
else
{
return v___x_1107_;
}
}
}
else
{
uint8_t v___x_1124_; 
v___x_1124_ = 0;
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0___boxed(lean_object* v_hoverPos_1125_, lean_object* v___y_1126_, lean_object* v_as_1127_, lean_object* v_i_1128_, lean_object* v_stop_1129_){
_start:
{
uint8_t v___y_2010__boxed_1130_; size_t v_i_boxed_1131_; size_t v_stop_boxed_1132_; uint8_t v_res_1133_; lean_object* v_r_1134_; 
v___y_2010__boxed_1130_ = lean_unbox(v___y_1126_);
v_i_boxed_1131_ = lean_unbox_usize(v_i_1128_);
lean_dec(v_i_1128_);
v_stop_boxed_1132_ = lean_unbox_usize(v_stop_1129_);
lean_dec(v_stop_1129_);
v_res_1133_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(v_hoverPos_1125_, v___y_2010__boxed_1130_, v_as_1127_, v_i_boxed_1131_, v_stop_boxed_1132_);
lean_dec_ref(v_as_1127_);
lean_dec(v_hoverPos_1125_);
v_r_1134_ = lean_box(v_res_1133_);
return v_r_1134_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(uint8_t v___x_1141_, uint8_t v_isCursorInProperWhitespace_1142_, lean_object* v_fileMap_1143_, lean_object* v_hoverFilePos_1144_, lean_object* v_hoverPos_1145_, uint8_t v___x_1146_, lean_object* v_leadingToken_x3f_1147_, lean_object* v_stx_1148_){
_start:
{
uint8_t v___y_1150_; 
if (lean_obj_tag(v_leadingToken_x3f_1147_) == 1)
{
lean_object* v_val_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; uint8_t v___x_1162_; 
v_val_1158_ = lean_ctor_get(v_leadingToken_x3f_1147_, 0);
lean_inc(v_stx_1148_);
v___x_1159_ = l_Lean_Syntax_getKind(v_stx_1148_);
v___x_1160_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1));
v___x_1161_ = lean_name_eq(v___x_1159_, v___x_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_bool_not(v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_Syntax_getTailPos_x3f(v_val_1158_, v___x_1141_);
if (lean_obj_tag(v___x_1163_) == 1)
{
lean_object* v_val_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_fieldsAndSeps_1167_; uint8_t v___y_1169_; lean_object* v___y_1177_; lean_object* v___x_1183_; 
v_val_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_val_1164_);
lean_dec_ref_known(v___x_1163_, 1);
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = l_Lean_Syntax_getArg(v_stx_1148_, v___x_1165_);
v_fieldsAndSeps_1167_ = l_Lean_Syntax_getArgs(v___x_1166_);
lean_dec(v___x_1166_);
v___x_1183_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1148_, v___x_1141_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_val_1158_, v___x_1141_);
v___y_1177_ = v___x_1184_;
goto v___jp_1176_;
}
else
{
v___y_1177_ = v___x_1183_;
goto v___jp_1176_;
}
v___jp_1168_:
{
if (v___y_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1170_ = l_Array_zipIdx___redArg(v_fieldsAndSeps_1167_, v___x_1165_);
v___x_1171_ = lean_array_get_size(v___x_1170_);
v___x_1172_ = lean_nat_dec_lt(v___x_1165_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_dec_ref(v___x_1170_);
v___y_1150_ = v___y_1169_;
goto v___jp_1149_;
}
else
{
if (v___x_1172_ == 0)
{
lean_dec_ref(v___x_1170_);
v___y_1150_ = v___y_1169_;
goto v___jp_1149_;
}
else
{
size_t v___x_1173_; size_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1173_ = ((size_t)0ULL);
v___x_1174_ = lean_usize_of_nat(v___x_1171_);
v___x_1175_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(v_hoverPos_1145_, v___y_1169_, v___x_1170_, v___x_1173_, v___x_1174_);
lean_dec_ref(v___x_1170_);
if (v___x_1175_ == 0)
{
v___y_1150_ = v___x_1175_;
goto v___jp_1149_;
}
else
{
lean_dec(v_stx_1148_);
lean_dec_ref(v_fileMap_1143_);
return v___x_1141_;
}
}
}
}
else
{
lean_dec_ref(v_fieldsAndSeps_1167_);
lean_dec(v_stx_1148_);
lean_dec_ref(v_fileMap_1143_);
return v___x_1141_;
}
}
v___jp_1176_:
{
if (lean_obj_tag(v___y_1177_) == 1)
{
lean_object* v_val_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v_val_1178_ = lean_ctor_get(v___y_1177_, 0);
lean_inc(v_val_1178_);
lean_dec_ref_known(v___y_1177_, 1);
v___x_1179_ = lean_array_get_size(v_fieldsAndSeps_1167_);
v___x_1180_ = lean_nat_dec_eq(v___x_1179_, v___x_1165_);
if (v___x_1180_ == 0)
{
lean_dec(v_val_1178_);
lean_dec(v_val_1164_);
v___y_1169_ = v___x_1180_;
goto v___jp_1168_;
}
else
{
lean_object* v_outerBounds_1181_; uint8_t v___x_1182_; 
v_outerBounds_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_outerBounds_1181_, 0, v_val_1164_);
lean_ctor_set(v_outerBounds_1181_, 1, v_val_1178_);
v___x_1182_ = l_Lean_Syntax_Range_contains(v_outerBounds_1181_, v_hoverPos_1145_, v___x_1141_);
lean_dec_ref_known(v_outerBounds_1181_, 2);
v___y_1169_ = v___x_1182_;
goto v___jp_1168_;
}
}
else
{
lean_dec(v___y_1177_);
lean_dec_ref(v_fieldsAndSeps_1167_);
lean_dec(v_val_1164_);
lean_dec(v_stx_1148_);
lean_dec_ref(v_fileMap_1143_);
return v___x_1162_;
}
}
}
else
{
lean_dec(v___x_1163_);
lean_dec(v_stx_1148_);
lean_dec_ref(v_fileMap_1143_);
return v___x_1162_;
}
}
else
{
lean_dec(v_stx_1148_);
lean_dec_ref(v_fileMap_1143_);
return v___x_1146_;
}
}
else
{
lean_dec(v_stx_1148_);
lean_dec_ref(v_fileMap_1143_);
return v___x_1146_;
}
v___jp_1149_:
{
uint8_t v___x_1151_; 
v___x_1151_ = lean_bool_not(v_isCursorInProperWhitespace_1142_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_Syntax_getPos_x3f(v_stx_1148_, v___x_1151_);
lean_dec(v_stx_1148_);
if (lean_obj_tag(v___x_1152_) == 1)
{
lean_object* v_val_1153_; lean_object* v___x_1154_; lean_object* v_column_1155_; lean_object* v_column_1156_; uint8_t v_isCursorInBlock_1157_; 
v_val_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_val_1153_);
lean_dec_ref_known(v___x_1152_, 1);
v___x_1154_ = l_Lean_FileMap_toPosition(v_fileMap_1143_, v_val_1153_);
lean_dec(v_val_1153_);
v_column_1155_ = lean_ctor_get(v___x_1154_, 1);
lean_inc(v_column_1155_);
lean_dec_ref(v___x_1154_);
v_column_1156_ = lean_ctor_get(v_hoverFilePos_1144_, 1);
v_isCursorInBlock_1157_ = lean_nat_dec_eq(v_column_1156_, v_column_1155_);
lean_dec(v_column_1155_);
return v_isCursorInBlock_1157_;
}
else
{
lean_dec(v___x_1152_);
lean_dec_ref(v_fileMap_1143_);
return v___x_1151_;
}
}
else
{
lean_dec(v_stx_1148_);
lean_dec_ref(v_fileMap_1143_);
return v___y_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___boxed(lean_object* v___x_1185_, lean_object* v_isCursorInProperWhitespace_1186_, lean_object* v_fileMap_1187_, lean_object* v_hoverFilePos_1188_, lean_object* v_hoverPos_1189_, lean_object* v___x_1190_, lean_object* v_leadingToken_x3f_1191_, lean_object* v_stx_1192_){
_start:
{
uint8_t v___x_2074__boxed_1193_; uint8_t v_isCursorInProperWhitespace_boxed_1194_; uint8_t v___x_2075__boxed_1195_; uint8_t v_res_1196_; lean_object* v_r_1197_; 
v___x_2074__boxed_1193_ = lean_unbox(v___x_1185_);
v_isCursorInProperWhitespace_boxed_1194_ = lean_unbox(v_isCursorInProperWhitespace_1186_);
v___x_2075__boxed_1195_ = lean_unbox(v___x_1190_);
v_res_1196_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(v___x_2074__boxed_1193_, v_isCursorInProperWhitespace_boxed_1194_, v_fileMap_1187_, v_hoverFilePos_1188_, v_hoverPos_1189_, v___x_2075__boxed_1195_, v_leadingToken_x3f_1191_, v_stx_1192_);
lean_dec(v_leadingToken_x3f_1191_);
lean_dec(v_hoverPos_1189_);
lean_dec_ref(v_hoverFilePos_1188_);
v_r_1197_ = lean_box(v_res_1196_);
return v_r_1197_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(lean_object* v_fileMap_1198_, lean_object* v_hoverPos_1199_, lean_object* v_cmdStx_1200_){
_start:
{
uint8_t v_isCursorOnWhitespace_1201_; uint8_t v___x_1202_; 
v_isCursorOnWhitespace_1201_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_1198_, v_hoverPos_1199_);
v___x_1202_ = lean_bool_not(v_isCursorOnWhitespace_1201_);
if (v___x_1202_ == 0)
{
uint8_t v_isCursorInProperWhitespace_1203_; uint8_t v___x_1204_; lean_object* v_hoverFilePos_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___f_1209_; lean_object* v___x_1210_; 
v_isCursorInProperWhitespace_1203_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_1198_, v_hoverPos_1199_);
v___x_1204_ = 1;
lean_inc_ref(v_fileMap_1198_);
v_hoverFilePos_1205_ = l_Lean_FileMap_toPosition(v_fileMap_1198_, v_hoverPos_1199_);
v___x_1206_ = lean_box(v___x_1204_);
v___x_1207_ = lean_box(v_isCursorInProperWhitespace_1203_);
v___x_1208_ = lean_box(v___x_1202_);
v___f_1209_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___boxed), 8, 6);
lean_closure_set(v___f_1209_, 0, v___x_1206_);
lean_closure_set(v___f_1209_, 1, v___x_1207_);
lean_closure_set(v___f_1209_, 2, v_fileMap_1198_);
lean_closure_set(v___f_1209_, 3, v_hoverFilePos_1205_);
lean_closure_set(v___f_1209_, 4, v_hoverPos_1199_);
lean_closure_set(v___f_1209_, 5, v___x_1208_);
v___x_1210_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f(v___f_1209_, v_cmdStx_1200_);
if (lean_obj_tag(v___x_1210_) == 0)
{
return v___x_1202_;
}
else
{
lean_dec_ref_known(v___x_1210_, 1);
return v___x_1204_;
}
}
else
{
uint8_t v___x_1211_; 
lean_dec(v_cmdStx_1200_);
lean_dec(v_hoverPos_1199_);
lean_dec_ref(v_fileMap_1198_);
v___x_1211_ = 0;
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___boxed(lean_object* v_fileMap_1212_, lean_object* v_hoverPos_1213_, lean_object* v_cmdStx_1214_){
_start:
{
uint8_t v_res_1215_; lean_object* v_r_1216_; 
v_res_1215_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(v_fileMap_1212_, v_hoverPos_1213_, v_cmdStx_1214_);
v_r_1216_ = lean_box(v_res_1215_);
return v_r_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticFieldCompletion_x3f(lean_object* v_fileMap_1217_, lean_object* v_hoverPos_1218_, lean_object* v_cmdStx_1219_, lean_object* v_infoTree_1220_){
_start:
{
uint8_t v___x_1221_; uint8_t v___x_1222_; 
lean_inc(v_hoverPos_1218_);
v___x_1221_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(v_fileMap_1217_, v_hoverPos_1218_, v_cmdStx_1219_);
v___x_1222_ = lean_bool_not(v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
v___x_1223_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt(v_infoTree_1220_, v_hoverPos_1218_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_box(0);
return v___x_1224_;
}
else
{
lean_object* v_val_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1248_; 
v_val_1225_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1227_ = v___x_1223_;
v_isShared_1228_ = v_isSharedCheck_1248_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_val_1225_);
lean_dec(v___x_1223_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1248_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v_fst_1229_; lean_object* v_snd_1230_; lean_object* v___x_1231_; 
v_fst_1229_ = lean_ctor_get(v_val_1225_, 0);
lean_inc(v_fst_1229_);
v_snd_1230_ = lean_ctor_get(v_val_1225_, 1);
lean_inc(v_snd_1230_);
lean_dec(v_val_1225_);
v___x_1231_ = l_Lean_Expr_getAppFn(v_snd_1230_);
lean_dec(v_snd_1230_);
if (lean_obj_tag(v___x_1231_) == 4)
{
lean_object* v_toCommandContextInfo_1232_; lean_object* v_declName_1233_; lean_object* v_env_1234_; uint8_t v___x_1235_; uint8_t v___x_1236_; 
v_toCommandContextInfo_1232_ = lean_ctor_get(v_fst_1229_, 0);
v_declName_1233_ = lean_ctor_get(v___x_1231_, 0);
lean_inc_n(v_declName_1233_, 2);
lean_dec_ref_known(v___x_1231_, 2);
v_env_1234_ = lean_ctor_get(v_toCommandContextInfo_1232_, 0);
lean_inc_ref(v_env_1234_);
v___x_1235_ = l_Lean_isStructure(v_env_1234_, v_declName_1233_);
v___x_1236_ = lean_bool_not(v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_box(0);
v___x_1239_ = lean_box(0);
v___x_1240_ = l_Lean_LocalContext_empty;
v___x_1241_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1238_);
lean_ctor_set(v___x_1241_, 1, v___x_1239_);
lean_ctor_set(v___x_1241_, 2, v___x_1240_);
lean_ctor_set(v___x_1241_, 3, v_declName_1233_);
v___x_1242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1237_);
lean_ctor_set(v___x_1242_, 1, v_fst_1229_);
lean_ctor_set(v___x_1242_, 2, v___x_1241_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1242_);
v___x_1244_ = v___x_1227_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
else
{
lean_object* v___x_1246_; 
lean_dec(v_declName_1233_);
lean_dec(v_fst_1229_);
lean_del_object(v___x_1227_);
v___x_1246_ = lean_box(0);
return v___x_1246_;
}
}
else
{
lean_object* v___x_1247_; 
lean_dec_ref(v___x_1231_);
lean_dec(v_fst_1229_);
lean_del_object(v___x_1227_);
v___x_1247_ = lean_box(0);
return v___x_1247_;
}
}
}
}
else
{
lean_object* v___x_1249_; 
lean_dec_ref(v_infoTree_1220_);
lean_dec(v_hoverPos_1218_);
v___x_1249_ = lean_box(0);
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findSyntheticCompletions(lean_object* v_fileMap_1252_, lean_object* v_hoverPos_1253_, lean_object* v_cmdStx_1254_, lean_object* v_infoTree_1255_){
_start:
{
lean_object* v___y_1257_; lean_object* v___x_1263_; 
lean_inc_ref(v_infoTree_1255_);
lean_inc(v_cmdStx_1254_);
lean_inc_ref(v_fileMap_1252_);
v___x_1263_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(v_fileMap_1252_, v_hoverPos_1253_, v_cmdStx_1254_, v_infoTree_1255_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v___x_1264_; 
lean_inc_ref(v_infoTree_1255_);
lean_inc(v_hoverPos_1253_);
v___x_1264_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticFieldCompletion_x3f(v_fileMap_1252_, v_hoverPos_1253_, v_cmdStx_1254_, v_infoTree_1255_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v___x_1265_; 
v___x_1265_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(v_hoverPos_1253_, v_infoTree_1255_);
v___y_1257_ = v___x_1265_;
goto v___jp_1256_;
}
else
{
lean_dec_ref(v_infoTree_1255_);
lean_dec(v_hoverPos_1253_);
v___y_1257_ = v___x_1264_;
goto v___jp_1256_;
}
}
else
{
lean_dec_ref(v_infoTree_1255_);
lean_dec(v_cmdStx_1254_);
lean_dec(v_hoverPos_1253_);
lean_dec_ref(v_fileMap_1252_);
v___y_1257_ = v___x_1263_;
goto v___jp_1256_;
}
v___jp_1256_:
{
if (lean_obj_tag(v___y_1257_) == 0)
{
lean_object* v___x_1258_; 
v___x_1258_ = ((lean_object*)(l_Lean_Server_Completion_findSyntheticCompletions___closed__0));
return v___x_1258_;
}
else
{
lean_object* v_val_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_val_1259_ = lean_ctor_get(v___y_1257_, 0);
lean_inc(v_val_1259_);
lean_dec_ref_known(v___y_1257_, 1);
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_mk_empty_array_with_capacity(v___x_1260_);
v___x_1262_ = lean_array_push(v___x_1261_, v_val_1259_);
return v___x_1262_;
}
}
}
}
lean_object* runtime_initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Completion_CompletionUtils(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion_SyntheticCompletion(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_InfoUtils(builtin);
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
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* initialize_Lean_Server_Completion_CompletionUtils(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_SyntheticCompletion(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_InfoUtils(builtin);
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
