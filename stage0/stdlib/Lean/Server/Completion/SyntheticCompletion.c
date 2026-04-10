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
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTrailingSize(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_List_dropWhile___redArg(lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__2_value;
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__3_value;
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__4_value;
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "completion"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__5_value;
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(231, 49, 5, 252, 150, 235, 247, 237)}};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__6_value;
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___boxed(lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0_value;
static const lean_closure_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1_value;
static const lean_closure_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__5 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__5_value;
static lean_once_cell_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeqBracketed"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__3 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
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
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty___boxed(lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
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
lean_dec_ref(v_a_2_);
lean_dec_ref(v_gt_1_);
v___x_5_ = 1;
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v_val_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v_val_6_ = lean_ctor_get(v_a_2_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v_a_2_);
v_val_7_ = lean_ctor_get(v_b_3_, 0);
lean_inc(v_val_7_);
lean_dec_ref(v_b_3_);
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
lean_dec_ref(v_head_29_);
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
lean_dec_ref(v_x_45_);
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
lean_dec_ref(v___x_61_);
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
lean_dec_ref(v_x_122_);
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
lean_dec_ref(v_x_122_);
lean_dec(v_postNode_120_);
lean_dec_ref(v_preNode_119_);
v___x_127_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3);
v___x_128_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(v___x_127_);
return v___x_128_;
}
else
{
lean_object* v_i_129_; lean_object* v_children_130_; lean_object* v_val_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_i_129_ = lean_ctor_get(v_x_122_, 0);
lean_inc_ref_n(v_i_129_, 2);
v_children_130_ = lean_ctor_get(v_x_122_, 1);
lean_inc_ref_n(v_children_130_, 2);
lean_dec_ref(v_x_122_);
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
v___x_147_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(v_preNode_119_, v_postNode_120_, v___x_144_, v___x_145_, v___x_146_);
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
lean_dec_ref(v_x_122_);
lean_dec(v_x_121_);
lean_dec(v_postNode_120_);
lean_dec_ref(v_preNode_119_);
v___x_150_ = lean_box(0);
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(lean_object* v_preNode_151_, lean_object* v_postNode_152_, lean_object* v___x_153_, lean_object* v_x_154_, lean_object* v_x_155_){
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
v___x_162_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v_preNode_151_, v_postNode_152_, v___x_153_, v_head_157_);
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
v___x_175_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v___f_172_, v___x_173_, v___x_174_, v_infoTree_169_);
if (lean_obj_tag(v___x_175_) == 0)
{
return v___x_174_;
}
else
{
lean_object* v_val_176_; 
v_val_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_176_);
lean_dec_ref(v___x_175_);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0(lean_object* v_00_u03b1_182_, lean_object* v_msg_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(v_msg_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0(lean_object* v_00_u03b1_185_, lean_object* v_preNode_186_, lean_object* v_postNode_187_, lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v_preNode_186_, v_postNode_187_, v_x_188_, v_x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1(lean_object* v_00_u03b1_191_, lean_object* v_preNode_192_, lean_object* v_postNode_193_, lean_object* v___x_194_, lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(v_preNode_192_, v_postNode_193_, v___x_194_, v_x_195_, v_x_196_);
return v___x_197_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter(lean_object* v_a_198_, lean_object* v_b_199_){
_start:
{
lean_object* v_snd_200_; lean_object* v_snd_201_; uint8_t v___y_203_; uint8_t v___y_207_; uint8_t v___y_208_; uint8_t v___y_209_; lean_object* v___x_210_; uint8_t v___x_211_; uint8_t v___y_213_; 
v_snd_200_ = lean_ctor_get(v_a_198_, 1);
v_snd_201_ = lean_ctor_get(v_b_199_, 1);
v___x_210_ = l_Lean_Elab_Info_lctx(v_snd_200_);
v___x_211_ = lean_local_ctx_is_empty(v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = l_Lean_Elab_Info_lctx(v_snd_201_);
v___x_218_ = lean_local_ctx_is_empty(v___x_217_);
if (v___x_218_ == 0)
{
v___y_213_ = v___x_218_;
goto v___jp_212_;
}
else
{
return v___x_218_;
}
}
else
{
uint8_t v___x_219_; 
v___x_219_ = 0;
v___y_213_ = v___x_219_;
goto v___jp_212_;
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
v___jp_206_:
{
if (v___y_209_ == 0)
{
v___y_203_ = v___y_207_;
goto v___jp_202_;
}
else
{
return v___y_208_;
}
}
v___jp_212_:
{
uint8_t v___x_214_; 
v___x_214_ = 1;
if (v___x_211_ == 0)
{
v___y_207_ = v___x_214_;
v___y_208_ = v___y_213_;
v___y_209_ = v___x_211_;
goto v___jp_206_;
}
else
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = l_Lean_Elab_Info_lctx(v_snd_201_);
v___x_216_ = lean_local_ctx_is_empty(v___x_215_);
if (v___x_216_ == 0)
{
v___y_207_ = v___x_214_;
v___y_208_ = v___y_213_;
v___y_209_ = v___x_211_;
goto v___jp_206_;
}
else
{
v___y_203_ = v___x_214_;
goto v___jp_202_;
}
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(lean_object* v_msg_243_){
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
lean_dec_ref(v___x_249_);
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
uint8_t v___x_258_; 
v___x_258_ = l_Lean_Syntax_hasArgs(v_stx_257_);
if (v___x_258_ == 0)
{
uint8_t v___x_259_; 
v___x_259_ = 1;
return v___x_259_;
}
else
{
uint8_t v___x_260_; 
v___x_260_ = 0;
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1___boxed(lean_object* v_stx_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1(v_stx_261_);
lean_dec(v_stx_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2(lean_object* v_x_276_){
_start:
{
lean_object* v_fst_277_; lean_object* v___x_278_; uint8_t v___x_279_; uint8_t v___y_281_; 
v_fst_277_ = lean_ctor_get(v_x_276_, 0);
lean_inc_n(v_fst_277_, 2);
lean_dec_ref(v_x_276_);
v___x_278_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__1));
v___x_279_ = l_Lean_Syntax_isOfKind(v_fst_277_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__6));
lean_inc(v_fst_277_);
v___x_284_ = l_Lean_Syntax_isOfKind(v_fst_277_, v___x_283_);
if (v___x_284_ == 0)
{
lean_dec(v_fst_277_);
v___y_281_ = v___x_279_;
goto v___jp_280_;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = l_Lean_Syntax_getArg(v_fst_277_, v___x_285_);
lean_dec(v_fst_277_);
v___x_287_ = l_Lean_Syntax_isOfKind(v___x_286_, v___x_278_);
if (v___x_287_ == 0)
{
v___y_281_ = v___x_287_;
goto v___jp_280_;
}
else
{
return v___x_279_;
}
}
}
else
{
uint8_t v___x_288_; 
lean_dec(v_fst_277_);
v___x_288_ = 0;
return v___x_288_;
}
v___jp_280_:
{
if (v___y_281_ == 0)
{
uint8_t v___x_282_; 
v___x_282_ = 1;
return v___x_282_;
}
else
{
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___boxed(lean_object* v_x_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2(v_x_289_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3(lean_object* v_x_298_){
_start:
{
lean_object* v_fst_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_fst_299_ = lean_ctor_get(v_x_298_, 0);
lean_inc_n(v_fst_299_, 2);
lean_dec_ref(v_x_298_);
v___x_300_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___closed__1));
v___x_301_ = l_Lean_Syntax_isOfKind(v_fst_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_dec(v_fst_299_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = l_Lean_Syntax_getArg(v_fst_299_, v___x_302_);
lean_dec(v_fst_299_);
v___x_304_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__1));
v___x_305_ = l_Lean_Syntax_isOfKind(v___x_303_, v___x_304_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3___boxed(lean_object* v_x_306_){
_start:
{
uint8_t v_res_307_; lean_object* v_r_308_; 
v_res_307_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__3(v_x_306_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__6(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_315_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__5));
v___x_316_ = lean_unsigned_to_nat(14u);
v___x_317_ = lean_unsigned_to_nat(22u);
v___x_318_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4));
v___x_319_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3));
v___x_320_ = l_mkPanicMessageWithDecl(v___x_319_, v___x_318_, v___x_317_, v___x_316_, v___x_315_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(lean_object* v_hoverPos_321_, lean_object* v_infoTree_322_){
_start:
{
lean_object* v___x_323_; 
lean_inc(v_hoverPos_321_);
v___x_323_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f(v_hoverPos_321_, v_infoTree_322_);
if (lean_obj_tag(v___x_323_) == 1)
{
lean_object* v_val_324_; lean_object* v_fst_325_; lean_object* v_snd_326_; lean_object* v___f_327_; lean_object* v___f_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_val_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_val_324_);
lean_dec_ref(v___x_323_);
v_fst_325_ = lean_ctor_get(v_val_324_, 0);
lean_inc(v_fst_325_);
v_snd_326_ = lean_ctor_get(v_val_324_, 1);
lean_inc(v_snd_326_);
lean_dec(v_val_324_);
lean_inc(v_hoverPos_321_);
v___f_327_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_327_, 0, v_hoverPos_321_);
v___f_328_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0));
v___x_329_ = l_Lean_Elab_Info_stx(v_snd_326_);
v___x_330_ = l_Lean_Syntax_findStack_x3f(v___x_329_, v___f_327_, v___f_328_);
if (lean_obj_tag(v___x_330_) == 1)
{
lean_object* v_val_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_387_; 
v_val_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_387_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_387_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_val_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_387_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___f_335_; lean_object* v_stack_336_; lean_object* v___x_337_; 
v___f_335_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1));
v_stack_336_ = l_List_dropWhile___redArg(v___f_335_, v_val_331_);
v___x_337_ = l_List_head_x3f___redArg(v_stack_336_);
if (lean_obj_tag(v___x_337_) == 1)
{
lean_object* v_val_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_385_; 
v_val_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_385_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_385_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_val_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_385_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_fst_342_; uint8_t v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; uint8_t v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___f_364_; uint8_t v_isDotIdCompletion_365_; lean_object* v_fst_367_; uint8_t v_snd_368_; 
v_fst_342_ = lean_ctor_get(v_val_338_, 0);
lean_inc(v_fst_342_);
lean_dec(v_val_338_);
v___f_364_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2));
v_isDotIdCompletion_365_ = l_List_any___redArg(v_stack_336_, v___f_364_);
if (v_isDotIdCompletion_365_ == 0)
{
lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_373_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__1));
lean_inc(v_fst_342_);
v___x_374_ = l_Lean_Syntax_isOfKind(v_fst_342_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__2___closed__6));
lean_inc(v_fst_342_);
v___x_376_ = l_Lean_Syntax_isOfKind(v_fst_342_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec(v_fst_342_);
lean_del_object(v___x_340_);
lean_del_object(v___x_333_);
lean_dec(v_snd_326_);
lean_dec(v_fst_325_);
lean_dec(v_hoverPos_321_);
v___x_377_ = lean_box(0);
return v___x_377_;
}
else
{
lean_object* v___x_378_; lean_object* v_id_379_; uint8_t v___x_380_; 
v___x_378_ = lean_unsigned_to_nat(0u);
v_id_379_ = l_Lean_Syntax_getArg(v_fst_342_, v___x_378_);
lean_inc(v_id_379_);
v___x_380_ = l_Lean_Syntax_isOfKind(v_id_379_, v___x_373_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
lean_dec(v_id_379_);
lean_dec(v_fst_342_);
lean_del_object(v___x_340_);
lean_del_object(v___x_333_);
lean_dec(v_snd_326_);
lean_dec(v_fst_325_);
lean_dec(v_hoverPos_321_);
v___x_381_ = lean_box(0);
return v___x_381_;
}
else
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_TSyntax_getId(v_id_379_);
lean_dec(v_id_379_);
v_fst_367_ = v___x_382_;
v_snd_368_ = v___x_380_;
goto v___jp_366_;
}
}
}
else
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_TSyntax_getId(v_fst_342_);
v_fst_367_ = v___x_383_;
v_snd_368_ = v_isDotIdCompletion_365_;
goto v___jp_366_;
}
}
else
{
lean_object* v___x_384_; 
lean_dec(v_fst_342_);
lean_del_object(v___x_340_);
lean_del_object(v___x_333_);
lean_dec(v_snd_326_);
lean_dec(v_fst_325_);
lean_dec(v_hoverPos_321_);
v___x_384_ = lean_box(0);
return v___x_384_;
}
v___jp_343_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_347_ = l_Lean_Elab_Info_lctx(v_snd_326_);
lean_dec(v_snd_326_);
v___x_348_ = lean_box(0);
v___x_349_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_349_, 0, v_fst_342_);
lean_ctor_set(v___x_349_, 1, v___y_345_);
lean_ctor_set(v___x_349_, 2, v___x_347_);
lean_ctor_set(v___x_349_, 3, v___x_348_);
lean_ctor_set_uint8(v___x_349_, sizeof(void*)*4, v___y_344_);
v___x_350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_350_, 0, v___y_346_);
lean_ctor_set(v___x_350_, 1, v_fst_325_);
lean_ctor_set(v___x_350_, 2, v___x_349_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_350_);
v___x_352_ = v___x_340_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
v___jp_354_:
{
uint8_t v___x_358_; 
v___x_358_ = lean_nat_dec_lt(v_hoverPos_321_, v___y_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
lean_dec(v___y_357_);
lean_del_object(v___x_333_);
lean_dec(v_hoverPos_321_);
v___x_359_ = lean_box(0);
v___y_344_ = v___y_355_;
v___y_345_ = v___y_356_;
v___y_346_ = v___x_359_;
goto v___jp_343_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = lean_nat_sub(v___y_357_, v_hoverPos_321_);
lean_dec(v_hoverPos_321_);
lean_dec(v___y_357_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_360_);
v___x_362_ = v___x_333_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
v___y_344_ = v___y_355_;
v___y_345_ = v___y_356_;
v___y_346_ = v___x_362_;
goto v___jp_343_;
}
}
}
v___jp_366_:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Syntax_getTailPos_x3f(v_fst_342_, v_isDotIdCompletion_365_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_obj_once(&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__6, &l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__6_once, _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__6);
v___x_371_ = l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(v___x_370_);
v___y_355_ = v_snd_368_;
v___y_356_ = v_fst_367_;
v___y_357_ = v___x_371_;
goto v___jp_354_;
}
else
{
lean_object* v_val_372_; 
v_val_372_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_val_372_);
lean_dec_ref(v___x_369_);
v___y_355_ = v_snd_368_;
v___y_356_ = v_fst_367_;
v___y_357_ = v_val_372_;
goto v___jp_354_;
}
}
}
}
else
{
lean_object* v___x_386_; 
lean_dec(v___x_337_);
lean_dec(v_stack_336_);
lean_del_object(v___x_333_);
lean_dec(v_snd_326_);
lean_dec(v_fst_325_);
lean_dec(v_hoverPos_321_);
v___x_386_ = lean_box(0);
return v___x_386_;
}
}
}
else
{
lean_object* v___x_388_; 
lean_dec(v___x_330_);
lean_dec(v_snd_326_);
lean_dec(v_fst_325_);
lean_dec(v_hoverPos_321_);
v___x_388_ = lean_box(0);
return v___x_388_;
}
}
else
{
lean_object* v___x_389_; 
lean_dec(v___x_323_);
lean_dec(v_hoverPos_321_);
v___x_389_ = lean_box(0);
return v___x_389_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(lean_object* v_fileMap_390_, lean_object* v_hoverPos_391_){
_start:
{
lean_object* v_source_392_; uint8_t v___x_393_; 
v_source_392_ = lean_ctor_get(v_fileMap_390_, 0);
v___x_393_ = lean_string_utf8_at_end(v_source_392_, v_hoverPos_391_);
if (v___x_393_ == 0)
{
uint32_t v___x_394_; uint8_t v___y_396_; uint32_t v___x_401_; uint8_t v___x_402_; 
v___x_394_ = lean_string_utf8_get(v_source_392_, v_hoverPos_391_);
v___x_401_ = 32;
v___x_402_ = lean_uint32_dec_eq(v___x_394_, v___x_401_);
if (v___x_402_ == 0)
{
uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 9;
v___x_404_ = lean_uint32_dec_eq(v___x_394_, v___x_403_);
v___y_396_ = v___x_404_;
goto v___jp_395_;
}
else
{
v___y_396_ = v___x_402_;
goto v___jp_395_;
}
v___jp_395_:
{
if (v___y_396_ == 0)
{
uint32_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 13;
v___x_398_ = lean_uint32_dec_eq(v___x_394_, v___x_397_);
if (v___x_398_ == 0)
{
uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_399_ = 10;
v___x_400_ = lean_uint32_dec_eq(v___x_394_, v___x_399_);
return v___x_400_;
}
else
{
return v___x_398_;
}
}
else
{
return v___y_396_;
}
}
}
else
{
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace___boxed(lean_object* v_fileMap_405_, lean_object* v_hoverPos_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_405_, v_hoverPos_406_);
lean_dec(v_hoverPos_406_);
lean_dec_ref(v_fileMap_405_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(lean_object* v_fileMap_409_, lean_object* v_hoverPos_410_){
_start:
{
uint32_t v___y_412_; uint8_t v___y_413_; lean_object* v_source_418_; uint8_t v___y_428_; uint8_t v___x_429_; 
v_source_418_ = lean_ctor_get(v_fileMap_409_, 0);
v___x_429_ = lean_string_utf8_at_end(v_source_418_, v_hoverPos_410_);
if (v___x_429_ == 0)
{
uint32_t v___x_430_; uint8_t v___y_432_; uint32_t v___x_437_; uint8_t v___x_438_; 
v___x_430_ = lean_string_utf8_get(v_source_418_, v_hoverPos_410_);
v___x_437_ = 32;
v___x_438_ = lean_uint32_dec_eq(v___x_430_, v___x_437_);
if (v___x_438_ == 0)
{
uint32_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = 9;
v___x_440_ = lean_uint32_dec_eq(v___x_430_, v___x_439_);
v___y_432_ = v___x_440_;
goto v___jp_431_;
}
else
{
v___y_432_ = v___x_438_;
goto v___jp_431_;
}
v___jp_431_:
{
if (v___y_432_ == 0)
{
uint32_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = 13;
v___x_434_ = lean_uint32_dec_eq(v___x_430_, v___x_433_);
if (v___x_434_ == 0)
{
uint32_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = 10;
v___x_436_ = lean_uint32_dec_eq(v___x_430_, v___x_435_);
v___y_428_ = v___x_436_;
goto v___jp_427_;
}
else
{
v___y_428_ = v___x_434_;
goto v___jp_427_;
}
}
else
{
goto v___jp_419_;
}
}
}
else
{
v___y_428_ = v___x_429_;
goto v___jp_427_;
}
v___jp_411_:
{
if (v___y_413_ == 0)
{
uint32_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = 13;
v___x_415_ = lean_uint32_dec_eq(v___y_412_, v___x_414_);
if (v___x_415_ == 0)
{
uint32_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = 10;
v___x_417_ = lean_uint32_dec_eq(v___y_412_, v___x_416_);
return v___x_417_;
}
else
{
return v___x_415_;
}
}
else
{
return v___y_413_;
}
}
v___jp_419_:
{
lean_object* v___x_420_; lean_object* v___x_421_; uint32_t v___x_422_; uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_420_ = lean_unsigned_to_nat(1u);
v___x_421_ = lean_nat_sub(v_hoverPos_410_, v___x_420_);
v___x_422_ = lean_string_utf8_get(v_source_418_, v___x_421_);
lean_dec(v___x_421_);
v___x_423_ = 32;
v___x_424_ = lean_uint32_dec_eq(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 9;
v___x_426_ = lean_uint32_dec_eq(v___x_422_, v___x_425_);
v___y_412_ = v___x_422_;
v___y_413_ = v___x_426_;
goto v___jp_411_;
}
else
{
v___y_412_ = v___x_422_;
v___y_413_ = v___x_424_;
goto v___jp_411_;
}
}
v___jp_427_:
{
if (v___y_428_ == 0)
{
return v___y_428_;
}
else
{
goto v___jp_419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace___boxed(lean_object* v_fileMap_441_, lean_object* v_hoverPos_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_441_, v_hoverPos_442_);
lean_dec(v_hoverPos_442_);
lean_dec_ref(v_fileMap_441_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(lean_object* v_stx_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
lean_inc(v_stx_458_);
v___x_459_ = l_Lean_Syntax_getKind(v_stx_458_);
v___x_460_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2));
v___x_461_ = lean_name_eq(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_463_ = lean_name_eq(v___x_459_, v___x_462_);
lean_dec(v___x_459_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
lean_dec(v_stx_458_);
v___x_464_ = lean_box(0);
return v___x_464_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = l_Lean_Syntax_getArg(v_stx_458_, v___x_465_);
lean_dec(v_stx_458_);
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v___x_459_);
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = l_Lean_Syntax_getArg(v_stx_458_, v___x_468_);
lean_dec(v_stx_458_);
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(lean_object* v_fileMap_471_, lean_object* v_hoverPos_472_, lean_object* v_hoverFilePos_473_, lean_object* v_stx_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(v_stx_474_);
if (lean_obj_tag(v___x_475_) == 1)
{
lean_object* v_val_476_; uint8_t v___x_477_; lean_object* v___x_478_; 
v_val_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_val_476_);
lean_dec_ref(v___x_475_);
v___x_477_ = 0;
v___x_478_ = l_Lean_Syntax_getPos_x3f(v_val_476_, v___x_477_);
lean_dec(v_val_476_);
if (lean_obj_tag(v___x_478_) == 1)
{
lean_object* v_val_479_; lean_object* v___x_480_; lean_object* v_column_481_; lean_object* v_column_482_; uint8_t v___x_483_; 
v_val_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_val_479_);
lean_dec_ref(v___x_478_);
lean_inc_ref(v_fileMap_471_);
v___x_480_ = l_Lean_FileMap_toPosition(v_fileMap_471_, v_val_479_);
lean_dec(v_val_479_);
v_column_481_ = lean_ctor_get(v___x_480_, 1);
lean_inc(v_column_481_);
lean_dec_ref(v___x_480_);
v_column_482_ = lean_ctor_get(v_hoverFilePos_473_, 1);
v___x_483_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_471_, v_hoverPos_472_);
lean_dec_ref(v_fileMap_471_);
if (v___x_483_ == 0)
{
lean_dec(v_column_481_);
return v___x_483_;
}
else
{
uint8_t v_isCursorInTacticBlock_484_; 
v_isCursorInTacticBlock_484_ = lean_nat_dec_eq(v_column_482_, v_column_481_);
lean_dec(v_column_481_);
return v_isCursorInTacticBlock_484_;
}
}
else
{
lean_dec(v___x_478_);
lean_dec_ref(v_fileMap_471_);
return v___x_477_;
}
}
else
{
uint8_t v___x_485_; 
lean_dec(v___x_475_);
lean_dec_ref(v_fileMap_471_);
v___x_485_ = 0;
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation___boxed(lean_object* v_fileMap_486_, lean_object* v_hoverPos_487_, lean_object* v_hoverFilePos_488_, lean_object* v_stx_489_){
_start:
{
uint8_t v_res_490_; lean_object* v_r_491_; 
v_res_490_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_486_, v_hoverPos_487_, v_hoverFilePos_488_, v_stx_489_);
lean_dec_ref(v_hoverFilePos_488_);
lean_dec(v_hoverPos_487_);
v_r_491_ = lean_box(v_res_490_);
return v_r_491_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(lean_object* v_hoverPos_493_, lean_object* v_as_494_, size_t v_i_495_, size_t v_stop_496_){
_start:
{
uint8_t v___x_501_; 
v___x_501_ = lean_usize_dec_eq(v_i_495_, v_stop_496_);
if (v___x_501_ == 0)
{
uint8_t v___x_502_; uint8_t v___y_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_502_ = 1;
v___x_505_ = lean_array_uget_borrowed(v_as_494_, v_i_495_);
v___x_506_ = l_Lean_Syntax_getTailPos_x3f(v___x_505_, v___x_501_);
if (lean_obj_tag(v___x_506_) == 1)
{
lean_object* v_val_507_; uint8_t v___y_509_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_val_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_val_507_);
lean_dec_ref(v___x_506_);
v___x_513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___closed__0));
lean_inc(v___x_505_);
v___x_514_ = l_Lean_Syntax_isToken(v___x_513_, v___x_505_);
if (v___x_514_ == 0)
{
v___y_509_ = v___x_514_;
goto v___jp_508_;
}
else
{
uint8_t v___x_515_; 
v___x_515_ = lean_nat_dec_le(v_val_507_, v_hoverPos_493_);
v___y_509_ = v___x_515_;
goto v___jp_508_;
}
v___jp_508_:
{
if (v___y_509_ == 0)
{
lean_dec(v_val_507_);
goto v___jp_497_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_510_ = l_Lean_Syntax_getTrailingSize(v___x_505_);
v___x_511_ = lean_nat_add(v_val_507_, v___x_510_);
lean_dec(v___x_510_);
lean_dec(v_val_507_);
v___x_512_ = lean_nat_dec_le(v_hoverPos_493_, v___x_511_);
lean_dec(v___x_511_);
v___y_504_ = v___x_512_;
goto v___jp_503_;
}
}
}
else
{
lean_dec(v___x_506_);
v___y_504_ = v___x_501_;
goto v___jp_503_;
}
v___jp_503_:
{
if (v___y_504_ == 0)
{
goto v___jp_497_;
}
else
{
return v___x_502_;
}
}
}
else
{
uint8_t v___x_516_; 
v___x_516_ = 0;
return v___x_516_;
}
v___jp_497_:
{
size_t v___x_498_; size_t v___x_499_; 
v___x_498_ = ((size_t)1ULL);
v___x_499_ = lean_usize_add(v_i_495_, v___x_498_);
v_i_495_ = v___x_499_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___boxed(lean_object* v_hoverPos_517_, lean_object* v_as_518_, lean_object* v_i_519_, lean_object* v_stop_520_){
_start:
{
size_t v_i_boxed_521_; size_t v_stop_boxed_522_; uint8_t v_res_523_; lean_object* v_r_524_; 
v_i_boxed_521_ = lean_unbox_usize(v_i_519_);
lean_dec(v_i_519_);
v_stop_boxed_522_ = lean_unbox_usize(v_stop_520_);
lean_dec(v_stop_520_);
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_517_, v_as_518_, v_i_boxed_521_, v_stop_boxed_522_);
lean_dec_ref(v_as_518_);
lean_dec(v_hoverPos_517_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(lean_object* v_fileMap_525_, lean_object* v_hoverPos_526_, lean_object* v_stx_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(v_stx_527_);
if (lean_obj_tag(v___x_528_) == 1)
{
lean_object* v_val_529_; uint8_t v___x_530_; 
v_val_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_val_529_);
lean_dec_ref(v___x_528_);
v___x_530_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_525_, v_hoverPos_526_);
if (v___x_530_ == 0)
{
lean_dec(v_val_529_);
return v___x_530_;
}
else
{
lean_object* v_tactics_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_tactics_531_ = l_Lean_Syntax_getArgs(v_val_529_);
lean_dec(v_val_529_);
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_array_get_size(v_tactics_531_);
v___x_534_ = lean_nat_dec_lt(v___x_532_, v___x_533_);
if (v___x_534_ == 0)
{
lean_dec_ref(v_tactics_531_);
return v___x_534_;
}
else
{
if (v___x_534_ == 0)
{
lean_dec_ref(v_tactics_531_);
return v___x_534_;
}
else
{
size_t v___x_535_; size_t v___x_536_; uint8_t v___x_537_; 
v___x_535_ = ((size_t)0ULL);
v___x_536_ = lean_usize_of_nat(v___x_533_);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_526_, v_tactics_531_, v___x_535_, v___x_536_);
lean_dec_ref(v_tactics_531_);
return v___x_537_;
}
}
}
}
else
{
uint8_t v___x_538_; 
lean_dec(v___x_528_);
v___x_538_ = 0;
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon___boxed(lean_object* v_fileMap_539_, lean_object* v_hoverPos_540_, lean_object* v_stx_541_){
_start:
{
uint8_t v_res_542_; lean_object* v_r_543_; 
v_res_542_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_539_, v_hoverPos_540_, v_stx_541_);
lean_dec(v_hoverPos_540_);
lean_dec_ref(v_fileMap_539_);
v_r_543_ = lean_box(v_res_542_);
return v_r_543_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(lean_object* v_a_544_){
_start:
{
switch(lean_obj_tag(v_a_544_))
{
case 0:
{
uint8_t v___x_545_; 
v___x_545_ = 1;
return v___x_545_;
}
case 1:
{
lean_object* v_args_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_args_546_ = lean_ctor_get(v_a_544_, 2);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_array_get_size(v_args_546_);
v___x_549_ = lean_nat_dec_lt(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
uint8_t v___x_550_; 
v___x_550_ = 1;
return v___x_550_;
}
else
{
if (v___x_549_ == 0)
{
return v___x_549_;
}
else
{
size_t v___x_551_; size_t v___x_552_; uint8_t v___x_553_; 
v___x_551_ = ((size_t)0ULL);
v___x_552_ = lean_usize_of_nat(v___x_548_);
v___x_553_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_args_546_, v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
return v___x_549_;
}
else
{
uint8_t v___x_554_; 
v___x_554_ = 0;
return v___x_554_;
}
}
}
}
default: 
{
uint8_t v___x_555_; 
v___x_555_ = 0;
return v___x_555_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(lean_object* v_as_556_, size_t v_i_557_, size_t v_stop_558_){
_start:
{
uint8_t v___x_559_; 
v___x_559_ = lean_usize_dec_eq(v_i_557_, v_stop_558_);
if (v___x_559_ == 0)
{
uint8_t v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_560_ = 1;
v___x_561_ = lean_array_uget_borrowed(v_as_556_, v_i_557_);
v___x_562_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v___x_561_);
if (v___x_562_ == 0)
{
return v___x_560_;
}
else
{
if (v___x_559_ == 0)
{
size_t v___x_563_; size_t v___x_564_; 
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_add(v_i_557_, v___x_563_);
v_i_557_ = v___x_564_;
goto _start;
}
else
{
return v___x_560_;
}
}
}
else
{
uint8_t v___x_566_; 
v___x_566_ = 0;
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0___boxed(lean_object* v_as_567_, lean_object* v_i_568_, lean_object* v_stop_569_){
_start:
{
size_t v_i_boxed_570_; size_t v_stop_boxed_571_; uint8_t v_res_572_; lean_object* v_r_573_; 
v_i_boxed_570_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_stop_boxed_571_ = lean_unbox_usize(v_stop_569_);
lean_dec(v_stop_569_);
v_res_572_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_as_567_, v_i_boxed_570_, v_stop_boxed_571_);
lean_dec_ref(v_as_567_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty___boxed(lean_object* v_a_574_){
_start:
{
uint8_t v_res_575_; lean_object* v_r_576_; 
v_res_575_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_a_574_);
lean_dec(v_a_574_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(lean_object* v_stx_583_){
_start:
{
uint8_t v___y_585_; uint8_t v___y_593_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
lean_inc(v_stx_583_);
v___x_598_ = l_Lean_Syntax_getKind(v_stx_583_);
v___x_599_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1));
v___x_600_ = lean_name_eq(v___x_598_, v___x_599_);
lean_dec(v___x_598_);
if (v___x_600_ == 0)
{
v___y_593_ = v___x_600_;
goto v___jp_592_;
}
else
{
uint8_t v___x_601_; 
v___x_601_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_stx_583_);
v___y_593_ = v___x_601_;
goto v___jp_592_;
}
v___jp_584_:
{
if (v___y_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
lean_inc(v_stx_583_);
v___x_586_ = l_Lean_Syntax_getKind(v_stx_583_);
v___x_587_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_588_ = lean_name_eq(v___x_586_, v___x_587_);
lean_dec(v___x_586_);
if (v___x_588_ == 0)
{
lean_dec(v_stx_583_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = l_Lean_Syntax_getArg(v_stx_583_, v___x_589_);
lean_dec(v_stx_583_);
v___x_591_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v___x_590_);
lean_dec(v___x_590_);
return v___x_591_;
}
}
else
{
lean_dec(v_stx_583_);
return v___y_585_;
}
}
v___jp_592_:
{
if (v___y_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
lean_inc(v_stx_583_);
v___x_594_ = l_Lean_Syntax_getKind(v_stx_583_);
v___x_595_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2));
v___x_596_ = lean_name_eq(v___x_594_, v___x_595_);
lean_dec(v___x_594_);
if (v___x_596_ == 0)
{
v___y_585_ = v___x_596_;
goto v___jp_584_;
}
else
{
uint8_t v___x_597_; 
v___x_597_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_stx_583_);
v___y_585_ = v___x_597_;
goto v___jp_584_;
}
}
else
{
lean_dec(v_stx_583_);
return v___y_593_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___boxed(lean_object* v_stx_602_){
_start:
{
uint8_t v_res_603_; lean_object* v_r_604_; 
v_res_603_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_602_);
v_r_604_ = lean_box(v_res_603_);
return v_r_604_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(lean_object* v_fileMap_605_, lean_object* v_hoverPos_606_, lean_object* v_stx_607_){
_start:
{
uint8_t v___x_608_; 
v___x_608_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_605_, v_hoverPos_606_);
if (v___x_608_ == 0)
{
lean_dec(v_stx_607_);
return v___x_608_;
}
else
{
uint8_t v___x_609_; 
v___x_609_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_607_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock___boxed(lean_object* v_fileMap_610_, lean_object* v_hoverPos_611_, lean_object* v_stx_612_){
_start:
{
uint8_t v_res_613_; lean_object* v_r_614_; 
v_res_613_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_610_, v_hoverPos_611_, v_stx_612_);
lean_dec(v_hoverPos_611_);
lean_dec_ref(v_fileMap_610_);
v_r_614_ = lean_box(v_res_613_);
return v_r_614_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(lean_object* v_fileMap_615_, lean_object* v_hoverPos_616_, lean_object* v_hoverFilePos_617_, lean_object* v_stx_618_, lean_object* v_leadingWs_619_){
_start:
{
uint8_t v___y_621_; uint8_t v___x_634_; lean_object* v___x_635_; 
v___x_634_ = 0;
v___x_635_ = l_Lean_Syntax_getPos_x3f(v_stx_618_, v___x_634_);
if (lean_obj_tag(v___x_635_) == 1)
{
lean_object* v_val_636_; lean_object* v___x_637_; 
v_val_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_val_636_);
lean_dec_ref(v___x_635_);
v___x_637_ = l_Lean_Syntax_getTailPos_x3f(v_stx_618_, v___x_634_);
if (lean_obj_tag(v___x_637_) == 1)
{
lean_object* v_val_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_val_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_638_);
lean_dec_ref(v___x_637_);
v___x_639_ = lean_nat_sub(v_val_636_, v_leadingWs_619_);
lean_dec(v_val_636_);
v___x_640_ = lean_nat_dec_le(v___x_639_, v_hoverPos_616_);
lean_dec(v___x_639_);
if (v___x_640_ == 0)
{
lean_dec(v_val_638_);
v___y_621_ = v___x_640_;
goto v___jp_620_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_641_ = l_Lean_Syntax_getTrailingSize(v_stx_618_);
v___x_642_ = lean_nat_add(v_val_638_, v___x_641_);
lean_dec(v___x_641_);
lean_dec(v_val_638_);
v___x_643_ = lean_nat_dec_le(v_hoverPos_616_, v___x_642_);
lean_dec(v___x_642_);
v___y_621_ = v___x_643_;
goto v___jp_620_;
}
}
else
{
uint8_t v___x_644_; 
lean_dec(v___x_637_);
lean_dec(v_val_636_);
lean_dec(v_leadingWs_619_);
v___x_644_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_615_, v_hoverPos_616_, v_stx_618_);
lean_dec_ref(v_fileMap_615_);
return v___x_644_;
}
}
else
{
uint8_t v___x_645_; 
lean_dec(v___x_635_);
lean_dec(v_leadingWs_619_);
v___x_645_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_615_, v_hoverPos_616_, v_stx_618_);
lean_dec_ref(v_fileMap_615_);
return v___x_645_;
}
v___jp_620_:
{
if (v___y_621_ == 0)
{
lean_dec(v_leadingWs_619_);
lean_dec(v_stx_618_);
lean_dec_ref(v_fileMap_615_);
return v___y_621_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; size_t v_sz_625_; size_t v___x_626_; lean_object* v___x_627_; lean_object* v_fst_628_; 
v___x_622_ = l_Lean_Syntax_getArgs(v_stx_618_);
v___x_623_ = lean_box(0);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v_leadingWs_619_);
v_sz_625_ = lean_array_size(v___x_622_);
v___x_626_ = ((size_t)0ULL);
lean_inc_ref(v_fileMap_615_);
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_615_, v_hoverPos_616_, v_hoverFilePos_617_, v___y_621_, v___x_622_, v_sz_625_, v___x_626_, v___x_624_);
lean_dec_ref(v___x_622_);
v_fst_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_fst_628_);
lean_dec_ref(v___x_627_);
if (lean_obj_tag(v_fst_628_) == 0)
{
uint8_t v___x_629_; 
lean_inc(v_stx_618_);
v___x_629_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_615_, v_hoverPos_616_, v_stx_618_);
if (v___x_629_ == 0)
{
uint8_t v___x_630_; 
lean_inc(v_stx_618_);
v___x_630_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_615_, v_hoverPos_616_, v_stx_618_);
if (v___x_630_ == 0)
{
uint8_t v___x_631_; 
v___x_631_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_615_, v_hoverPos_616_, v_hoverFilePos_617_, v_stx_618_);
return v___x_631_;
}
else
{
lean_dec(v_stx_618_);
lean_dec_ref(v_fileMap_615_);
return v___y_621_;
}
}
else
{
lean_dec(v_stx_618_);
lean_dec_ref(v_fileMap_615_);
return v___y_621_;
}
}
else
{
lean_object* v_val_632_; uint8_t v___x_633_; 
lean_dec(v_stx_618_);
lean_dec_ref(v_fileMap_615_);
v_val_632_ = lean_ctor_get(v_fst_628_, 0);
lean_inc(v_val_632_);
lean_dec_ref(v_fst_628_);
v___x_633_ = lean_unbox(v_val_632_);
lean_dec(v_val_632_);
return v___x_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(lean_object* v_fileMap_646_, lean_object* v_hoverPos_647_, lean_object* v_hoverFilePos_648_, uint8_t v___y_649_, lean_object* v_as_650_, size_t v_sz_651_, size_t v_i_652_, lean_object* v_b_653_){
_start:
{
uint8_t v___x_654_; 
v___x_654_ = lean_usize_dec_lt(v_i_652_, v_sz_651_);
if (v___x_654_ == 0)
{
lean_dec_ref(v_fileMap_646_);
return v_b_653_;
}
else
{
lean_object* v_snd_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_674_; 
v_snd_655_ = lean_ctor_get(v_b_653_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v_b_653_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v_b_653_, 0);
lean_dec(v_unused_675_);
v___x_657_ = v_b_653_;
v_isShared_658_ = v_isSharedCheck_674_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_snd_655_);
lean_dec(v_b_653_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_674_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_a_659_; uint8_t v___x_660_; 
v_a_659_ = lean_array_uget_borrowed(v_as_650_, v_i_652_);
lean_inc(v_snd_655_);
lean_inc(v_a_659_);
lean_inc_ref(v_fileMap_646_);
v___x_660_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_646_, v_hoverPos_647_, v_hoverFilePos_648_, v_a_659_, v_snd_655_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
lean_dec(v_snd_655_);
v___x_661_ = lean_box(0);
v___x_662_ = l_Lean_Syntax_getTrailingSize(v_a_659_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___x_662_);
lean_ctor_set(v___x_657_, 0, v___x_661_);
v___x_664_ = v___x_657_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_662_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
size_t v___x_665_; size_t v___x_666_; 
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_add(v_i_652_, v___x_665_);
v_i_652_ = v___x_666_;
v_b_653_ = v___x_664_;
goto _start;
}
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
lean_dec_ref(v_fileMap_646_);
v___x_669_ = lean_box(v___y_649_);
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_670_);
v___x_672_ = v___x_657_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_snd_655_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0___boxed(lean_object* v_fileMap_676_, lean_object* v_hoverPos_677_, lean_object* v_hoverFilePos_678_, lean_object* v___y_679_, lean_object* v_as_680_, lean_object* v_sz_681_, lean_object* v_i_682_, lean_object* v_b_683_){
_start:
{
uint8_t v___y_953__boxed_684_; size_t v_sz_boxed_685_; size_t v_i_boxed_686_; lean_object* v_res_687_; 
v___y_953__boxed_684_ = lean_unbox(v___y_679_);
v_sz_boxed_685_ = lean_unbox_usize(v_sz_681_);
lean_dec(v_sz_681_);
v_i_boxed_686_ = lean_unbox_usize(v_i_682_);
lean_dec(v_i_682_);
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_676_, v_hoverPos_677_, v_hoverFilePos_678_, v___y_953__boxed_684_, v_as_680_, v_sz_boxed_685_, v_i_boxed_686_, v_b_683_);
lean_dec_ref(v_as_680_);
lean_dec_ref(v_hoverFilePos_678_);
lean_dec(v_hoverPos_677_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go___boxed(lean_object* v_fileMap_688_, lean_object* v_hoverPos_689_, lean_object* v_hoverFilePos_690_, lean_object* v_stx_691_, lean_object* v_leadingWs_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_688_, v_hoverPos_689_, v_hoverFilePos_690_, v_stx_691_, v_leadingWs_692_);
lean_dec_ref(v_hoverFilePos_690_);
lean_dec(v_hoverPos_689_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(lean_object* v_fileMap_695_, lean_object* v_hoverPos_696_, lean_object* v_cmdStx_697_){
_start:
{
lean_object* v_hoverFilePos_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
lean_inc_ref(v_fileMap_695_);
v_hoverFilePos_698_ = l_Lean_FileMap_toPosition(v_fileMap_695_, v_hoverPos_696_);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_695_, v_hoverPos_696_, v_hoverFilePos_698_, v_cmdStx_697_, v___x_699_);
lean_dec_ref(v_hoverFilePos_698_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion___boxed(lean_object* v_fileMap_701_, lean_object* v_hoverPos_702_, lean_object* v_cmdStx_703_){
_start:
{
uint8_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_701_, v_hoverPos_702_, v_cmdStx_703_);
lean_dec(v_hoverPos_702_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(lean_object* v_as_711_, size_t v_sz_712_, size_t v_i_713_, lean_object* v_b_714_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = lean_usize_dec_lt(v_i_713_, v_sz_712_);
if (v___x_715_ == 0)
{
lean_inc_ref(v_b_714_);
return v_b_714_;
}
else
{
lean_object* v___x_716_; lean_object* v_a_717_; lean_object* v___x_718_; 
v___x_716_ = lean_box(0);
v_a_717_ = lean_array_uget_borrowed(v_as_711_, v_i_713_);
v___x_718_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_a_717_);
if (lean_obj_tag(v___x_718_) == 1)
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___x_716_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; size_t v___x_722_; size_t v___x_723_; 
lean_dec(v___x_718_);
v___x_721_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v___x_722_ = ((size_t)1ULL);
v___x_723_ = lean_usize_add(v_i_713_, v___x_722_);
v_i_713_ = v___x_723_;
v_b_714_ = v___x_721_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(lean_object* v_as_725_, size_t v_sz_726_, size_t v_i_727_, lean_object* v_b_728_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = lean_usize_dec_lt(v_i_727_, v_sz_726_);
if (v___x_729_ == 0)
{
lean_inc_ref(v_b_728_);
return v_b_728_;
}
else
{
lean_object* v___x_730_; lean_object* v_a_731_; lean_object* v___x_732_; 
v___x_730_ = lean_box(0);
v_a_731_ = lean_array_uget_borrowed(v_as_725_, v_i_727_);
lean_inc(v_a_731_);
v___x_732_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_a_731_);
if (lean_obj_tag(v___x_732_) == 1)
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v___x_730_);
return v___x_734_;
}
else
{
lean_object* v___x_735_; size_t v___x_736_; size_t v___x_737_; 
lean_dec(v___x_732_);
v___x_735_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v___x_736_ = ((size_t)1ULL);
v___x_737_ = lean_usize_add(v_i_727_, v___x_736_);
v_i_727_ = v___x_737_;
v_b_728_ = v___x_735_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(lean_object* v_x_739_){
_start:
{
if (lean_obj_tag(v_x_739_) == 0)
{
lean_object* v_cs_740_; lean_object* v___x_741_; lean_object* v___x_742_; size_t v_sz_743_; size_t v___x_744_; lean_object* v___x_745_; lean_object* v_fst_746_; 
v_cs_740_ = lean_ctor_get(v_x_739_, 0);
v___x_741_ = lean_box(0);
v___x_742_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_743_ = lean_array_size(v_cs_740_);
v___x_744_ = ((size_t)0ULL);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_cs_740_, v_sz_743_, v___x_744_, v___x_742_);
v_fst_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_fst_746_);
lean_dec_ref(v___x_745_);
if (lean_obj_tag(v_fst_746_) == 0)
{
return v___x_741_;
}
else
{
lean_object* v_val_747_; 
v_val_747_ = lean_ctor_get(v_fst_746_, 0);
lean_inc(v_val_747_);
lean_dec_ref(v_fst_746_);
return v_val_747_;
}
}
else
{
lean_object* v_vs_748_; lean_object* v___x_749_; lean_object* v___x_750_; size_t v_sz_751_; size_t v___x_752_; lean_object* v___x_753_; lean_object* v_fst_754_; 
v_vs_748_ = lean_ctor_get(v_x_739_, 0);
v___x_749_ = lean_box(0);
v___x_750_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_751_ = lean_array_size(v_vs_748_);
v___x_752_ = ((size_t)0ULL);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_vs_748_, v_sz_751_, v___x_752_, v___x_750_);
v_fst_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_fst_754_);
lean_dec_ref(v___x_753_);
if (lean_obj_tag(v_fst_754_) == 0)
{
return v___x_749_;
}
else
{
lean_object* v_val_755_; 
v_val_755_ = lean_ctor_get(v_fst_754_, 0);
lean_inc(v_val_755_);
lean_dec_ref(v_fst_754_);
return v_val_755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(lean_object* v_t_756_){
_start:
{
lean_object* v_root_757_; lean_object* v_tail_758_; lean_object* v___x_759_; 
v_root_757_ = lean_ctor_get(v_t_756_, 0);
v_tail_758_ = lean_ctor_get(v_t_756_, 1);
v___x_759_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_root_757_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v___x_760_; size_t v_sz_761_; size_t v___x_762_; lean_object* v___x_763_; lean_object* v_fst_764_; 
v___x_760_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_761_ = lean_array_size(v_tail_758_);
v___x_762_ = ((size_t)0ULL);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_tail_758_, v_sz_761_, v___x_762_, v___x_760_);
v_fst_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_fst_764_);
lean_dec_ref(v___x_763_);
if (lean_obj_tag(v_fst_764_) == 0)
{
return v___x_759_;
}
else
{
lean_object* v_val_765_; 
v_val_765_ = lean_ctor_get(v_fst_764_, 0);
lean_inc(v_val_765_);
lean_dec_ref(v_fst_764_);
return v_val_765_;
}
}
else
{
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(lean_object* v_i_766_){
_start:
{
switch(lean_obj_tag(v_i_766_))
{
case 0:
{
lean_object* v_i_767_; 
v_i_767_ = lean_ctor_get(v_i_766_, 0);
lean_inc_ref(v_i_767_);
if (lean_obj_tag(v_i_767_) == 0)
{
lean_object* v_info_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_i_766_);
v_info_768_ = lean_ctor_get(v_i_767_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_i_767_);
if (v_isSharedCheck_778_ == 0)
{
v___x_770_ = v_i_767_;
v_isShared_771_ = v_isSharedCheck_778_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_info_768_);
lean_dec(v_i_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_778_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_772_ = lean_box(0);
v___x_773_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go___closed__0));
v___x_774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_774_, 0, v_info_768_);
lean_ctor_set(v___x_774_, 1, v___x_772_);
lean_ctor_set(v___x_774_, 2, v___x_773_);
if (v_isShared_771_ == 0)
{
lean_ctor_set_tag(v___x_770_, 1);
lean_ctor_set(v___x_770_, 0, v___x_774_);
v___x_776_ = v___x_770_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
else
{
lean_object* v_t_779_; 
lean_dec_ref(v_i_767_);
v_t_779_ = lean_ctor_get(v_i_766_, 1);
lean_inc_ref(v_t_779_);
lean_dec_ref(v_i_766_);
v_i_766_ = v_t_779_;
goto _start;
}
}
case 1:
{
lean_object* v_children_781_; lean_object* v___x_782_; 
v_children_781_ = lean_ctor_get(v_i_766_, 1);
lean_inc_ref(v_children_781_);
lean_dec_ref(v_i_766_);
v___x_782_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(v_children_781_);
lean_dec_ref(v_children_781_);
return v___x_782_;
}
default: 
{
lean_object* v___x_783_; 
lean_dec_ref(v_i_766_);
v___x_783_ = lean_box(0);
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___boxed(lean_object* v_t_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(v_t_784_);
lean_dec_ref(v_t_784_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1___boxed(lean_object* v_as_786_, lean_object* v_sz_787_, lean_object* v_i_788_, lean_object* v_b_789_){
_start:
{
size_t v_sz_boxed_790_; size_t v_i_boxed_791_; lean_object* v_res_792_; 
v_sz_boxed_790_ = lean_unbox_usize(v_sz_787_);
lean_dec(v_sz_787_);
v_i_boxed_791_ = lean_unbox_usize(v_i_788_);
lean_dec(v_i_788_);
v_res_792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_as_786_, v_sz_boxed_790_, v_i_boxed_791_, v_b_789_);
lean_dec_ref(v_b_789_);
lean_dec_ref(v_as_786_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1___boxed(lean_object* v_as_793_, lean_object* v_sz_794_, lean_object* v_i_795_, lean_object* v_b_796_){
_start:
{
size_t v_sz_boxed_797_; size_t v_i_boxed_798_; lean_object* v_res_799_; 
v_sz_boxed_797_ = lean_unbox_usize(v_sz_794_);
lean_dec(v_sz_794_);
v_i_boxed_798_ = lean_unbox_usize(v_i_795_);
lean_dec(v_i_795_);
v_res_799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_as_793_, v_sz_boxed_797_, v_i_boxed_798_, v_b_796_);
lean_dec_ref(v_b_796_);
lean_dec_ref(v_as_793_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0___boxed(lean_object* v_x_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_x_800_);
lean_dec_ref(v_x_800_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f(lean_object* v_i_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_i_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(lean_object* v_fileMap_806_, lean_object* v_hoverPos_807_, lean_object* v_cmdStx_808_, lean_object* v_infoTree_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_infoTree_809_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_811_; 
lean_dec(v_cmdStx_808_);
lean_dec_ref(v_fileMap_806_);
v___x_811_ = lean_box(0);
return v___x_811_;
}
else
{
lean_object* v_val_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_824_; 
v_val_812_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_824_ == 0)
{
v___x_814_ = v___x_810_;
v_isShared_815_ = v_isSharedCheck_824_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_val_812_);
lean_dec(v___x_810_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_824_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
uint8_t v___x_816_; 
v___x_816_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_806_, v_hoverPos_807_, v_cmdStx_808_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
lean_del_object(v___x_814_);
lean_dec(v_val_812_);
v___x_817_ = lean_box(0);
return v___x_817_;
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_818_ = lean_box(0);
v___x_819_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___closed__0));
v___x_820_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v_val_812_);
lean_ctor_set(v___x_820_, 2, v___x_819_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_820_);
v___x_822_ = v___x_814_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___boxed(lean_object* v_fileMap_825_, lean_object* v_hoverPos_826_, lean_object* v_cmdStx_827_, lean_object* v_infoTree_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(v_fileMap_825_, v_hoverPos_826_, v_cmdStx_827_, v_infoTree_828_);
lean_dec(v_hoverPos_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(lean_object* v_msg_830_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = l_Lean_instInhabitedExpr;
v___x_832_ = lean_panic_fn_borrowed(v___x_831_, v_msg_830_);
return v___x_832_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(lean_object* v_hoverPos_833_, lean_object* v_i_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_Elab_Info_pos_x3f(v_i_834_);
if (lean_obj_tag(v___x_835_) == 1)
{
lean_object* v_val_836_; lean_object* v___x_837_; 
v_val_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_val_836_);
lean_dec_ref(v___x_835_);
v___x_837_ = l_Lean_Elab_Info_tailPos_x3f(v_i_834_);
if (lean_obj_tag(v___x_837_) == 1)
{
if (lean_obj_tag(v_i_834_) == 1)
{
lean_object* v_i_838_; lean_object* v_expectedType_x3f_839_; 
v_i_838_ = lean_ctor_get(v_i_834_, 0);
v_expectedType_x3f_839_ = lean_ctor_get(v_i_838_, 2);
if (lean_obj_tag(v_expectedType_x3f_839_) == 0)
{
uint8_t v___x_840_; 
lean_dec_ref(v___x_837_);
lean_dec(v_val_836_);
v___x_840_ = 0;
return v___x_840_;
}
else
{
lean_object* v_val_841_; uint8_t v___x_842_; 
v_val_841_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_val_841_);
lean_dec_ref(v___x_837_);
v___x_842_ = lean_nat_dec_le(v_val_836_, v_hoverPos_833_);
lean_dec(v_val_836_);
if (v___x_842_ == 0)
{
lean_dec(v_val_841_);
return v___x_842_;
}
else
{
uint8_t v___x_843_; 
v___x_843_ = lean_nat_dec_le(v_hoverPos_833_, v_val_841_);
lean_dec(v_val_841_);
return v___x_843_;
}
}
}
else
{
uint8_t v___x_844_; 
lean_dec_ref(v___x_837_);
lean_dec(v_val_836_);
v___x_844_ = 0;
return v___x_844_;
}
}
else
{
uint8_t v___x_845_; 
lean_dec(v___x_837_);
lean_dec(v_val_836_);
v___x_845_ = 0;
return v___x_845_;
}
}
else
{
uint8_t v___x_846_; 
lean_dec(v___x_835_);
v___x_846_ = 0;
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed(lean_object* v_hoverPos_847_, lean_object* v_i_848_){
_start:
{
uint8_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(v_hoverPos_847_, v_i_848_);
lean_dec_ref(v_i_848_);
lean_dec(v_hoverPos_847_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt(lean_object* v_infoTree_851_, lean_object* v_hoverPos_852_){
_start:
{
lean_object* v___f_853_; lean_object* v___x_854_; 
v___f_853_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed), 2, 1);
lean_closure_set(v___f_853_, 0, v_hoverPos_852_);
v___x_854_ = l_Lean_Elab_InfoTree_smallestInfo_x3f(v___f_853_, v_infoTree_851_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v___x_855_; 
v___x_855_ = lean_box(0);
return v___x_855_;
}
else
{
lean_object* v_val_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_880_; 
v_val_856_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_880_ == 0)
{
v___x_858_ = v___x_854_;
v_isShared_859_ = v_isSharedCheck_880_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_val_856_);
lean_dec(v___x_854_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_880_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_fst_860_; lean_object* v_snd_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_879_; 
v_fst_860_ = lean_ctor_get(v_val_856_, 0);
v_snd_861_ = lean_ctor_get(v_val_856_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v_val_856_);
if (v_isSharedCheck_879_ == 0)
{
v___x_863_ = v_val_856_;
v_isShared_864_ = v_isSharedCheck_879_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_snd_861_);
lean_inc(v_fst_860_);
lean_dec(v_val_856_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_879_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___y_866_; 
if (lean_obj_tag(v_snd_861_) == 1)
{
lean_object* v_i_873_; lean_object* v_expectedType_x3f_874_; 
v_i_873_ = lean_ctor_get(v_snd_861_, 0);
lean_inc_ref(v_i_873_);
lean_dec_ref(v_snd_861_);
v_expectedType_x3f_874_ = lean_ctor_get(v_i_873_, 2);
lean_inc(v_expectedType_x3f_874_);
lean_dec_ref(v_i_873_);
if (lean_obj_tag(v_expectedType_x3f_874_) == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_obj_once(&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__6, &l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__6_once, _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__6);
v___x_876_ = l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(v___x_875_);
v___y_866_ = v___x_876_;
goto v___jp_865_;
}
else
{
lean_object* v_val_877_; 
v_val_877_ = lean_ctor_get(v_expectedType_x3f_874_, 0);
lean_inc(v_val_877_);
lean_dec_ref(v_expectedType_x3f_874_);
v___y_866_ = v_val_877_;
goto v___jp_865_;
}
}
else
{
lean_object* v___x_878_; 
lean_del_object(v___x_863_);
lean_dec(v_snd_861_);
lean_dec(v_fst_860_);
lean_del_object(v___x_858_);
v___x_878_ = lean_box(0);
return v___x_878_;
}
v___jp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v___y_866_);
v___x_868_ = v___x_863_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_fst_860_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___y_866_);
v___x_868_ = v_reuseFailAlloc_872_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_870_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_868_);
v___x_870_ = v___x_858_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(lean_object* v_f_881_, lean_object* v_leadingToken_x3f_882_, lean_object* v_acc_883_, lean_object* v_stx_884_){
_start:
{
lean_object* v___f_885_; lean_object* v___f_886_; lean_object* v___f_887_; lean_object* v___f_888_; lean_object* v___f_889_; lean_object* v___f_890_; lean_object* v___f_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v_acc_895_; 
v___f_885_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0));
v___f_886_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1));
v___f_887_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2));
v___f_888_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3));
v___f_889_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4));
v___f_890_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5));
v___f_891_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6));
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v___f_885_);
lean_ctor_set(v___x_892_, 1, v___f_886_);
v___x_893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v___f_887_);
lean_ctor_set(v___x_893_, 2, v___f_888_);
lean_ctor_set(v___x_893_, 3, v___f_889_);
lean_ctor_set(v___x_893_, 4, v___f_890_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v___f_891_);
lean_inc(v_f_881_);
lean_inc(v_stx_884_);
lean_inc(v_leadingToken_x3f_882_);
v_acc_895_ = lean_apply_3(v_f_881_, v_acc_883_, v_leadingToken_x3f_882_, v_stx_884_);
switch(lean_obj_tag(v_stx_884_))
{
case 0:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec_ref(v___x_894_);
lean_dec(v_leadingToken_x3f_882_);
lean_dec(v_f_881_);
v___x_896_ = lean_box(0);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v_acc_895_);
return v___x_897_;
}
case 1:
{
lean_object* v_args_898_; lean_object* v___f_899_; lean_object* v_lastToken_x3f_900_; lean_object* v___x_901_; size_t v_sz_902_; size_t v___x_903_; lean_object* v___x_904_; lean_object* v_fst_905_; lean_object* v_snd_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
v_args_898_ = lean_ctor_get(v_stx_884_, 2);
lean_inc_ref(v_args_898_);
lean_dec_ref(v_stx_884_);
v___f_899_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0), 5, 2);
lean_closure_set(v___f_899_, 0, v_f_881_);
lean_closure_set(v___f_899_, 1, v_leadingToken_x3f_882_);
v_lastToken_x3f_900_ = lean_box(0);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v_acc_895_);
lean_ctor_set(v___x_901_, 1, v_lastToken_x3f_900_);
v_sz_902_ = lean_array_size(v_args_898_);
v___x_903_ = ((size_t)0ULL);
v___x_904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_894_, v_args_898_, v___f_899_, v_sz_902_, v___x_903_, v___x_901_);
v_fst_905_ = lean_ctor_get(v___x_904_, 0);
v_snd_906_ = lean_ctor_get(v___x_904_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_904_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_snd_906_);
lean_inc(v_fst_905_);
lean_dec(v___x_904_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 1, v_fst_905_);
lean_ctor_set(v___x_908_, 0, v_snd_906_);
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_snd_906_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_fst_905_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
default: 
{
lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec_ref(v___x_894_);
lean_dec(v_leadingToken_x3f_882_);
lean_dec(v_f_881_);
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v_stx_884_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v_acc_895_);
return v___x_915_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0(lean_object* v_f_916_, lean_object* v_leadingToken_x3f_917_, lean_object* v_a_918_, lean_object* v_x_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v_fst_926_; lean_object* v_snd_927_; lean_object* v___y_929_; 
v_fst_926_ = lean_ctor_get(v___y_920_, 0);
lean_inc(v_fst_926_);
v_snd_927_ = lean_ctor_get(v___y_920_, 1);
lean_inc(v_snd_927_);
lean_dec_ref(v___y_920_);
if (lean_obj_tag(v_snd_927_) == 0)
{
v___y_929_ = v_leadingToken_x3f_917_;
goto v___jp_928_;
}
else
{
lean_dec(v_leadingToken_x3f_917_);
lean_inc_ref(v_snd_927_);
v___y_929_ = v_snd_927_;
goto v___jp_928_;
}
v___jp_921_:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v___y_922_);
lean_ctor_set(v___x_924_, 1, v___y_923_);
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
return v___x_925_;
}
v___jp_928_:
{
lean_object* v___x_930_; lean_object* v_fst_931_; 
v___x_930_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_916_, v___y_929_, v_fst_926_, v_a_918_);
v_fst_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_fst_931_);
if (lean_obj_tag(v_fst_931_) == 0)
{
lean_object* v_snd_932_; 
v_snd_932_ = lean_ctor_get(v___x_930_, 1);
lean_inc(v_snd_932_);
lean_dec_ref(v___x_930_);
v___y_922_ = v_snd_932_;
v___y_923_ = v_snd_927_;
goto v___jp_921_;
}
else
{
lean_object* v_snd_933_; 
lean_dec(v_snd_927_);
v_snd_933_ = lean_ctor_get(v___x_930_, 1);
lean_inc(v_snd_933_);
lean_dec_ref(v___x_930_);
v___y_922_ = v_snd_933_;
v___y_923_ = v_fst_931_;
goto v___jp_921_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(lean_object* v_00_u03b1_934_, lean_object* v_f_935_, lean_object* v_inst_936_, lean_object* v_leadingToken_x3f_937_, lean_object* v_acc_938_, lean_object* v_stx_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_935_, v_leadingToken_x3f_937_, v_acc_938_, v_stx_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___boxed(lean_object* v_00_u03b1_941_, lean_object* v_f_942_, lean_object* v_inst_943_, lean_object* v_leadingToken_x3f_944_, lean_object* v_acc_945_, lean_object* v_stx_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(v_00_u03b1_941_, v_f_942_, v_inst_943_, v_leadingToken_x3f_944_, v_acc_945_, v_stx_946_);
lean_dec(v_inst_943_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(lean_object* v_f_948_, lean_object* v_init_949_, lean_object* v_stx_950_){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v_snd_953_; 
v___x_951_ = lean_box(0);
v___x_952_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_948_, v___x_951_, v_init_949_, v_stx_950_);
v_snd_953_ = lean_ctor_get(v___x_952_, 1);
lean_inc(v_snd_953_);
lean_dec_ref(v___x_952_);
return v_snd_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(lean_object* v_00_u03b1_954_, lean_object* v_inst_955_, lean_object* v_f_956_, lean_object* v_init_957_, lean_object* v_stx_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(v_f_956_, v_init_957_, v_stx_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___boxed(lean_object* v_00_u03b1_960_, lean_object* v_inst_961_, lean_object* v_f_962_, lean_object* v_init_963_, lean_object* v_stx_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(v_00_u03b1_960_, v_inst_961_, v_f_962_, v_init_963_, v_stx_964_);
lean_dec(v_inst_961_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(lean_object* v_p_966_, lean_object* v_foundStx_x3f_967_, lean_object* v_leadingToken_x3f_968_, lean_object* v_stx_969_){
_start:
{
if (lean_obj_tag(v_foundStx_x3f_967_) == 0)
{
lean_object* v___x_970_; uint8_t v___x_971_; 
lean_inc(v_stx_969_);
v___x_970_ = lean_apply_2(v_p_966_, v_leadingToken_x3f_968_, v_stx_969_);
v___x_971_ = lean_unbox(v___x_970_);
if (v___x_971_ == 0)
{
lean_dec(v_stx_969_);
return v_foundStx_x3f_967_;
}
else
{
lean_object* v___x_972_; 
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v_stx_969_);
return v___x_972_;
}
}
else
{
lean_dec(v_stx_969_);
lean_dec(v_leadingToken_x3f_968_);
lean_dec_ref(v_p_966_);
lean_inc_ref(v_foundStx_x3f_967_);
return v_foundStx_x3f_967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed(lean_object* v_p_973_, lean_object* v_foundStx_x3f_974_, lean_object* v_leadingToken_x3f_975_, lean_object* v_stx_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(v_p_973_, v_foundStx_x3f_974_, v_leadingToken_x3f_975_, v_stx_976_);
lean_dec(v_foundStx_x3f_974_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f(lean_object* v_p_978_, lean_object* v_stx_979_){
_start:
{
lean_object* v___f_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___f_980_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_980_, 0, v_p_978_);
v___x_981_ = lean_box(0);
v___x_982_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(v___f_980_, v___x_981_, v_stx_979_);
return v___x_982_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(uint8_t v___y_983_, lean_object* v_hoverPos_984_, lean_object* v_as_985_, size_t v_i_986_, size_t v_stop_987_){
_start:
{
uint8_t v___x_988_; 
v___x_988_ = lean_usize_dec_eq(v_i_986_, v_stop_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v_fst_990_; lean_object* v_snd_991_; lean_object* v___x_992_; uint8_t v___x_993_; uint8_t v___y_995_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_989_ = lean_array_uget_borrowed(v_as_985_, v_i_986_);
v_fst_990_ = lean_ctor_get(v___x_989_, 0);
v_snd_991_ = lean_ctor_get(v___x_989_, 1);
v___x_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = 1;
v___x_999_ = lean_unsigned_to_nat(2u);
v___x_1000_ = lean_nat_mod(v_snd_991_, v___x_999_);
v___x_1001_ = lean_nat_dec_eq(v___x_1000_, v___x_992_);
lean_dec(v___x_1000_);
if (v___x_1001_ == 0)
{
uint8_t v___x_1002_; 
v___x_1002_ = l_Lean_Syntax_isAtom(v_fst_990_);
if (v___x_1002_ == 0)
{
v___y_995_ = v___y_983_;
goto v___jp_994_;
}
else
{
if (v___x_1001_ == 0)
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_Syntax_getTailPos_x3f(v_fst_990_, v___x_1001_);
if (lean_obj_tag(v___x_1003_) == 1)
{
lean_object* v_val_1004_; uint8_t v___x_1005_; 
v_val_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_val_1004_);
lean_dec_ref(v___x_1003_);
v___x_1005_ = lean_nat_dec_le(v_val_1004_, v_hoverPos_984_);
if (v___x_1005_ == 0)
{
lean_dec(v_val_1004_);
v___y_995_ = v___x_1005_;
goto v___jp_994_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1006_ = l_Lean_Syntax_getTrailingSize(v_fst_990_);
v___x_1007_ = lean_nat_add(v_val_1004_, v___x_1006_);
lean_dec(v___x_1006_);
lean_dec(v_val_1004_);
v___x_1008_ = lean_nat_dec_le(v_hoverPos_984_, v___x_1007_);
lean_dec(v___x_1007_);
v___y_995_ = v___x_1008_;
goto v___jp_994_;
}
}
else
{
lean_dec(v___x_1003_);
v___y_995_ = v___x_1001_;
goto v___jp_994_;
}
}
else
{
v___y_995_ = v___y_983_;
goto v___jp_994_;
}
}
}
else
{
v___y_995_ = v___y_983_;
goto v___jp_994_;
}
v___jp_994_:
{
if (v___y_995_ == 0)
{
size_t v___x_996_; size_t v___x_997_; 
v___x_996_ = ((size_t)1ULL);
v___x_997_ = lean_usize_add(v_i_986_, v___x_996_);
v_i_986_ = v___x_997_;
goto _start;
}
else
{
return v___x_993_;
}
}
}
else
{
uint8_t v___x_1009_; 
v___x_1009_ = 0;
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0___boxed(lean_object* v___y_1010_, lean_object* v_hoverPos_1011_, lean_object* v_as_1012_, lean_object* v_i_1013_, lean_object* v_stop_1014_){
_start:
{
uint8_t v___y_2411__boxed_1015_; size_t v_i_boxed_1016_; size_t v_stop_boxed_1017_; uint8_t v_res_1018_; lean_object* v_r_1019_; 
v___y_2411__boxed_1015_ = lean_unbox(v___y_1010_);
v_i_boxed_1016_ = lean_unbox_usize(v_i_1013_);
lean_dec(v_i_1013_);
v_stop_boxed_1017_ = lean_unbox_usize(v_stop_1014_);
lean_dec(v_stop_1014_);
v_res_1018_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(v___y_2411__boxed_1015_, v_hoverPos_1011_, v_as_1012_, v_i_boxed_1016_, v_stop_boxed_1017_);
lean_dec_ref(v_as_1012_);
lean_dec(v_hoverPos_1011_);
v_r_1019_ = lean_box(v_res_1018_);
return v_r_1019_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(uint8_t v___x_1026_, uint8_t v_isCursorOnWhitespace_1027_, uint8_t v_isCursorInProperWhitespace_1028_, lean_object* v_fileMap_1029_, lean_object* v_hoverFilePos_1030_, lean_object* v_hoverPos_1031_, lean_object* v_leadingToken_x3f_1032_, lean_object* v_stx_1033_){
_start:
{
uint8_t v___y_1035_; 
if (lean_obj_tag(v_leadingToken_x3f_1032_) == 1)
{
lean_object* v_val_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_val_1042_ = lean_ctor_get(v_leadingToken_x3f_1032_, 0);
lean_inc(v_stx_1033_);
v___x_1043_ = l_Lean_Syntax_getKind(v_stx_1033_);
v___x_1044_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1));
v___x_1045_ = lean_name_eq(v___x_1043_, v___x_1044_);
lean_dec(v___x_1043_);
if (v___x_1045_ == 0)
{
lean_dec(v_stx_1033_);
lean_dec_ref(v_fileMap_1029_);
return v___x_1026_;
}
else
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_Syntax_getTailPos_x3f(v_val_1042_, v_isCursorOnWhitespace_1027_);
if (lean_obj_tag(v___x_1046_) == 1)
{
lean_object* v_val_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v_fieldsAndSeps_1050_; uint8_t v___y_1052_; lean_object* v___y_1060_; lean_object* v___x_1066_; 
v_val_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_val_1047_);
lean_dec_ref(v___x_1046_);
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = l_Lean_Syntax_getArg(v_stx_1033_, v___x_1048_);
v_fieldsAndSeps_1050_ = l_Lean_Syntax_getArgs(v___x_1049_);
lean_dec(v___x_1049_);
v___x_1066_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1033_, v_isCursorOnWhitespace_1027_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_val_1042_, v_isCursorOnWhitespace_1027_);
v___y_1060_ = v___x_1067_;
goto v___jp_1059_;
}
else
{
v___y_1060_ = v___x_1066_;
goto v___jp_1059_;
}
v___jp_1051_:
{
if (v___y_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1053_ = l_Array_zipIdx___redArg(v_fieldsAndSeps_1050_, v___x_1048_);
lean_dec_ref(v_fieldsAndSeps_1050_);
v___x_1054_ = lean_array_get_size(v___x_1053_);
v___x_1055_ = lean_nat_dec_lt(v___x_1048_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_dec_ref(v___x_1053_);
v___y_1035_ = v___y_1052_;
goto v___jp_1034_;
}
else
{
if (v___x_1055_ == 0)
{
lean_dec_ref(v___x_1053_);
v___y_1035_ = v___y_1052_;
goto v___jp_1034_;
}
else
{
size_t v___x_1056_; size_t v___x_1057_; uint8_t v___x_1058_; 
v___x_1056_ = ((size_t)0ULL);
v___x_1057_ = lean_usize_of_nat(v___x_1054_);
v___x_1058_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(v___y_1052_, v_hoverPos_1031_, v___x_1053_, v___x_1056_, v___x_1057_);
lean_dec_ref(v___x_1053_);
if (v___x_1058_ == 0)
{
v___y_1035_ = v___x_1058_;
goto v___jp_1034_;
}
else
{
lean_dec(v_stx_1033_);
lean_dec_ref(v_fileMap_1029_);
return v_isCursorOnWhitespace_1027_;
}
}
}
}
else
{
lean_dec_ref(v_fieldsAndSeps_1050_);
lean_dec(v_stx_1033_);
lean_dec_ref(v_fileMap_1029_);
return v_isCursorOnWhitespace_1027_;
}
}
v___jp_1059_:
{
if (lean_obj_tag(v___y_1060_) == 1)
{
lean_object* v_val_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v_val_1061_ = lean_ctor_get(v___y_1060_, 0);
lean_inc(v_val_1061_);
lean_dec_ref(v___y_1060_);
v___x_1062_ = lean_array_get_size(v_fieldsAndSeps_1050_);
v___x_1063_ = lean_nat_dec_eq(v___x_1062_, v___x_1048_);
if (v___x_1063_ == 0)
{
lean_dec(v_val_1061_);
lean_dec(v_val_1047_);
v___y_1052_ = v___x_1063_;
goto v___jp_1051_;
}
else
{
lean_object* v_outerBounds_1064_; uint8_t v___x_1065_; 
v_outerBounds_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_outerBounds_1064_, 0, v_val_1047_);
lean_ctor_set(v_outerBounds_1064_, 1, v_val_1061_);
v___x_1065_ = l_Lean_Syntax_Range_contains(v_outerBounds_1064_, v_hoverPos_1031_, v_isCursorOnWhitespace_1027_);
lean_dec_ref(v_outerBounds_1064_);
v___y_1052_ = v___x_1065_;
goto v___jp_1051_;
}
}
else
{
lean_dec(v___y_1060_);
lean_dec_ref(v_fieldsAndSeps_1050_);
lean_dec(v_val_1047_);
lean_dec(v_stx_1033_);
lean_dec_ref(v_fileMap_1029_);
return v___x_1026_;
}
}
}
else
{
lean_dec(v___x_1046_);
lean_dec(v_stx_1033_);
lean_dec_ref(v_fileMap_1029_);
return v___x_1026_;
}
}
}
else
{
lean_dec(v_stx_1033_);
lean_dec_ref(v_fileMap_1029_);
return v___x_1026_;
}
v___jp_1034_:
{
if (v_isCursorInProperWhitespace_1028_ == 0)
{
lean_dec(v_stx_1033_);
lean_dec_ref(v_fileMap_1029_);
return v___y_1035_;
}
else
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Lean_Syntax_getPos_x3f(v_stx_1033_, v___y_1035_);
lean_dec(v_stx_1033_);
if (lean_obj_tag(v___x_1036_) == 1)
{
lean_object* v_val_1037_; lean_object* v___x_1038_; lean_object* v_column_1039_; lean_object* v_column_1040_; uint8_t v_isCursorInBlock_1041_; 
v_val_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_val_1037_);
lean_dec_ref(v___x_1036_);
v___x_1038_ = l_Lean_FileMap_toPosition(v_fileMap_1029_, v_val_1037_);
lean_dec(v_val_1037_);
v_column_1039_ = lean_ctor_get(v___x_1038_, 1);
lean_inc(v_column_1039_);
lean_dec_ref(v___x_1038_);
v_column_1040_ = lean_ctor_get(v_hoverFilePos_1030_, 1);
v_isCursorInBlock_1041_ = lean_nat_dec_eq(v_column_1040_, v_column_1039_);
lean_dec(v_column_1039_);
return v_isCursorInBlock_1041_;
}
else
{
lean_dec(v___x_1036_);
lean_dec_ref(v_fileMap_1029_);
return v___y_1035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___boxed(lean_object* v___x_1068_, lean_object* v_isCursorOnWhitespace_1069_, lean_object* v_isCursorInProperWhitespace_1070_, lean_object* v_fileMap_1071_, lean_object* v_hoverFilePos_1072_, lean_object* v_hoverPos_1073_, lean_object* v_leadingToken_x3f_1074_, lean_object* v_stx_1075_){
_start:
{
uint8_t v___x_2473__boxed_1076_; uint8_t v_isCursorOnWhitespace_boxed_1077_; uint8_t v_isCursorInProperWhitespace_boxed_1078_; uint8_t v_res_1079_; lean_object* v_r_1080_; 
v___x_2473__boxed_1076_ = lean_unbox(v___x_1068_);
v_isCursorOnWhitespace_boxed_1077_ = lean_unbox(v_isCursorOnWhitespace_1069_);
v_isCursorInProperWhitespace_boxed_1078_ = lean_unbox(v_isCursorInProperWhitespace_1070_);
v_res_1079_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(v___x_2473__boxed_1076_, v_isCursorOnWhitespace_boxed_1077_, v_isCursorInProperWhitespace_boxed_1078_, v_fileMap_1071_, v_hoverFilePos_1072_, v_hoverPos_1073_, v_leadingToken_x3f_1074_, v_stx_1075_);
lean_dec(v_leadingToken_x3f_1074_);
lean_dec(v_hoverPos_1073_);
lean_dec_ref(v_hoverFilePos_1072_);
v_r_1080_ = lean_box(v_res_1079_);
return v_r_1080_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(lean_object* v_fileMap_1081_, lean_object* v_hoverPos_1082_, lean_object* v_cmdStx_1083_){
_start:
{
uint8_t v_isCursorOnWhitespace_1084_; 
v_isCursorOnWhitespace_1084_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_1081_, v_hoverPos_1082_);
if (v_isCursorOnWhitespace_1084_ == 0)
{
lean_dec(v_cmdStx_1083_);
lean_dec(v_hoverPos_1082_);
lean_dec_ref(v_fileMap_1081_);
return v_isCursorOnWhitespace_1084_;
}
else
{
uint8_t v_isCursorInProperWhitespace_1085_; uint8_t v___x_1086_; lean_object* v_hoverFilePos_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___f_1091_; lean_object* v___x_1092_; 
v_isCursorInProperWhitespace_1085_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_1081_, v_hoverPos_1082_);
v___x_1086_ = 0;
lean_inc_ref(v_fileMap_1081_);
v_hoverFilePos_1087_ = l_Lean_FileMap_toPosition(v_fileMap_1081_, v_hoverPos_1082_);
v___x_1088_ = lean_box(v___x_1086_);
v___x_1089_ = lean_box(v_isCursorOnWhitespace_1084_);
v___x_1090_ = lean_box(v_isCursorInProperWhitespace_1085_);
v___f_1091_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___boxed), 8, 6);
lean_closure_set(v___f_1091_, 0, v___x_1088_);
lean_closure_set(v___f_1091_, 1, v___x_1089_);
lean_closure_set(v___f_1091_, 2, v___x_1090_);
lean_closure_set(v___f_1091_, 3, v_fileMap_1081_);
lean_closure_set(v___f_1091_, 4, v_hoverFilePos_1087_);
lean_closure_set(v___f_1091_, 5, v_hoverPos_1082_);
v___x_1092_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f(v___f_1091_, v_cmdStx_1083_);
if (lean_obj_tag(v___x_1092_) == 0)
{
return v___x_1086_;
}
else
{
lean_dec_ref(v___x_1092_);
return v_isCursorOnWhitespace_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___boxed(lean_object* v_fileMap_1093_, lean_object* v_hoverPos_1094_, lean_object* v_cmdStx_1095_){
_start:
{
uint8_t v_res_1096_; lean_object* v_r_1097_; 
v_res_1096_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(v_fileMap_1093_, v_hoverPos_1094_, v_cmdStx_1095_);
v_r_1097_ = lean_box(v_res_1096_);
return v_r_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticFieldCompletion_x3f(lean_object* v_fileMap_1098_, lean_object* v_hoverPos_1099_, lean_object* v_cmdStx_1100_, lean_object* v_infoTree_1101_){
_start:
{
uint8_t v___x_1102_; 
lean_inc(v_hoverPos_1099_);
v___x_1102_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(v_fileMap_1098_, v_hoverPos_1099_, v_cmdStx_1100_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; 
lean_dec_ref(v_infoTree_1101_);
lean_dec(v_hoverPos_1099_);
v___x_1103_ = lean_box(0);
return v___x_1103_;
}
else
{
lean_object* v___x_1104_; 
v___x_1104_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt(v_infoTree_1101_, v_hoverPos_1099_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_box(0);
return v___x_1105_;
}
else
{
lean_object* v_val_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1128_; 
v_val_1106_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1108_ = v___x_1104_;
v_isShared_1109_ = v_isSharedCheck_1128_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_val_1106_);
lean_dec(v___x_1104_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1128_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_fst_1110_; lean_object* v_snd_1111_; lean_object* v___x_1112_; 
v_fst_1110_ = lean_ctor_get(v_val_1106_, 0);
lean_inc(v_fst_1110_);
v_snd_1111_ = lean_ctor_get(v_val_1106_, 1);
lean_inc(v_snd_1111_);
lean_dec(v_val_1106_);
v___x_1112_ = l_Lean_Expr_getAppFn(v_snd_1111_);
lean_dec(v_snd_1111_);
if (lean_obj_tag(v___x_1112_) == 4)
{
lean_object* v_toCommandContextInfo_1113_; lean_object* v_declName_1114_; lean_object* v_env_1115_; uint8_t v___x_1116_; 
v_toCommandContextInfo_1113_ = lean_ctor_get(v_fst_1110_, 0);
v_declName_1114_ = lean_ctor_get(v___x_1112_, 0);
lean_inc_n(v_declName_1114_, 2);
lean_dec_ref(v___x_1112_);
v_env_1115_ = lean_ctor_get(v_toCommandContextInfo_1113_, 0);
lean_inc_ref(v_env_1115_);
v___x_1116_ = l_Lean_isStructure(v_env_1115_, v_declName_1114_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_dec(v_declName_1114_);
lean_dec(v_fst_1110_);
lean_del_object(v___x_1108_);
v___x_1117_ = lean_box(0);
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1118_ = lean_box(0);
v___x_1119_ = lean_box(0);
v___x_1120_ = lean_box(0);
v___x_1121_ = l_Lean_LocalContext_empty;
v___x_1122_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1119_);
lean_ctor_set(v___x_1122_, 1, v___x_1120_);
lean_ctor_set(v___x_1122_, 2, v___x_1121_);
lean_ctor_set(v___x_1122_, 3, v_declName_1114_);
v___x_1123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1118_);
lean_ctor_set(v___x_1123_, 1, v_fst_1110_);
lean_ctor_set(v___x_1123_, 2, v___x_1122_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1123_);
v___x_1125_ = v___x_1108_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
lean_object* v___x_1127_; 
lean_dec_ref(v___x_1112_);
lean_dec(v_fst_1110_);
lean_del_object(v___x_1108_);
v___x_1127_ = lean_box(0);
return v___x_1127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findSyntheticCompletions(lean_object* v_fileMap_1131_, lean_object* v_hoverPos_1132_, lean_object* v_cmdStx_1133_, lean_object* v_infoTree_1134_){
_start:
{
lean_object* v___y_1136_; lean_object* v___x_1142_; 
lean_inc_ref(v_infoTree_1134_);
lean_inc(v_cmdStx_1133_);
lean_inc_ref(v_fileMap_1131_);
v___x_1142_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(v_fileMap_1131_, v_hoverPos_1132_, v_cmdStx_1133_, v_infoTree_1134_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v___x_1143_; 
lean_inc_ref(v_infoTree_1134_);
lean_inc(v_hoverPos_1132_);
v___x_1143_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticFieldCompletion_x3f(v_fileMap_1131_, v_hoverPos_1132_, v_cmdStx_1133_, v_infoTree_1134_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v___x_1144_; 
v___x_1144_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(v_hoverPos_1132_, v_infoTree_1134_);
v___y_1136_ = v___x_1144_;
goto v___jp_1135_;
}
else
{
lean_dec_ref(v_infoTree_1134_);
lean_dec(v_hoverPos_1132_);
v___y_1136_ = v___x_1143_;
goto v___jp_1135_;
}
}
else
{
lean_dec_ref(v_infoTree_1134_);
lean_dec(v_cmdStx_1133_);
lean_dec(v_hoverPos_1132_);
lean_dec_ref(v_fileMap_1131_);
v___y_1136_ = v___x_1142_;
goto v___jp_1135_;
}
v___jp_1135_:
{
if (lean_obj_tag(v___y_1136_) == 0)
{
lean_object* v___x_1137_; 
v___x_1137_ = ((lean_object*)(l_Lean_Server_Completion_findSyntheticCompletions___closed__0));
return v___x_1137_;
}
else
{
lean_object* v_val_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_val_1138_ = lean_ctor_get(v___y_1136_, 0);
lean_inc(v_val_1138_);
lean_dec_ref(v___y_1136_);
v___x_1139_ = lean_unsigned_to_nat(1u);
v___x_1140_ = lean_mk_empty_array_with_capacity(v___x_1139_);
v___x_1141_ = lean_array_push(v___x_1140_, v_val_1138_);
return v___x_1141_;
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
