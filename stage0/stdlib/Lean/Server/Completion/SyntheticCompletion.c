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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
return v_x_276_;
}
else
{
lean_object* v_head_277_; lean_object* v_tail_278_; uint8_t v___y_280_; lean_object* v_fst_282_; lean_object* v___x_283_; uint8_t v___x_284_; uint8_t v___y_286_; 
v_head_277_ = lean_ctor_get(v_x_276_, 0);
v_tail_278_ = lean_ctor_get(v_x_276_, 1);
v_fst_282_ = lean_ctor_get(v_head_277_, 0);
v___x_283_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
lean_inc(v_fst_282_);
v___x_284_ = l_Lean_Syntax_isOfKind(v_fst_282_, v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6));
lean_inc(v_fst_282_);
v___x_289_ = l_Lean_Syntax_isOfKind(v_fst_282_, v___x_288_);
if (v___x_289_ == 0)
{
v___y_286_ = v___x_284_;
goto v___jp_285_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = l_Lean_Syntax_getArg(v_fst_282_, v___x_290_);
v___x_292_ = l_Lean_Syntax_isOfKind(v___x_291_, v___x_283_);
if (v___x_292_ == 0)
{
v___y_286_ = v___x_292_;
goto v___jp_285_;
}
else
{
v___y_280_ = v___x_284_;
goto v___jp_279_;
}
}
}
else
{
return v_x_276_;
}
v___jp_279_:
{
if (v___y_280_ == 0)
{
return v_x_276_;
}
else
{
lean_inc(v_tail_278_);
lean_dec_ref(v_x_276_);
v_x_276_ = v_tail_278_;
goto _start;
}
}
v___jp_285_:
{
if (v___y_286_ == 0)
{
lean_inc(v_tail_278_);
lean_dec_ref(v_x_276_);
v_x_276_ = v_tail_278_;
goto _start;
}
else
{
v___y_280_ = v___x_284_;
goto v___jp_279_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(lean_object* v_x_299_){
_start:
{
if (lean_obj_tag(v_x_299_) == 0)
{
uint8_t v___x_300_; 
v___x_300_ = 0;
return v___x_300_;
}
else
{
lean_object* v_head_301_; lean_object* v_tail_302_; uint8_t v___y_304_; lean_object* v_fst_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_head_301_ = lean_ctor_get(v_x_299_, 0);
lean_inc(v_head_301_);
v_tail_302_ = lean_ctor_get(v_x_299_, 1);
lean_inc(v_tail_302_);
lean_dec_ref(v_x_299_);
v_fst_306_ = lean_ctor_get(v_head_301_, 0);
lean_inc_n(v_fst_306_, 2);
lean_dec(v_head_301_);
v___x_307_ = ((lean_object*)(l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1));
v___x_308_ = l_Lean_Syntax_isOfKind(v_fst_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_dec(v_fst_306_);
v___y_304_ = v___x_308_;
goto v___jp_303_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = l_Lean_Syntax_getArg(v_fst_306_, v___x_309_);
lean_dec(v_fst_306_);
v___x_311_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
v___x_312_ = l_Lean_Syntax_isOfKind(v___x_310_, v___x_311_);
v___y_304_ = v___x_312_;
goto v___jp_303_;
}
v___jp_303_:
{
if (v___y_304_ == 0)
{
v_x_299_ = v_tail_302_;
goto _start;
}
else
{
lean_dec(v_tail_302_);
return v___y_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___boxed(lean_object* v_x_313_){
_start:
{
uint8_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(v_x_313_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_320_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3));
v___x_321_ = lean_unsigned_to_nat(14u);
v___x_322_ = lean_unsigned_to_nat(22u);
v___x_323_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2));
v___x_324_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1));
v___x_325_ = l_mkPanicMessageWithDecl(v___x_324_, v___x_323_, v___x_322_, v___x_321_, v___x_320_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(lean_object* v_hoverPos_326_, lean_object* v_infoTree_327_){
_start:
{
lean_object* v___x_328_; 
lean_inc(v_hoverPos_326_);
v___x_328_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f(v_hoverPos_326_, v_infoTree_327_);
if (lean_obj_tag(v___x_328_) == 1)
{
lean_object* v_val_329_; lean_object* v_fst_330_; lean_object* v_snd_331_; lean_object* v___f_332_; lean_object* v___f_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_val_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_val_329_);
lean_dec_ref(v___x_328_);
v_fst_330_ = lean_ctor_get(v_val_329_, 0);
lean_inc(v_fst_330_);
v_snd_331_ = lean_ctor_get(v_val_329_, 1);
lean_inc(v_snd_331_);
lean_dec(v_val_329_);
lean_inc(v_hoverPos_326_);
v___f_332_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_332_, 0, v_hoverPos_326_);
v___f_333_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0));
v___x_334_ = l_Lean_Elab_Info_stx(v_snd_331_);
v___x_335_ = l_Lean_Syntax_findStack_x3f(v___x_334_, v___f_332_, v___f_333_);
if (lean_obj_tag(v___x_335_) == 1)
{
lean_object* v_val_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_390_; 
v_val_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_390_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_390_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_val_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_390_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v_stack_340_; lean_object* v___x_341_; 
v_stack_340_ = l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(v_val_336_);
v___x_341_ = l_List_head_x3f___redArg(v_stack_340_);
if (lean_obj_tag(v___x_341_) == 1)
{
lean_object* v_val_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_388_; 
v_val_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_388_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_388_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_val_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_388_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v_fst_346_; uint8_t v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; uint8_t v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; uint8_t v_isDotIdCompletion_368_; lean_object* v_fst_370_; uint8_t v_snd_371_; 
v_fst_346_ = lean_ctor_get(v_val_342_, 0);
lean_inc(v_fst_346_);
lean_dec(v_val_342_);
v_isDotIdCompletion_368_ = l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(v_stack_340_);
if (v_isDotIdCompletion_368_ == 0)
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
lean_inc(v_fst_346_);
v___x_377_ = l_Lean_Syntax_isOfKind(v_fst_346_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6));
lean_inc(v_fst_346_);
v___x_379_ = l_Lean_Syntax_isOfKind(v_fst_346_, v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; 
lean_dec(v_fst_346_);
lean_del_object(v___x_344_);
lean_del_object(v___x_338_);
lean_dec(v_snd_331_);
lean_dec(v_fst_330_);
lean_dec(v_hoverPos_326_);
v___x_380_ = lean_box(0);
return v___x_380_;
}
else
{
lean_object* v___x_381_; lean_object* v_id_382_; uint8_t v___x_383_; 
v___x_381_ = lean_unsigned_to_nat(0u);
v_id_382_ = l_Lean_Syntax_getArg(v_fst_346_, v___x_381_);
lean_inc(v_id_382_);
v___x_383_ = l_Lean_Syntax_isOfKind(v_id_382_, v___x_376_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; 
lean_dec(v_id_382_);
lean_dec(v_fst_346_);
lean_del_object(v___x_344_);
lean_del_object(v___x_338_);
lean_dec(v_snd_331_);
lean_dec(v_fst_330_);
lean_dec(v_hoverPos_326_);
v___x_384_ = lean_box(0);
return v___x_384_;
}
else
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_TSyntax_getId(v_id_382_);
lean_dec(v_id_382_);
v_fst_370_ = v___x_385_;
v_snd_371_ = v___x_383_;
goto v___jp_369_;
}
}
}
else
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_TSyntax_getId(v_fst_346_);
v_fst_370_ = v___x_386_;
v_snd_371_ = v_isDotIdCompletion_368_;
goto v___jp_369_;
}
}
else
{
lean_object* v___x_387_; 
lean_dec(v_fst_346_);
lean_del_object(v___x_344_);
lean_del_object(v___x_338_);
lean_dec(v_snd_331_);
lean_dec(v_fst_330_);
lean_dec(v_hoverPos_326_);
v___x_387_ = lean_box(0);
return v___x_387_;
}
v___jp_347_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_351_ = l_Lean_Elab_Info_lctx(v_snd_331_);
lean_dec(v_snd_331_);
v___x_352_ = lean_box(0);
v___x_353_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_353_, 0, v_fst_346_);
lean_ctor_set(v___x_353_, 1, v___y_349_);
lean_ctor_set(v___x_353_, 2, v___x_351_);
lean_ctor_set(v___x_353_, 3, v___x_352_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*4, v___y_348_);
v___x_354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_354_, 0, v___y_350_);
lean_ctor_set(v___x_354_, 1, v_fst_330_);
lean_ctor_set(v___x_354_, 2, v___x_353_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_354_);
v___x_356_ = v___x_344_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
v___jp_358_:
{
uint8_t v___x_362_; 
v___x_362_ = lean_nat_dec_lt(v_hoverPos_326_, v___y_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec(v___y_361_);
lean_del_object(v___x_338_);
lean_dec(v_hoverPos_326_);
v___x_363_ = lean_box(0);
v___y_348_ = v___y_359_;
v___y_349_ = v___y_360_;
v___y_350_ = v___x_363_;
goto v___jp_347_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_364_ = lean_nat_sub(v___y_361_, v_hoverPos_326_);
lean_dec(v_hoverPos_326_);
lean_dec(v___y_361_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_364_);
v___x_366_ = v___x_338_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
v___y_348_ = v___y_359_;
v___y_349_ = v___y_360_;
v___y_350_ = v___x_366_;
goto v___jp_347_;
}
}
}
v___jp_369_:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Syntax_getTailPos_x3f(v_fst_346_, v_isDotIdCompletion_368_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_obj_once(&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4, &l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_once, _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4);
v___x_374_ = l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__2(v___x_373_);
v___y_359_ = v_snd_371_;
v___y_360_ = v_fst_370_;
v___y_361_ = v___x_374_;
goto v___jp_358_;
}
else
{
lean_object* v_val_375_; 
v_val_375_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_val_375_);
lean_dec_ref(v___x_372_);
v___y_359_ = v_snd_371_;
v___y_360_ = v_fst_370_;
v___y_361_ = v_val_375_;
goto v___jp_358_;
}
}
}
}
else
{
lean_object* v___x_389_; 
lean_dec(v___x_341_);
lean_dec(v_stack_340_);
lean_del_object(v___x_338_);
lean_dec(v_snd_331_);
lean_dec(v_fst_330_);
lean_dec(v_hoverPos_326_);
v___x_389_ = lean_box(0);
return v___x_389_;
}
}
}
else
{
lean_object* v___x_391_; 
lean_dec(v___x_335_);
lean_dec(v_snd_331_);
lean_dec(v_fst_330_);
lean_dec(v_hoverPos_326_);
v___x_391_ = lean_box(0);
return v___x_391_;
}
}
else
{
lean_object* v___x_392_; 
lean_dec(v___x_328_);
lean_dec(v_hoverPos_326_);
v___x_392_ = lean_box(0);
return v___x_392_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(lean_object* v_fileMap_393_, lean_object* v_hoverPos_394_){
_start:
{
lean_object* v_source_395_; uint8_t v___x_396_; 
v_source_395_ = lean_ctor_get(v_fileMap_393_, 0);
v___x_396_ = lean_string_utf8_at_end(v_source_395_, v_hoverPos_394_);
if (v___x_396_ == 0)
{
uint32_t v___x_397_; uint8_t v___y_399_; uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_397_ = lean_string_utf8_get(v_source_395_, v_hoverPos_394_);
v___x_404_ = 32;
v___x_405_ = lean_uint32_dec_eq(v___x_397_, v___x_404_);
if (v___x_405_ == 0)
{
uint32_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = 9;
v___x_407_ = lean_uint32_dec_eq(v___x_397_, v___x_406_);
v___y_399_ = v___x_407_;
goto v___jp_398_;
}
else
{
v___y_399_ = v___x_405_;
goto v___jp_398_;
}
v___jp_398_:
{
if (v___y_399_ == 0)
{
uint32_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 13;
v___x_401_ = lean_uint32_dec_eq(v___x_397_, v___x_400_);
if (v___x_401_ == 0)
{
uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 10;
v___x_403_ = lean_uint32_dec_eq(v___x_397_, v___x_402_);
return v___x_403_;
}
else
{
return v___x_401_;
}
}
else
{
return v___y_399_;
}
}
}
else
{
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace___boxed(lean_object* v_fileMap_408_, lean_object* v_hoverPos_409_){
_start:
{
uint8_t v_res_410_; lean_object* v_r_411_; 
v_res_410_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_408_, v_hoverPos_409_);
lean_dec(v_hoverPos_409_);
lean_dec_ref(v_fileMap_408_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(lean_object* v_fileMap_412_, lean_object* v_hoverPos_413_){
_start:
{
uint32_t v___y_415_; uint8_t v___y_416_; lean_object* v_source_421_; uint8_t v___y_431_; uint8_t v___x_432_; 
v_source_421_ = lean_ctor_get(v_fileMap_412_, 0);
v___x_432_ = lean_string_utf8_at_end(v_source_421_, v_hoverPos_413_);
if (v___x_432_ == 0)
{
uint32_t v___x_433_; uint8_t v___y_435_; uint32_t v___x_440_; uint8_t v___x_441_; 
v___x_433_ = lean_string_utf8_get(v_source_421_, v_hoverPos_413_);
v___x_440_ = 32;
v___x_441_ = lean_uint32_dec_eq(v___x_433_, v___x_440_);
if (v___x_441_ == 0)
{
uint32_t v___x_442_; uint8_t v___x_443_; 
v___x_442_ = 9;
v___x_443_ = lean_uint32_dec_eq(v___x_433_, v___x_442_);
v___y_435_ = v___x_443_;
goto v___jp_434_;
}
else
{
v___y_435_ = v___x_441_;
goto v___jp_434_;
}
v___jp_434_:
{
if (v___y_435_ == 0)
{
uint32_t v___x_436_; uint8_t v___x_437_; 
v___x_436_ = 13;
v___x_437_ = lean_uint32_dec_eq(v___x_433_, v___x_436_);
if (v___x_437_ == 0)
{
uint32_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = 10;
v___x_439_ = lean_uint32_dec_eq(v___x_433_, v___x_438_);
v___y_431_ = v___x_439_;
goto v___jp_430_;
}
else
{
v___y_431_ = v___x_437_;
goto v___jp_430_;
}
}
else
{
goto v___jp_422_;
}
}
}
else
{
v___y_431_ = v___x_432_;
goto v___jp_430_;
}
v___jp_414_:
{
if (v___y_416_ == 0)
{
uint32_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = 13;
v___x_418_ = lean_uint32_dec_eq(v___y_415_, v___x_417_);
if (v___x_418_ == 0)
{
uint32_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 10;
v___x_420_ = lean_uint32_dec_eq(v___y_415_, v___x_419_);
return v___x_420_;
}
else
{
return v___x_418_;
}
}
else
{
return v___y_416_;
}
}
v___jp_422_:
{
lean_object* v___x_423_; lean_object* v___x_424_; uint32_t v___x_425_; uint32_t v___x_426_; uint8_t v___x_427_; 
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = lean_nat_sub(v_hoverPos_413_, v___x_423_);
v___x_425_ = lean_string_utf8_get(v_source_421_, v___x_424_);
lean_dec(v___x_424_);
v___x_426_ = 32;
v___x_427_ = lean_uint32_dec_eq(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
uint32_t v___x_428_; uint8_t v___x_429_; 
v___x_428_ = 9;
v___x_429_ = lean_uint32_dec_eq(v___x_425_, v___x_428_);
v___y_415_ = v___x_425_;
v___y_416_ = v___x_429_;
goto v___jp_414_;
}
else
{
v___y_415_ = v___x_425_;
v___y_416_ = v___x_427_;
goto v___jp_414_;
}
}
v___jp_430_:
{
if (v___y_431_ == 0)
{
return v___y_431_;
}
else
{
goto v___jp_422_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace___boxed(lean_object* v_fileMap_444_, lean_object* v_hoverPos_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_444_, v_hoverPos_445_);
lean_dec(v_hoverPos_445_);
lean_dec_ref(v_fileMap_444_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(lean_object* v_stx_461_){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
lean_inc(v_stx_461_);
v___x_462_ = l_Lean_Syntax_getKind(v_stx_461_);
v___x_463_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2));
v___x_464_ = lean_name_eq(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_466_ = lean_name_eq(v___x_462_, v___x_465_);
lean_dec(v___x_462_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
lean_dec(v_stx_461_);
v___x_467_ = lean_box(0);
return v___x_467_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = l_Lean_Syntax_getArg(v_stx_461_, v___x_468_);
lean_dec(v_stx_461_);
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec(v___x_462_);
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = l_Lean_Syntax_getArg(v_stx_461_, v___x_471_);
lean_dec(v_stx_461_);
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(lean_object* v_fileMap_474_, lean_object* v_hoverPos_475_, lean_object* v_hoverFilePos_476_, lean_object* v_stx_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(v_stx_477_);
if (lean_obj_tag(v___x_478_) == 1)
{
lean_object* v_val_479_; uint8_t v___x_480_; lean_object* v___x_481_; 
v_val_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_val_479_);
lean_dec_ref(v___x_478_);
v___x_480_ = 0;
v___x_481_ = l_Lean_Syntax_getPos_x3f(v_val_479_, v___x_480_);
lean_dec(v_val_479_);
if (lean_obj_tag(v___x_481_) == 1)
{
lean_object* v_val_482_; lean_object* v___x_483_; lean_object* v_column_484_; lean_object* v_column_485_; uint8_t v___x_486_; 
v_val_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_val_482_);
lean_dec_ref(v___x_481_);
lean_inc_ref(v_fileMap_474_);
v___x_483_ = l_Lean_FileMap_toPosition(v_fileMap_474_, v_val_482_);
lean_dec(v_val_482_);
v_column_484_ = lean_ctor_get(v___x_483_, 1);
lean_inc(v_column_484_);
lean_dec_ref(v___x_483_);
v_column_485_ = lean_ctor_get(v_hoverFilePos_476_, 1);
v___x_486_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_474_, v_hoverPos_475_);
lean_dec_ref(v_fileMap_474_);
if (v___x_486_ == 0)
{
lean_dec(v_column_484_);
return v___x_486_;
}
else
{
uint8_t v_isCursorInTacticBlock_487_; 
v_isCursorInTacticBlock_487_ = lean_nat_dec_eq(v_column_485_, v_column_484_);
lean_dec(v_column_484_);
return v_isCursorInTacticBlock_487_;
}
}
else
{
lean_dec(v___x_481_);
lean_dec_ref(v_fileMap_474_);
return v___x_480_;
}
}
else
{
uint8_t v___x_488_; 
lean_dec(v___x_478_);
lean_dec_ref(v_fileMap_474_);
v___x_488_ = 0;
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation___boxed(lean_object* v_fileMap_489_, lean_object* v_hoverPos_490_, lean_object* v_hoverFilePos_491_, lean_object* v_stx_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_489_, v_hoverPos_490_, v_hoverFilePos_491_, v_stx_492_);
lean_dec_ref(v_hoverFilePos_491_);
lean_dec(v_hoverPos_490_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(lean_object* v_hoverPos_496_, lean_object* v_as_497_, size_t v_i_498_, size_t v_stop_499_){
_start:
{
uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_eq(v_i_498_, v_stop_499_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; uint8_t v___y_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_505_ = 1;
v___x_508_ = lean_array_uget_borrowed(v_as_497_, v_i_498_);
v___x_509_ = l_Lean_Syntax_getTailPos_x3f(v___x_508_, v___x_504_);
if (lean_obj_tag(v___x_509_) == 1)
{
lean_object* v_val_510_; uint8_t v___y_512_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_val_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_val_510_);
lean_dec_ref(v___x_509_);
v___x_516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___closed__0));
lean_inc(v___x_508_);
v___x_517_ = l_Lean_Syntax_isToken(v___x_516_, v___x_508_);
if (v___x_517_ == 0)
{
v___y_512_ = v___x_517_;
goto v___jp_511_;
}
else
{
uint8_t v___x_518_; 
v___x_518_ = lean_nat_dec_le(v_val_510_, v_hoverPos_496_);
v___y_512_ = v___x_518_;
goto v___jp_511_;
}
v___jp_511_:
{
if (v___y_512_ == 0)
{
lean_dec(v_val_510_);
goto v___jp_500_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_513_ = l_Lean_Syntax_getTrailingSize(v___x_508_);
v___x_514_ = lean_nat_add(v_val_510_, v___x_513_);
lean_dec(v___x_513_);
lean_dec(v_val_510_);
v___x_515_ = lean_nat_dec_le(v_hoverPos_496_, v___x_514_);
lean_dec(v___x_514_);
v___y_507_ = v___x_515_;
goto v___jp_506_;
}
}
}
else
{
lean_dec(v___x_509_);
v___y_507_ = v___x_504_;
goto v___jp_506_;
}
v___jp_506_:
{
if (v___y_507_ == 0)
{
goto v___jp_500_;
}
else
{
return v___x_505_;
}
}
}
else
{
uint8_t v___x_519_; 
v___x_519_ = 0;
return v___x_519_;
}
v___jp_500_:
{
size_t v___x_501_; size_t v___x_502_; 
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_add(v_i_498_, v___x_501_);
v_i_498_ = v___x_502_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___boxed(lean_object* v_hoverPos_520_, lean_object* v_as_521_, lean_object* v_i_522_, lean_object* v_stop_523_){
_start:
{
size_t v_i_boxed_524_; size_t v_stop_boxed_525_; uint8_t v_res_526_; lean_object* v_r_527_; 
v_i_boxed_524_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_stop_boxed_525_ = lean_unbox_usize(v_stop_523_);
lean_dec(v_stop_523_);
v_res_526_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_520_, v_as_521_, v_i_boxed_524_, v_stop_boxed_525_);
lean_dec_ref(v_as_521_);
lean_dec(v_hoverPos_520_);
v_r_527_ = lean_box(v_res_526_);
return v_r_527_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(lean_object* v_fileMap_528_, lean_object* v_hoverPos_529_, lean_object* v_stx_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(v_stx_530_);
if (lean_obj_tag(v___x_531_) == 1)
{
lean_object* v_val_532_; uint8_t v___x_533_; 
v_val_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_val_532_);
lean_dec_ref(v___x_531_);
v___x_533_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_528_, v_hoverPos_529_);
if (v___x_533_ == 0)
{
lean_dec(v_val_532_);
return v___x_533_;
}
else
{
lean_object* v_tactics_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v_tactics_534_ = l_Lean_Syntax_getArgs(v_val_532_);
lean_dec(v_val_532_);
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = lean_array_get_size(v_tactics_534_);
v___x_537_ = lean_nat_dec_lt(v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
lean_dec_ref(v_tactics_534_);
return v___x_537_;
}
else
{
if (v___x_537_ == 0)
{
lean_dec_ref(v_tactics_534_);
return v___x_537_;
}
else
{
size_t v___x_538_; size_t v___x_539_; uint8_t v___x_540_; 
v___x_538_ = ((size_t)0ULL);
v___x_539_ = lean_usize_of_nat(v___x_536_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_529_, v_tactics_534_, v___x_538_, v___x_539_);
lean_dec_ref(v_tactics_534_);
return v___x_540_;
}
}
}
}
else
{
uint8_t v___x_541_; 
lean_dec(v___x_531_);
v___x_541_ = 0;
return v___x_541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon___boxed(lean_object* v_fileMap_542_, lean_object* v_hoverPos_543_, lean_object* v_stx_544_){
_start:
{
uint8_t v_res_545_; lean_object* v_r_546_; 
v_res_545_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_542_, v_hoverPos_543_, v_stx_544_);
lean_dec(v_hoverPos_543_);
lean_dec_ref(v_fileMap_542_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(lean_object* v_fileMap_547_, lean_object* v_b_548_){
_start:
{
lean_object* v_fst_549_; lean_object* v_snd_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_572_; 
v_fst_549_ = lean_ctor_get(v_b_548_, 0);
v_snd_550_ = lean_ctor_get(v_b_548_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_b_548_);
if (v_isSharedCheck_572_ == 0)
{
v___x_552_ = v_b_548_;
v_isShared_553_ = v_isSharedCheck_572_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_snd_550_);
lean_inc(v_fst_549_);
lean_dec(v_b_548_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_572_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v_source_554_; uint8_t v___x_555_; 
v_source_554_ = lean_ctor_get(v_fileMap_547_, 0);
v___x_555_ = lean_string_utf8_at_end(v_source_554_, v_fst_549_);
if (v___x_555_ == 0)
{
uint32_t v___x_556_; uint32_t v___x_557_; uint8_t v___x_558_; 
v___x_556_ = lean_string_utf8_get(v_source_554_, v_fst_549_);
v___x_557_ = 32;
v___x_558_ = lean_uint32_dec_eq(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_560_; 
if (v_isShared_553_ == 0)
{
v___x_560_ = v___x_552_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_fst_549_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_snd_550_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
else
{
lean_object* v_p_562_; lean_object* v___x_563_; lean_object* v_n_564_; lean_object* v___x_566_; 
v_p_562_ = lean_string_utf8_next(v_source_554_, v_fst_549_);
lean_dec(v_fst_549_);
v___x_563_ = lean_unsigned_to_nat(1u);
v_n_564_ = lean_nat_add(v_snd_550_, v___x_563_);
lean_dec(v_snd_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v_n_564_);
lean_ctor_set(v___x_552_, 0, v_p_562_);
v___x_566_ = v___x_552_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_p_562_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_n_564_);
v___x_566_ = v_reuseFailAlloc_568_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
v_b_548_ = v___x_566_;
goto _start;
}
}
}
else
{
lean_object* v___x_570_; 
if (v_isShared_553_ == 0)
{
v___x_570_ = v___x_552_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_fst_549_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_snd_550_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___boxed(lean_object* v_fileMap_573_, lean_object* v_b_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(v_fileMap_573_, v_b_574_);
lean_dec_ref(v_fileMap_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(lean_object* v_fileMap_576_, lean_object* v_pos_577_){
_start:
{
lean_object* v_n_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_snd_581_; 
v_n_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_pos_577_);
lean_ctor_set(v___x_579_, 1, v_n_578_);
v___x_580_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(v_fileMap_576_, v___x_579_);
v_snd_581_ = lean_ctor_get(v___x_580_, 1);
lean_inc(v_snd_581_);
lean_dec_ref(v___x_580_);
return v_snd_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces___boxed(lean_object* v_fileMap_582_, lean_object* v_pos_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(v_fileMap_582_, v_pos_583_);
lean_dec_ref(v_fileMap_582_);
return v_res_584_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(lean_object* v_fileMap_585_, lean_object* v_hoverPos_586_, lean_object* v_leadingTokenTailPos_x3f_587_){
_start:
{
if (lean_obj_tag(v_leadingTokenTailPos_x3f_587_) == 1)
{
lean_object* v_val_588_; lean_object* v_hoverFilePos_589_; lean_object* v_line_590_; lean_object* v_column_591_; lean_object* v_tokenTailFilePos_592_; lean_object* v_line_593_; uint8_t v___x_594_; 
v_val_588_ = lean_ctor_get(v_leadingTokenTailPos_x3f_587_, 0);
lean_inc_ref_n(v_fileMap_585_, 2);
v_hoverFilePos_589_ = l_Lean_FileMap_toPosition(v_fileMap_585_, v_hoverPos_586_);
v_line_590_ = lean_ctor_get(v_hoverFilePos_589_, 0);
lean_inc(v_line_590_);
v_column_591_ = lean_ctor_get(v_hoverFilePos_589_, 1);
lean_inc(v_column_591_);
lean_dec_ref(v_hoverFilePos_589_);
v_tokenTailFilePos_592_ = l_Lean_FileMap_toPosition(v_fileMap_585_, v_val_588_);
v_line_593_ = lean_ctor_get(v_tokenTailFilePos_592_, 0);
lean_inc(v_line_593_);
lean_dec_ref(v_tokenTailFilePos_592_);
v___x_594_ = lean_nat_dec_eq(v_line_590_, v_line_593_);
lean_dec(v_line_590_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v_expectedColumn_598_; uint8_t v___x_599_; 
v___x_595_ = l_Lean_FileMap_lineStart(v_fileMap_585_, v_line_593_);
lean_dec(v_line_593_);
v___x_596_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(v_fileMap_585_, v___x_595_);
lean_dec_ref(v_fileMap_585_);
v___x_597_ = lean_unsigned_to_nat(2u);
v_expectedColumn_598_ = lean_nat_add(v___x_596_, v___x_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_nat_dec_eq(v_column_591_, v_expectedColumn_598_);
lean_dec(v_expectedColumn_598_);
lean_dec(v_column_591_);
return v___x_599_;
}
else
{
uint8_t v___x_600_; 
lean_dec(v_line_593_);
lean_dec(v_column_591_);
lean_dec_ref(v_fileMap_585_);
v___x_600_ = lean_nat_dec_le(v_val_588_, v_hoverPos_586_);
return v___x_600_;
}
}
else
{
uint8_t v___x_601_; 
lean_dec_ref(v_fileMap_585_);
v___x_601_ = 1;
return v___x_601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation___boxed(lean_object* v_fileMap_602_, lean_object* v_hoverPos_603_, lean_object* v_leadingTokenTailPos_x3f_604_){
_start:
{
uint8_t v_res_605_; lean_object* v_r_606_; 
v_res_605_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(v_fileMap_602_, v_hoverPos_603_, v_leadingTokenTailPos_x3f_604_);
lean_dec(v_leadingTokenTailPos_x3f_604_);
lean_dec(v_hoverPos_603_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(lean_object* v_a_607_){
_start:
{
switch(lean_obj_tag(v_a_607_))
{
case 0:
{
uint8_t v___x_608_; 
v___x_608_ = 1;
return v___x_608_;
}
case 1:
{
lean_object* v_args_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v_args_609_ = lean_ctor_get(v_a_607_, 2);
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_array_get_size(v_args_609_);
v___x_612_ = lean_nat_dec_lt(v___x_610_, v___x_611_);
if (v___x_612_ == 0)
{
uint8_t v___x_613_; 
v___x_613_ = 1;
return v___x_613_;
}
else
{
if (v___x_612_ == 0)
{
return v___x_612_;
}
else
{
size_t v___x_614_; size_t v___x_615_; uint8_t v___x_616_; 
v___x_614_ = ((size_t)0ULL);
v___x_615_ = lean_usize_of_nat(v___x_611_);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_args_609_, v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
return v___x_612_;
}
else
{
uint8_t v___x_617_; 
v___x_617_ = 0;
return v___x_617_;
}
}
}
}
default: 
{
uint8_t v___x_618_; 
v___x_618_ = 0;
return v___x_618_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(lean_object* v_as_619_, size_t v_i_620_, size_t v_stop_621_){
_start:
{
uint8_t v___x_622_; 
v___x_622_ = lean_usize_dec_eq(v_i_620_, v_stop_621_);
if (v___x_622_ == 0)
{
uint8_t v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_623_ = 1;
v___x_624_ = lean_array_uget_borrowed(v_as_619_, v_i_620_);
v___x_625_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v___x_624_);
if (v___x_625_ == 0)
{
return v___x_623_;
}
else
{
if (v___x_622_ == 0)
{
size_t v___x_626_; size_t v___x_627_; 
v___x_626_ = ((size_t)1ULL);
v___x_627_ = lean_usize_add(v_i_620_, v___x_626_);
v_i_620_ = v___x_627_;
goto _start;
}
else
{
return v___x_623_;
}
}
}
else
{
uint8_t v___x_629_; 
v___x_629_ = 0;
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0___boxed(lean_object* v_as_630_, lean_object* v_i_631_, lean_object* v_stop_632_){
_start:
{
size_t v_i_boxed_633_; size_t v_stop_boxed_634_; uint8_t v_res_635_; lean_object* v_r_636_; 
v_i_boxed_633_ = lean_unbox_usize(v_i_631_);
lean_dec(v_i_631_);
v_stop_boxed_634_ = lean_unbox_usize(v_stop_632_);
lean_dec(v_stop_632_);
v_res_635_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_as_630_, v_i_boxed_633_, v_stop_boxed_634_);
lean_dec_ref(v_as_630_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty___boxed(lean_object* v_a_637_){
_start:
{
uint8_t v_res_638_; lean_object* v_r_639_; 
v_res_638_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_a_637_);
lean_dec(v_a_637_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(lean_object* v_stx_646_){
_start:
{
uint8_t v___y_648_; uint8_t v___y_656_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
lean_inc(v_stx_646_);
v___x_661_ = l_Lean_Syntax_getKind(v_stx_646_);
v___x_662_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1));
v___x_663_ = lean_name_eq(v___x_661_, v___x_662_);
lean_dec(v___x_661_);
if (v___x_663_ == 0)
{
v___y_656_ = v___x_663_;
goto v___jp_655_;
}
else
{
uint8_t v___x_664_; 
v___x_664_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_stx_646_);
v___y_656_ = v___x_664_;
goto v___jp_655_;
}
v___jp_647_:
{
if (v___y_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
lean_inc(v_stx_646_);
v___x_649_ = l_Lean_Syntax_getKind(v_stx_646_);
v___x_650_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_651_ = lean_name_eq(v___x_649_, v___x_650_);
lean_dec(v___x_649_);
if (v___x_651_ == 0)
{
lean_dec(v_stx_646_);
return v___x_651_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = l_Lean_Syntax_getArg(v_stx_646_, v___x_652_);
lean_dec(v_stx_646_);
v___x_654_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v___x_653_);
lean_dec(v___x_653_);
return v___x_654_;
}
}
else
{
lean_dec(v_stx_646_);
return v___y_648_;
}
}
v___jp_655_:
{
if (v___y_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
lean_inc(v_stx_646_);
v___x_657_ = l_Lean_Syntax_getKind(v_stx_646_);
v___x_658_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2));
v___x_659_ = lean_name_eq(v___x_657_, v___x_658_);
lean_dec(v___x_657_);
if (v___x_659_ == 0)
{
v___y_648_ = v___x_659_;
goto v___jp_647_;
}
else
{
uint8_t v___x_660_; 
v___x_660_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_stx_646_);
v___y_648_ = v___x_660_;
goto v___jp_647_;
}
}
else
{
lean_dec(v_stx_646_);
return v___y_656_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___boxed(lean_object* v_stx_665_){
_start:
{
uint8_t v_res_666_; lean_object* v_r_667_; 
v_res_666_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_665_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(lean_object* v_fileMap_668_, lean_object* v_hoverPos_669_, lean_object* v_stx_670_, lean_object* v_leadingTokenTailPos_x3f_671_){
_start:
{
uint8_t v___x_672_; 
v___x_672_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_668_, v_hoverPos_669_);
if (v___x_672_ == 0)
{
lean_dec(v_stx_670_);
lean_dec_ref(v_fileMap_668_);
return v___x_672_;
}
else
{
uint8_t v___x_673_; uint8_t v___x_674_; 
v___x_673_ = 0;
lean_inc(v_stx_670_);
v___x_674_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_670_);
if (v___x_674_ == 0)
{
lean_dec(v_stx_670_);
lean_dec_ref(v_fileMap_668_);
return v___x_673_;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
lean_inc(v_stx_670_);
v___x_675_ = l_Lean_Syntax_getKind(v_stx_670_);
v___x_676_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_677_ = lean_name_eq(v___x_675_, v___x_676_);
lean_dec(v___x_675_);
if (v___x_677_ == 0)
{
uint8_t v___x_678_; 
lean_dec(v_stx_670_);
v___x_678_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(v_fileMap_668_, v_hoverPos_669_, v_leadingTokenTailPos_x3f_671_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec_ref(v_fileMap_668_);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = l_Lean_Syntax_getArg(v_stx_670_, v___x_679_);
v___x_681_ = l_Lean_Syntax_getTailPos_x3f(v___x_680_, v___x_673_);
lean_dec(v___x_680_);
if (lean_obj_tag(v___x_681_) == 1)
{
lean_object* v_val_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_val_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_val_682_);
lean_dec_ref(v___x_681_);
v___x_683_ = lean_unsigned_to_nat(2u);
v___x_684_ = l_Lean_Syntax_getArg(v_stx_670_, v___x_683_);
lean_dec(v_stx_670_);
v___x_685_ = l_Lean_Syntax_getPos_x3f(v___x_684_, v___x_673_);
lean_dec(v___x_684_);
if (lean_obj_tag(v___x_685_) == 1)
{
lean_object* v_val_686_; uint8_t v___x_687_; 
v_val_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_val_686_);
lean_dec_ref(v___x_685_);
v___x_687_ = lean_nat_dec_le(v_val_682_, v_hoverPos_669_);
lean_dec(v_val_682_);
if (v___x_687_ == 0)
{
lean_dec(v_val_686_);
return v___x_687_;
}
else
{
uint8_t v___x_688_; 
v___x_688_ = lean_nat_dec_le(v_hoverPos_669_, v_val_686_);
lean_dec(v_val_686_);
return v___x_688_;
}
}
else
{
lean_dec(v___x_685_);
lean_dec(v_val_682_);
return v___x_673_;
}
}
else
{
lean_dec(v___x_681_);
lean_dec(v_stx_670_);
return v___x_673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock___boxed(lean_object* v_fileMap_689_, lean_object* v_hoverPos_690_, lean_object* v_stx_691_, lean_object* v_leadingTokenTailPos_x3f_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_689_, v_hoverPos_690_, v_stx_691_, v_leadingTokenTailPos_x3f_692_);
lean_dec(v_leadingTokenTailPos_x3f_692_);
lean_dec(v_hoverPos_690_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(lean_object* v_fileMap_695_, lean_object* v_hoverPos_696_, lean_object* v_hoverFilePos_697_, lean_object* v_stx_698_, lean_object* v_leadingWs_699_, lean_object* v_leadingTokenTailPos_x3f_700_){
_start:
{
uint8_t v___y_702_; uint8_t v___x_718_; lean_object* v___x_719_; 
v___x_718_ = 0;
v___x_719_ = l_Lean_Syntax_getPos_x3f(v_stx_698_, v___x_718_);
if (lean_obj_tag(v___x_719_) == 1)
{
lean_object* v_val_720_; lean_object* v___x_721_; 
v_val_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_val_720_);
lean_dec_ref(v___x_719_);
v___x_721_ = l_Lean_Syntax_getTailPos_x3f(v_stx_698_, v___x_718_);
if (lean_obj_tag(v___x_721_) == 1)
{
lean_object* v_val_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_val_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_val_722_);
lean_dec_ref(v___x_721_);
v___x_723_ = lean_nat_sub(v_val_720_, v_leadingWs_699_);
lean_dec(v_val_720_);
v___x_724_ = lean_nat_dec_le(v___x_723_, v_hoverPos_696_);
lean_dec(v___x_723_);
if (v___x_724_ == 0)
{
lean_dec(v_val_722_);
v___y_702_ = v___x_724_;
goto v___jp_701_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_725_ = l_Lean_Syntax_getTrailingSize(v_stx_698_);
v___x_726_ = lean_nat_add(v_val_722_, v___x_725_);
lean_dec(v___x_725_);
lean_dec(v_val_722_);
v___x_727_ = lean_nat_dec_le(v_hoverPos_696_, v___x_726_);
lean_dec(v___x_726_);
v___y_702_ = v___x_727_;
goto v___jp_701_;
}
}
else
{
uint8_t v___x_728_; 
lean_dec(v___x_721_);
lean_dec(v_val_720_);
lean_dec(v_leadingWs_699_);
v___x_728_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_695_, v_hoverPos_696_, v_stx_698_, v_leadingTokenTailPos_x3f_700_);
lean_dec(v_leadingTokenTailPos_x3f_700_);
return v___x_728_;
}
}
else
{
uint8_t v___x_729_; 
lean_dec(v___x_719_);
lean_dec(v_leadingWs_699_);
v___x_729_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_695_, v_hoverPos_696_, v_stx_698_, v_leadingTokenTailPos_x3f_700_);
lean_dec(v_leadingTokenTailPos_x3f_700_);
return v___x_729_;
}
v___jp_701_:
{
if (v___y_702_ == 0)
{
lean_dec(v_leadingTokenTailPos_x3f_700_);
lean_dec(v_leadingWs_699_);
lean_dec(v_stx_698_);
lean_dec_ref(v_fileMap_695_);
return v___y_702_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; size_t v_sz_707_; size_t v___x_708_; lean_object* v___x_709_; lean_object* v_fst_710_; 
v___x_703_ = l_Lean_Syntax_getArgs(v_stx_698_);
v___x_704_ = lean_box(0);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v_leadingWs_699_);
lean_ctor_set(v___x_705_, 1, v_leadingTokenTailPos_x3f_700_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v_sz_707_ = lean_array_size(v___x_703_);
v___x_708_ = ((size_t)0ULL);
lean_inc_ref(v_fileMap_695_);
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_695_, v_hoverPos_696_, v_hoverFilePos_697_, v___y_702_, v___x_703_, v_sz_707_, v___x_708_, v___x_706_);
lean_dec_ref(v___x_703_);
v_fst_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_fst_710_);
if (lean_obj_tag(v_fst_710_) == 0)
{
lean_object* v_snd_711_; lean_object* v_snd_712_; uint8_t v___x_713_; 
v_snd_711_ = lean_ctor_get(v___x_709_, 1);
lean_inc(v_snd_711_);
lean_dec_ref(v___x_709_);
v_snd_712_ = lean_ctor_get(v_snd_711_, 1);
lean_inc(v_snd_712_);
lean_dec(v_snd_711_);
lean_inc(v_stx_698_);
lean_inc_ref(v_fileMap_695_);
v___x_713_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_695_, v_hoverPos_696_, v_stx_698_, v_snd_712_);
lean_dec(v_snd_712_);
if (v___x_713_ == 0)
{
uint8_t v___x_714_; 
lean_inc(v_stx_698_);
v___x_714_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_695_, v_hoverPos_696_, v_stx_698_);
if (v___x_714_ == 0)
{
uint8_t v___x_715_; 
v___x_715_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_695_, v_hoverPos_696_, v_hoverFilePos_697_, v_stx_698_);
return v___x_715_;
}
else
{
lean_dec(v_stx_698_);
lean_dec_ref(v_fileMap_695_);
return v___y_702_;
}
}
else
{
lean_dec(v_stx_698_);
lean_dec_ref(v_fileMap_695_);
return v___y_702_;
}
}
else
{
lean_object* v_val_716_; uint8_t v___x_717_; 
lean_dec_ref(v___x_709_);
lean_dec(v_stx_698_);
lean_dec_ref(v_fileMap_695_);
v_val_716_ = lean_ctor_get(v_fst_710_, 0);
lean_inc(v_val_716_);
lean_dec_ref(v_fst_710_);
v___x_717_ = lean_unbox(v_val_716_);
lean_dec(v_val_716_);
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(lean_object* v_fileMap_730_, lean_object* v_hoverPos_731_, lean_object* v_hoverFilePos_732_, uint8_t v___y_733_, lean_object* v_as_734_, size_t v_sz_735_, size_t v_i_736_, lean_object* v_b_737_){
_start:
{
uint8_t v___x_738_; 
v___x_738_ = lean_usize_dec_lt(v_i_736_, v_sz_735_);
if (v___x_738_ == 0)
{
lean_dec_ref(v_fileMap_730_);
return v_b_737_;
}
else
{
lean_object* v_snd_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_773_; 
v_snd_739_ = lean_ctor_get(v_b_737_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_b_737_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_b_737_, 0);
lean_dec(v_unused_774_);
v___x_741_ = v_b_737_;
v_isShared_742_ = v_isSharedCheck_773_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_snd_739_);
lean_dec(v_b_737_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_773_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v_fst_743_; lean_object* v_snd_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_772_; 
v_fst_743_ = lean_ctor_get(v_snd_739_, 0);
v_snd_744_ = lean_ctor_get(v_snd_739_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v_snd_739_);
if (v_isSharedCheck_772_ == 0)
{
v___x_746_ = v_snd_739_;
v_isShared_747_ = v_isSharedCheck_772_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_snd_744_);
lean_inc(v_fst_743_);
lean_dec(v_snd_739_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_772_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_a_748_; uint8_t v___x_749_; 
v_a_748_ = lean_array_uget_borrowed(v_as_734_, v_i_736_);
lean_inc(v_snd_744_);
lean_inc(v_fst_743_);
lean_inc(v_a_748_);
lean_inc_ref(v_fileMap_730_);
v___x_749_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_730_, v_hoverPos_731_, v_hoverFilePos_732_, v_a_748_, v_fst_743_, v_snd_744_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___y_753_; lean_object* v___x_763_; 
lean_dec(v_fst_743_);
v___x_750_ = lean_box(0);
v___x_751_ = l_Lean_Syntax_getTrailingSize(v_a_748_);
v___x_763_ = l_Lean_Syntax_getTailPos_x3f(v_a_748_, v___x_749_);
if (lean_obj_tag(v___x_763_) == 0)
{
v___y_753_ = v_snd_744_;
goto v___jp_752_;
}
else
{
lean_dec(v_snd_744_);
v___y_753_ = v___x_763_;
goto v___jp_752_;
}
v___jp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___y_753_);
lean_ctor_set(v___x_746_, 0, v___x_751_);
v___x_755_ = v___x_746_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___y_753_);
v___x_755_ = v_reuseFailAlloc_762_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_757_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___x_755_);
lean_ctor_set(v___x_741_, 0, v___x_750_);
v___x_757_ = v___x_741_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_755_);
v___x_757_ = v_reuseFailAlloc_761_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
size_t v___x_758_; size_t v___x_759_; 
v___x_758_ = ((size_t)1ULL);
v___x_759_ = lean_usize_add(v_i_736_, v___x_758_);
v_i_736_ = v___x_759_;
v_b_737_ = v___x_757_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
lean_dec_ref(v_fileMap_730_);
v___x_764_ = lean_box(v___y_733_);
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
if (v_isShared_747_ == 0)
{
v___x_767_ = v___x_746_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_fst_743_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_snd_744_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___x_767_);
lean_ctor_set(v___x_741_, 0, v___x_765_);
v___x_769_ = v___x_741_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0___boxed(lean_object* v_fileMap_775_, lean_object* v_hoverPos_776_, lean_object* v_hoverFilePos_777_, lean_object* v___y_778_, lean_object* v_as_779_, lean_object* v_sz_780_, lean_object* v_i_781_, lean_object* v_b_782_){
_start:
{
uint8_t v___y_1087__boxed_783_; size_t v_sz_boxed_784_; size_t v_i_boxed_785_; lean_object* v_res_786_; 
v___y_1087__boxed_783_ = lean_unbox(v___y_778_);
v_sz_boxed_784_ = lean_unbox_usize(v_sz_780_);
lean_dec(v_sz_780_);
v_i_boxed_785_ = lean_unbox_usize(v_i_781_);
lean_dec(v_i_781_);
v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_775_, v_hoverPos_776_, v_hoverFilePos_777_, v___y_1087__boxed_783_, v_as_779_, v_sz_boxed_784_, v_i_boxed_785_, v_b_782_);
lean_dec_ref(v_as_779_);
lean_dec_ref(v_hoverFilePos_777_);
lean_dec(v_hoverPos_776_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go___boxed(lean_object* v_fileMap_787_, lean_object* v_hoverPos_788_, lean_object* v_hoverFilePos_789_, lean_object* v_stx_790_, lean_object* v_leadingWs_791_, lean_object* v_leadingTokenTailPos_x3f_792_){
_start:
{
uint8_t v_res_793_; lean_object* v_r_794_; 
v_res_793_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_787_, v_hoverPos_788_, v_hoverFilePos_789_, v_stx_790_, v_leadingWs_791_, v_leadingTokenTailPos_x3f_792_);
lean_dec_ref(v_hoverFilePos_789_);
lean_dec(v_hoverPos_788_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(lean_object* v_fileMap_795_, lean_object* v_hoverPos_796_, lean_object* v_cmdStx_797_){
_start:
{
lean_object* v_hoverFilePos_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
lean_inc_ref(v_fileMap_795_);
v_hoverFilePos_798_ = l_Lean_FileMap_toPosition(v_fileMap_795_, v_hoverPos_796_);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_box(0);
v___x_801_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_795_, v_hoverPos_796_, v_hoverFilePos_798_, v_cmdStx_797_, v___x_799_, v___x_800_);
lean_dec_ref(v_hoverFilePos_798_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion___boxed(lean_object* v_fileMap_802_, lean_object* v_hoverPos_803_, lean_object* v_cmdStx_804_){
_start:
{
uint8_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_802_, v_hoverPos_803_, v_cmdStx_804_);
lean_dec(v_hoverPos_803_);
v_r_806_ = lean_box(v_res_805_);
return v_r_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(lean_object* v_as_812_, size_t v_sz_813_, size_t v_i_814_, lean_object* v_b_815_){
_start:
{
uint8_t v___x_816_; 
v___x_816_ = lean_usize_dec_lt(v_i_814_, v_sz_813_);
if (v___x_816_ == 0)
{
lean_inc_ref(v_b_815_);
return v_b_815_;
}
else
{
lean_object* v___x_817_; lean_object* v_a_818_; lean_object* v___x_819_; 
v___x_817_ = lean_box(0);
v_a_818_ = lean_array_uget_borrowed(v_as_812_, v_i_814_);
v___x_819_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_a_818_);
if (lean_obj_tag(v___x_819_) == 1)
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v___x_817_);
return v___x_821_;
}
else
{
lean_object* v___x_822_; size_t v___x_823_; size_t v___x_824_; 
lean_dec(v___x_819_);
v___x_822_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v___x_823_ = ((size_t)1ULL);
v___x_824_ = lean_usize_add(v_i_814_, v___x_823_);
v_i_814_ = v___x_824_;
v_b_815_ = v___x_822_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(lean_object* v_as_826_, size_t v_sz_827_, size_t v_i_828_, lean_object* v_b_829_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = lean_usize_dec_lt(v_i_828_, v_sz_827_);
if (v___x_830_ == 0)
{
lean_inc_ref(v_b_829_);
return v_b_829_;
}
else
{
lean_object* v___x_831_; lean_object* v_a_832_; lean_object* v___x_833_; 
v___x_831_ = lean_box(0);
v_a_832_ = lean_array_uget_borrowed(v_as_826_, v_i_828_);
lean_inc(v_a_832_);
v___x_833_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_a_832_);
if (lean_obj_tag(v___x_833_) == 1)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_831_);
return v___x_835_;
}
else
{
lean_object* v___x_836_; size_t v___x_837_; size_t v___x_838_; 
lean_dec(v___x_833_);
v___x_836_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_i_828_, v___x_837_);
v_i_828_ = v___x_838_;
v_b_829_ = v___x_836_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(lean_object* v_x_840_){
_start:
{
if (lean_obj_tag(v_x_840_) == 0)
{
lean_object* v_cs_841_; lean_object* v___x_842_; lean_object* v___x_843_; size_t v_sz_844_; size_t v___x_845_; lean_object* v___x_846_; lean_object* v_fst_847_; 
v_cs_841_ = lean_ctor_get(v_x_840_, 0);
v___x_842_ = lean_box(0);
v___x_843_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_844_ = lean_array_size(v_cs_841_);
v___x_845_ = ((size_t)0ULL);
v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_cs_841_, v_sz_844_, v___x_845_, v___x_843_);
v_fst_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_fst_847_);
lean_dec_ref(v___x_846_);
if (lean_obj_tag(v_fst_847_) == 0)
{
return v___x_842_;
}
else
{
lean_object* v_val_848_; 
v_val_848_ = lean_ctor_get(v_fst_847_, 0);
lean_inc(v_val_848_);
lean_dec_ref(v_fst_847_);
return v_val_848_;
}
}
else
{
lean_object* v_vs_849_; lean_object* v___x_850_; lean_object* v___x_851_; size_t v_sz_852_; size_t v___x_853_; lean_object* v___x_854_; lean_object* v_fst_855_; 
v_vs_849_ = lean_ctor_get(v_x_840_, 0);
v___x_850_ = lean_box(0);
v___x_851_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_852_ = lean_array_size(v_vs_849_);
v___x_853_ = ((size_t)0ULL);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_vs_849_, v_sz_852_, v___x_853_, v___x_851_);
v_fst_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_fst_855_);
lean_dec_ref(v___x_854_);
if (lean_obj_tag(v_fst_855_) == 0)
{
return v___x_850_;
}
else
{
lean_object* v_val_856_; 
v_val_856_ = lean_ctor_get(v_fst_855_, 0);
lean_inc(v_val_856_);
lean_dec_ref(v_fst_855_);
return v_val_856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(lean_object* v_t_857_){
_start:
{
lean_object* v_root_858_; lean_object* v_tail_859_; lean_object* v___x_860_; 
v_root_858_ = lean_ctor_get(v_t_857_, 0);
v_tail_859_ = lean_ctor_get(v_t_857_, 1);
v___x_860_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_root_858_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v___x_861_; size_t v_sz_862_; size_t v___x_863_; lean_object* v___x_864_; lean_object* v_fst_865_; 
v___x_861_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_862_ = lean_array_size(v_tail_859_);
v___x_863_ = ((size_t)0ULL);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_tail_859_, v_sz_862_, v___x_863_, v___x_861_);
v_fst_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_fst_865_);
lean_dec_ref(v___x_864_);
if (lean_obj_tag(v_fst_865_) == 0)
{
return v___x_860_;
}
else
{
lean_object* v_val_866_; 
v_val_866_ = lean_ctor_get(v_fst_865_, 0);
lean_inc(v_val_866_);
lean_dec_ref(v_fst_865_);
return v_val_866_;
}
}
else
{
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(lean_object* v_i_867_){
_start:
{
switch(lean_obj_tag(v_i_867_))
{
case 0:
{
lean_object* v_i_868_; 
v_i_868_ = lean_ctor_get(v_i_867_, 0);
lean_inc_ref(v_i_868_);
if (lean_obj_tag(v_i_868_) == 0)
{
lean_object* v_info_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v_i_867_);
v_info_869_ = lean_ctor_get(v_i_868_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v_i_868_);
if (v_isSharedCheck_879_ == 0)
{
v___x_871_ = v_i_868_;
v_isShared_872_ = v_isSharedCheck_879_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_info_869_);
lean_dec(v_i_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_879_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_873_ = lean_box(0);
v___x_874_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go___closed__0));
v___x_875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_875_, 0, v_info_869_);
lean_ctor_set(v___x_875_, 1, v___x_873_);
lean_ctor_set(v___x_875_, 2, v___x_874_);
if (v_isShared_872_ == 0)
{
lean_ctor_set_tag(v___x_871_, 1);
lean_ctor_set(v___x_871_, 0, v___x_875_);
v___x_877_ = v___x_871_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_t_880_; 
lean_dec_ref(v_i_868_);
v_t_880_ = lean_ctor_get(v_i_867_, 1);
lean_inc_ref(v_t_880_);
lean_dec_ref(v_i_867_);
v_i_867_ = v_t_880_;
goto _start;
}
}
case 1:
{
lean_object* v_children_882_; lean_object* v___x_883_; 
v_children_882_ = lean_ctor_get(v_i_867_, 1);
lean_inc_ref(v_children_882_);
lean_dec_ref(v_i_867_);
v___x_883_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(v_children_882_);
lean_dec_ref(v_children_882_);
return v___x_883_;
}
default: 
{
lean_object* v___x_884_; 
lean_dec_ref(v_i_867_);
v___x_884_ = lean_box(0);
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___boxed(lean_object* v_t_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(v_t_885_);
lean_dec_ref(v_t_885_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1___boxed(lean_object* v_as_887_, lean_object* v_sz_888_, lean_object* v_i_889_, lean_object* v_b_890_){
_start:
{
size_t v_sz_boxed_891_; size_t v_i_boxed_892_; lean_object* v_res_893_; 
v_sz_boxed_891_ = lean_unbox_usize(v_sz_888_);
lean_dec(v_sz_888_);
v_i_boxed_892_ = lean_unbox_usize(v_i_889_);
lean_dec(v_i_889_);
v_res_893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_as_887_, v_sz_boxed_891_, v_i_boxed_892_, v_b_890_);
lean_dec_ref(v_b_890_);
lean_dec_ref(v_as_887_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1___boxed(lean_object* v_as_894_, lean_object* v_sz_895_, lean_object* v_i_896_, lean_object* v_b_897_){
_start:
{
size_t v_sz_boxed_898_; size_t v_i_boxed_899_; lean_object* v_res_900_; 
v_sz_boxed_898_ = lean_unbox_usize(v_sz_895_);
lean_dec(v_sz_895_);
v_i_boxed_899_ = lean_unbox_usize(v_i_896_);
lean_dec(v_i_896_);
v_res_900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_as_894_, v_sz_boxed_898_, v_i_boxed_899_, v_b_897_);
lean_dec_ref(v_b_897_);
lean_dec_ref(v_as_894_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0___boxed(lean_object* v_x_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_x_901_);
lean_dec_ref(v_x_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f(lean_object* v_i_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_i_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(lean_object* v_fileMap_907_, lean_object* v_hoverPos_908_, lean_object* v_cmdStx_909_, lean_object* v_infoTree_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_infoTree_910_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v___x_912_; 
lean_dec(v_cmdStx_909_);
lean_dec_ref(v_fileMap_907_);
v___x_912_ = lean_box(0);
return v___x_912_;
}
else
{
lean_object* v_val_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_925_; 
v_val_913_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_925_ == 0)
{
v___x_915_ = v___x_911_;
v_isShared_916_ = v_isSharedCheck_925_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_val_913_);
lean_dec(v___x_911_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_925_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
uint8_t v___x_917_; 
v___x_917_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_907_, v_hoverPos_908_, v_cmdStx_909_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; 
lean_del_object(v___x_915_);
lean_dec(v_val_913_);
v___x_918_ = lean_box(0);
return v___x_918_;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_919_ = lean_box(0);
v___x_920_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___closed__0));
v___x_921_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set(v___x_921_, 1, v_val_913_);
lean_ctor_set(v___x_921_, 2, v___x_920_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_921_);
v___x_923_ = v___x_915_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___boxed(lean_object* v_fileMap_926_, lean_object* v_hoverPos_927_, lean_object* v_cmdStx_928_, lean_object* v_infoTree_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(v_fileMap_926_, v_hoverPos_927_, v_cmdStx_928_, v_infoTree_929_);
lean_dec(v_hoverPos_927_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(lean_object* v_msg_931_){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = l_Lean_instInhabitedExpr;
v___x_933_ = lean_panic_fn_borrowed(v___x_932_, v_msg_931_);
return v___x_933_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(lean_object* v_hoverPos_934_, lean_object* v_i_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_Elab_Info_pos_x3f(v_i_935_);
if (lean_obj_tag(v___x_936_) == 1)
{
lean_object* v_val_937_; lean_object* v___x_938_; 
v_val_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_val_937_);
lean_dec_ref(v___x_936_);
v___x_938_ = l_Lean_Elab_Info_tailPos_x3f(v_i_935_);
if (lean_obj_tag(v___x_938_) == 1)
{
if (lean_obj_tag(v_i_935_) == 1)
{
lean_object* v_i_939_; lean_object* v_expectedType_x3f_940_; 
v_i_939_ = lean_ctor_get(v_i_935_, 0);
v_expectedType_x3f_940_ = lean_ctor_get(v_i_939_, 2);
if (lean_obj_tag(v_expectedType_x3f_940_) == 0)
{
uint8_t v___x_941_; 
lean_dec_ref(v___x_938_);
lean_dec(v_val_937_);
v___x_941_ = 0;
return v___x_941_;
}
else
{
lean_object* v_val_942_; uint8_t v___x_943_; 
v_val_942_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_val_942_);
lean_dec_ref(v___x_938_);
v___x_943_ = lean_nat_dec_le(v_val_937_, v_hoverPos_934_);
lean_dec(v_val_937_);
if (v___x_943_ == 0)
{
lean_dec(v_val_942_);
return v___x_943_;
}
else
{
uint8_t v___x_944_; 
v___x_944_ = lean_nat_dec_le(v_hoverPos_934_, v_val_942_);
lean_dec(v_val_942_);
return v___x_944_;
}
}
}
else
{
uint8_t v___x_945_; 
lean_dec_ref(v___x_938_);
lean_dec(v_val_937_);
v___x_945_ = 0;
return v___x_945_;
}
}
else
{
uint8_t v___x_946_; 
lean_dec(v___x_938_);
lean_dec(v_val_937_);
v___x_946_ = 0;
return v___x_946_;
}
}
else
{
uint8_t v___x_947_; 
lean_dec(v___x_936_);
v___x_947_ = 0;
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed(lean_object* v_hoverPos_948_, lean_object* v_i_949_){
_start:
{
uint8_t v_res_950_; lean_object* v_r_951_; 
v_res_950_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(v_hoverPos_948_, v_i_949_);
lean_dec_ref(v_i_949_);
lean_dec(v_hoverPos_948_);
v_r_951_ = lean_box(v_res_950_);
return v_r_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt(lean_object* v_infoTree_952_, lean_object* v_hoverPos_953_){
_start:
{
lean_object* v___f_954_; lean_object* v___x_955_; 
v___f_954_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed), 2, 1);
lean_closure_set(v___f_954_, 0, v_hoverPos_953_);
v___x_955_ = l_Lean_Elab_InfoTree_smallestInfo_x3f(v___f_954_, v_infoTree_952_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v___x_956_; 
v___x_956_ = lean_box(0);
return v___x_956_;
}
else
{
lean_object* v_val_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_981_; 
v_val_957_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_981_ == 0)
{
v___x_959_ = v___x_955_;
v_isShared_960_ = v_isSharedCheck_981_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_val_957_);
lean_dec(v___x_955_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_981_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_fst_961_; lean_object* v_snd_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_980_; 
v_fst_961_ = lean_ctor_get(v_val_957_, 0);
v_snd_962_ = lean_ctor_get(v_val_957_, 1);
v_isSharedCheck_980_ = !lean_is_exclusive(v_val_957_);
if (v_isSharedCheck_980_ == 0)
{
v___x_964_ = v_val_957_;
v_isShared_965_ = v_isSharedCheck_980_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_snd_962_);
lean_inc(v_fst_961_);
lean_dec(v_val_957_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_980_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___y_967_; 
if (lean_obj_tag(v_snd_962_) == 1)
{
lean_object* v_i_974_; lean_object* v_expectedType_x3f_975_; 
v_i_974_ = lean_ctor_get(v_snd_962_, 0);
lean_inc_ref(v_i_974_);
lean_dec_ref(v_snd_962_);
v_expectedType_x3f_975_ = lean_ctor_get(v_i_974_, 2);
lean_inc(v_expectedType_x3f_975_);
lean_dec_ref(v_i_974_);
if (lean_obj_tag(v_expectedType_x3f_975_) == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_obj_once(&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4, &l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_once, _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4);
v___x_977_ = l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(v___x_976_);
v___y_967_ = v___x_977_;
goto v___jp_966_;
}
else
{
lean_object* v_val_978_; 
v_val_978_ = lean_ctor_get(v_expectedType_x3f_975_, 0);
lean_inc(v_val_978_);
lean_dec_ref(v_expectedType_x3f_975_);
v___y_967_ = v_val_978_;
goto v___jp_966_;
}
}
else
{
lean_object* v___x_979_; 
lean_del_object(v___x_964_);
lean_dec(v_snd_962_);
lean_dec(v_fst_961_);
lean_del_object(v___x_959_);
v___x_979_ = lean_box(0);
return v___x_979_;
}
v___jp_966_:
{
lean_object* v___x_969_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v___y_967_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_fst_961_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v___y_967_);
v___x_969_ = v_reuseFailAlloc_973_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_971_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_969_);
v___x_971_ = v___x_959_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(lean_object* v_f_982_, lean_object* v_leadingToken_x3f_983_, lean_object* v_acc_984_, lean_object* v_stx_985_){
_start:
{
lean_object* v___f_986_; lean_object* v___f_987_; lean_object* v___f_988_; lean_object* v___f_989_; lean_object* v___f_990_; lean_object* v___f_991_; lean_object* v___f_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v_acc_996_; 
v___f_986_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0));
v___f_987_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1));
v___f_988_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2));
v___f_989_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3));
v___f_990_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4));
v___f_991_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5));
v___f_992_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6));
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v___f_986_);
lean_ctor_set(v___x_993_, 1, v___f_987_);
v___x_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v___f_988_);
lean_ctor_set(v___x_994_, 2, v___f_989_);
lean_ctor_set(v___x_994_, 3, v___f_990_);
lean_ctor_set(v___x_994_, 4, v___f_991_);
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___f_992_);
lean_inc(v_f_982_);
lean_inc(v_stx_985_);
lean_inc(v_leadingToken_x3f_983_);
v_acc_996_ = lean_apply_3(v_f_982_, v_acc_984_, v_leadingToken_x3f_983_, v_stx_985_);
switch(lean_obj_tag(v_stx_985_))
{
case 0:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec_ref(v___x_995_);
lean_dec(v_leadingToken_x3f_983_);
lean_dec(v_f_982_);
v___x_997_ = lean_box(0);
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v_acc_996_);
return v___x_998_;
}
case 1:
{
lean_object* v_args_999_; lean_object* v___f_1000_; lean_object* v_lastToken_x3f_1001_; lean_object* v___x_1002_; size_t v_sz_1003_; size_t v___x_1004_; lean_object* v___x_1005_; lean_object* v_fst_1006_; lean_object* v_snd_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
v_args_999_ = lean_ctor_get(v_stx_985_, 2);
lean_inc_ref(v_args_999_);
lean_dec_ref(v_stx_985_);
v___f_1000_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1000_, 0, v_f_982_);
lean_closure_set(v___f_1000_, 1, v_leadingToken_x3f_983_);
v_lastToken_x3f_1001_ = lean_box(0);
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v_acc_996_);
lean_ctor_set(v___x_1002_, 1, v_lastToken_x3f_1001_);
v_sz_1003_ = lean_array_size(v_args_999_);
v___x_1004_ = ((size_t)0ULL);
v___x_1005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_995_, v_args_999_, v___f_1000_, v_sz_1003_, v___x_1004_, v___x_1002_);
v_fst_1006_ = lean_ctor_get(v___x_1005_, 0);
v_snd_1007_ = lean_ctor_get(v___x_1005_, 1);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1005_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_snd_1007_);
lean_inc(v_fst_1006_);
lean_dec(v___x_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v_fst_1006_);
lean_ctor_set(v___x_1009_, 0, v_snd_1007_);
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_snd_1007_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_fst_1006_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
default: 
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec_ref(v___x_995_);
lean_dec(v_leadingToken_x3f_983_);
lean_dec(v_f_982_);
v___x_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1015_, 0, v_stx_985_);
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v_acc_996_);
return v___x_1016_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0(lean_object* v_f_1017_, lean_object* v_leadingToken_x3f_1018_, lean_object* v_a_1019_, lean_object* v_x_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v_fst_1027_; lean_object* v_snd_1028_; lean_object* v___y_1030_; 
v_fst_1027_ = lean_ctor_get(v___y_1021_, 0);
lean_inc(v_fst_1027_);
v_snd_1028_ = lean_ctor_get(v___y_1021_, 1);
lean_inc(v_snd_1028_);
lean_dec_ref(v___y_1021_);
if (lean_obj_tag(v_snd_1028_) == 0)
{
v___y_1030_ = v_leadingToken_x3f_1018_;
goto v___jp_1029_;
}
else
{
lean_dec(v_leadingToken_x3f_1018_);
lean_inc_ref(v_snd_1028_);
v___y_1030_ = v_snd_1028_;
goto v___jp_1029_;
}
v___jp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___y_1023_);
lean_ctor_set(v___x_1025_, 1, v___y_1024_);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
return v___x_1026_;
}
v___jp_1029_:
{
lean_object* v___x_1031_; lean_object* v_fst_1032_; 
v___x_1031_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1017_, v___y_1030_, v_fst_1027_, v_a_1019_);
v_fst_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_fst_1032_);
if (lean_obj_tag(v_fst_1032_) == 0)
{
lean_object* v_snd_1033_; 
v_snd_1033_ = lean_ctor_get(v___x_1031_, 1);
lean_inc(v_snd_1033_);
lean_dec_ref(v___x_1031_);
v___y_1023_ = v_snd_1033_;
v___y_1024_ = v_snd_1028_;
goto v___jp_1022_;
}
else
{
lean_object* v_snd_1034_; 
lean_dec(v_snd_1028_);
v_snd_1034_ = lean_ctor_get(v___x_1031_, 1);
lean_inc(v_snd_1034_);
lean_dec_ref(v___x_1031_);
v___y_1023_ = v_snd_1034_;
v___y_1024_ = v_fst_1032_;
goto v___jp_1022_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(lean_object* v_00_u03b1_1035_, lean_object* v_f_1036_, lean_object* v_inst_1037_, lean_object* v_leadingToken_x3f_1038_, lean_object* v_acc_1039_, lean_object* v_stx_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1036_, v_leadingToken_x3f_1038_, v_acc_1039_, v_stx_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_f_1043_, lean_object* v_inst_1044_, lean_object* v_leadingToken_x3f_1045_, lean_object* v_acc_1046_, lean_object* v_stx_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(v_00_u03b1_1042_, v_f_1043_, v_inst_1044_, v_leadingToken_x3f_1045_, v_acc_1046_, v_stx_1047_);
lean_dec(v_inst_1044_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(lean_object* v_f_1049_, lean_object* v_init_1050_, lean_object* v_stx_1051_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v_snd_1054_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1049_, v___x_1052_, v_init_1050_, v_stx_1051_);
v_snd_1054_ = lean_ctor_get(v___x_1053_, 1);
lean_inc(v_snd_1054_);
lean_dec_ref(v___x_1053_);
return v_snd_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(lean_object* v_00_u03b1_1055_, lean_object* v_inst_1056_, lean_object* v_f_1057_, lean_object* v_init_1058_, lean_object* v_stx_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(v_f_1057_, v_init_1058_, v_stx_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___boxed(lean_object* v_00_u03b1_1061_, lean_object* v_inst_1062_, lean_object* v_f_1063_, lean_object* v_init_1064_, lean_object* v_stx_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(v_00_u03b1_1061_, v_inst_1062_, v_f_1063_, v_init_1064_, v_stx_1065_);
lean_dec(v_inst_1062_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(lean_object* v_p_1067_, lean_object* v_foundStx_x3f_1068_, lean_object* v_leadingToken_x3f_1069_, lean_object* v_stx_1070_){
_start:
{
if (lean_obj_tag(v_foundStx_x3f_1068_) == 0)
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
lean_inc(v_stx_1070_);
v___x_1071_ = lean_apply_2(v_p_1067_, v_leadingToken_x3f_1069_, v_stx_1070_);
v___x_1072_ = lean_unbox(v___x_1071_);
if (v___x_1072_ == 0)
{
lean_dec(v_stx_1070_);
return v_foundStx_x3f_1068_;
}
else
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1073_, 0, v_stx_1070_);
return v___x_1073_;
}
}
else
{
lean_dec(v_stx_1070_);
lean_dec(v_leadingToken_x3f_1069_);
lean_dec_ref(v_p_1067_);
lean_inc_ref(v_foundStx_x3f_1068_);
return v_foundStx_x3f_1068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed(lean_object* v_p_1074_, lean_object* v_foundStx_x3f_1075_, lean_object* v_leadingToken_x3f_1076_, lean_object* v_stx_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(v_p_1074_, v_foundStx_x3f_1075_, v_leadingToken_x3f_1076_, v_stx_1077_);
lean_dec(v_foundStx_x3f_1075_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f(lean_object* v_p_1079_, lean_object* v_stx_1080_){
_start:
{
lean_object* v___f_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___f_1081_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1081_, 0, v_p_1079_);
v___x_1082_ = lean_box(0);
v___x_1083_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(v___f_1081_, v___x_1082_, v_stx_1080_);
return v___x_1083_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(uint8_t v___y_1084_, lean_object* v_hoverPos_1085_, lean_object* v_as_1086_, size_t v_i_1087_, size_t v_stop_1088_){
_start:
{
uint8_t v___x_1089_; 
v___x_1089_ = lean_usize_dec_eq(v_i_1087_, v_stop_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v_fst_1091_; lean_object* v_snd_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; uint8_t v___y_1096_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1090_ = lean_array_uget_borrowed(v_as_1086_, v_i_1087_);
v_fst_1091_ = lean_ctor_get(v___x_1090_, 0);
v_snd_1092_ = lean_ctor_get(v___x_1090_, 1);
v___x_1093_ = lean_unsigned_to_nat(0u);
v___x_1094_ = 1;
v___x_1100_ = lean_unsigned_to_nat(2u);
v___x_1101_ = lean_nat_mod(v_snd_1092_, v___x_1100_);
v___x_1102_ = lean_nat_dec_eq(v___x_1101_, v___x_1093_);
lean_dec(v___x_1101_);
if (v___x_1102_ == 0)
{
uint8_t v___x_1103_; 
v___x_1103_ = l_Lean_Syntax_isAtom(v_fst_1091_);
if (v___x_1103_ == 0)
{
v___y_1096_ = v___y_1084_;
goto v___jp_1095_;
}
else
{
if (v___x_1102_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_Syntax_getTailPos_x3f(v_fst_1091_, v___x_1102_);
if (lean_obj_tag(v___x_1104_) == 1)
{
lean_object* v_val_1105_; uint8_t v___x_1106_; 
v_val_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_val_1105_);
lean_dec_ref(v___x_1104_);
v___x_1106_ = lean_nat_dec_le(v_val_1105_, v_hoverPos_1085_);
if (v___x_1106_ == 0)
{
lean_dec(v_val_1105_);
v___y_1096_ = v___x_1106_;
goto v___jp_1095_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1107_ = l_Lean_Syntax_getTrailingSize(v_fst_1091_);
v___x_1108_ = lean_nat_add(v_val_1105_, v___x_1107_);
lean_dec(v___x_1107_);
lean_dec(v_val_1105_);
v___x_1109_ = lean_nat_dec_le(v_hoverPos_1085_, v___x_1108_);
lean_dec(v___x_1108_);
v___y_1096_ = v___x_1109_;
goto v___jp_1095_;
}
}
else
{
lean_dec(v___x_1104_);
v___y_1096_ = v___x_1102_;
goto v___jp_1095_;
}
}
else
{
v___y_1096_ = v___y_1084_;
goto v___jp_1095_;
}
}
}
else
{
v___y_1096_ = v___y_1084_;
goto v___jp_1095_;
}
v___jp_1095_:
{
if (v___y_1096_ == 0)
{
size_t v___x_1097_; size_t v___x_1098_; 
v___x_1097_ = ((size_t)1ULL);
v___x_1098_ = lean_usize_add(v_i_1087_, v___x_1097_);
v_i_1087_ = v___x_1098_;
goto _start;
}
else
{
return v___x_1094_;
}
}
}
else
{
uint8_t v___x_1110_; 
v___x_1110_ = 0;
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0___boxed(lean_object* v___y_1111_, lean_object* v_hoverPos_1112_, lean_object* v_as_1113_, lean_object* v_i_1114_, lean_object* v_stop_1115_){
_start:
{
uint8_t v___y_2411__boxed_1116_; size_t v_i_boxed_1117_; size_t v_stop_boxed_1118_; uint8_t v_res_1119_; lean_object* v_r_1120_; 
v___y_2411__boxed_1116_ = lean_unbox(v___y_1111_);
v_i_boxed_1117_ = lean_unbox_usize(v_i_1114_);
lean_dec(v_i_1114_);
v_stop_boxed_1118_ = lean_unbox_usize(v_stop_1115_);
lean_dec(v_stop_1115_);
v_res_1119_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(v___y_2411__boxed_1116_, v_hoverPos_1112_, v_as_1113_, v_i_boxed_1117_, v_stop_boxed_1118_);
lean_dec_ref(v_as_1113_);
lean_dec(v_hoverPos_1112_);
v_r_1120_ = lean_box(v_res_1119_);
return v_r_1120_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(uint8_t v___x_1127_, uint8_t v_isCursorOnWhitespace_1128_, uint8_t v_isCursorInProperWhitespace_1129_, lean_object* v_fileMap_1130_, lean_object* v_hoverFilePos_1131_, lean_object* v_hoverPos_1132_, lean_object* v_leadingToken_x3f_1133_, lean_object* v_stx_1134_){
_start:
{
uint8_t v___y_1136_; 
if (lean_obj_tag(v_leadingToken_x3f_1133_) == 1)
{
lean_object* v_val_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v_val_1143_ = lean_ctor_get(v_leadingToken_x3f_1133_, 0);
lean_inc(v_stx_1134_);
v___x_1144_ = l_Lean_Syntax_getKind(v_stx_1134_);
v___x_1145_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1));
v___x_1146_ = lean_name_eq(v___x_1144_, v___x_1145_);
lean_dec(v___x_1144_);
if (v___x_1146_ == 0)
{
lean_dec(v_stx_1134_);
lean_dec_ref(v_fileMap_1130_);
return v___x_1127_;
}
else
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Syntax_getTailPos_x3f(v_val_1143_, v_isCursorOnWhitespace_1128_);
if (lean_obj_tag(v___x_1147_) == 1)
{
lean_object* v_val_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v_fieldsAndSeps_1151_; uint8_t v___y_1153_; lean_object* v___y_1161_; lean_object* v___x_1167_; 
v_val_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_val_1148_);
lean_dec_ref(v___x_1147_);
v___x_1149_ = lean_unsigned_to_nat(0u);
v___x_1150_ = l_Lean_Syntax_getArg(v_stx_1134_, v___x_1149_);
v_fieldsAndSeps_1151_ = l_Lean_Syntax_getArgs(v___x_1150_);
lean_dec(v___x_1150_);
v___x_1167_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1134_, v_isCursorOnWhitespace_1128_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_val_1143_, v_isCursorOnWhitespace_1128_);
v___y_1161_ = v___x_1168_;
goto v___jp_1160_;
}
else
{
v___y_1161_ = v___x_1167_;
goto v___jp_1160_;
}
v___jp_1152_:
{
if (v___y_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1154_ = l_Array_zipIdx___redArg(v_fieldsAndSeps_1151_, v___x_1149_);
lean_dec_ref(v_fieldsAndSeps_1151_);
v___x_1155_ = lean_array_get_size(v___x_1154_);
v___x_1156_ = lean_nat_dec_lt(v___x_1149_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_dec_ref(v___x_1154_);
v___y_1136_ = v___y_1153_;
goto v___jp_1135_;
}
else
{
if (v___x_1156_ == 0)
{
lean_dec_ref(v___x_1154_);
v___y_1136_ = v___y_1153_;
goto v___jp_1135_;
}
else
{
size_t v___x_1157_; size_t v___x_1158_; uint8_t v___x_1159_; 
v___x_1157_ = ((size_t)0ULL);
v___x_1158_ = lean_usize_of_nat(v___x_1155_);
v___x_1159_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(v___y_1153_, v_hoverPos_1132_, v___x_1154_, v___x_1157_, v___x_1158_);
lean_dec_ref(v___x_1154_);
if (v___x_1159_ == 0)
{
v___y_1136_ = v___x_1159_;
goto v___jp_1135_;
}
else
{
lean_dec(v_stx_1134_);
lean_dec_ref(v_fileMap_1130_);
return v_isCursorOnWhitespace_1128_;
}
}
}
}
else
{
lean_dec_ref(v_fieldsAndSeps_1151_);
lean_dec(v_stx_1134_);
lean_dec_ref(v_fileMap_1130_);
return v_isCursorOnWhitespace_1128_;
}
}
v___jp_1160_:
{
if (lean_obj_tag(v___y_1161_) == 1)
{
lean_object* v_val_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v_val_1162_ = lean_ctor_get(v___y_1161_, 0);
lean_inc(v_val_1162_);
lean_dec_ref(v___y_1161_);
v___x_1163_ = lean_array_get_size(v_fieldsAndSeps_1151_);
v___x_1164_ = lean_nat_dec_eq(v___x_1163_, v___x_1149_);
if (v___x_1164_ == 0)
{
lean_dec(v_val_1162_);
lean_dec(v_val_1148_);
v___y_1153_ = v___x_1164_;
goto v___jp_1152_;
}
else
{
lean_object* v_outerBounds_1165_; uint8_t v___x_1166_; 
v_outerBounds_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_outerBounds_1165_, 0, v_val_1148_);
lean_ctor_set(v_outerBounds_1165_, 1, v_val_1162_);
v___x_1166_ = l_Lean_Syntax_Range_contains(v_outerBounds_1165_, v_hoverPos_1132_, v_isCursorOnWhitespace_1128_);
lean_dec_ref(v_outerBounds_1165_);
v___y_1153_ = v___x_1166_;
goto v___jp_1152_;
}
}
else
{
lean_dec(v___y_1161_);
lean_dec_ref(v_fieldsAndSeps_1151_);
lean_dec(v_val_1148_);
lean_dec(v_stx_1134_);
lean_dec_ref(v_fileMap_1130_);
return v___x_1127_;
}
}
}
else
{
lean_dec(v___x_1147_);
lean_dec(v_stx_1134_);
lean_dec_ref(v_fileMap_1130_);
return v___x_1127_;
}
}
}
else
{
lean_dec(v_stx_1134_);
lean_dec_ref(v_fileMap_1130_);
return v___x_1127_;
}
v___jp_1135_:
{
if (v_isCursorInProperWhitespace_1129_ == 0)
{
lean_dec(v_stx_1134_);
lean_dec_ref(v_fileMap_1130_);
return v___y_1136_;
}
else
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_Syntax_getPos_x3f(v_stx_1134_, v___y_1136_);
lean_dec(v_stx_1134_);
if (lean_obj_tag(v___x_1137_) == 1)
{
lean_object* v_val_1138_; lean_object* v___x_1139_; lean_object* v_column_1140_; lean_object* v_column_1141_; uint8_t v_isCursorInBlock_1142_; 
v_val_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_val_1138_);
lean_dec_ref(v___x_1137_);
v___x_1139_ = l_Lean_FileMap_toPosition(v_fileMap_1130_, v_val_1138_);
lean_dec(v_val_1138_);
v_column_1140_ = lean_ctor_get(v___x_1139_, 1);
lean_inc(v_column_1140_);
lean_dec_ref(v___x_1139_);
v_column_1141_ = lean_ctor_get(v_hoverFilePos_1131_, 1);
v_isCursorInBlock_1142_ = lean_nat_dec_eq(v_column_1141_, v_column_1140_);
lean_dec(v_column_1140_);
return v_isCursorInBlock_1142_;
}
else
{
lean_dec(v___x_1137_);
lean_dec_ref(v_fileMap_1130_);
return v___y_1136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___boxed(lean_object* v___x_1169_, lean_object* v_isCursorOnWhitespace_1170_, lean_object* v_isCursorInProperWhitespace_1171_, lean_object* v_fileMap_1172_, lean_object* v_hoverFilePos_1173_, lean_object* v_hoverPos_1174_, lean_object* v_leadingToken_x3f_1175_, lean_object* v_stx_1176_){
_start:
{
uint8_t v___x_2473__boxed_1177_; uint8_t v_isCursorOnWhitespace_boxed_1178_; uint8_t v_isCursorInProperWhitespace_boxed_1179_; uint8_t v_res_1180_; lean_object* v_r_1181_; 
v___x_2473__boxed_1177_ = lean_unbox(v___x_1169_);
v_isCursorOnWhitespace_boxed_1178_ = lean_unbox(v_isCursorOnWhitespace_1170_);
v_isCursorInProperWhitespace_boxed_1179_ = lean_unbox(v_isCursorInProperWhitespace_1171_);
v_res_1180_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(v___x_2473__boxed_1177_, v_isCursorOnWhitespace_boxed_1178_, v_isCursorInProperWhitespace_boxed_1179_, v_fileMap_1172_, v_hoverFilePos_1173_, v_hoverPos_1174_, v_leadingToken_x3f_1175_, v_stx_1176_);
lean_dec(v_leadingToken_x3f_1175_);
lean_dec(v_hoverPos_1174_);
lean_dec_ref(v_hoverFilePos_1173_);
v_r_1181_ = lean_box(v_res_1180_);
return v_r_1181_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(lean_object* v_fileMap_1182_, lean_object* v_hoverPos_1183_, lean_object* v_cmdStx_1184_){
_start:
{
uint8_t v_isCursorOnWhitespace_1185_; 
v_isCursorOnWhitespace_1185_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_1182_, v_hoverPos_1183_);
if (v_isCursorOnWhitespace_1185_ == 0)
{
lean_dec(v_cmdStx_1184_);
lean_dec(v_hoverPos_1183_);
lean_dec_ref(v_fileMap_1182_);
return v_isCursorOnWhitespace_1185_;
}
else
{
uint8_t v_isCursorInProperWhitespace_1186_; uint8_t v___x_1187_; lean_object* v_hoverFilePos_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; 
v_isCursorInProperWhitespace_1186_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_1182_, v_hoverPos_1183_);
v___x_1187_ = 0;
lean_inc_ref(v_fileMap_1182_);
v_hoverFilePos_1188_ = l_Lean_FileMap_toPosition(v_fileMap_1182_, v_hoverPos_1183_);
v___x_1189_ = lean_box(v___x_1187_);
v___x_1190_ = lean_box(v_isCursorOnWhitespace_1185_);
v___x_1191_ = lean_box(v_isCursorInProperWhitespace_1186_);
v___f_1192_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___boxed), 8, 6);
lean_closure_set(v___f_1192_, 0, v___x_1189_);
lean_closure_set(v___f_1192_, 1, v___x_1190_);
lean_closure_set(v___f_1192_, 2, v___x_1191_);
lean_closure_set(v___f_1192_, 3, v_fileMap_1182_);
lean_closure_set(v___f_1192_, 4, v_hoverFilePos_1188_);
lean_closure_set(v___f_1192_, 5, v_hoverPos_1183_);
v___x_1193_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f(v___f_1192_, v_cmdStx_1184_);
if (lean_obj_tag(v___x_1193_) == 0)
{
return v___x_1187_;
}
else
{
lean_dec_ref(v___x_1193_);
return v_isCursorOnWhitespace_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___boxed(lean_object* v_fileMap_1194_, lean_object* v_hoverPos_1195_, lean_object* v_cmdStx_1196_){
_start:
{
uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_res_1197_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(v_fileMap_1194_, v_hoverPos_1195_, v_cmdStx_1196_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticFieldCompletion_x3f(lean_object* v_fileMap_1199_, lean_object* v_hoverPos_1200_, lean_object* v_cmdStx_1201_, lean_object* v_infoTree_1202_){
_start:
{
uint8_t v___x_1203_; 
lean_inc(v_hoverPos_1200_);
v___x_1203_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(v_fileMap_1199_, v_hoverPos_1200_, v_cmdStx_1201_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; 
lean_dec_ref(v_infoTree_1202_);
lean_dec(v_hoverPos_1200_);
v___x_1204_ = lean_box(0);
return v___x_1204_;
}
else
{
lean_object* v___x_1205_; 
v___x_1205_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt(v_infoTree_1202_, v_hoverPos_1200_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_box(0);
return v___x_1206_;
}
else
{
lean_object* v_val_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1229_; 
v_val_1207_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1209_ = v___x_1205_;
v_isShared_1210_ = v_isSharedCheck_1229_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_val_1207_);
lean_dec(v___x_1205_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1229_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v_fst_1211_; lean_object* v_snd_1212_; lean_object* v___x_1213_; 
v_fst_1211_ = lean_ctor_get(v_val_1207_, 0);
lean_inc(v_fst_1211_);
v_snd_1212_ = lean_ctor_get(v_val_1207_, 1);
lean_inc(v_snd_1212_);
lean_dec(v_val_1207_);
v___x_1213_ = l_Lean_Expr_getAppFn(v_snd_1212_);
lean_dec(v_snd_1212_);
if (lean_obj_tag(v___x_1213_) == 4)
{
lean_object* v_toCommandContextInfo_1214_; lean_object* v_declName_1215_; lean_object* v_env_1216_; uint8_t v___x_1217_; 
v_toCommandContextInfo_1214_ = lean_ctor_get(v_fst_1211_, 0);
v_declName_1215_ = lean_ctor_get(v___x_1213_, 0);
lean_inc_n(v_declName_1215_, 2);
lean_dec_ref(v___x_1213_);
v_env_1216_ = lean_ctor_get(v_toCommandContextInfo_1214_, 0);
lean_inc_ref(v_env_1216_);
v___x_1217_ = l_Lean_isStructure(v_env_1216_, v_declName_1215_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; 
lean_dec(v_declName_1215_);
lean_dec(v_fst_1211_);
lean_del_object(v___x_1209_);
v___x_1218_ = lean_box(0);
return v___x_1218_;
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1219_ = lean_box(0);
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_box(0);
v___x_1222_ = l_Lean_LocalContext_empty;
v___x_1223_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1220_);
lean_ctor_set(v___x_1223_, 1, v___x_1221_);
lean_ctor_set(v___x_1223_, 2, v___x_1222_);
lean_ctor_set(v___x_1223_, 3, v_declName_1215_);
v___x_1224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1219_);
lean_ctor_set(v___x_1224_, 1, v_fst_1211_);
lean_ctor_set(v___x_1224_, 2, v___x_1223_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1224_);
v___x_1226_ = v___x_1209_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
else
{
lean_object* v___x_1228_; 
lean_dec_ref(v___x_1213_);
lean_dec(v_fst_1211_);
lean_del_object(v___x_1209_);
v___x_1228_ = lean_box(0);
return v___x_1228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findSyntheticCompletions(lean_object* v_fileMap_1232_, lean_object* v_hoverPos_1233_, lean_object* v_cmdStx_1234_, lean_object* v_infoTree_1235_){
_start:
{
lean_object* v___y_1237_; lean_object* v___x_1243_; 
lean_inc_ref(v_infoTree_1235_);
lean_inc(v_cmdStx_1234_);
lean_inc_ref(v_fileMap_1232_);
v___x_1243_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(v_fileMap_1232_, v_hoverPos_1233_, v_cmdStx_1234_, v_infoTree_1235_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v___x_1244_; 
lean_inc_ref(v_infoTree_1235_);
lean_inc(v_hoverPos_1233_);
v___x_1244_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticFieldCompletion_x3f(v_fileMap_1232_, v_hoverPos_1233_, v_cmdStx_1234_, v_infoTree_1235_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v___x_1245_; 
v___x_1245_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(v_hoverPos_1233_, v_infoTree_1235_);
v___y_1237_ = v___x_1245_;
goto v___jp_1236_;
}
else
{
lean_dec_ref(v_infoTree_1235_);
lean_dec(v_hoverPos_1233_);
v___y_1237_ = v___x_1244_;
goto v___jp_1236_;
}
}
else
{
lean_dec_ref(v_infoTree_1235_);
lean_dec(v_cmdStx_1234_);
lean_dec(v_hoverPos_1233_);
lean_dec_ref(v_fileMap_1232_);
v___y_1237_ = v___x_1243_;
goto v___jp_1236_;
}
v___jp_1236_:
{
if (lean_obj_tag(v___y_1237_) == 0)
{
lean_object* v___x_1238_; 
v___x_1238_ = ((lean_object*)(l_Lean_Server_Completion_findSyntheticCompletions___closed__0));
return v___x_1238_;
}
else
{
lean_object* v_val_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_val_1239_ = lean_ctor_get(v___y_1237_, 0);
lean_inc(v_val_1239_);
lean_dec_ref(v___y_1237_);
v___x_1240_ = lean_unsigned_to_nat(1u);
v___x_1241_ = lean_mk_empty_array_with_capacity(v___x_1240_);
v___x_1242_ = lean_array_push(v___x_1241_, v_val_1239_);
return v___x_1242_;
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
