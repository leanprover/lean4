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
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* v_snd_200_; lean_object* v_snd_201_; uint8_t v___y_203_; uint8_t v___y_204_; uint8_t v___y_205_; lean_object* v___x_208_; uint8_t v___x_209_; uint8_t v___y_211_; 
v_snd_200_ = lean_ctor_get(v_a_198_, 1);
v_snd_201_ = lean_ctor_get(v_b_199_, 1);
v___x_208_ = l_Lean_Elab_Info_lctx(v_snd_200_);
v___x_209_ = lean_local_ctx_is_empty(v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = l_Lean_Elab_Info_lctx(v_snd_201_);
v___x_216_ = lean_local_ctx_is_empty(v___x_215_);
if (v___x_216_ == 0)
{
v___y_211_ = v___x_216_;
goto v___jp_210_;
}
else
{
return v___x_216_;
}
}
else
{
uint8_t v___x_217_; 
v___x_217_ = 0;
v___y_211_ = v___x_217_;
goto v___jp_210_;
}
v___jp_202_:
{
if (v___y_205_ == 0)
{
uint8_t v___x_206_; 
v___x_206_ = l_Lean_Elab_Info_isSmaller(v_snd_200_, v_snd_201_);
if (v___x_206_ == 0)
{
uint8_t v___x_207_; 
v___x_207_ = l_Lean_Elab_Info_isSmaller(v_snd_201_, v_snd_200_);
if (v___x_207_ == 0)
{
return v___x_207_;
}
else
{
return v___x_206_;
}
}
else
{
return v___y_203_;
}
}
else
{
return v___y_204_;
}
}
v___jp_210_:
{
uint8_t v___x_212_; 
v___x_212_ = 1;
if (v___x_209_ == 0)
{
v___y_203_ = v___x_212_;
v___y_204_ = v___y_211_;
v___y_205_ = v___x_209_;
goto v___jp_202_;
}
else
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = l_Lean_Elab_Info_lctx(v_snd_201_);
v___x_214_ = lean_local_ctx_is_empty(v___x_213_);
if (v___x_214_ == 0)
{
v___y_203_ = v___x_212_;
v___y_204_ = v___y_211_;
v___y_205_ = v___x_209_;
goto v___jp_202_;
}
else
{
v___y_203_ = v___x_212_;
v___y_204_ = v___y_211_;
v___y_205_ = v___y_211_;
goto v___jp_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter___boxed(lean_object* v_a_218_, lean_object* v_b_219_){
_start:
{
uint8_t v_res_220_; lean_object* v_r_221_; 
v_res_220_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter(v_a_218_, v_b_219_);
lean_dec_ref(v_b_219_);
lean_dec_ref(v_a_218_);
v_r_221_ = lean_box(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0(lean_object* v_hoverPos_222_, lean_object* v_ctx_223_, lean_object* v_info_224_, lean_object* v_x_225_){
_start:
{
uint8_t v___x_226_; 
v___x_226_ = l_Lean_Elab_Info_occursInOrOnBoundary(v_info_224_, v_hoverPos_222_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; 
lean_dec_ref(v_info_224_);
lean_dec_ref(v_ctx_223_);
v___x_227_ = lean_box(0);
return v___x_227_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v_ctx_223_);
lean_ctor_set(v___x_228_, 1, v_info_224_);
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0___boxed(lean_object* v_hoverPos_230_, lean_object* v_ctx_231_, lean_object* v_info_232_, lean_object* v_x_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0(v_hoverPos_230_, v_ctx_231_, v_info_232_, v_x_233_);
lean_dec_ref(v_x_233_);
lean_dec(v_hoverPos_230_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f(lean_object* v_hoverPos_236_, lean_object* v_infoTree_237_){
_start:
{
lean_object* v___f_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___f_238_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_238_, 0, v_hoverPos_236_);
v___x_239_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___closed__0));
v___x_240_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(v_infoTree_237_, v___x_239_, v___f_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__2(lean_object* v_msg_241_){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_panic_fn_borrowed(v___x_242_, v_msg_241_);
return v___x_243_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0(lean_object* v_hoverPos_244_, lean_object* v_x_245_){
_start:
{
uint8_t v___x_246_; lean_object* v___x_247_; 
v___x_246_ = 0;
v___x_247_ = l_Lean_Syntax_getRange_x3f(v_x_245_, v___x_246_);
if (lean_obj_tag(v___x_247_) == 0)
{
return v___x_246_;
}
else
{
lean_object* v_val_248_; uint8_t v___x_249_; uint8_t v___x_250_; 
v_val_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_val_248_);
lean_dec_ref_known(v___x_247_, 1);
v___x_249_ = 1;
v___x_250_ = l_Lean_Syntax_Range_contains(v_val_248_, v_hoverPos_244_, v___x_249_);
lean_dec(v_val_248_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0___boxed(lean_object* v_hoverPos_251_, lean_object* v_x_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0(v_hoverPos_251_, v_x_252_);
lean_dec(v_x_252_);
lean_dec(v_hoverPos_251_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1(lean_object* v_stx_255_){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = l_Lean_Syntax_hasArgs(v_stx_255_);
if (v___x_256_ == 0)
{
uint8_t v___x_257_; 
v___x_257_ = 1;
return v___x_257_;
}
else
{
uint8_t v___x_258_; 
v___x_258_ = 0;
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1___boxed(lean_object* v_stx_259_){
_start:
{
uint8_t v_res_260_; lean_object* v_r_261_; 
v_res_260_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1(v_stx_259_);
lean_dec(v_stx_259_);
v_r_261_ = lean_box(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(lean_object* v_x_274_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
return v_x_274_;
}
else
{
lean_object* v_head_275_; lean_object* v_tail_276_; uint8_t v___y_278_; lean_object* v_fst_280_; lean_object* v___x_281_; uint8_t v___x_282_; uint8_t v___y_284_; 
v_head_275_ = lean_ctor_get(v_x_274_, 0);
v_tail_276_ = lean_ctor_get(v_x_274_, 1);
v_fst_280_ = lean_ctor_get(v_head_275_, 0);
v___x_281_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
lean_inc(v_fst_280_);
v___x_282_ = l_Lean_Syntax_isOfKind(v_fst_280_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6));
lean_inc(v_fst_280_);
v___x_287_ = l_Lean_Syntax_isOfKind(v_fst_280_, v___x_286_);
if (v___x_287_ == 0)
{
v___y_284_ = v___x_287_;
goto v___jp_283_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = l_Lean_Syntax_getArg(v_fst_280_, v___x_288_);
v___x_290_ = l_Lean_Syntax_isOfKind(v___x_289_, v___x_281_);
if (v___x_290_ == 0)
{
v___y_284_ = v___x_290_;
goto v___jp_283_;
}
else
{
v___y_278_ = v___x_282_;
goto v___jp_277_;
}
}
}
else
{
return v_x_274_;
}
v___jp_277_:
{
if (v___y_278_ == 0)
{
return v_x_274_;
}
else
{
lean_inc(v_tail_276_);
lean_dec_ref_known(v_x_274_, 2);
v_x_274_ = v_tail_276_;
goto _start;
}
}
v___jp_283_:
{
if (v___y_284_ == 0)
{
lean_inc(v_tail_276_);
lean_dec_ref_known(v_x_274_, 2);
v_x_274_ = v_tail_276_;
goto _start;
}
else
{
v___y_278_ = v___x_282_;
goto v___jp_277_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(lean_object* v_x_297_){
_start:
{
if (lean_obj_tag(v_x_297_) == 0)
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
else
{
lean_object* v_head_299_; lean_object* v_tail_300_; uint8_t v___y_302_; lean_object* v_fst_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v_head_299_ = lean_ctor_get(v_x_297_, 0);
lean_inc(v_head_299_);
v_tail_300_ = lean_ctor_get(v_x_297_, 1);
lean_inc(v_tail_300_);
lean_dec_ref_known(v_x_297_, 2);
v_fst_304_ = lean_ctor_get(v_head_299_, 0);
lean_inc_n(v_fst_304_, 2);
lean_dec(v_head_299_);
v___x_305_ = ((lean_object*)(l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1));
v___x_306_ = l_Lean_Syntax_isOfKind(v_fst_304_, v___x_305_);
if (v___x_306_ == 0)
{
lean_dec(v_fst_304_);
v___y_302_ = v___x_306_;
goto v___jp_301_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = l_Lean_Syntax_getArg(v_fst_304_, v___x_307_);
lean_dec(v_fst_304_);
v___x_309_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
v___x_310_ = l_Lean_Syntax_isOfKind(v___x_308_, v___x_309_);
v___y_302_ = v___x_310_;
goto v___jp_301_;
}
v___jp_301_:
{
if (v___y_302_ == 0)
{
v_x_297_ = v_tail_300_;
goto _start;
}
else
{
lean_dec(v_tail_300_);
return v___y_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___boxed(lean_object* v_x_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(v_x_311_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_318_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3));
v___x_319_ = lean_unsigned_to_nat(14u);
v___x_320_ = lean_unsigned_to_nat(22u);
v___x_321_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2));
v___x_322_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1));
v___x_323_ = l_mkPanicMessageWithDecl(v___x_322_, v___x_321_, v___x_320_, v___x_319_, v___x_318_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(lean_object* v_hoverPos_324_, lean_object* v_infoTree_325_){
_start:
{
lean_object* v___x_326_; 
lean_inc(v_hoverPos_324_);
v___x_326_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f(v_hoverPos_324_, v_infoTree_325_);
if (lean_obj_tag(v___x_326_) == 1)
{
lean_object* v_val_327_; lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v___f_330_; lean_object* v___f_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_val_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_val_327_);
lean_dec_ref_known(v___x_326_, 1);
v_fst_328_ = lean_ctor_get(v_val_327_, 0);
lean_inc(v_fst_328_);
v_snd_329_ = lean_ctor_get(v_val_327_, 1);
lean_inc(v_snd_329_);
lean_dec(v_val_327_);
lean_inc(v_hoverPos_324_);
v___f_330_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_330_, 0, v_hoverPos_324_);
v___f_331_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0));
v___x_332_ = l_Lean_Elab_Info_stx(v_snd_329_);
v___x_333_ = l_Lean_Syntax_findStack_x3f(v___x_332_, v___f_330_, v___f_331_);
if (lean_obj_tag(v___x_333_) == 1)
{
lean_object* v_val_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_390_; 
v_val_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_390_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_390_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_val_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_390_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v_stack_338_; lean_object* v___x_339_; 
v_stack_338_ = l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(v_val_334_);
v___x_339_ = l_List_head_x3f___redArg(v_stack_338_);
if (lean_obj_tag(v___x_339_) == 1)
{
lean_object* v_val_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_388_; 
v_val_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_388_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_388_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_val_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_388_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v_fst_344_; uint8_t v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; uint8_t v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; uint8_t v_isDotIdCompletion_368_; lean_object* v_fst_370_; uint8_t v_snd_371_; 
v_fst_344_ = lean_ctor_get(v_val_340_, 0);
lean_inc(v_fst_344_);
lean_dec(v_val_340_);
v_isDotIdCompletion_368_ = l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(v_stack_338_);
if (v_isDotIdCompletion_368_ == 0)
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1));
lean_inc(v_fst_344_);
v___x_377_ = l_Lean_Syntax_isOfKind(v_fst_344_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = ((lean_object*)(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6));
lean_inc(v_fst_344_);
v___x_379_ = l_Lean_Syntax_isOfKind(v_fst_344_, v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; 
lean_dec(v_fst_344_);
lean_del_object(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_snd_329_);
lean_dec(v_fst_328_);
lean_dec(v_hoverPos_324_);
v___x_380_ = lean_box(0);
return v___x_380_;
}
else
{
lean_object* v___x_381_; lean_object* v_id_382_; uint8_t v___x_383_; 
v___x_381_ = lean_unsigned_to_nat(0u);
v_id_382_ = l_Lean_Syntax_getArg(v_fst_344_, v___x_381_);
lean_inc(v_id_382_);
v___x_383_ = l_Lean_Syntax_isOfKind(v_id_382_, v___x_376_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; 
lean_dec(v_id_382_);
lean_dec(v_fst_344_);
lean_del_object(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_snd_329_);
lean_dec(v_fst_328_);
lean_dec(v_hoverPos_324_);
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
v___x_386_ = l_Lean_TSyntax_getId(v_fst_344_);
v_fst_370_ = v___x_386_;
v_snd_371_ = v_isDotIdCompletion_368_;
goto v___jp_369_;
}
}
else
{
lean_object* v___x_387_; 
lean_dec(v_fst_344_);
lean_del_object(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_snd_329_);
lean_dec(v_fst_328_);
lean_dec(v_hoverPos_324_);
v___x_387_ = lean_box(0);
return v___x_387_;
}
v___jp_345_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_349_ = l_Lean_Elab_Info_lctx(v_snd_329_);
lean_dec(v_snd_329_);
v___x_350_ = lean_box(0);
v___x_351_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_351_, 0, v_fst_344_);
lean_ctor_set(v___x_351_, 1, v___y_347_);
lean_ctor_set(v___x_351_, 2, v___x_349_);
lean_ctor_set(v___x_351_, 3, v___x_350_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*4, v___y_346_);
v___x_352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_352_, 0, v___y_348_);
lean_ctor_set(v___x_352_, 1, v_fst_328_);
lean_ctor_set(v___x_352_, 2, v___x_351_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_352_);
v___x_354_ = v___x_342_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
v___jp_356_:
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = lean_nat_add(v_hoverPos_324_, v___x_360_);
v___x_362_ = lean_nat_dec_le(v___x_361_, v___y_359_);
lean_dec(v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec(v___y_359_);
lean_del_object(v___x_336_);
lean_dec(v_hoverPos_324_);
v___x_363_ = lean_box(0);
v___y_346_ = v___y_357_;
v___y_347_ = v___y_358_;
v___y_348_ = v___x_363_;
goto v___jp_345_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_364_ = lean_nat_sub(v___y_359_, v_hoverPos_324_);
lean_dec(v_hoverPos_324_);
lean_dec(v___y_359_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_364_);
v___x_366_ = v___x_336_;
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
v___y_346_ = v___y_357_;
v___y_347_ = v___y_358_;
v___y_348_ = v___x_366_;
goto v___jp_345_;
}
}
}
v___jp_369_:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Syntax_getTailPos_x3f(v_fst_344_, v_isDotIdCompletion_368_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_obj_once(&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4, &l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_once, _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4);
v___x_374_ = l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__2(v___x_373_);
v___y_357_ = v_snd_371_;
v___y_358_ = v_fst_370_;
v___y_359_ = v___x_374_;
goto v___jp_356_;
}
else
{
lean_object* v_val_375_; 
v_val_375_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_val_375_);
lean_dec_ref_known(v___x_372_, 1);
v___y_357_ = v_snd_371_;
v___y_358_ = v_fst_370_;
v___y_359_ = v_val_375_;
goto v___jp_356_;
}
}
}
}
else
{
lean_object* v___x_389_; 
lean_dec(v___x_339_);
lean_dec(v_stack_338_);
lean_del_object(v___x_336_);
lean_dec(v_snd_329_);
lean_dec(v_fst_328_);
lean_dec(v_hoverPos_324_);
v___x_389_ = lean_box(0);
return v___x_389_;
}
}
}
else
{
lean_object* v___x_391_; 
lean_dec(v___x_333_);
lean_dec(v_snd_329_);
lean_dec(v_fst_328_);
lean_dec(v_hoverPos_324_);
v___x_391_ = lean_box(0);
return v___x_391_;
}
}
else
{
lean_object* v___x_392_; 
lean_dec(v___x_326_);
lean_dec(v_hoverPos_324_);
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
uint32_t v___x_397_; uint32_t v___x_398_; uint8_t v___x_399_; 
v___x_397_ = lean_string_utf8_get(v_source_395_, v_hoverPos_394_);
v___x_398_ = 32;
v___x_399_ = lean_uint32_dec_eq(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
uint32_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 9;
v___x_401_ = lean_uint32_dec_eq(v___x_397_, v___x_400_);
if (v___x_401_ == 0)
{
uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 13;
v___x_403_ = lean_uint32_dec_eq(v___x_397_, v___x_402_);
if (v___x_403_ == 0)
{
uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = 10;
v___x_405_ = lean_uint32_dec_eq(v___x_397_, v___x_404_);
return v___x_405_;
}
else
{
return v___x_403_;
}
}
else
{
return v___x_401_;
}
}
else
{
return v___x_399_;
}
}
else
{
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace___boxed(lean_object* v_fileMap_406_, lean_object* v_hoverPos_407_){
_start:
{
uint8_t v_res_408_; lean_object* v_r_409_; 
v_res_408_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_406_, v_hoverPos_407_);
lean_dec(v_hoverPos_407_);
lean_dec_ref(v_fileMap_406_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(lean_object* v_fileMap_410_, lean_object* v_hoverPos_411_){
_start:
{
lean_object* v_source_412_; uint8_t v___y_426_; uint8_t v___x_427_; 
v_source_412_ = lean_ctor_get(v_fileMap_410_, 0);
v___x_427_ = lean_string_utf8_at_end(v_source_412_, v_hoverPos_411_);
if (v___x_427_ == 0)
{
uint32_t v___x_428_; uint32_t v___x_429_; uint8_t v___x_430_; 
v___x_428_ = lean_string_utf8_get(v_source_412_, v_hoverPos_411_);
v___x_429_ = 32;
v___x_430_ = lean_uint32_dec_eq(v___x_428_, v___x_429_);
if (v___x_430_ == 0)
{
uint32_t v___x_431_; uint8_t v___x_432_; 
v___x_431_ = 9;
v___x_432_ = lean_uint32_dec_eq(v___x_428_, v___x_431_);
if (v___x_432_ == 0)
{
uint32_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = 13;
v___x_434_ = lean_uint32_dec_eq(v___x_428_, v___x_433_);
if (v___x_434_ == 0)
{
uint32_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = 10;
v___x_436_ = lean_uint32_dec_eq(v___x_428_, v___x_435_);
v___y_426_ = v___x_436_;
goto v___jp_425_;
}
else
{
goto v___jp_413_;
}
}
else
{
goto v___jp_413_;
}
}
else
{
goto v___jp_413_;
}
}
else
{
v___y_426_ = v___x_427_;
goto v___jp_425_;
}
v___jp_413_:
{
lean_object* v___x_414_; lean_object* v___x_415_; uint32_t v___x_416_; uint32_t v___x_417_; uint8_t v___x_418_; 
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = lean_nat_sub(v_hoverPos_411_, v___x_414_);
v___x_416_ = lean_string_utf8_get(v_source_412_, v___x_415_);
lean_dec(v___x_415_);
v___x_417_ = 32;
v___x_418_ = lean_uint32_dec_eq(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
uint32_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 9;
v___x_420_ = lean_uint32_dec_eq(v___x_416_, v___x_419_);
if (v___x_420_ == 0)
{
uint32_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 13;
v___x_422_ = lean_uint32_dec_eq(v___x_416_, v___x_421_);
if (v___x_422_ == 0)
{
uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 10;
v___x_424_ = lean_uint32_dec_eq(v___x_416_, v___x_423_);
return v___x_424_;
}
else
{
return v___x_422_;
}
}
else
{
return v___x_420_;
}
}
else
{
return v___x_418_;
}
}
v___jp_425_:
{
if (v___y_426_ == 0)
{
return v___y_426_;
}
else
{
goto v___jp_413_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace___boxed(lean_object* v_fileMap_437_, lean_object* v_hoverPos_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_437_, v_hoverPos_438_);
lean_dec(v_hoverPos_438_);
lean_dec_ref(v_fileMap_437_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(lean_object* v_stx_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
lean_inc(v_stx_454_);
v___x_455_ = l_Lean_Syntax_getKind(v_stx_454_);
v___x_456_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2));
v___x_457_ = lean_name_eq(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_459_ = lean_name_eq(v___x_455_, v___x_458_);
lean_dec(v___x_455_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_dec(v_stx_454_);
v___x_460_ = lean_box(0);
return v___x_460_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = l_Lean_Syntax_getArg(v_stx_454_, v___x_461_);
lean_dec(v_stx_454_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec(v___x_455_);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = l_Lean_Syntax_getArg(v_stx_454_, v___x_464_);
lean_dec(v_stx_454_);
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(lean_object* v_fileMap_467_, lean_object* v_hoverPos_468_, lean_object* v_hoverFilePos_469_, lean_object* v_stx_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(v_stx_470_);
if (lean_obj_tag(v___x_471_) == 1)
{
lean_object* v_val_472_; uint8_t v___x_473_; lean_object* v___x_474_; 
v_val_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v___x_471_, 1);
v___x_473_ = 0;
v___x_474_ = l_Lean_Syntax_getPos_x3f(v_val_472_, v___x_473_);
lean_dec(v_val_472_);
if (lean_obj_tag(v___x_474_) == 1)
{
lean_object* v_val_475_; lean_object* v___x_476_; lean_object* v_column_477_; lean_object* v_column_478_; uint8_t v___x_479_; 
v_val_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_val_475_);
lean_dec_ref_known(v___x_474_, 1);
lean_inc_ref(v_fileMap_467_);
v___x_476_ = l_Lean_FileMap_toPosition(v_fileMap_467_, v_val_475_);
lean_dec(v_val_475_);
v_column_477_ = lean_ctor_get(v___x_476_, 1);
lean_inc(v_column_477_);
lean_dec_ref(v___x_476_);
v_column_478_ = lean_ctor_get(v_hoverFilePos_469_, 1);
v___x_479_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_467_, v_hoverPos_468_);
lean_dec_ref(v_fileMap_467_);
if (v___x_479_ == 0)
{
lean_dec(v_column_477_);
return v___x_479_;
}
else
{
uint8_t v_isCursorInTacticBlock_480_; 
v_isCursorInTacticBlock_480_ = lean_nat_dec_eq(v_column_478_, v_column_477_);
lean_dec(v_column_477_);
return v_isCursorInTacticBlock_480_;
}
}
else
{
lean_dec(v___x_474_);
lean_dec_ref(v_fileMap_467_);
return v___x_473_;
}
}
else
{
uint8_t v___x_481_; 
lean_dec(v___x_471_);
lean_dec_ref(v_fileMap_467_);
v___x_481_ = 0;
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation___boxed(lean_object* v_fileMap_482_, lean_object* v_hoverPos_483_, lean_object* v_hoverFilePos_484_, lean_object* v_stx_485_){
_start:
{
uint8_t v_res_486_; lean_object* v_r_487_; 
v_res_486_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_482_, v_hoverPos_483_, v_hoverFilePos_484_, v_stx_485_);
lean_dec_ref(v_hoverFilePos_484_);
lean_dec(v_hoverPos_483_);
v_r_487_ = lean_box(v_res_486_);
return v_r_487_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(lean_object* v_hoverPos_489_, lean_object* v_as_490_, size_t v_i_491_, size_t v_stop_492_){
_start:
{
uint8_t v___x_497_; 
v___x_497_ = lean_usize_dec_eq(v_i_491_, v_stop_492_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_array_uget_borrowed(v_as_490_, v_i_491_);
v___x_499_ = l_Lean_Syntax_getTailPos_x3f(v___x_498_, v___x_497_);
if (lean_obj_tag(v___x_499_) == 1)
{
lean_object* v_val_500_; uint8_t v___x_501_; uint8_t v___y_503_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_val_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_val_500_);
lean_dec_ref_known(v___x_499_, 1);
v___x_501_ = 1;
v___x_507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___closed__0));
lean_inc(v___x_498_);
v___x_508_ = l_Lean_Syntax_isToken(v___x_507_, v___x_498_);
if (v___x_508_ == 0)
{
v___y_503_ = v___x_508_;
goto v___jp_502_;
}
else
{
uint8_t v___x_509_; 
v___x_509_ = lean_nat_dec_le(v_val_500_, v_hoverPos_489_);
v___y_503_ = v___x_509_;
goto v___jp_502_;
}
v___jp_502_:
{
if (v___y_503_ == 0)
{
lean_dec(v_val_500_);
goto v___jp_493_;
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_504_ = l_Lean_Syntax_getTrailingSize(v___x_498_);
v___x_505_ = lean_nat_add(v_val_500_, v___x_504_);
lean_dec(v___x_504_);
lean_dec(v_val_500_);
v___x_506_ = lean_nat_dec_le(v_hoverPos_489_, v___x_505_);
lean_dec(v___x_505_);
if (v___x_506_ == 0)
{
goto v___jp_493_;
}
else
{
return v___x_501_;
}
}
}
}
else
{
lean_dec(v___x_499_);
goto v___jp_493_;
}
}
else
{
uint8_t v___x_510_; 
v___x_510_ = 0;
return v___x_510_;
}
v___jp_493_:
{
size_t v___x_494_; size_t v___x_495_; 
v___x_494_ = ((size_t)1ULL);
v___x_495_ = lean_usize_add(v_i_491_, v___x_494_);
v_i_491_ = v___x_495_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___boxed(lean_object* v_hoverPos_511_, lean_object* v_as_512_, lean_object* v_i_513_, lean_object* v_stop_514_){
_start:
{
size_t v_i_boxed_515_; size_t v_stop_boxed_516_; uint8_t v_res_517_; lean_object* v_r_518_; 
v_i_boxed_515_ = lean_unbox_usize(v_i_513_);
lean_dec(v_i_513_);
v_stop_boxed_516_ = lean_unbox_usize(v_stop_514_);
lean_dec(v_stop_514_);
v_res_517_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_511_, v_as_512_, v_i_boxed_515_, v_stop_boxed_516_);
lean_dec_ref(v_as_512_);
lean_dec(v_hoverPos_511_);
v_r_518_ = lean_box(v_res_517_);
return v_r_518_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(lean_object* v_fileMap_519_, lean_object* v_hoverPos_520_, lean_object* v_stx_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(v_stx_521_);
if (lean_obj_tag(v___x_522_) == 1)
{
lean_object* v_val_523_; uint8_t v___x_524_; 
v_val_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_519_, v_hoverPos_520_);
if (v___x_524_ == 0)
{
lean_dec(v_val_523_);
return v___x_524_;
}
else
{
lean_object* v_tactics_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_tactics_525_ = l_Lean_Syntax_getArgs(v_val_523_);
lean_dec(v_val_523_);
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = lean_array_get_size(v_tactics_525_);
v___x_528_ = lean_nat_dec_lt(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
lean_dec_ref(v_tactics_525_);
return v___x_528_;
}
else
{
if (v___x_528_ == 0)
{
lean_dec_ref(v_tactics_525_);
return v___x_528_;
}
else
{
size_t v___x_529_; size_t v___x_530_; uint8_t v___x_531_; 
v___x_529_ = ((size_t)0ULL);
v___x_530_ = lean_usize_of_nat(v___x_527_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_520_, v_tactics_525_, v___x_529_, v___x_530_);
lean_dec_ref(v_tactics_525_);
return v___x_531_;
}
}
}
}
else
{
uint8_t v___x_532_; 
lean_dec(v___x_522_);
v___x_532_ = 0;
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon___boxed(lean_object* v_fileMap_533_, lean_object* v_hoverPos_534_, lean_object* v_stx_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_533_, v_hoverPos_534_, v_stx_535_);
lean_dec(v_hoverPos_534_);
lean_dec_ref(v_fileMap_533_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(lean_object* v_fileMap_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_fst_540_; lean_object* v_snd_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_563_; 
v_fst_540_ = lean_ctor_get(v_a_539_, 0);
v_snd_541_ = lean_ctor_get(v_a_539_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_a_539_);
if (v_isSharedCheck_563_ == 0)
{
v___x_543_ = v_a_539_;
v_isShared_544_ = v_isSharedCheck_563_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_snd_541_);
lean_inc(v_fst_540_);
lean_dec(v_a_539_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_563_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v_source_545_; uint8_t v___x_546_; 
v_source_545_ = lean_ctor_get(v_fileMap_538_, 0);
v___x_546_ = lean_string_utf8_at_end(v_source_545_, v_fst_540_);
if (v___x_546_ == 0)
{
uint32_t v___x_547_; uint32_t v___x_548_; uint8_t v___x_549_; 
v___x_547_ = lean_string_utf8_get(v_source_545_, v_fst_540_);
v___x_548_ = 32;
v___x_549_ = lean_uint32_dec_eq(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_551_; 
if (v_isShared_544_ == 0)
{
v___x_551_ = v___x_543_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_fst_540_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_snd_541_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_553_ = lean_string_utf8_next(v_source_545_, v_fst_540_);
lean_dec(v_fst_540_);
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_nat_add(v_snd_541_, v___x_554_);
lean_dec(v_snd_541_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v___x_555_);
lean_ctor_set(v___x_543_, 0, v___x_553_);
v___x_557_ = v___x_543_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_555_);
v___x_557_ = v_reuseFailAlloc_559_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
v_a_539_ = v___x_557_;
goto _start;
}
}
}
else
{
lean_object* v___x_561_; 
if (v_isShared_544_ == 0)
{
v___x_561_ = v___x_543_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_fst_540_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_snd_541_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg___boxed(lean_object* v_fileMap_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_564_, v_a_565_);
lean_dec_ref(v_fileMap_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(lean_object* v_fileMap_567_, lean_object* v_pos_568_){
_start:
{
lean_object* v_n_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v_snd_572_; 
v_n_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v_pos_568_);
lean_ctor_set(v___x_570_, 1, v_n_569_);
v___x_571_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_567_, v___x_570_);
v_snd_572_ = lean_ctor_get(v___x_571_, 1);
lean_inc(v_snd_572_);
lean_dec_ref(v___x_571_);
return v_snd_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces___boxed(lean_object* v_fileMap_573_, lean_object* v_pos_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(v_fileMap_573_, v_pos_574_);
lean_dec_ref(v_fileMap_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(lean_object* v_fileMap_576_, lean_object* v_inst_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_576_, v_a_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___boxed(lean_object* v_fileMap_580_, lean_object* v_inst_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(v_fileMap_580_, v_inst_581_, v_a_582_);
lean_dec_ref(v_fileMap_580_);
return v_res_583_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(lean_object* v_fileMap_584_, lean_object* v_hoverPos_585_, lean_object* v_leadingTokenTailPos_x3f_586_){
_start:
{
if (lean_obj_tag(v_leadingTokenTailPos_x3f_586_) == 1)
{
lean_object* v_val_587_; lean_object* v_hoverFilePos_588_; lean_object* v_line_589_; lean_object* v_column_590_; lean_object* v_tokenTailFilePos_591_; lean_object* v_line_592_; uint8_t v___x_593_; 
v_val_587_ = lean_ctor_get(v_leadingTokenTailPos_x3f_586_, 0);
lean_inc_ref_n(v_fileMap_584_, 2);
v_hoverFilePos_588_ = l_Lean_FileMap_toPosition(v_fileMap_584_, v_hoverPos_585_);
v_line_589_ = lean_ctor_get(v_hoverFilePos_588_, 0);
lean_inc(v_line_589_);
v_column_590_ = lean_ctor_get(v_hoverFilePos_588_, 1);
lean_inc(v_column_590_);
lean_dec_ref(v_hoverFilePos_588_);
v_tokenTailFilePos_591_ = l_Lean_FileMap_toPosition(v_fileMap_584_, v_val_587_);
v_line_592_ = lean_ctor_get(v_tokenTailFilePos_591_, 0);
lean_inc(v_line_592_);
lean_dec_ref(v_tokenTailFilePos_591_);
v___x_593_ = lean_nat_dec_eq(v_line_589_, v_line_592_);
lean_dec(v_line_589_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v_expectedColumn_597_; uint8_t v___x_598_; 
v___x_594_ = l_Lean_FileMap_lineStart(v_fileMap_584_, v_line_592_);
lean_dec(v_line_592_);
v___x_595_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(v_fileMap_584_, v___x_594_);
lean_dec_ref(v_fileMap_584_);
v___x_596_ = lean_unsigned_to_nat(2u);
v_expectedColumn_597_ = lean_nat_add(v___x_595_, v___x_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_nat_dec_eq(v_column_590_, v_expectedColumn_597_);
lean_dec(v_expectedColumn_597_);
lean_dec(v_column_590_);
return v___x_598_;
}
else
{
uint8_t v___x_599_; 
lean_dec(v_line_592_);
lean_dec(v_column_590_);
lean_dec_ref(v_fileMap_584_);
v___x_599_ = lean_nat_dec_le(v_val_587_, v_hoverPos_585_);
return v___x_599_;
}
}
else
{
uint8_t v___x_600_; 
lean_dec_ref(v_fileMap_584_);
v___x_600_ = 1;
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation___boxed(lean_object* v_fileMap_601_, lean_object* v_hoverPos_602_, lean_object* v_leadingTokenTailPos_x3f_603_){
_start:
{
uint8_t v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(v_fileMap_601_, v_hoverPos_602_, v_leadingTokenTailPos_x3f_603_);
lean_dec(v_leadingTokenTailPos_x3f_603_);
lean_dec(v_hoverPos_602_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(lean_object* v_a_606_){
_start:
{
switch(lean_obj_tag(v_a_606_))
{
case 0:
{
uint8_t v___x_607_; 
v___x_607_ = 1;
return v___x_607_;
}
case 1:
{
lean_object* v_args_608_; lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_args_608_ = lean_ctor_get(v_a_606_, 2);
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = lean_array_get_size(v_args_608_);
v___x_611_ = lean_nat_dec_lt(v___x_609_, v___x_610_);
if (v___x_611_ == 0)
{
uint8_t v___x_612_; 
v___x_612_ = 1;
return v___x_612_;
}
else
{
if (v___x_611_ == 0)
{
return v___x_611_;
}
else
{
size_t v___x_613_; size_t v___x_614_; uint8_t v___x_615_; 
v___x_613_ = ((size_t)0ULL);
v___x_614_ = lean_usize_of_nat(v___x_610_);
v___x_615_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_args_608_, v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
return v___x_611_;
}
else
{
uint8_t v___x_616_; 
v___x_616_ = 0;
return v___x_616_;
}
}
}
}
default: 
{
uint8_t v___x_617_; 
v___x_617_ = 0;
return v___x_617_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(lean_object* v_as_618_, size_t v_i_619_, size_t v_stop_620_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = lean_usize_dec_eq(v_i_619_, v_stop_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_array_uget_borrowed(v_as_618_, v_i_619_);
v___x_623_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v___x_622_);
if (v___x_623_ == 0)
{
uint8_t v___x_624_; 
v___x_624_ = 1;
return v___x_624_;
}
else
{
size_t v___x_625_; size_t v___x_626_; 
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_add(v_i_619_, v___x_625_);
v_i_619_ = v___x_626_;
goto _start;
}
}
else
{
uint8_t v___x_628_; 
v___x_628_ = 0;
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0___boxed(lean_object* v_as_629_, lean_object* v_i_630_, lean_object* v_stop_631_){
_start:
{
size_t v_i_boxed_632_; size_t v_stop_boxed_633_; uint8_t v_res_634_; lean_object* v_r_635_; 
v_i_boxed_632_ = lean_unbox_usize(v_i_630_);
lean_dec(v_i_630_);
v_stop_boxed_633_ = lean_unbox_usize(v_stop_631_);
lean_dec(v_stop_631_);
v_res_634_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_as_629_, v_i_boxed_632_, v_stop_boxed_633_);
lean_dec_ref(v_as_629_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty___boxed(lean_object* v_a_636_){
_start:
{
uint8_t v_res_637_; lean_object* v_r_638_; 
v_res_637_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_a_636_);
lean_dec(v_a_636_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(lean_object* v_stx_645_){
_start:
{
uint8_t v___y_647_; uint8_t v___y_655_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
lean_inc(v_stx_645_);
v___x_660_ = l_Lean_Syntax_getKind(v_stx_645_);
v___x_661_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1));
v___x_662_ = lean_name_eq(v___x_660_, v___x_661_);
lean_dec(v___x_660_);
if (v___x_662_ == 0)
{
v___y_655_ = v___x_662_;
goto v___jp_654_;
}
else
{
uint8_t v___x_663_; 
v___x_663_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_stx_645_);
v___y_655_ = v___x_663_;
goto v___jp_654_;
}
v___jp_646_:
{
if (v___y_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
lean_inc(v_stx_645_);
v___x_648_ = l_Lean_Syntax_getKind(v_stx_645_);
v___x_649_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_650_ = lean_name_eq(v___x_648_, v___x_649_);
lean_dec(v___x_648_);
if (v___x_650_ == 0)
{
lean_dec(v_stx_645_);
return v___x_650_;
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = l_Lean_Syntax_getArg(v_stx_645_, v___x_651_);
lean_dec(v_stx_645_);
v___x_653_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v___x_652_);
lean_dec(v___x_652_);
return v___x_653_;
}
}
else
{
lean_dec(v_stx_645_);
return v___y_647_;
}
}
v___jp_654_:
{
if (v___y_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
lean_inc(v_stx_645_);
v___x_656_ = l_Lean_Syntax_getKind(v_stx_645_);
v___x_657_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2));
v___x_658_ = lean_name_eq(v___x_656_, v___x_657_);
lean_dec(v___x_656_);
if (v___x_658_ == 0)
{
v___y_647_ = v___x_658_;
goto v___jp_646_;
}
else
{
uint8_t v___x_659_; 
v___x_659_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_stx_645_);
v___y_647_ = v___x_659_;
goto v___jp_646_;
}
}
else
{
lean_dec(v_stx_645_);
return v___y_655_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___boxed(lean_object* v_stx_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_664_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(lean_object* v_fileMap_667_, lean_object* v_hoverPos_668_, lean_object* v_stx_669_, lean_object* v_leadingTokenTailPos_x3f_670_){
_start:
{
uint8_t v___x_671_; 
v___x_671_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_667_, v_hoverPos_668_);
if (v___x_671_ == 0)
{
lean_dec(v_stx_669_);
lean_dec_ref(v_fileMap_667_);
return v___x_671_;
}
else
{
uint8_t v___x_672_; uint8_t v___x_673_; 
v___x_672_ = 0;
lean_inc(v_stx_669_);
v___x_673_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_669_);
if (v___x_673_ == 0)
{
lean_dec(v_stx_669_);
lean_dec_ref(v_fileMap_667_);
return v___x_672_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
lean_inc(v_stx_669_);
v___x_674_ = l_Lean_Syntax_getKind(v_stx_669_);
v___x_675_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4));
v___x_676_ = lean_name_eq(v___x_674_, v___x_675_);
lean_dec(v___x_674_);
if (v___x_676_ == 0)
{
uint8_t v___x_677_; 
lean_dec(v_stx_669_);
v___x_677_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(v_fileMap_667_, v_hoverPos_668_, v_leadingTokenTailPos_x3f_670_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec_ref(v_fileMap_667_);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = l_Lean_Syntax_getArg(v_stx_669_, v___x_678_);
v___x_680_ = l_Lean_Syntax_getTailPos_x3f(v___x_679_, v___x_672_);
lean_dec(v___x_679_);
if (lean_obj_tag(v___x_680_) == 1)
{
lean_object* v_val_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_val_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_val_681_);
lean_dec_ref_known(v___x_680_, 1);
v___x_682_ = lean_unsigned_to_nat(2u);
v___x_683_ = l_Lean_Syntax_getArg(v_stx_669_, v___x_682_);
lean_dec(v_stx_669_);
v___x_684_ = l_Lean_Syntax_getPos_x3f(v___x_683_, v___x_672_);
lean_dec(v___x_683_);
if (lean_obj_tag(v___x_684_) == 1)
{
lean_object* v_val_685_; uint8_t v___x_686_; 
v_val_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_val_685_);
lean_dec_ref_known(v___x_684_, 1);
v___x_686_ = lean_nat_dec_le(v_val_681_, v_hoverPos_668_);
lean_dec(v_val_681_);
if (v___x_686_ == 0)
{
lean_dec(v_val_685_);
return v___x_672_;
}
else
{
uint8_t v___x_687_; 
v___x_687_ = lean_nat_dec_le(v_hoverPos_668_, v_val_685_);
lean_dec(v_val_685_);
return v___x_687_;
}
}
else
{
lean_dec(v___x_684_);
lean_dec(v_val_681_);
return v___x_672_;
}
}
else
{
lean_dec(v___x_680_);
lean_dec(v_stx_669_);
return v___x_672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock___boxed(lean_object* v_fileMap_688_, lean_object* v_hoverPos_689_, lean_object* v_stx_690_, lean_object* v_leadingTokenTailPos_x3f_691_){
_start:
{
uint8_t v_res_692_; lean_object* v_r_693_; 
v_res_692_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_688_, v_hoverPos_689_, v_stx_690_, v_leadingTokenTailPos_x3f_691_);
lean_dec(v_leadingTokenTailPos_x3f_691_);
lean_dec(v_hoverPos_689_);
v_r_693_ = lean_box(v_res_692_);
return v_r_693_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(lean_object* v_fileMap_694_, lean_object* v_hoverPos_695_, lean_object* v_hoverFilePos_696_, lean_object* v_stx_697_, lean_object* v_leadingWs_698_, lean_object* v_leadingTokenTailPos_x3f_699_){
_start:
{
uint8_t v___x_700_; lean_object* v___x_701_; 
v___x_700_ = 0;
v___x_701_ = l_Lean_Syntax_getPos_x3f(v_stx_697_, v___x_700_);
if (lean_obj_tag(v___x_701_) == 1)
{
lean_object* v_val_702_; lean_object* v___x_703_; 
v_val_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_val_702_);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = l_Lean_Syntax_getTailPos_x3f(v_stx_697_, v___x_700_);
if (lean_obj_tag(v___x_703_) == 1)
{
lean_object* v_val_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_val_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_val_704_);
lean_dec_ref_known(v___x_703_, 1);
v___x_705_ = lean_nat_sub(v_val_702_, v_leadingWs_698_);
lean_dec(v_val_702_);
v___x_706_ = lean_nat_dec_le(v___x_705_, v_hoverPos_695_);
lean_dec(v___x_705_);
if (v___x_706_ == 0)
{
lean_dec(v_val_704_);
lean_dec(v_leadingTokenTailPos_x3f_699_);
lean_dec(v_leadingWs_698_);
lean_dec(v_stx_697_);
lean_dec_ref(v_fileMap_694_);
return v___x_706_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_707_ = l_Lean_Syntax_getTrailingSize(v_stx_697_);
v___x_708_ = lean_nat_add(v_val_704_, v___x_707_);
lean_dec(v___x_707_);
lean_dec(v_val_704_);
v___x_709_ = lean_nat_dec_le(v_hoverPos_695_, v___x_708_);
if (v___x_709_ == 0)
{
lean_dec(v___x_708_);
lean_dec(v_leadingTokenTailPos_x3f_699_);
lean_dec(v_leadingWs_698_);
lean_dec(v_stx_697_);
lean_dec_ref(v_fileMap_694_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; size_t v_sz_714_; size_t v___x_715_; lean_object* v___x_716_; lean_object* v_fst_717_; 
v___x_710_ = l_Lean_Syntax_getArgs(v_stx_697_);
v___x_711_ = lean_box(0);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_leadingWs_698_);
lean_ctor_set(v___x_712_, 1, v_leadingTokenTailPos_x3f_699_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v_sz_714_ = lean_array_size(v___x_710_);
v___x_715_ = ((size_t)0ULL);
lean_inc_ref(v_fileMap_694_);
v___x_716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_694_, v_hoverPos_695_, v_hoverFilePos_696_, v_hoverPos_695_, v___x_708_, v___x_710_, v_sz_714_, v___x_715_, v___x_713_);
lean_dec_ref(v___x_710_);
lean_dec(v___x_708_);
v_fst_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_fst_717_);
if (lean_obj_tag(v_fst_717_) == 0)
{
lean_object* v_snd_718_; lean_object* v_snd_719_; uint8_t v___x_720_; 
v_snd_718_ = lean_ctor_get(v___x_716_, 1);
lean_inc(v_snd_718_);
lean_dec_ref(v___x_716_);
v_snd_719_ = lean_ctor_get(v_snd_718_, 1);
lean_inc(v_snd_719_);
lean_dec(v_snd_718_);
lean_inc(v_stx_697_);
lean_inc_ref(v_fileMap_694_);
v___x_720_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_694_, v_hoverPos_695_, v_stx_697_, v_snd_719_);
lean_dec(v_snd_719_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; 
lean_inc(v_stx_697_);
v___x_721_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_694_, v_hoverPos_695_, v_stx_697_);
if (v___x_721_ == 0)
{
uint8_t v___x_722_; 
v___x_722_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_694_, v_hoverPos_695_, v_hoverFilePos_696_, v_stx_697_);
return v___x_722_;
}
else
{
lean_dec(v_stx_697_);
lean_dec_ref(v_fileMap_694_);
return v___x_709_;
}
}
else
{
lean_dec(v_stx_697_);
lean_dec_ref(v_fileMap_694_);
return v___x_709_;
}
}
else
{
lean_object* v_val_723_; uint8_t v___x_724_; 
lean_dec_ref(v___x_716_);
lean_dec(v_stx_697_);
lean_dec_ref(v_fileMap_694_);
v_val_723_ = lean_ctor_get(v_fst_717_, 0);
lean_inc(v_val_723_);
lean_dec_ref_known(v_fst_717_, 1);
v___x_724_ = lean_unbox(v_val_723_);
lean_dec(v_val_723_);
return v___x_724_;
}
}
}
}
else
{
uint8_t v___x_725_; 
lean_dec(v___x_703_);
lean_dec(v_val_702_);
lean_dec(v_leadingWs_698_);
v___x_725_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_694_, v_hoverPos_695_, v_stx_697_, v_leadingTokenTailPos_x3f_699_);
lean_dec(v_leadingTokenTailPos_x3f_699_);
return v___x_725_;
}
}
else
{
uint8_t v___x_726_; 
lean_dec(v___x_701_);
lean_dec(v_leadingWs_698_);
v___x_726_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_694_, v_hoverPos_695_, v_stx_697_, v_leadingTokenTailPos_x3f_699_);
lean_dec(v_leadingTokenTailPos_x3f_699_);
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(lean_object* v_fileMap_727_, lean_object* v_hoverPos_728_, lean_object* v_hoverFilePos_729_, lean_object* v___x_730_, lean_object* v___x_731_, lean_object* v_as_732_, size_t v_sz_733_, size_t v_i_734_, lean_object* v_b_735_){
_start:
{
uint8_t v___x_736_; 
v___x_736_ = lean_usize_dec_lt(v_i_734_, v_sz_733_);
if (v___x_736_ == 0)
{
lean_dec_ref(v_fileMap_727_);
return v_b_735_;
}
else
{
lean_object* v_snd_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_772_; 
v_snd_737_ = lean_ctor_get(v_b_735_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v_b_735_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; 
v_unused_773_ = lean_ctor_get(v_b_735_, 0);
lean_dec(v_unused_773_);
v___x_739_ = v_b_735_;
v_isShared_740_ = v_isSharedCheck_772_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_snd_737_);
lean_dec(v_b_735_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_772_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_fst_741_; lean_object* v_snd_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_771_; 
v_fst_741_ = lean_ctor_get(v_snd_737_, 0);
v_snd_742_ = lean_ctor_get(v_snd_737_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_snd_737_);
if (v_isSharedCheck_771_ == 0)
{
v___x_744_ = v_snd_737_;
v_isShared_745_ = v_isSharedCheck_771_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_snd_742_);
lean_inc(v_fst_741_);
lean_dec(v_snd_737_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_771_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_a_746_; uint8_t v___x_747_; 
v_a_746_ = lean_array_uget_borrowed(v_as_732_, v_i_734_);
lean_inc(v_snd_742_);
lean_inc(v_fst_741_);
lean_inc(v_a_746_);
lean_inc_ref(v_fileMap_727_);
v___x_747_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_727_, v_hoverPos_728_, v_hoverFilePos_729_, v_a_746_, v_fst_741_, v_snd_742_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___y_751_; lean_object* v___x_761_; 
lean_dec(v_fst_741_);
v___x_748_ = lean_box(0);
v___x_749_ = l_Lean_Syntax_getTrailingSize(v_a_746_);
v___x_761_ = l_Lean_Syntax_getTailPos_x3f(v_a_746_, v___x_747_);
if (lean_obj_tag(v___x_761_) == 0)
{
v___y_751_ = v_snd_742_;
goto v___jp_750_;
}
else
{
lean_dec(v_snd_742_);
v___y_751_ = v___x_761_;
goto v___jp_750_;
}
v___jp_750_:
{
lean_object* v___x_753_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v___y_751_);
lean_ctor_set(v___x_744_, 0, v___x_749_);
v___x_753_ = v___x_744_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___y_751_);
v___x_753_ = v_reuseFailAlloc_760_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_753_);
lean_ctor_set(v___x_739_, 0, v___x_748_);
v___x_755_ = v___x_739_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v___x_753_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
size_t v___x_756_; size_t v___x_757_; 
v___x_756_ = ((size_t)1ULL);
v___x_757_ = lean_usize_add(v_i_734_, v___x_756_);
v_i_734_ = v___x_757_;
v_b_735_ = v___x_755_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
lean_dec_ref(v_fileMap_727_);
v___x_762_ = lean_nat_dec_le(v___x_730_, v___x_731_);
v___x_763_ = lean_box(v___x_762_);
v___x_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
if (v_isShared_745_ == 0)
{
v___x_766_ = v___x_744_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_fst_741_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_snd_742_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_766_);
lean_ctor_set(v___x_739_, 0, v___x_764_);
v___x_768_ = v___x_739_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0___boxed(lean_object* v_fileMap_774_, lean_object* v_hoverPos_775_, lean_object* v_hoverFilePos_776_, lean_object* v___x_777_, lean_object* v___x_778_, lean_object* v_as_779_, lean_object* v_sz_780_, lean_object* v_i_781_, lean_object* v_b_782_){
_start:
{
size_t v_sz_boxed_783_; size_t v_i_boxed_784_; lean_object* v_res_785_; 
v_sz_boxed_783_ = lean_unbox_usize(v_sz_780_);
lean_dec(v_sz_780_);
v_i_boxed_784_ = lean_unbox_usize(v_i_781_);
lean_dec(v_i_781_);
v_res_785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_774_, v_hoverPos_775_, v_hoverFilePos_776_, v___x_777_, v___x_778_, v_as_779_, v_sz_boxed_783_, v_i_boxed_784_, v_b_782_);
lean_dec_ref(v_as_779_);
lean_dec(v___x_778_);
lean_dec(v___x_777_);
lean_dec_ref(v_hoverFilePos_776_);
lean_dec(v_hoverPos_775_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go___boxed(lean_object* v_fileMap_786_, lean_object* v_hoverPos_787_, lean_object* v_hoverFilePos_788_, lean_object* v_stx_789_, lean_object* v_leadingWs_790_, lean_object* v_leadingTokenTailPos_x3f_791_){
_start:
{
uint8_t v_res_792_; lean_object* v_r_793_; 
v_res_792_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_786_, v_hoverPos_787_, v_hoverFilePos_788_, v_stx_789_, v_leadingWs_790_, v_leadingTokenTailPos_x3f_791_);
lean_dec_ref(v_hoverFilePos_788_);
lean_dec(v_hoverPos_787_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(lean_object* v_fileMap_794_, lean_object* v_hoverPos_795_, lean_object* v_cmdStx_796_){
_start:
{
lean_object* v_hoverFilePos_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
lean_inc_ref(v_fileMap_794_);
v_hoverFilePos_797_ = l_Lean_FileMap_toPosition(v_fileMap_794_, v_hoverPos_795_);
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_box(0);
v___x_800_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_794_, v_hoverPos_795_, v_hoverFilePos_797_, v_cmdStx_796_, v___x_798_, v___x_799_);
lean_dec_ref(v_hoverFilePos_797_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion___boxed(lean_object* v_fileMap_801_, lean_object* v_hoverPos_802_, lean_object* v_cmdStx_803_){
_start:
{
uint8_t v_res_804_; lean_object* v_r_805_; 
v_res_804_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_801_, v_hoverPos_802_, v_cmdStx_803_);
lean_dec(v_hoverPos_802_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(lean_object* v_as_811_, size_t v_sz_812_, size_t v_i_813_, lean_object* v_b_814_){
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
v___x_818_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_a_817_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(lean_object* v_as_825_, size_t v_sz_826_, size_t v_i_827_, lean_object* v_b_828_){
_start:
{
uint8_t v___x_829_; 
v___x_829_ = lean_usize_dec_lt(v_i_827_, v_sz_826_);
if (v___x_829_ == 0)
{
lean_inc_ref(v_b_828_);
return v_b_828_;
}
else
{
lean_object* v___x_830_; lean_object* v_a_831_; lean_object* v___x_832_; 
v___x_830_ = lean_box(0);
v_a_831_ = lean_array_uget_borrowed(v_as_825_, v_i_827_);
lean_inc(v_a_831_);
v___x_832_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_a_831_);
if (lean_obj_tag(v___x_832_) == 1)
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v___x_830_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; size_t v___x_836_; size_t v___x_837_; 
lean_dec(v___x_832_);
v___x_835_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v___x_836_ = ((size_t)1ULL);
v___x_837_ = lean_usize_add(v_i_827_, v___x_836_);
v_i_827_ = v___x_837_;
v_b_828_ = v___x_835_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(lean_object* v_x_839_){
_start:
{
if (lean_obj_tag(v_x_839_) == 0)
{
lean_object* v_cs_840_; lean_object* v___x_841_; lean_object* v___x_842_; size_t v_sz_843_; size_t v___x_844_; lean_object* v___x_845_; lean_object* v_fst_846_; 
v_cs_840_ = lean_ctor_get(v_x_839_, 0);
v___x_841_ = lean_box(0);
v___x_842_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_843_ = lean_array_size(v_cs_840_);
v___x_844_ = ((size_t)0ULL);
v___x_845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_cs_840_, v_sz_843_, v___x_844_, v___x_842_);
v_fst_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_fst_846_);
lean_dec_ref(v___x_845_);
if (lean_obj_tag(v_fst_846_) == 0)
{
return v___x_841_;
}
else
{
lean_object* v_val_847_; 
v_val_847_ = lean_ctor_get(v_fst_846_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v_fst_846_, 1);
return v_val_847_;
}
}
else
{
lean_object* v_vs_848_; lean_object* v___x_849_; lean_object* v___x_850_; size_t v_sz_851_; size_t v___x_852_; lean_object* v___x_853_; lean_object* v_fst_854_; 
v_vs_848_ = lean_ctor_get(v_x_839_, 0);
v___x_849_ = lean_box(0);
v___x_850_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_851_ = lean_array_size(v_vs_848_);
v___x_852_ = ((size_t)0ULL);
v___x_853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_vs_848_, v_sz_851_, v___x_852_, v___x_850_);
v_fst_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_fst_854_);
lean_dec_ref(v___x_853_);
if (lean_obj_tag(v_fst_854_) == 0)
{
return v___x_849_;
}
else
{
lean_object* v_val_855_; 
v_val_855_ = lean_ctor_get(v_fst_854_, 0);
lean_inc(v_val_855_);
lean_dec_ref_known(v_fst_854_, 1);
return v_val_855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(lean_object* v_t_856_){
_start:
{
lean_object* v_root_857_; lean_object* v_tail_858_; lean_object* v___x_859_; 
v_root_857_ = lean_ctor_get(v_t_856_, 0);
v_tail_858_ = lean_ctor_get(v_t_856_, 1);
v___x_859_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_root_857_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v___x_860_; size_t v_sz_861_; size_t v___x_862_; lean_object* v___x_863_; lean_object* v_fst_864_; 
v___x_860_ = ((lean_object*)(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0));
v_sz_861_ = lean_array_size(v_tail_858_);
v___x_862_ = ((size_t)0ULL);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_tail_858_, v_sz_861_, v___x_862_, v___x_860_);
v_fst_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_fst_864_);
lean_dec_ref(v___x_863_);
if (lean_obj_tag(v_fst_864_) == 0)
{
return v___x_859_;
}
else
{
lean_object* v_val_865_; 
v_val_865_ = lean_ctor_get(v_fst_864_, 0);
lean_inc(v_val_865_);
lean_dec_ref_known(v_fst_864_, 1);
return v_val_865_;
}
}
else
{
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(lean_object* v_i_866_){
_start:
{
switch(lean_obj_tag(v_i_866_))
{
case 0:
{
lean_object* v_i_867_; 
v_i_867_ = lean_ctor_get(v_i_866_, 0);
lean_inc_ref(v_i_867_);
if (lean_obj_tag(v_i_867_) == 0)
{
lean_object* v_info_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_878_; 
lean_dec_ref_known(v_i_866_, 2);
v_info_868_ = lean_ctor_get(v_i_867_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v_i_867_);
if (v_isSharedCheck_878_ == 0)
{
v___x_870_ = v_i_867_;
v_isShared_871_ = v_isSharedCheck_878_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_info_868_);
lean_dec(v_i_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_878_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_872_ = lean_box(0);
v___x_873_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go___closed__0));
v___x_874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_874_, 0, v_info_868_);
lean_ctor_set(v___x_874_, 1, v___x_872_);
lean_ctor_set(v___x_874_, 2, v___x_873_);
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 1);
lean_ctor_set(v___x_870_, 0, v___x_874_);
v___x_876_ = v___x_870_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
else
{
lean_object* v_t_879_; 
lean_dec_ref(v_i_867_);
v_t_879_ = lean_ctor_get(v_i_866_, 1);
lean_inc_ref(v_t_879_);
lean_dec_ref_known(v_i_866_, 2);
v_i_866_ = v_t_879_;
goto _start;
}
}
case 1:
{
lean_object* v_children_881_; lean_object* v___x_882_; 
v_children_881_ = lean_ctor_get(v_i_866_, 1);
lean_inc_ref(v_children_881_);
lean_dec_ref_known(v_i_866_, 2);
v___x_882_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(v_children_881_);
lean_dec_ref(v_children_881_);
return v___x_882_;
}
default: 
{
lean_object* v___x_883_; 
lean_dec_ref_known(v_i_866_, 1);
v___x_883_ = lean_box(0);
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___boxed(lean_object* v_t_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(v_t_884_);
lean_dec_ref(v_t_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1___boxed(lean_object* v_as_886_, lean_object* v_sz_887_, lean_object* v_i_888_, lean_object* v_b_889_){
_start:
{
size_t v_sz_boxed_890_; size_t v_i_boxed_891_; lean_object* v_res_892_; 
v_sz_boxed_890_ = lean_unbox_usize(v_sz_887_);
lean_dec(v_sz_887_);
v_i_boxed_891_ = lean_unbox_usize(v_i_888_);
lean_dec(v_i_888_);
v_res_892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_as_886_, v_sz_boxed_890_, v_i_boxed_891_, v_b_889_);
lean_dec_ref(v_b_889_);
lean_dec_ref(v_as_886_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1___boxed(lean_object* v_as_893_, lean_object* v_sz_894_, lean_object* v_i_895_, lean_object* v_b_896_){
_start:
{
size_t v_sz_boxed_897_; size_t v_i_boxed_898_; lean_object* v_res_899_; 
v_sz_boxed_897_ = lean_unbox_usize(v_sz_894_);
lean_dec(v_sz_894_);
v_i_boxed_898_ = lean_unbox_usize(v_i_895_);
lean_dec(v_i_895_);
v_res_899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_as_893_, v_sz_boxed_897_, v_i_boxed_898_, v_b_896_);
lean_dec_ref(v_b_896_);
lean_dec_ref(v_as_893_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0___boxed(lean_object* v_x_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_x_900_);
lean_dec_ref(v_x_900_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f(lean_object* v_i_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_i_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(lean_object* v_fileMap_906_, lean_object* v_hoverPos_907_, lean_object* v_cmdStx_908_, lean_object* v_infoTree_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_infoTree_909_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v___x_911_; 
lean_dec(v_cmdStx_908_);
lean_dec_ref(v_fileMap_906_);
v___x_911_ = lean_box(0);
return v___x_911_;
}
else
{
lean_object* v_val_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_924_; 
v_val_912_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_924_ == 0)
{
v___x_914_ = v___x_910_;
v_isShared_915_ = v_isSharedCheck_924_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_val_912_);
lean_dec(v___x_910_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_924_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
uint8_t v___x_916_; 
v___x_916_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_906_, v_hoverPos_907_, v_cmdStx_908_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
lean_del_object(v___x_914_);
lean_dec(v_val_912_);
v___x_917_ = lean_box(0);
return v___x_917_;
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_918_ = lean_box(0);
v___x_919_ = ((lean_object*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___closed__0));
v___x_920_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v_val_912_);
lean_ctor_set(v___x_920_, 2, v___x_919_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_920_);
v___x_922_ = v___x_914_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___boxed(lean_object* v_fileMap_925_, lean_object* v_hoverPos_926_, lean_object* v_cmdStx_927_, lean_object* v_infoTree_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(v_fileMap_925_, v_hoverPos_926_, v_cmdStx_927_, v_infoTree_928_);
lean_dec(v_hoverPos_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(lean_object* v_msg_930_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = l_Lean_instInhabitedExpr;
v___x_932_ = lean_panic_fn_borrowed(v___x_931_, v_msg_930_);
return v___x_932_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(lean_object* v_hoverPos_933_, lean_object* v_i_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_Elab_Info_pos_x3f(v_i_934_);
if (lean_obj_tag(v___x_935_) == 1)
{
lean_object* v_val_936_; lean_object* v___x_937_; 
v_val_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v___x_935_, 1);
v___x_937_ = l_Lean_Elab_Info_tailPos_x3f(v_i_934_);
if (lean_obj_tag(v___x_937_) == 1)
{
if (lean_obj_tag(v_i_934_) == 1)
{
lean_object* v_i_938_; lean_object* v_expectedType_x3f_939_; 
v_i_938_ = lean_ctor_get(v_i_934_, 0);
v_expectedType_x3f_939_ = lean_ctor_get(v_i_938_, 2);
if (lean_obj_tag(v_expectedType_x3f_939_) == 0)
{
uint8_t v___x_940_; 
lean_dec_ref_known(v___x_937_, 1);
lean_dec(v_val_936_);
v___x_940_ = 0;
return v___x_940_;
}
else
{
lean_object* v_val_941_; uint8_t v___x_942_; 
v_val_941_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_val_941_);
lean_dec_ref_known(v___x_937_, 1);
v___x_942_ = lean_nat_dec_le(v_val_936_, v_hoverPos_933_);
lean_dec(v_val_936_);
if (v___x_942_ == 0)
{
lean_dec(v_val_941_);
return v___x_942_;
}
else
{
uint8_t v___x_943_; 
v___x_943_ = lean_nat_dec_le(v_hoverPos_933_, v_val_941_);
lean_dec(v_val_941_);
return v___x_943_;
}
}
}
else
{
uint8_t v___x_944_; 
lean_dec_ref_known(v___x_937_, 1);
lean_dec(v_val_936_);
v___x_944_ = 0;
return v___x_944_;
}
}
else
{
uint8_t v___x_945_; 
lean_dec(v___x_937_);
lean_dec(v_val_936_);
v___x_945_ = 0;
return v___x_945_;
}
}
else
{
uint8_t v___x_946_; 
lean_dec(v___x_935_);
v___x_946_ = 0;
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed(lean_object* v_hoverPos_947_, lean_object* v_i_948_){
_start:
{
uint8_t v_res_949_; lean_object* v_r_950_; 
v_res_949_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(v_hoverPos_947_, v_i_948_);
lean_dec_ref(v_i_948_);
lean_dec(v_hoverPos_947_);
v_r_950_ = lean_box(v_res_949_);
return v_r_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt(lean_object* v_infoTree_951_, lean_object* v_hoverPos_952_){
_start:
{
lean_object* v___f_953_; lean_object* v___x_954_; 
v___f_953_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed), 2, 1);
lean_closure_set(v___f_953_, 0, v_hoverPos_952_);
v___x_954_ = l_Lean_Elab_InfoTree_smallestInfo_x3f(v___f_953_, v_infoTree_951_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v___x_955_; 
v___x_955_ = lean_box(0);
return v___x_955_;
}
else
{
lean_object* v_val_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_980_; 
v_val_956_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_980_ == 0)
{
v___x_958_ = v___x_954_;
v_isShared_959_ = v_isSharedCheck_980_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_val_956_);
lean_dec(v___x_954_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_980_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_fst_960_; lean_object* v_snd_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_979_; 
v_fst_960_ = lean_ctor_get(v_val_956_, 0);
v_snd_961_ = lean_ctor_get(v_val_956_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_val_956_);
if (v_isSharedCheck_979_ == 0)
{
v___x_963_ = v_val_956_;
v_isShared_964_ = v_isSharedCheck_979_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_snd_961_);
lean_inc(v_fst_960_);
lean_dec(v_val_956_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_979_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___y_966_; 
if (lean_obj_tag(v_snd_961_) == 1)
{
lean_object* v_i_973_; lean_object* v_expectedType_x3f_974_; 
v_i_973_ = lean_ctor_get(v_snd_961_, 0);
lean_inc_ref(v_i_973_);
lean_dec_ref_known(v_snd_961_, 1);
v_expectedType_x3f_974_ = lean_ctor_get(v_i_973_, 2);
lean_inc(v_expectedType_x3f_974_);
lean_dec_ref(v_i_973_);
if (lean_obj_tag(v_expectedType_x3f_974_) == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_obj_once(&l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4, &l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_once, _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4);
v___x_976_ = l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(v___x_975_);
v___y_966_ = v___x_976_;
goto v___jp_965_;
}
else
{
lean_object* v_val_977_; 
v_val_977_ = lean_ctor_get(v_expectedType_x3f_974_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v_expectedType_x3f_974_, 1);
v___y_966_ = v_val_977_;
goto v___jp_965_;
}
}
else
{
lean_object* v___x_978_; 
lean_del_object(v___x_963_);
lean_dec(v_snd_961_);
lean_dec(v_fst_960_);
lean_del_object(v___x_958_);
v___x_978_ = lean_box(0);
return v___x_978_;
}
v___jp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v___y_966_);
v___x_968_ = v___x_963_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_fst_960_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___y_966_);
v___x_968_ = v_reuseFailAlloc_972_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_970_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_968_);
v___x_970_ = v___x_958_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(lean_object* v_f_981_, lean_object* v_leadingToken_x3f_982_, lean_object* v_acc_983_, lean_object* v_stx_984_){
_start:
{
lean_object* v___f_985_; lean_object* v___f_986_; lean_object* v___f_987_; lean_object* v___f_988_; lean_object* v___f_989_; lean_object* v___f_990_; lean_object* v___f_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_acc_995_; 
v___f_985_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0));
v___f_986_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1));
v___f_987_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2));
v___f_988_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3));
v___f_989_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4));
v___f_990_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5));
v___f_991_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6));
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v___f_985_);
lean_ctor_set(v___x_992_, 1, v___f_986_);
v___x_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___f_987_);
lean_ctor_set(v___x_993_, 2, v___f_988_);
lean_ctor_set(v___x_993_, 3, v___f_989_);
lean_ctor_set(v___x_993_, 4, v___f_990_);
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v___f_991_);
lean_inc(v_f_981_);
lean_inc(v_stx_984_);
lean_inc(v_leadingToken_x3f_982_);
v_acc_995_ = lean_apply_3(v_f_981_, v_acc_983_, v_leadingToken_x3f_982_, v_stx_984_);
switch(lean_obj_tag(v_stx_984_))
{
case 0:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec_ref_known(v___x_994_, 2);
lean_dec(v_leadingToken_x3f_982_);
lean_dec(v_f_981_);
v___x_996_ = lean_box(0);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v_acc_995_);
return v___x_997_;
}
case 1:
{
lean_object* v_args_998_; lean_object* v___f_999_; lean_object* v_lastToken_x3f_1000_; lean_object* v___x_1001_; size_t v_sz_1002_; size_t v___x_1003_; lean_object* v___x_1004_; lean_object* v_fst_1005_; lean_object* v_snd_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_args_998_ = lean_ctor_get(v_stx_984_, 2);
lean_inc_ref(v_args_998_);
lean_dec_ref_known(v_stx_984_, 3);
v___f_999_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0), 5, 2);
lean_closure_set(v___f_999_, 0, v_f_981_);
lean_closure_set(v___f_999_, 1, v_leadingToken_x3f_982_);
v_lastToken_x3f_1000_ = lean_box(0);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v_acc_995_);
lean_ctor_set(v___x_1001_, 1, v_lastToken_x3f_1000_);
v_sz_1002_ = lean_array_size(v_args_998_);
v___x_1003_ = ((size_t)0ULL);
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_994_, v_args_998_, v___f_999_, v_sz_1002_, v___x_1003_, v___x_1001_);
v_fst_1005_ = lean_ctor_get(v___x_1004_, 0);
v_snd_1006_ = lean_ctor_get(v___x_1004_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1004_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_snd_1006_);
lean_inc(v_fst_1005_);
lean_dec(v___x_1004_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v_fst_1005_);
lean_ctor_set(v___x_1008_, 0, v_snd_1006_);
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_snd_1006_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_fst_1005_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
default: 
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec_ref_known(v___x_994_, 2);
lean_dec(v_leadingToken_x3f_982_);
lean_dec(v_f_981_);
v___x_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1014_, 0, v_stx_984_);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v_acc_995_);
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0(lean_object* v_f_1016_, lean_object* v_leadingToken_x3f_1017_, lean_object* v_a_1018_, lean_object* v_x_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v_fst_1026_; lean_object* v_snd_1027_; lean_object* v___y_1029_; 
v_fst_1026_ = lean_ctor_get(v___y_1020_, 0);
lean_inc(v_fst_1026_);
v_snd_1027_ = lean_ctor_get(v___y_1020_, 1);
lean_inc(v_snd_1027_);
lean_dec_ref(v___y_1020_);
if (lean_obj_tag(v_snd_1027_) == 0)
{
v___y_1029_ = v_leadingToken_x3f_1017_;
goto v___jp_1028_;
}
else
{
lean_dec(v_leadingToken_x3f_1017_);
lean_inc_ref(v_snd_1027_);
v___y_1029_ = v_snd_1027_;
goto v___jp_1028_;
}
v___jp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___y_1022_);
lean_ctor_set(v___x_1024_, 1, v___y_1023_);
v___x_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
v___jp_1028_:
{
lean_object* v___x_1030_; lean_object* v_fst_1031_; 
v___x_1030_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1016_, v___y_1029_, v_fst_1026_, v_a_1018_);
v_fst_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_fst_1031_);
if (lean_obj_tag(v_fst_1031_) == 0)
{
lean_object* v_snd_1032_; 
v_snd_1032_ = lean_ctor_get(v___x_1030_, 1);
lean_inc(v_snd_1032_);
lean_dec_ref(v___x_1030_);
v___y_1022_ = v_snd_1032_;
v___y_1023_ = v_snd_1027_;
goto v___jp_1021_;
}
else
{
lean_object* v_snd_1033_; 
lean_dec(v_snd_1027_);
v_snd_1033_ = lean_ctor_get(v___x_1030_, 1);
lean_inc(v_snd_1033_);
lean_dec_ref(v___x_1030_);
v___y_1022_ = v_snd_1033_;
v___y_1023_ = v_fst_1031_;
goto v___jp_1021_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(lean_object* v_00_u03b1_1034_, lean_object* v_f_1035_, lean_object* v_inst_1036_, lean_object* v_leadingToken_x3f_1037_, lean_object* v_acc_1038_, lean_object* v_stx_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1035_, v_leadingToken_x3f_1037_, v_acc_1038_, v_stx_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___boxed(lean_object* v_00_u03b1_1041_, lean_object* v_f_1042_, lean_object* v_inst_1043_, lean_object* v_leadingToken_x3f_1044_, lean_object* v_acc_1045_, lean_object* v_stx_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(v_00_u03b1_1041_, v_f_1042_, v_inst_1043_, v_leadingToken_x3f_1044_, v_acc_1045_, v_stx_1046_);
lean_dec(v_inst_1043_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(lean_object* v_f_1048_, lean_object* v_init_1049_, lean_object* v_stx_1050_){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v_snd_1053_; 
v___x_1051_ = lean_box(0);
v___x_1052_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_1048_, v___x_1051_, v_init_1049_, v_stx_1050_);
v_snd_1053_ = lean_ctor_get(v___x_1052_, 1);
lean_inc(v_snd_1053_);
lean_dec_ref(v___x_1052_);
return v_snd_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(lean_object* v_00_u03b1_1054_, lean_object* v_inst_1055_, lean_object* v_f_1056_, lean_object* v_init_1057_, lean_object* v_stx_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(v_f_1056_, v_init_1057_, v_stx_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___boxed(lean_object* v_00_u03b1_1060_, lean_object* v_inst_1061_, lean_object* v_f_1062_, lean_object* v_init_1063_, lean_object* v_stx_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(v_00_u03b1_1060_, v_inst_1061_, v_f_1062_, v_init_1063_, v_stx_1064_);
lean_dec(v_inst_1061_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(lean_object* v_p_1066_, lean_object* v_foundStx_x3f_1067_, lean_object* v_leadingToken_x3f_1068_, lean_object* v_stx_1069_){
_start:
{
if (lean_obj_tag(v_foundStx_x3f_1067_) == 0)
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
lean_inc(v_stx_1069_);
v___x_1070_ = lean_apply_2(v_p_1066_, v_leadingToken_x3f_1068_, v_stx_1069_);
v___x_1071_ = lean_unbox(v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec(v_stx_1069_);
return v_foundStx_x3f_1067_;
}
else
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_stx_1069_);
return v___x_1072_;
}
}
else
{
lean_dec(v_stx_1069_);
lean_dec(v_leadingToken_x3f_1068_);
lean_dec_ref(v_p_1066_);
lean_inc_ref(v_foundStx_x3f_1067_);
return v_foundStx_x3f_1067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed(lean_object* v_p_1073_, lean_object* v_foundStx_x3f_1074_, lean_object* v_leadingToken_x3f_1075_, lean_object* v_stx_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(v_p_1073_, v_foundStx_x3f_1074_, v_leadingToken_x3f_1075_, v_stx_1076_);
lean_dec(v_foundStx_x3f_1074_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f(lean_object* v_p_1078_, lean_object* v_stx_1079_){
_start:
{
lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___f_1080_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1080_, 0, v_p_1078_);
v___x_1081_ = lean_box(0);
v___x_1082_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(v___f_1080_, v___x_1081_, v_stx_1079_);
return v___x_1082_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(uint8_t v___y_1083_, lean_object* v_hoverPos_1084_, lean_object* v_as_1085_, size_t v_i_1086_, size_t v_stop_1087_){
_start:
{
uint8_t v___x_1092_; 
v___x_1092_ = lean_usize_dec_eq(v_i_1086_, v_stop_1087_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v_fst_1094_; lean_object* v_snd_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; uint8_t v___y_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1093_ = lean_array_uget_borrowed(v_as_1085_, v_i_1086_);
v_fst_1094_ = lean_ctor_get(v___x_1093_, 0);
v_snd_1095_ = lean_ctor_get(v___x_1093_, 1);
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = 1;
v___x_1100_ = lean_unsigned_to_nat(2u);
v___x_1101_ = lean_nat_mod(v_snd_1095_, v___x_1100_);
v___x_1102_ = lean_nat_dec_eq(v___x_1101_, v___x_1096_);
lean_dec(v___x_1101_);
if (v___x_1102_ == 0)
{
uint8_t v___x_1103_; 
v___x_1103_ = l_Lean_Syntax_isAtom(v_fst_1094_);
if (v___x_1103_ == 0)
{
v___y_1099_ = v___y_1083_;
goto v___jp_1098_;
}
else
{
if (v___y_1083_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_Syntax_getTailPos_x3f(v_fst_1094_, v___y_1083_);
if (lean_obj_tag(v___x_1104_) == 1)
{
lean_object* v_val_1105_; uint8_t v___x_1106_; 
v_val_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_val_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v___x_1106_ = lean_nat_dec_le(v_val_1105_, v_hoverPos_1084_);
if (v___x_1106_ == 0)
{
lean_dec(v_val_1105_);
goto v___jp_1088_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1107_ = l_Lean_Syntax_getTrailingSize(v_fst_1094_);
v___x_1108_ = lean_nat_add(v_val_1105_, v___x_1107_);
lean_dec(v___x_1107_);
lean_dec(v_val_1105_);
v___x_1109_ = lean_nat_dec_le(v_hoverPos_1084_, v___x_1108_);
lean_dec(v___x_1108_);
v___y_1099_ = v___x_1109_;
goto v___jp_1098_;
}
}
else
{
lean_dec(v___x_1104_);
goto v___jp_1088_;
}
}
else
{
return v___x_1097_;
}
}
}
else
{
v___y_1099_ = v___y_1083_;
goto v___jp_1098_;
}
v___jp_1098_:
{
if (v___y_1099_ == 0)
{
goto v___jp_1088_;
}
else
{
return v___x_1097_;
}
}
}
else
{
uint8_t v___x_1110_; 
v___x_1110_ = 0;
return v___x_1110_;
}
v___jp_1088_:
{
size_t v___x_1089_; size_t v___x_1090_; 
v___x_1089_ = ((size_t)1ULL);
v___x_1090_ = lean_usize_add(v_i_1086_, v___x_1089_);
v_i_1086_ = v___x_1090_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0___boxed(lean_object* v___y_1111_, lean_object* v_hoverPos_1112_, lean_object* v_as_1113_, lean_object* v_i_1114_, lean_object* v_stop_1115_){
_start:
{
uint8_t v___y_1669__boxed_1116_; size_t v_i_boxed_1117_; size_t v_stop_boxed_1118_; uint8_t v_res_1119_; lean_object* v_r_1120_; 
v___y_1669__boxed_1116_ = lean_unbox(v___y_1111_);
v_i_boxed_1117_ = lean_unbox_usize(v_i_1114_);
lean_dec(v_i_1114_);
v_stop_boxed_1118_ = lean_unbox_usize(v_stop_1115_);
lean_dec(v_stop_1115_);
v_res_1119_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(v___y_1669__boxed_1116_, v_hoverPos_1112_, v_as_1113_, v_i_boxed_1117_, v_stop_boxed_1118_);
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
lean_dec_ref_known(v___x_1147_, 1);
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
lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1154_ = l_Array_zipIdx___redArg(v_fieldsAndSeps_1151_, v___x_1149_);
v___x_1155_ = lean_array_get_size(v___x_1154_);
v___x_1156_ = lean_nat_dec_lt(v___x_1149_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_dec_ref(v___x_1154_);
v___y_1136_ = v___x_1156_;
goto v___jp_1135_;
}
else
{
if (v___x_1156_ == 0)
{
lean_dec_ref(v___x_1154_);
v___y_1136_ = v___x_1156_;
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
v___jp_1160_:
{
if (lean_obj_tag(v___y_1161_) == 1)
{
lean_object* v_val_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v_val_1162_ = lean_ctor_get(v___y_1161_, 0);
lean_inc(v_val_1162_);
lean_dec_ref_known(v___y_1161_, 1);
v___x_1163_ = lean_array_get_size(v_fieldsAndSeps_1151_);
v___x_1164_ = lean_nat_dec_eq(v___x_1163_, v___x_1149_);
if (v___x_1164_ == 0)
{
lean_dec(v_val_1162_);
lean_dec(v_val_1148_);
v___y_1153_ = v___x_1127_;
goto v___jp_1152_;
}
else
{
lean_object* v_outerBounds_1165_; uint8_t v___x_1166_; 
v_outerBounds_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_outerBounds_1165_, 0, v_val_1148_);
lean_ctor_set(v_outerBounds_1165_, 1, v_val_1162_);
v___x_1166_ = l_Lean_Syntax_Range_contains(v_outerBounds_1165_, v_hoverPos_1132_, v_isCursorOnWhitespace_1128_);
lean_dec_ref_known(v_outerBounds_1165_, 2);
if (v___x_1166_ == 0)
{
v___y_1153_ = v___x_1166_;
goto v___jp_1152_;
}
else
{
lean_dec_ref(v_fieldsAndSeps_1151_);
lean_dec(v_stx_1134_);
lean_dec_ref(v_fileMap_1130_);
return v_isCursorOnWhitespace_1128_;
}
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
lean_dec_ref_known(v___x_1137_, 1);
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
uint8_t v___x_1733__boxed_1177_; uint8_t v_isCursorOnWhitespace_boxed_1178_; uint8_t v_isCursorInProperWhitespace_boxed_1179_; uint8_t v_res_1180_; lean_object* v_r_1181_; 
v___x_1733__boxed_1177_ = lean_unbox(v___x_1169_);
v_isCursorOnWhitespace_boxed_1178_ = lean_unbox(v_isCursorOnWhitespace_1170_);
v_isCursorInProperWhitespace_boxed_1179_ = lean_unbox(v_isCursorInProperWhitespace_1171_);
v_res_1180_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(v___x_1733__boxed_1177_, v_isCursorOnWhitespace_boxed_1178_, v_isCursorInProperWhitespace_boxed_1179_, v_fileMap_1172_, v_hoverFilePos_1173_, v_hoverPos_1174_, v_leadingToken_x3f_1175_, v_stx_1176_);
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
lean_dec_ref_known(v___x_1193_, 1);
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
lean_dec_ref_known(v___x_1213_, 2);
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
lean_dec_ref_known(v___y_1237_, 1);
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion_SyntheticCompletion(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
