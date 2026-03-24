// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Pattern
// Imports: public import Lean.Elab.Tactic.Simp public import Lean.Elab.Tactic.Conv.Basic
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
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
uint8_t l_Lean_instBEqHeadIndex_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getRhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setMemoize(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_List_getLast_x3f___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "positive integer expected"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "'pattern' conv tactic failed, pattern was not found"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "'pattern' conv tactic failed, pattern was found only "};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " times but "};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " expected"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14;
static const lean_array_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "occurrence list is not distinct"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17;
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18_value;
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__21_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "occsWildcard"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "occsIndexed"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24_value;
static const lean_array_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__25_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__25_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "occs"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed(lean_object**);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pattern"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__4_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__5_value),LEAN_SCALAR_PTR_LITERAL(59, 139, 144, 223, 221, 17, 152, 53)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalPattern"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__3_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 226, 241, 79, 162, 140, 83, 90)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(105) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(142) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(105) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(105) << 1) | 1)),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4_value),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_a_8_);
lean_dec_ref(v___x_7_);
v___x_9_ = l_Lean_Meta_Simp_neutralConfig;
v___x_10_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___closed__0));
v___x_11_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_9_, v___x_10_, v_a_8_, v_a_3_, v_a_4_, v_a_5_);
return v___x_11_;
}
else
{
lean_object* v_a_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_19_; 
v_a_12_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_19_ == 0)
{
v___x_14_ = v___x_7_;
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_a_12_);
lean_dec(v___x_7_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
if (v_isShared_15_ == 0)
{
v___x_17_ = v___x_14_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_a_12_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___boxed(lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v_a_20_, v_a_21_, v_a_22_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec_ref(v_a_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v_a_25_, v_a_27_, v_a_28_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___boxed(lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(v_a_31_, v_a_32_, v_a_33_, v_a_34_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
lean_dec(v_a_32_);
lean_dec_ref(v_a_31_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(lean_object* v_pattern_39_, lean_object* v_e_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
lean_inc_ref(v_e_40_);
v___x_46_ = l_Lean_Expr_toHeadIndex(v_e_40_);
lean_inc_ref(v_pattern_39_);
v___x_47_ = l_Lean_Expr_toHeadIndex(v_pattern_39_);
v___x_48_ = l_Lean_instBEqHeadIndex_beq(v___x_46_, v___x_47_);
lean_dec(v___x_47_);
lean_dec(v___x_46_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec_ref(v_e_40_);
lean_dec_ref(v_pattern_39_);
v___x_49_ = lean_box(0);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v___x_51_; 
lean_inc(v_a_44_);
lean_inc_ref(v_a_43_);
lean_inc(v_a_42_);
lean_inc_ref(v_a_41_);
lean_inc_ref(v_e_40_);
lean_inc_ref(v_pattern_39_);
v___x_51_ = l_Lean_Meta_isExprDefEqGuarded(v_pattern_39_, v_e_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_98_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_98_ == 0)
{
v___x_54_ = v___x_51_;
v_isShared_55_ = v_isSharedCheck_98_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_51_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_98_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
uint8_t v___x_56_; 
v___x_56_ = lean_unbox(v_a_52_);
lean_dec(v_a_52_);
if (v___x_56_ == 0)
{
uint8_t v___x_57_; 
v___x_57_ = l_Lean_Expr_isApp(v_e_40_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_60_; 
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec_ref(v_e_40_);
lean_dec_ref(v_pattern_39_);
v___x_58_ = lean_box(0);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_58_);
v___x_60_ = v___x_54_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_58_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
else
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_del_object(v___x_54_);
v___x_62_ = l_Lean_Expr_appFn_x21(v_e_40_);
v___x_63_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_pattern_39_, v___x_62_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_a_64_);
if (lean_obj_tag(v_a_64_) == 0)
{
lean_dec_ref(v_e_40_);
return v___x_63_;
}
else
{
lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_90_; 
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; 
v_unused_91_ = lean_ctor_get(v___x_63_, 0);
lean_dec(v_unused_91_);
v___x_66_ = v___x_63_;
v_isShared_67_ = v_isSharedCheck_90_;
goto v_resetjp_65_;
}
else
{
lean_dec(v___x_63_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_90_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v_val_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_89_; 
v_val_68_ = lean_ctor_get(v_a_64_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v_a_64_);
if (v_isSharedCheck_89_ == 0)
{
v___x_70_ = v_a_64_;
v_isShared_71_ = v_isSharedCheck_89_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_val_68_);
lean_dec(v_a_64_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_89_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v_fst_72_; lean_object* v_snd_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_88_; 
v_fst_72_ = lean_ctor_get(v_val_68_, 0);
v_snd_73_ = lean_ctor_get(v_val_68_, 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v_val_68_);
if (v_isSharedCheck_88_ == 0)
{
v___x_75_ = v_val_68_;
v_isShared_76_ = v_isSharedCheck_88_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_snd_73_);
lean_inc(v_fst_72_);
lean_dec(v_val_68_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_88_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_77_ = l_Lean_Expr_appArg_x21(v_e_40_);
lean_dec_ref(v_e_40_);
v___x_78_ = lean_array_push(v_snd_73_, v___x_77_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_78_);
v___x_80_ = v___x_75_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_fst_72_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v___x_78_);
v___x_80_ = v_reuseFailAlloc_87_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_82_; 
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_80_);
v___x_82_ = v___x_70_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_80_);
v___x_82_ = v_reuseFailAlloc_86_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_84_; 
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 0, v___x_82_);
v___x_84_ = v___x_66_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_40_);
return v___x_63_;
}
}
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec_ref(v_pattern_39_);
v___x_92_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0));
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v_e_40_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_94_);
v___x_96_ = v___x_54_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
else
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec_ref(v_e_40_);
lean_dec_ref(v_pattern_39_);
v_a_99_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_51_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_51_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___boxed(lean_object* v_pattern_107_, lean_object* v_e_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_pattern_107_, v_e_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(lean_object* v_k_115_, uint8_t v_allowLevelAssignments_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_116_, v_k_115_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
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
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
v_a_131_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_122_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_122_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg___boxed(lean_object* v_k_139_, lean_object* v_allowLevelAssignments_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_146_; lean_object* v_res_147_; 
v_allowLevelAssignments_boxed_146_ = lean_unbox(v_allowLevelAssignments_140_);
v_res_147_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v_k_139_, v_allowLevelAssignments_boxed_146_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0(lean_object* v_00_u03b1_148_, lean_object* v_k_149_, uint8_t v_allowLevelAssignments_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v_k_149_, v_allowLevelAssignments_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___boxed(lean_object* v_00_u03b1_157_, lean_object* v_k_158_, lean_object* v_allowLevelAssignments_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_165_; lean_object* v_res_166_; 
v_allowLevelAssignments_boxed_165_ = lean_unbox(v_allowLevelAssignments_159_);
v_res_166_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0(v_00_u03b1_157_, v_k_158_, v_allowLevelAssignments_boxed_165_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
return v_res_166_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0(void){
_start:
{
uint8_t v___x_167_; uint64_t v___x_168_; 
v___x_167_ = 2;
v___x_168_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(lean_object* v_pattern_169_, lean_object* v_e_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_176_; 
lean_inc_ref(v___y_171_);
v___x_176_ = l_Lean_Meta_openAbstractMVarsResult(v_pattern_169_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v_snd_178_; lean_object* v_snd_179_; lean_object* v___x_180_; uint8_t v_foApprox_181_; uint8_t v_ctxApprox_182_; uint8_t v_quasiPatternApprox_183_; uint8_t v_constApprox_184_; uint8_t v_isDefEqStuckEx_185_; uint8_t v_unificationHints_186_; uint8_t v_proofIrrelevance_187_; uint8_t v_assignSyntheticOpaque_188_; uint8_t v_offsetCnstrs_189_; uint8_t v_etaStruct_190_; uint8_t v_univApprox_191_; uint8_t v_iota_192_; uint8_t v_beta_193_; uint8_t v_proj_194_; uint8_t v_zeta_195_; uint8_t v_zetaDelta_196_; uint8_t v_zetaUnused_197_; uint8_t v_zetaHave_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_238_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref(v___x_176_);
v_snd_178_ = lean_ctor_get(v_a_177_, 1);
lean_inc(v_snd_178_);
lean_dec(v_a_177_);
v_snd_179_ = lean_ctor_get(v_snd_178_, 1);
lean_inc(v_snd_179_);
lean_dec(v_snd_178_);
v___x_180_ = l_Lean_Meta_Context_config(v___y_171_);
v_foApprox_181_ = lean_ctor_get_uint8(v___x_180_, 0);
v_ctxApprox_182_ = lean_ctor_get_uint8(v___x_180_, 1);
v_quasiPatternApprox_183_ = lean_ctor_get_uint8(v___x_180_, 2);
v_constApprox_184_ = lean_ctor_get_uint8(v___x_180_, 3);
v_isDefEqStuckEx_185_ = lean_ctor_get_uint8(v___x_180_, 4);
v_unificationHints_186_ = lean_ctor_get_uint8(v___x_180_, 5);
v_proofIrrelevance_187_ = lean_ctor_get_uint8(v___x_180_, 6);
v_assignSyntheticOpaque_188_ = lean_ctor_get_uint8(v___x_180_, 7);
v_offsetCnstrs_189_ = lean_ctor_get_uint8(v___x_180_, 8);
v_etaStruct_190_ = lean_ctor_get_uint8(v___x_180_, 10);
v_univApprox_191_ = lean_ctor_get_uint8(v___x_180_, 11);
v_iota_192_ = lean_ctor_get_uint8(v___x_180_, 12);
v_beta_193_ = lean_ctor_get_uint8(v___x_180_, 13);
v_proj_194_ = lean_ctor_get_uint8(v___x_180_, 14);
v_zeta_195_ = lean_ctor_get_uint8(v___x_180_, 15);
v_zetaDelta_196_ = lean_ctor_get_uint8(v___x_180_, 16);
v_zetaUnused_197_ = lean_ctor_get_uint8(v___x_180_, 17);
v_zetaHave_198_ = lean_ctor_get_uint8(v___x_180_, 18);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_238_ == 0)
{
v___x_200_ = v___x_180_;
v_isShared_201_ = v_isSharedCheck_238_;
goto v_resetjp_199_;
}
else
{
lean_dec(v___x_180_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_238_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
uint8_t v_trackZetaDelta_202_; lean_object* v_zetaDeltaSet_203_; lean_object* v_lctx_204_; lean_object* v_localInstances_205_; lean_object* v_defEqCtx_x3f_206_; lean_object* v_synthPendingDepth_207_; lean_object* v_canUnfold_x3f_208_; uint8_t v_univApprox_209_; uint8_t v_inTypeClassResolution_210_; uint8_t v_cacheInferType_211_; uint8_t v___x_212_; lean_object* v_config_214_; 
v_trackZetaDelta_202_ = lean_ctor_get_uint8(v___y_171_, sizeof(void*)*7);
v_zetaDeltaSet_203_ = lean_ctor_get(v___y_171_, 1);
lean_inc(v_zetaDeltaSet_203_);
v_lctx_204_ = lean_ctor_get(v___y_171_, 2);
lean_inc_ref(v_lctx_204_);
v_localInstances_205_ = lean_ctor_get(v___y_171_, 3);
lean_inc_ref(v_localInstances_205_);
v_defEqCtx_x3f_206_ = lean_ctor_get(v___y_171_, 4);
lean_inc(v_defEqCtx_x3f_206_);
v_synthPendingDepth_207_ = lean_ctor_get(v___y_171_, 5);
lean_inc(v_synthPendingDepth_207_);
v_canUnfold_x3f_208_ = lean_ctor_get(v___y_171_, 6);
lean_inc(v_canUnfold_x3f_208_);
v_univApprox_209_ = lean_ctor_get_uint8(v___y_171_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_210_ = lean_ctor_get_uint8(v___y_171_, sizeof(void*)*7 + 2);
v_cacheInferType_211_ = lean_ctor_get_uint8(v___y_171_, sizeof(void*)*7 + 3);
v___x_212_ = 2;
if (v_isShared_201_ == 0)
{
v_config_214_ = v___x_200_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 0, v_foApprox_181_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 1, v_ctxApprox_182_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 2, v_quasiPatternApprox_183_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 3, v_constApprox_184_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 4, v_isDefEqStuckEx_185_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 5, v_unificationHints_186_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 6, v_proofIrrelevance_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 7, v_assignSyntheticOpaque_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 8, v_offsetCnstrs_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 10, v_etaStruct_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 11, v_univApprox_191_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 12, v_iota_192_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 13, v_beta_193_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 14, v_proj_194_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 15, v_zeta_195_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 16, v_zetaDelta_196_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 17, v_zetaUnused_197_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 18, v_zetaHave_198_);
v_config_214_ = v_reuseFailAlloc_237_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
uint64_t v___x_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_229_; 
lean_ctor_set_uint8(v_config_214_, 9, v___x_212_);
v___x_215_ = l_Lean_Meta_Context_configKey(v___y_171_);
v_isSharedCheck_229_ = !lean_is_exclusive(v___y_171_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; lean_object* v_unused_233_; lean_object* v_unused_234_; lean_object* v_unused_235_; lean_object* v_unused_236_; 
v_unused_230_ = lean_ctor_get(v___y_171_, 6);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v___y_171_, 5);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v___y_171_, 4);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v___y_171_, 3);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v___y_171_, 2);
lean_dec(v_unused_234_);
v_unused_235_ = lean_ctor_get(v___y_171_, 1);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v___y_171_, 0);
lean_dec(v_unused_236_);
v___x_217_ = v___y_171_;
v_isShared_218_ = v_isSharedCheck_229_;
goto v_resetjp_216_;
}
else
{
lean_dec(v___y_171_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_229_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
uint64_t v___x_219_; uint64_t v___x_220_; uint64_t v___x_221_; uint64_t v___x_222_; uint64_t v_key_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_219_ = 2ULL;
v___x_220_ = lean_uint64_shift_right(v___x_215_, v___x_219_);
v___x_221_ = lean_uint64_shift_left(v___x_220_, v___x_219_);
v___x_222_ = lean_uint64_once(&l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0);
v_key_223_ = lean_uint64_lor(v___x_221_, v___x_222_);
v___x_224_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_224_, 0, v_config_214_);
lean_ctor_set_uint64(v___x_224_, sizeof(void*)*1, v_key_223_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_224_);
v___x_226_ = v___x_217_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_zetaDeltaSet_203_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_lctx_204_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v_localInstances_205_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v_defEqCtx_x3f_206_);
lean_ctor_set(v_reuseFailAlloc_228_, 5, v_synthPendingDepth_207_);
lean_ctor_set(v_reuseFailAlloc_228_, 6, v_canUnfold_x3f_208_);
lean_ctor_set_uint8(v_reuseFailAlloc_228_, sizeof(void*)*7, v_trackZetaDelta_202_);
lean_ctor_set_uint8(v_reuseFailAlloc_228_, sizeof(void*)*7 + 1, v_univApprox_209_);
lean_ctor_set_uint8(v_reuseFailAlloc_228_, sizeof(void*)*7 + 2, v_inTypeClassResolution_210_);
lean_ctor_set_uint8(v_reuseFailAlloc_228_, sizeof(void*)*7 + 3, v_cacheInferType_211_);
v___x_226_ = v_reuseFailAlloc_228_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; 
v___x_227_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_snd_179_, v_e_170_, v___x_226_, v___y_172_, v___y_173_, v___y_174_);
return v___x_227_;
}
}
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec_ref(v_e_170_);
v_a_239_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_176_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_176_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed(lean_object* v_pattern_247_, lean_object* v_e_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(v_pattern_247_, v_e_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f(lean_object* v_pattern_255_, lean_object* v_e_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___f_262_; uint8_t v___x_263_; lean_object* v___x_264_; 
v___f_262_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_262_, 0, v_pattern_255_);
lean_closure_set(v___f_262_, 1, v_e_256_);
v___x_263_ = 0;
v___x_264_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v___f_262_, v___x_263_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___boxed(lean_object* v_pattern_265_, lean_object* v_e_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(v_pattern_265_, v_e_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(lean_object* v_x_273_){
_start:
{
if (lean_obj_tag(v_x_273_) == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_unsigned_to_nat(0u);
return v___x_274_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = lean_unsigned_to_nat(1u);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___boxed(lean_object* v_x_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(v_x_276_);
lean_dec_ref(v_x_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(lean_object* v_t_278_, lean_object* v_k_279_){
_start:
{
if (lean_obj_tag(v_t_278_) == 0)
{
lean_object* v_subgoals_280_; lean_object* v___x_281_; 
v_subgoals_280_ = lean_ctor_get(v_t_278_, 0);
lean_inc_ref(v_subgoals_280_);
lean_dec_ref(v_t_278_);
v___x_281_ = lean_apply_1(v_k_279_, v_subgoals_280_);
return v___x_281_;
}
else
{
lean_object* v_subgoals_282_; lean_object* v_idx_283_; lean_object* v_remaining_284_; lean_object* v___x_285_; 
v_subgoals_282_ = lean_ctor_get(v_t_278_, 0);
lean_inc_ref(v_subgoals_282_);
v_idx_283_ = lean_ctor_get(v_t_278_, 1);
lean_inc(v_idx_283_);
v_remaining_284_ = lean_ctor_get(v_t_278_, 2);
lean_inc(v_remaining_284_);
lean_dec_ref(v_t_278_);
v___x_285_ = lean_apply_3(v_k_279_, v_subgoals_282_, v_idx_283_, v_remaining_284_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(lean_object* v_motive_286_, lean_object* v_ctorIdx_287_, lean_object* v_t_288_, lean_object* v_h_289_, lean_object* v_k_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_288_, v_k_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___boxed(lean_object* v_motive_292_, lean_object* v_ctorIdx_293_, lean_object* v_t_294_, lean_object* v_h_295_, lean_object* v_k_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(v_motive_292_, v_ctorIdx_293_, v_t_294_, v_h_295_, v_k_296_);
lean_dec(v_ctorIdx_293_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim___redArg(lean_object* v_t_298_, lean_object* v_all_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_298_, v_all_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim(lean_object* v_motive_301_, lean_object* v_t_302_, lean_object* v_h_303_, lean_object* v_all_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_302_, v_all_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim___redArg(lean_object* v_t_306_, lean_object* v_occs_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_306_, v_occs_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim(lean_object* v_motive_309_, lean_object* v_t_310_, lean_object* v_h_311_, lean_object* v_occs_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_310_, v_occs_312_);
return v___x_313_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(lean_object* v_x_314_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
uint8_t v___x_315_; 
v___x_315_ = 0;
return v___x_315_;
}
else
{
lean_object* v_remaining_316_; uint8_t v___x_317_; 
v_remaining_316_ = lean_ctor_get(v_x_314_, 2);
v___x_317_ = l_List_isEmpty___redArg(v_remaining_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone___boxed(lean_object* v_x_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v_x_318_);
lean_dec_ref(v_x_318_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
uint8_t v___x_322_; 
v___x_322_ = 1;
return v___x_322_;
}
else
{
lean_object* v_remaining_323_; 
v_remaining_323_ = lean_ctor_get(v_x_321_, 2);
if (lean_obj_tag(v_remaining_323_) == 1)
{
lean_object* v_head_324_; lean_object* v_idx_325_; lean_object* v_fst_326_; uint8_t v___x_327_; 
v_head_324_ = lean_ctor_get(v_remaining_323_, 0);
v_idx_325_ = lean_ctor_get(v_x_321_, 1);
v_fst_326_ = lean_ctor_get(v_head_324_, 0);
v___x_327_ = lean_nat_dec_eq(v_idx_325_, v_fst_326_);
return v___x_327_;
}
else
{
uint8_t v___x_328_; 
v___x_328_ = 0;
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady___boxed(lean_object* v_x_329_){
_start:
{
uint8_t v_res_330_; lean_object* v_r_331_; 
v_res_330_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v_x_329_);
lean_dec_ref(v_x_329_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(lean_object* v_x_332_){
_start:
{
if (lean_obj_tag(v_x_332_) == 1)
{
lean_object* v_subgoals_333_; lean_object* v_idx_334_; lean_object* v_remaining_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_344_; 
v_subgoals_333_ = lean_ctor_get(v_x_332_, 0);
v_idx_334_ = lean_ctor_get(v_x_332_, 1);
v_remaining_335_ = lean_ctor_get(v_x_332_, 2);
v_isSharedCheck_344_ = !lean_is_exclusive(v_x_332_);
if (v_isSharedCheck_344_ == 0)
{
v___x_337_ = v_x_332_;
v_isShared_338_ = v_isSharedCheck_344_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_remaining_335_);
lean_inc(v_idx_334_);
lean_inc(v_subgoals_333_);
lean_dec(v_x_332_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_344_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_add(v_idx_334_, v___x_339_);
lean_dec(v_idx_334_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v___x_340_);
v___x_342_ = v___x_337_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_subgoals_333_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_remaining_335_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
else
{
return v_x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(lean_object* v_mvarId_345_, lean_object* v_x_346_){
_start:
{
if (lean_obj_tag(v_x_346_) == 0)
{
lean_object* v_subgoals_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_355_; 
v_subgoals_347_ = lean_ctor_get(v_x_346_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v_x_346_);
if (v_isSharedCheck_355_ == 0)
{
v___x_349_ = v_x_346_;
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_subgoals_347_);
lean_dec(v_x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_array_push(v_subgoals_347_, v_mvarId_345_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_351_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
else
{
lean_object* v_remaining_356_; 
v_remaining_356_ = lean_ctor_get(v_x_346_, 2);
if (lean_obj_tag(v_remaining_356_) == 1)
{
lean_object* v_head_357_; lean_object* v_subgoals_358_; lean_object* v_idx_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_379_; 
lean_inc_ref(v_remaining_356_);
v_head_357_ = lean_ctor_get(v_remaining_356_, 0);
lean_inc(v_head_357_);
v_subgoals_358_ = lean_ctor_get(v_x_346_, 0);
v_idx_359_ = lean_ctor_get(v_x_346_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v_x_346_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v_x_346_, 2);
lean_dec(v_unused_380_);
v___x_361_ = v_x_346_;
v_isShared_362_ = v_isSharedCheck_379_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_idx_359_);
lean_inc(v_subgoals_358_);
lean_dec(v_x_346_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_379_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v_tail_363_; lean_object* v_snd_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_377_; 
v_tail_363_ = lean_ctor_get(v_remaining_356_, 1);
lean_inc(v_tail_363_);
lean_dec_ref(v_remaining_356_);
v_snd_364_ = lean_ctor_get(v_head_357_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v_head_357_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v_head_357_, 0);
lean_dec(v_unused_378_);
v___x_366_ = v_head_357_;
v_isShared_367_ = v_isSharedCheck_377_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_snd_364_);
lean_dec(v_head_357_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_377_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v_mvarId_345_);
lean_ctor_set(v___x_366_, 0, v_snd_364_);
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_snd_364_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_mvarId_345_);
v___x_369_ = v_reuseFailAlloc_376_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_370_ = lean_array_push(v_subgoals_358_, v___x_369_);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_add(v_idx_359_, v___x_371_);
lean_dec(v_idx_359_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 2, v_tail_363_);
lean_ctor_set(v___x_361_, 1, v___x_372_);
lean_ctor_set(v___x_361_, 0, v___x_370_);
v___x_374_ = v___x_361_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_tail_363_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
else
{
lean_dec(v_mvarId_345_);
return v_x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(lean_object* v_as_381_, size_t v_sz_382_, size_t v_i_383_, lean_object* v_b_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
uint8_t v___x_390_; 
v___x_390_ = lean_usize_dec_lt(v_i_383_, v_sz_382_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v_b_384_);
return v___x_391_;
}
else
{
lean_object* v_a_392_; lean_object* v___x_393_; 
v_a_392_ = lean_array_uget_borrowed(v_as_381_, v_i_383_);
lean_inc(v___y_388_);
lean_inc_ref(v___y_387_);
lean_inc(v___y_386_);
lean_inc_ref(v___y_385_);
lean_inc(v_a_392_);
v___x_393_ = l_Lean_Meta_mkCongrFun(v_b_384_, v_a_392_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; size_t v___x_395_; size_t v___x_396_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
lean_dec_ref(v___x_393_);
v___x_395_ = ((size_t)1ULL);
v___x_396_ = lean_usize_add(v_i_383_, v___x_395_);
v_i_383_ = v___x_396_;
v_b_384_ = v_a_394_;
goto _start;
}
else
{
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg___boxed(lean_object* v_as_398_, lean_object* v_sz_399_, lean_object* v_i_400_, lean_object* v_b_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
size_t v_sz_boxed_407_; size_t v_i_boxed_408_; lean_object* v_res_409_; 
v_sz_boxed_407_ = lean_unbox_usize(v_sz_399_);
lean_dec(v_sz_399_);
v_i_boxed_408_ = lean_unbox_usize(v_i_400_);
lean_dec(v_i_400_);
v_res_409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_398_, v_sz_boxed_407_, v_i_boxed_408_, v_b_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec_ref(v_as_398_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(lean_object* v_pattern_412_, lean_object* v_state_413_, lean_object* v_e_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_423_; uint8_t v___x_424_; uint8_t v___x_425_; 
v___x_423_ = lean_st_ref_get(v_state_413_);
v___x_424_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v___x_423_);
lean_dec(v___x_423_);
v___x_425_ = 1;
if (v___x_424_ == 0)
{
lean_object* v___x_426_; 
lean_inc(v_a_421_);
lean_inc_ref(v_a_420_);
lean_inc(v_a_419_);
lean_inc_ref(v_a_418_);
v___x_426_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(v_pattern_412_, v_e_414_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_493_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_493_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_493_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_493_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
if (lean_obj_tag(v_a_427_) == 1)
{
lean_object* v_val_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_488_; 
v_val_431_ = lean_ctor_get(v_a_427_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v_a_427_);
if (v_isSharedCheck_488_ == 0)
{
v___x_433_ = v_a_427_;
v_isShared_434_ = v_isSharedCheck_488_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_val_431_);
lean_dec(v_a_427_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_488_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v_fst_435_; lean_object* v_snd_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_fst_435_ = lean_ctor_get(v_val_431_, 0);
lean_inc(v_fst_435_);
v_snd_436_ = lean_ctor_get(v_val_431_, 1);
lean_inc(v_snd_436_);
lean_dec(v_val_431_);
v___x_437_ = lean_st_ref_get(v_state_413_);
v___x_438_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v___x_437_);
lean_dec(v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
lean_dec(v_snd_436_);
lean_dec(v_fst_435_);
lean_del_object(v___x_433_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
v___x_439_ = lean_st_ref_take(v_state_413_);
v___x_440_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(v___x_439_);
v___x_441_ = lean_st_ref_set(v_state_413_, v___x_440_);
v___x_442_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0));
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_442_);
v___x_444_ = v___x_429_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; 
lean_del_object(v___x_429_);
v___x_446_ = lean_box(0);
lean_inc(v_a_421_);
lean_inc_ref(v_a_420_);
lean_inc(v_a_419_);
lean_inc_ref(v_a_418_);
v___x_447_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_fst_435_, v___x_446_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v_fst_449_; lean_object* v_snd_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; size_t v_sz_455_; size_t v___x_456_; lean_object* v___x_457_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref(v___x_447_);
v_fst_449_ = lean_ctor_get(v_a_448_, 0);
lean_inc(v_fst_449_);
v_snd_450_ = lean_ctor_get(v_a_448_, 1);
lean_inc(v_snd_450_);
lean_dec(v_a_448_);
v___x_451_ = lean_st_ref_take(v_state_413_);
v___x_452_ = l_Lean_Expr_mvarId_x21(v_snd_450_);
v___x_453_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(v___x_452_, v___x_451_);
v___x_454_ = lean_st_ref_set(v_state_413_, v___x_453_);
v_sz_455_ = lean_array_size(v_snd_436_);
v___x_456_ = ((size_t)0ULL);
v___x_457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_snd_436_, v_sz_455_, v___x_456_, v_snd_450_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_471_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_471_ == 0)
{
v___x_460_ = v___x_457_;
v_isShared_461_ = v_isSharedCheck_471_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_471_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = l_Lean_mkAppN(v_fst_449_, v_snd_436_);
lean_dec(v_snd_436_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v_a_458_);
v___x_464_ = v___x_433_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_458_);
v___x_464_ = v_reuseFailAlloc_470_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_465_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_465_, 0, v___x_462_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
lean_ctor_set_uint8(v___x_465_, sizeof(void*)*2, v___x_425_);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_466_);
v___x_468_ = v___x_460_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec(v_fst_449_);
lean_dec(v_snd_436_);
lean_del_object(v___x_433_);
v_a_472_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_457_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_457_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec(v_snd_436_);
lean_del_object(v___x_433_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
v_a_480_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_447_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_447_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
}
else
{
lean_object* v___x_489_; lean_object* v___x_491_; 
lean_dec(v_a_427_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
v___x_489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0));
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_489_);
v___x_491_ = v___x_429_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
v_a_494_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_426_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_426_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec_ref(v_pattern_412_);
v___x_502_ = lean_box(0);
v___x_503_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_503_, 0, v_e_414_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
lean_ctor_set_uint8(v___x_503_, sizeof(void*)*2, v___x_425_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed(lean_object* v_pattern_506_, lean_object* v_state_507_, lean_object* v_e_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(v_pattern_506_, v_state_507_, v_e_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec(v_state_507_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(lean_object* v_as_518_, size_t v_sz_519_, size_t v_i_520_, lean_object* v_b_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_518_, v_sz_519_, v_i_520_, v_b_521_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___boxed(lean_object* v_as_531_, lean_object* v_sz_532_, lean_object* v_i_533_, lean_object* v_b_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
size_t v_sz_boxed_543_; size_t v_i_boxed_544_; lean_object* v_res_545_; 
v_sz_boxed_543_ = lean_unbox_usize(v_sz_532_);
lean_dec(v_sz_532_);
v_i_boxed_544_ = lean_unbox_usize(v_i_533_);
lean_dec(v_i_533_);
v_res_545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(v_as_531_, v_sz_boxed_543_, v_i_boxed_544_, v_b_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v_as_531_);
return v_res_545_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = lean_box(0);
v___x_547_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0);
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___boxed(lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(lean_object* v_00_u03b1_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___boxed(lean_object* v_00_u03b1_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(v_00_u03b1_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(lean_object* v_a_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___boxed(lean_object* v_a_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(v_a_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(lean_object* v_00_u03b1_594_, lean_object* v_a_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___boxed(lean_object* v_00_u03b1_604_, lean_object* v_a_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(v_00_u03b1_604_, v_a_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(lean_object* v_e_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v_e_614_);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed(lean_object* v_e_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(v_e_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(lean_object* v___x_635_, lean_object* v___x_636_, uint8_t v___x_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; 
lean_inc(v___y_643_);
lean_inc_ref(v___y_642_);
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
v___x_645_ = l_Lean_Elab_Term_elabTerm(v___x_635_, v___x_636_, v___x_637_, v___x_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref(v___x_645_);
v___x_647_ = l_Lean_Meta_abstractMVars(v_a_646_, v___x_637_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
return v___x_647_;
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
v_a_648_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_645_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_645_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed(lean_object* v___x_656_, lean_object* v___x_657_, lean_object* v___x_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
uint8_t v___x_18426__boxed_666_; lean_object* v_res_667_; 
v___x_18426__boxed_666_ = lean_unbox(v___x_658_);
v_res_667_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(v___x_656_, v___x_657_, v___x_18426__boxed_666_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(lean_object* v___x_668_, lean_object* v___f_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_fileName_677_; lean_object* v_fileMap_678_; lean_object* v_options_679_; lean_object* v_currRecDepth_680_; lean_object* v_maxRecDepth_681_; lean_object* v_ref_682_; lean_object* v_currNamespace_683_; lean_object* v_openDecls_684_; lean_object* v_initHeartbeats_685_; lean_object* v_maxHeartbeats_686_; lean_object* v_quotContext_687_; lean_object* v_currMacroScope_688_; uint8_t v_diag_689_; lean_object* v_cancelTk_x3f_690_; uint8_t v_suppressElabErrors_691_; lean_object* v_inheritedTraceOptions_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_701_; 
v_fileName_677_ = lean_ctor_get(v___y_674_, 0);
v_fileMap_678_ = lean_ctor_get(v___y_674_, 1);
v_options_679_ = lean_ctor_get(v___y_674_, 2);
v_currRecDepth_680_ = lean_ctor_get(v___y_674_, 3);
v_maxRecDepth_681_ = lean_ctor_get(v___y_674_, 4);
v_ref_682_ = lean_ctor_get(v___y_674_, 5);
v_currNamespace_683_ = lean_ctor_get(v___y_674_, 6);
v_openDecls_684_ = lean_ctor_get(v___y_674_, 7);
v_initHeartbeats_685_ = lean_ctor_get(v___y_674_, 8);
v_maxHeartbeats_686_ = lean_ctor_get(v___y_674_, 9);
v_quotContext_687_ = lean_ctor_get(v___y_674_, 10);
v_currMacroScope_688_ = lean_ctor_get(v___y_674_, 11);
v_diag_689_ = lean_ctor_get_uint8(v___y_674_, sizeof(void*)*14);
v_cancelTk_x3f_690_ = lean_ctor_get(v___y_674_, 12);
v_suppressElabErrors_691_ = lean_ctor_get_uint8(v___y_674_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_692_ = lean_ctor_get(v___y_674_, 13);
v_isSharedCheck_701_ = !lean_is_exclusive(v___y_674_);
if (v_isSharedCheck_701_ == 0)
{
v___x_694_ = v___y_674_;
v_isShared_695_ = v_isSharedCheck_701_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_inheritedTraceOptions_692_);
lean_inc(v_cancelTk_x3f_690_);
lean_inc(v_currMacroScope_688_);
lean_inc(v_quotContext_687_);
lean_inc(v_maxHeartbeats_686_);
lean_inc(v_initHeartbeats_685_);
lean_inc(v_openDecls_684_);
lean_inc(v_currNamespace_683_);
lean_inc(v_ref_682_);
lean_inc(v_maxRecDepth_681_);
lean_inc(v_currRecDepth_680_);
lean_inc(v_options_679_);
lean_inc(v_fileMap_678_);
lean_inc(v_fileName_677_);
lean_dec(v___y_674_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_701_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_ref_696_; lean_object* v___x_698_; 
v_ref_696_ = l_Lean_replaceRef(v___x_668_, v_ref_682_);
lean_dec(v_ref_682_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 5, v_ref_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_fileName_677_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_fileMap_678_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_options_679_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_currRecDepth_680_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v_maxRecDepth_681_);
lean_ctor_set(v_reuseFailAlloc_700_, 5, v_ref_696_);
lean_ctor_set(v_reuseFailAlloc_700_, 6, v_currNamespace_683_);
lean_ctor_set(v_reuseFailAlloc_700_, 7, v_openDecls_684_);
lean_ctor_set(v_reuseFailAlloc_700_, 8, v_initHeartbeats_685_);
lean_ctor_set(v_reuseFailAlloc_700_, 9, v_maxHeartbeats_686_);
lean_ctor_set(v_reuseFailAlloc_700_, 10, v_quotContext_687_);
lean_ctor_set(v_reuseFailAlloc_700_, 11, v_currMacroScope_688_);
lean_ctor_set(v_reuseFailAlloc_700_, 12, v_cancelTk_x3f_690_);
lean_ctor_set(v_reuseFailAlloc_700_, 13, v_inheritedTraceOptions_692_);
lean_ctor_set_uint8(v_reuseFailAlloc_700_, sizeof(void*)*14, v_diag_689_);
lean_ctor_set_uint8(v_reuseFailAlloc_700_, sizeof(void*)*14 + 1, v_suppressElabErrors_691_);
v___x_698_ = v_reuseFailAlloc_700_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___x_698_, v___y_675_);
return v___x_699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed(lean_object* v___x_702_, lean_object* v___f_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(v___x_702_, v___f_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___x_702_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(lean_object* v___x_712_, uint8_t v___x_713_, lean_object* v_e_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_723_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_723_, 0, v_e_714_);
lean_ctor_set(v___x_723_, 1, v___x_712_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*2, v___x_713_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed(lean_object* v___x_726_, lean_object* v___x_727_, lean_object* v_e_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
uint8_t v___x_18520__boxed_737_; lean_object* v_res_738_; 
v___x_18520__boxed_737_ = lean_unbox(v___x_727_);
v_res_738_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(v___x_726_, v___x_18520__boxed_737_, v_e_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(lean_object* v___x_739_, lean_object* v_x_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_739_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed(lean_object* v___x_751_, lean_object* v_x_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(v___x_751_, v_x_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v_x_752_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(lean_object* v___x_762_, lean_object* v_x_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_762_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed(lean_object* v___x_773_, lean_object* v_x_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(v___x_773_, v_x_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v_x_774_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(size_t v_sz_784_, size_t v_i_785_, lean_object* v_bs_786_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = lean_usize_dec_lt(v_i_785_, v_sz_784_);
if (v___x_787_ == 0)
{
return v_bs_786_;
}
else
{
lean_object* v_v_788_; lean_object* v_snd_789_; lean_object* v___x_790_; lean_object* v_bs_x27_791_; size_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; 
v_v_788_ = lean_array_uget_borrowed(v_bs_786_, v_i_785_);
v_snd_789_ = lean_ctor_get(v_v_788_, 1);
lean_inc(v_snd_789_);
v___x_790_ = lean_unsigned_to_nat(0u);
v_bs_x27_791_ = lean_array_uset(v_bs_786_, v_i_785_, v___x_790_);
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_add(v_i_785_, v___x_792_);
v___x_794_ = lean_array_uset(v_bs_x27_791_, v_i_785_, v_snd_789_);
v_i_785_ = v___x_793_;
v_bs_786_ = v___x_794_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5___boxed(lean_object* v_sz_796_, lean_object* v_i_797_, lean_object* v_bs_798_){
_start:
{
size_t v_sz_boxed_799_; size_t v_i_boxed_800_; lean_object* v_res_801_; 
v_sz_boxed_799_ = lean_unbox_usize(v_sz_796_);
lean_dec(v_sz_796_);
v_i_boxed_800_ = lean_unbox_usize(v_i_797_);
lean_dec(v_i_797_);
v_res_801_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_boxed_799_, v_i_boxed_800_, v_bs_798_);
return v_res_801_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(lean_object* v_x1_802_, lean_object* v_x2_803_){
_start:
{
lean_object* v_fst_804_; lean_object* v_fst_805_; uint8_t v___x_806_; 
v_fst_804_ = lean_ctor_get(v_x1_802_, 0);
v_fst_805_ = lean_ctor_get(v_x2_803_, 0);
v___x_806_ = lean_nat_dec_lt(v_fst_804_, v_fst_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(lean_object* v_x1_807_, lean_object* v_x2_808_){
_start:
{
uint8_t v_res_809_; lean_object* v_r_810_; 
v_res_809_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v_x1_807_, v_x2_808_);
lean_dec_ref(v_x2_808_);
lean_dec_ref(v_x1_807_);
v_r_810_ = lean_box(v_res_809_);
return v_r_810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(lean_object* v_as_812_, lean_object* v_lo_813_, lean_object* v_hi_814_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = lean_nat_dec_lt(v_lo_813_, v_hi_814_);
if (v___x_815_ == 0)
{
lean_dec(v_lo_813_);
return v_as_812_;
}
else
{
lean_object* v___f_816_; lean_object* v___x_817_; lean_object* v_fst_818_; lean_object* v_snd_819_; uint8_t v___x_820_; 
v___f_816_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___closed__0));
lean_inc(v_lo_813_);
v___x_817_ = l_Array_qpartition___redArg(v_as_812_, v___f_816_, v_lo_813_, v_hi_814_);
v_fst_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_fst_818_);
v_snd_819_ = lean_ctor_get(v___x_817_, 1);
lean_inc(v_snd_819_);
lean_dec_ref(v___x_817_);
v___x_820_ = lean_nat_dec_le(v_hi_814_, v_fst_818_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_snd_819_, v_lo_813_, v_fst_818_);
v___x_822_ = lean_unsigned_to_nat(1u);
v___x_823_ = lean_nat_add(v_fst_818_, v___x_822_);
lean_dec(v_fst_818_);
v_as_812_ = v___x_821_;
v_lo_813_ = v___x_823_;
goto _start;
}
else
{
lean_dec(v_fst_818_);
lean_dec(v_lo_813_);
return v_snd_819_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___boxed(lean_object* v_as_825_, lean_object* v_lo_826_, lean_object* v_hi_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_as_825_, v_lo_826_, v_hi_827_);
lean_dec(v_hi_827_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(lean_object* v_msgData_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; lean_object* v_env_836_; lean_object* v___x_837_; lean_object* v_mctx_838_; lean_object* v_lctx_839_; lean_object* v_options_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_835_ = lean_st_ref_get(v___y_833_);
v_env_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc_ref(v_env_836_);
lean_dec(v___x_835_);
v___x_837_ = lean_st_ref_get(v___y_831_);
v_mctx_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc_ref(v_mctx_838_);
lean_dec(v___x_837_);
v_lctx_839_ = lean_ctor_get(v___y_830_, 2);
v_options_840_ = lean_ctor_get(v___y_832_, 2);
lean_inc_ref(v_options_840_);
lean_inc_ref(v_lctx_839_);
v___x_841_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_841_, 0, v_env_836_);
lean_ctor_set(v___x_841_, 1, v_mctx_838_);
lean_ctor_set(v___x_841_, 2, v_lctx_839_);
lean_ctor_set(v___x_841_, 3, v_options_840_);
v___x_842_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v_msgData_829_);
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(lean_object* v_msgData_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msgData_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(lean_object* v_msg_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_ref_857_; lean_object* v___x_858_; lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_867_; 
v_ref_857_ = lean_ctor_get(v___y_854_, 5);
v___x_858_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msg_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_867_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_865_; 
lean_inc(v_ref_857_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_ref_857_);
lean_ctor_set(v___x_863_, 1, v_a_859_);
if (v_isShared_862_ == 0)
{
lean_ctor_set_tag(v___x_861_, 1);
lean_ctor_set(v___x_861_, 0, v___x_863_);
v___x_865_ = v___x_861_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg___boxed(lean_object* v_msg_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__14___redArg(lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
lean_object* v_ks_879_; lean_object* v_vs_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_904_; 
v_ks_879_ = lean_ctor_get(v_x_875_, 0);
v_vs_880_ = lean_ctor_get(v_x_875_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v_x_875_);
if (v_isSharedCheck_904_ == 0)
{
v___x_882_ = v_x_875_;
v_isShared_883_ = v_isSharedCheck_904_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_vs_880_);
lean_inc(v_ks_879_);
lean_dec(v_x_875_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_904_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_884_ = lean_array_get_size(v_ks_879_);
v___x_885_ = lean_nat_dec_lt(v_x_876_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
lean_dec(v_x_876_);
v___x_886_ = lean_array_push(v_ks_879_, v_x_877_);
v___x_887_ = lean_array_push(v_vs_880_, v_x_878_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v___x_887_);
lean_ctor_set(v___x_882_, 0, v___x_886_);
v___x_889_ = v___x_882_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
else
{
lean_object* v_k_x27_891_; uint8_t v___x_892_; 
v_k_x27_891_ = lean_array_fget_borrowed(v_ks_879_, v_x_876_);
v___x_892_ = l_Lean_instBEqMVarId_beq(v_x_877_, v_k_x27_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_894_; 
if (v_isShared_883_ == 0)
{
v___x_894_ = v___x_882_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_ks_879_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_vs_880_);
v___x_894_ = v_reuseFailAlloc_898_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_unsigned_to_nat(1u);
v___x_896_ = lean_nat_add(v_x_876_, v___x_895_);
lean_dec(v_x_876_);
v_x_875_ = v___x_894_;
v_x_876_ = v___x_896_;
goto _start;
}
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_899_ = lean_array_fset(v_ks_879_, v_x_876_, v_x_877_);
v___x_900_ = lean_array_fset(v_vs_880_, v_x_876_, v_x_878_);
lean_dec(v_x_876_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v___x_900_);
lean_ctor_set(v___x_882_, 0, v___x_899_);
v___x_902_ = v___x_882_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_900_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_n_905_, lean_object* v_k_906_, lean_object* v_v_907_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__14___redArg(v_n_905_, v___x_908_, v_k_906_, v_v_907_);
return v___x_909_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_910_; size_t v___x_911_; size_t v___x_912_; 
v___x_910_ = ((size_t)5ULL);
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_shift_left(v___x_911_, v___x_910_);
return v___x_912_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_913_; size_t v___x_914_; size_t v___x_915_; 
v___x_913_ = ((size_t)1ULL);
v___x_914_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_915_ = lean_usize_sub(v___x_914_, v___x_913_);
return v___x_915_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(lean_object* v_x_917_, size_t v_x_918_, size_t v_x_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
if (lean_obj_tag(v_x_917_) == 0)
{
lean_object* v_es_922_; size_t v___x_923_; size_t v___x_924_; size_t v___x_925_; size_t v___x_926_; lean_object* v_j_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_es_922_ = lean_ctor_get(v_x_917_, 0);
v___x_923_ = ((size_t)5ULL);
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_926_ = lean_usize_land(v_x_918_, v___x_925_);
v_j_927_ = lean_usize_to_nat(v___x_926_);
v___x_928_ = lean_array_get_size(v_es_922_);
v___x_929_ = lean_nat_dec_lt(v_j_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_dec(v_j_927_);
lean_dec(v_x_921_);
lean_dec(v_x_920_);
return v_x_917_;
}
else
{
lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_966_; 
lean_inc_ref(v_es_922_);
v_isSharedCheck_966_ = !lean_is_exclusive(v_x_917_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v_x_917_, 0);
lean_dec(v_unused_967_);
v___x_931_ = v_x_917_;
v_isShared_932_ = v_isSharedCheck_966_;
goto v_resetjp_930_;
}
else
{
lean_dec(v_x_917_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_966_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_v_933_; lean_object* v___x_934_; lean_object* v_xs_x27_935_; lean_object* v___y_937_; 
v_v_933_ = lean_array_fget(v_es_922_, v_j_927_);
v___x_934_ = lean_box(0);
v_xs_x27_935_ = lean_array_fset(v_es_922_, v_j_927_, v___x_934_);
switch(lean_obj_tag(v_v_933_))
{
case 0:
{
lean_object* v_key_942_; lean_object* v_val_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_953_; 
v_key_942_ = lean_ctor_get(v_v_933_, 0);
v_val_943_ = lean_ctor_get(v_v_933_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v_v_933_);
if (v_isSharedCheck_953_ == 0)
{
v___x_945_ = v_v_933_;
v_isShared_946_ = v_isSharedCheck_953_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_val_943_);
lean_inc(v_key_942_);
lean_dec(v_v_933_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_953_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
uint8_t v___x_947_; 
v___x_947_ = l_Lean_instBEqMVarId_beq(v_x_920_, v_key_942_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_del_object(v___x_945_);
v___x_948_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_942_, v_val_943_, v_x_920_, v_x_921_);
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
v___y_937_ = v___x_949_;
goto v___jp_936_;
}
else
{
lean_object* v___x_951_; 
lean_dec(v_val_943_);
lean_dec(v_key_942_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v_x_921_);
lean_ctor_set(v___x_945_, 0, v_x_920_);
v___x_951_ = v___x_945_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_x_920_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_x_921_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
v___y_937_ = v___x_951_;
goto v___jp_936_;
}
}
}
}
case 1:
{
lean_object* v_node_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_964_; 
v_node_954_ = lean_ctor_get(v_v_933_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_v_933_);
if (v_isSharedCheck_964_ == 0)
{
v___x_956_ = v_v_933_;
v_isShared_957_ = v_isSharedCheck_964_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_node_954_);
lean_dec(v_v_933_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_964_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
size_t v___x_958_; size_t v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_958_ = lean_usize_shift_right(v_x_918_, v___x_923_);
v___x_959_ = lean_usize_add(v_x_919_, v___x_924_);
v___x_960_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_node_954_, v___x_958_, v___x_959_, v_x_920_, v_x_921_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_960_);
v___x_962_ = v___x_956_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
v___y_937_ = v___x_962_;
goto v___jp_936_;
}
}
}
default: 
{
lean_object* v___x_965_; 
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v_x_920_);
lean_ctor_set(v___x_965_, 1, v_x_921_);
v___y_937_ = v___x_965_;
goto v___jp_936_;
}
}
v___jp_936_:
{
lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_938_ = lean_array_fset(v_xs_x27_935_, v_j_927_, v___y_937_);
lean_dec(v_j_927_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_938_);
v___x_940_ = v___x_931_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
else
{
lean_object* v_ks_968_; lean_object* v_vs_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_989_; 
v_ks_968_ = lean_ctor_get(v_x_917_, 0);
v_vs_969_ = lean_ctor_get(v_x_917_, 1);
v_isSharedCheck_989_ = !lean_is_exclusive(v_x_917_);
if (v_isSharedCheck_989_ == 0)
{
v___x_971_ = v_x_917_;
v_isShared_972_ = v_isSharedCheck_989_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_vs_969_);
lean_inc(v_ks_968_);
lean_dec(v_x_917_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_989_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_ks_968_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_vs_969_);
v___x_974_ = v_reuseFailAlloc_988_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v_newNode_975_; uint8_t v___y_977_; size_t v___x_983_; uint8_t v___x_984_; 
v_newNode_975_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v___x_974_, v_x_920_, v_x_921_);
v___x_983_ = ((size_t)7ULL);
v___x_984_ = lean_usize_dec_le(v___x_983_, v_x_919_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_985_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_975_);
v___x_986_ = lean_unsigned_to_nat(4u);
v___x_987_ = lean_nat_dec_lt(v___x_985_, v___x_986_);
lean_dec(v___x_985_);
v___y_977_ = v___x_987_;
goto v___jp_976_;
}
else
{
v___y_977_ = v___x_984_;
goto v___jp_976_;
}
v___jp_976_:
{
if (v___y_977_ == 0)
{
lean_object* v_ks_978_; lean_object* v_vs_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_ks_978_ = lean_ctor_get(v_newNode_975_, 0);
lean_inc_ref(v_ks_978_);
v_vs_979_ = lean_ctor_get(v_newNode_975_, 1);
lean_inc_ref(v_vs_979_);
lean_dec_ref(v_newNode_975_);
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2);
v___x_982_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_x_919_, v_ks_978_, v_vs_979_, v___x_980_, v___x_981_);
lean_dec_ref(v_vs_979_);
lean_dec_ref(v_ks_978_);
return v___x_982_;
}
else
{
return v_newNode_975_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(size_t v_depth_990_, lean_object* v_keys_991_, lean_object* v_vals_992_, lean_object* v_i_993_, lean_object* v_entries_994_){
_start:
{
lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_995_ = lean_array_get_size(v_keys_991_);
v___x_996_ = lean_nat_dec_lt(v_i_993_, v___x_995_);
if (v___x_996_ == 0)
{
lean_dec(v_i_993_);
return v_entries_994_;
}
else
{
lean_object* v_k_997_; lean_object* v_v_998_; uint64_t v___x_999_; size_t v_h_1000_; size_t v___x_1001_; lean_object* v___x_1002_; size_t v___x_1003_; size_t v___x_1004_; size_t v___x_1005_; size_t v_h_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_k_997_ = lean_array_fget_borrowed(v_keys_991_, v_i_993_);
v_v_998_ = lean_array_fget_borrowed(v_vals_992_, v_i_993_);
v___x_999_ = l_Lean_instHashableMVarId_hash(v_k_997_);
v_h_1000_ = lean_uint64_to_usize(v___x_999_);
v___x_1001_ = ((size_t)5ULL);
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_sub(v_depth_990_, v___x_1003_);
v___x_1005_ = lean_usize_mul(v___x_1001_, v___x_1004_);
v_h_1006_ = lean_usize_shift_right(v_h_1000_, v___x_1005_);
v___x_1007_ = lean_nat_add(v_i_993_, v___x_1002_);
lean_dec(v_i_993_);
lean_inc(v_v_998_);
lean_inc(v_k_997_);
v___x_1008_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_entries_994_, v_h_1006_, v_depth_990_, v_k_997_, v_v_998_);
v_i_993_ = v___x_1007_;
v_entries_994_ = v___x_1008_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg___boxed(lean_object* v_depth_1010_, lean_object* v_keys_1011_, lean_object* v_vals_1012_, lean_object* v_i_1013_, lean_object* v_entries_1014_){
_start:
{
size_t v_depth_boxed_1015_; lean_object* v_res_1016_; 
v_depth_boxed_1015_ = lean_unbox_usize(v_depth_1010_);
lean_dec(v_depth_1010_);
v_res_1016_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_boxed_1015_, v_keys_1011_, v_vals_1012_, v_i_1013_, v_entries_1014_);
lean_dec_ref(v_vals_1012_);
lean_dec_ref(v_keys_1011_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_x_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_){
_start:
{
size_t v_x_18814__boxed_1022_; size_t v_x_18815__boxed_1023_; lean_object* v_res_1024_; 
v_x_18814__boxed_1022_ = lean_unbox_usize(v_x_1018_);
lean_dec(v_x_1018_);
v_x_18815__boxed_1023_ = lean_unbox_usize(v_x_1019_);
lean_dec(v_x_1019_);
v_res_1024_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1017_, v_x_18814__boxed_1022_, v_x_18815__boxed_1023_, v_x_1020_, v_x_1021_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(lean_object* v_x_1025_, lean_object* v_x_1026_, lean_object* v_x_1027_){
_start:
{
uint64_t v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1028_ = l_Lean_instHashableMVarId_hash(v_x_1026_);
v___x_1029_ = lean_uint64_to_usize(v___x_1028_);
v___x_1030_ = ((size_t)1ULL);
v___x_1031_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1025_, v___x_1029_, v___x_1030_, v_x_1026_, v_x_1027_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(lean_object* v_mvarId_1032_, lean_object* v_val_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___x_1036_; lean_object* v_mctx_1037_; lean_object* v_cache_1038_; lean_object* v_zetaDeltaFVarIds_1039_; lean_object* v_postponed_1040_; lean_object* v_diag_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1068_; 
v___x_1036_ = lean_st_ref_take(v___y_1034_);
v_mctx_1037_ = lean_ctor_get(v___x_1036_, 0);
v_cache_1038_ = lean_ctor_get(v___x_1036_, 1);
v_zetaDeltaFVarIds_1039_ = lean_ctor_get(v___x_1036_, 2);
v_postponed_1040_ = lean_ctor_get(v___x_1036_, 3);
v_diag_1041_ = lean_ctor_get(v___x_1036_, 4);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1043_ = v___x_1036_;
v_isShared_1044_ = v_isSharedCheck_1068_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_diag_1041_);
lean_inc(v_postponed_1040_);
lean_inc(v_zetaDeltaFVarIds_1039_);
lean_inc(v_cache_1038_);
lean_inc(v_mctx_1037_);
lean_dec(v___x_1036_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1068_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_depth_1045_; lean_object* v_levelAssignDepth_1046_; lean_object* v_mvarCounter_1047_; lean_object* v_lDepth_1048_; lean_object* v_decls_1049_; lean_object* v_userNames_1050_; lean_object* v_lAssignment_1051_; lean_object* v_eAssignment_1052_; lean_object* v_dAssignment_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1067_; 
v_depth_1045_ = lean_ctor_get(v_mctx_1037_, 0);
v_levelAssignDepth_1046_ = lean_ctor_get(v_mctx_1037_, 1);
v_mvarCounter_1047_ = lean_ctor_get(v_mctx_1037_, 2);
v_lDepth_1048_ = lean_ctor_get(v_mctx_1037_, 3);
v_decls_1049_ = lean_ctor_get(v_mctx_1037_, 4);
v_userNames_1050_ = lean_ctor_get(v_mctx_1037_, 5);
v_lAssignment_1051_ = lean_ctor_get(v_mctx_1037_, 6);
v_eAssignment_1052_ = lean_ctor_get(v_mctx_1037_, 7);
v_dAssignment_1053_ = lean_ctor_get(v_mctx_1037_, 8);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_mctx_1037_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1055_ = v_mctx_1037_;
v_isShared_1056_ = v_isSharedCheck_1067_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_dAssignment_1053_);
lean_inc(v_eAssignment_1052_);
lean_inc(v_lAssignment_1051_);
lean_inc(v_userNames_1050_);
lean_inc(v_decls_1049_);
lean_inc(v_lDepth_1048_);
lean_inc(v_mvarCounter_1047_);
lean_inc(v_levelAssignDepth_1046_);
lean_inc(v_depth_1045_);
lean_dec(v_mctx_1037_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1067_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_eAssignment_1052_, v_mvarId_1032_, v_val_1033_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 7, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_depth_1045_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_levelAssignDepth_1046_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v_mvarCounter_1047_);
lean_ctor_set(v_reuseFailAlloc_1066_, 3, v_lDepth_1048_);
lean_ctor_set(v_reuseFailAlloc_1066_, 4, v_decls_1049_);
lean_ctor_set(v_reuseFailAlloc_1066_, 5, v_userNames_1050_);
lean_ctor_set(v_reuseFailAlloc_1066_, 6, v_lAssignment_1051_);
lean_ctor_set(v_reuseFailAlloc_1066_, 7, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1066_, 8, v_dAssignment_1053_);
v___x_1059_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1059_);
v___x_1061_ = v___x_1043_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_cache_1038_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v_zetaDeltaFVarIds_1039_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v_postponed_1040_);
lean_ctor_set(v_reuseFailAlloc_1065_, 4, v_diag_1041_);
v___x_1061_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = lean_st_ref_set(v___y_1034_, v___x_1061_);
v___x_1063_ = lean_box(0);
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(lean_object* v_mvarId_1069_, lean_object* v_val_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1069_, v_val_1070_, v___y_1071_);
lean_dec(v___y_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(lean_object* v_x1_1074_, lean_object* v_x2_1075_){
_start:
{
lean_object* v_fst_1076_; lean_object* v_fst_1077_; uint8_t v___x_1078_; 
v_fst_1076_ = lean_ctor_get(v_x1_1074_, 0);
v_fst_1077_ = lean_ctor_get(v_x2_1075_, 0);
v___x_1078_ = lean_nat_dec_lt(v_fst_1076_, v_fst_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0___boxed(lean_object* v_x1_1079_, lean_object* v_x2_1080_){
_start:
{
uint8_t v_res_1081_; lean_object* v_r_1082_; 
v_res_1081_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v_x1_1079_, v_x2_1080_);
lean_dec_ref(v_x2_1080_);
lean_dec_ref(v_x1_1079_);
v_r_1082_ = lean_box(v_res_1081_);
return v_r_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(lean_object* v_as_1084_, lean_object* v_lo_1085_, lean_object* v_hi_1086_){
_start:
{
uint8_t v___x_1087_; 
v___x_1087_ = lean_nat_dec_lt(v_lo_1085_, v_hi_1086_);
if (v___x_1087_ == 0)
{
lean_dec(v_lo_1085_);
return v_as_1084_;
}
else
{
lean_object* v___f_1088_; lean_object* v___x_1089_; lean_object* v_fst_1090_; lean_object* v_snd_1091_; uint8_t v___x_1092_; 
v___f_1088_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___closed__0));
lean_inc(v_lo_1085_);
v___x_1089_ = l_Array_qpartition___redArg(v_as_1084_, v___f_1088_, v_lo_1085_, v_hi_1086_);
v_fst_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_fst_1090_);
v_snd_1091_ = lean_ctor_get(v___x_1089_, 1);
lean_inc(v_snd_1091_);
lean_dec_ref(v___x_1089_);
v___x_1092_ = lean_nat_dec_le(v_hi_1086_, v_fst_1090_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_snd_1091_, v_lo_1085_, v_fst_1090_);
v___x_1094_ = lean_unsigned_to_nat(1u);
v___x_1095_ = lean_nat_add(v_fst_1090_, v___x_1094_);
lean_dec(v_fst_1090_);
v_as_1084_ = v___x_1093_;
v_lo_1085_ = v___x_1095_;
goto _start;
}
else
{
lean_dec(v_fst_1090_);
lean_dec(v_lo_1085_);
return v_snd_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___boxed(lean_object* v_as_1097_, lean_object* v_lo_1098_, lean_object* v_hi_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_as_1097_, v_lo_1098_, v_hi_1099_);
lean_dec(v_hi_1099_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(lean_object* v_ref_1101_, lean_object* v_msg_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_fileName_1112_; lean_object* v_fileMap_1113_; lean_object* v_options_1114_; lean_object* v_currRecDepth_1115_; lean_object* v_maxRecDepth_1116_; lean_object* v_ref_1117_; lean_object* v_currNamespace_1118_; lean_object* v_openDecls_1119_; lean_object* v_initHeartbeats_1120_; lean_object* v_maxHeartbeats_1121_; lean_object* v_quotContext_1122_; lean_object* v_currMacroScope_1123_; uint8_t v_diag_1124_; lean_object* v_cancelTk_x3f_1125_; uint8_t v_suppressElabErrors_1126_; lean_object* v_inheritedTraceOptions_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1136_; 
v_fileName_1112_ = lean_ctor_get(v___y_1109_, 0);
v_fileMap_1113_ = lean_ctor_get(v___y_1109_, 1);
v_options_1114_ = lean_ctor_get(v___y_1109_, 2);
v_currRecDepth_1115_ = lean_ctor_get(v___y_1109_, 3);
v_maxRecDepth_1116_ = lean_ctor_get(v___y_1109_, 4);
v_ref_1117_ = lean_ctor_get(v___y_1109_, 5);
v_currNamespace_1118_ = lean_ctor_get(v___y_1109_, 6);
v_openDecls_1119_ = lean_ctor_get(v___y_1109_, 7);
v_initHeartbeats_1120_ = lean_ctor_get(v___y_1109_, 8);
v_maxHeartbeats_1121_ = lean_ctor_get(v___y_1109_, 9);
v_quotContext_1122_ = lean_ctor_get(v___y_1109_, 10);
v_currMacroScope_1123_ = lean_ctor_get(v___y_1109_, 11);
v_diag_1124_ = lean_ctor_get_uint8(v___y_1109_, sizeof(void*)*14);
v_cancelTk_x3f_1125_ = lean_ctor_get(v___y_1109_, 12);
v_suppressElabErrors_1126_ = lean_ctor_get_uint8(v___y_1109_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1127_ = lean_ctor_get(v___y_1109_, 13);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___y_1109_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1129_ = v___y_1109_;
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_inheritedTraceOptions_1127_);
lean_inc(v_cancelTk_x3f_1125_);
lean_inc(v_currMacroScope_1123_);
lean_inc(v_quotContext_1122_);
lean_inc(v_maxHeartbeats_1121_);
lean_inc(v_initHeartbeats_1120_);
lean_inc(v_openDecls_1119_);
lean_inc(v_currNamespace_1118_);
lean_inc(v_ref_1117_);
lean_inc(v_maxRecDepth_1116_);
lean_inc(v_currRecDepth_1115_);
lean_inc(v_options_1114_);
lean_inc(v_fileMap_1113_);
lean_inc(v_fileName_1112_);
lean_dec(v___y_1109_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v_ref_1131_; lean_object* v___x_1133_; 
v_ref_1131_ = l_Lean_replaceRef(v_ref_1101_, v_ref_1117_);
lean_dec(v_ref_1117_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 5, v_ref_1131_);
v___x_1133_ = v___x_1129_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_fileName_1112_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_fileMap_1113_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_options_1114_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_currRecDepth_1115_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_maxRecDepth_1116_);
lean_ctor_set(v_reuseFailAlloc_1135_, 5, v_ref_1131_);
lean_ctor_set(v_reuseFailAlloc_1135_, 6, v_currNamespace_1118_);
lean_ctor_set(v_reuseFailAlloc_1135_, 7, v_openDecls_1119_);
lean_ctor_set(v_reuseFailAlloc_1135_, 8, v_initHeartbeats_1120_);
lean_ctor_set(v_reuseFailAlloc_1135_, 9, v_maxHeartbeats_1121_);
lean_ctor_set(v_reuseFailAlloc_1135_, 10, v_quotContext_1122_);
lean_ctor_set(v_reuseFailAlloc_1135_, 11, v_currMacroScope_1123_);
lean_ctor_set(v_reuseFailAlloc_1135_, 12, v_cancelTk_x3f_1125_);
lean_ctor_set(v_reuseFailAlloc_1135_, 13, v_inheritedTraceOptions_1127_);
lean_ctor_set_uint8(v_reuseFailAlloc_1135_, sizeof(void*)*14, v_diag_1124_);
lean_ctor_set_uint8(v_reuseFailAlloc_1135_, sizeof(void*)*14 + 1, v_suppressElabErrors_1126_);
v___x_1133_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_1102_, v___y_1107_, v___y_1108_, v___x_1133_, v___y_1110_);
lean_dec_ref(v___x_1133_);
return v___x_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(lean_object* v_ref_1137_, lean_object* v_msg_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_ref_1137_, v_msg_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v_ref_1137_);
return v_res_1148_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0));
v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(lean_object* v_as_1152_, lean_object* v_i_1153_, lean_object* v_j_1154_, lean_object* v_bs_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_zero_1165_; uint8_t v_isZero_1166_; 
v_zero_1165_ = lean_unsigned_to_nat(0u);
v_isZero_1166_ = lean_nat_dec_eq(v_i_1153_, v_zero_1165_);
if (v_isZero_1166_ == 1)
{
lean_object* v___x_1167_; 
lean_dec_ref(v___y_1162_);
lean_dec(v_j_1154_);
lean_dec(v_i_1153_);
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_bs_1155_);
return v___x_1167_;
}
else
{
lean_object* v_one_1168_; lean_object* v_n_1169_; lean_object* v_a_1171_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v_isZero_1177_; 
v_one_1168_ = lean_unsigned_to_nat(1u);
v_n_1169_ = lean_nat_sub(v_i_1153_, v_one_1168_);
lean_dec(v_i_1153_);
v___x_1175_ = lean_array_fget_borrowed(v_as_1152_, v_j_1154_);
v___x_1176_ = l_Lean_TSyntax_getNat(v___x_1175_);
v_isZero_1177_ = lean_nat_dec_eq(v___x_1176_, v_zero_1165_);
if (v_isZero_1177_ == 1)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v___x_1176_);
lean_dec(v_n_1169_);
lean_dec_ref(v_bs_1155_);
lean_dec(v_j_1154_);
v___x_1178_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1);
v___x_1179_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v___x_1175_, v___x_1178_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
else
{
lean_object* v_n_1188_; lean_object* v___x_1189_; 
v_n_1188_ = lean_nat_sub(v___x_1176_, v_one_1168_);
lean_dec(v___x_1176_);
lean_inc(v_j_1154_);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v_n_1188_);
lean_ctor_set(v___x_1189_, 1, v_j_1154_);
v_a_1171_ = v___x_1189_;
goto v___jp_1170_;
}
v___jp_1170_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_nat_add(v_j_1154_, v_one_1168_);
lean_dec(v_j_1154_);
v___x_1173_ = lean_array_push(v_bs_1155_, v_a_1171_);
v_i_1153_ = v_n_1169_;
v_j_1154_ = v___x_1172_;
v_bs_1155_ = v___x_1173_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(lean_object* v_as_1190_, lean_object* v_i_1191_, lean_object* v_j_1192_, lean_object* v_bs_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_as_1190_, v_i_1191_, v_j_1192_, v_bs_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec_ref(v_as_1190_);
return v_res_1203_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10_spec__12___redArg(lean_object* v_as_1204_, lean_object* v_a_1205_, lean_object* v_x_1206_){
_start:
{
lean_object* v_zero_1207_; uint8_t v_isZero_1208_; 
v_zero_1207_ = lean_unsigned_to_nat(0u);
v_isZero_1208_ = lean_nat_dec_eq(v_x_1206_, v_zero_1207_);
if (v_isZero_1208_ == 1)
{
lean_dec(v_x_1206_);
return v_isZero_1208_;
}
else
{
lean_object* v_fst_1209_; lean_object* v_one_1210_; lean_object* v_n_1211_; lean_object* v___x_1212_; lean_object* v_fst_1213_; uint8_t v___x_1214_; 
v_fst_1209_ = lean_ctor_get(v_a_1205_, 0);
v_one_1210_ = lean_unsigned_to_nat(1u);
v_n_1211_ = lean_nat_sub(v_x_1206_, v_one_1210_);
lean_dec(v_x_1206_);
v___x_1212_ = lean_array_fget_borrowed(v_as_1204_, v_n_1211_);
v_fst_1213_ = lean_ctor_get(v___x_1212_, 0);
v___x_1214_ = lean_nat_dec_eq(v_fst_1209_, v_fst_1213_);
if (v___x_1214_ == 0)
{
v_x_1206_ = v_n_1211_;
goto _start;
}
else
{
lean_dec(v_n_1211_);
return v_isZero_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10_spec__12___redArg___boxed(lean_object* v_as_1216_, lean_object* v_a_1217_, lean_object* v_x_1218_){
_start:
{
uint8_t v_res_1219_; lean_object* v_r_1220_; 
v_res_1219_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10_spec__12___redArg(v_as_1216_, v_a_1217_, v_x_1218_);
lean_dec_ref(v_a_1217_);
lean_dec_ref(v_as_1216_);
v_r_1220_ = lean_box(v_res_1219_);
return v_r_1220_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10(lean_object* v_as_1221_, lean_object* v_i_1222_){
_start:
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = lean_array_get_size(v_as_1221_);
v___x_1224_ = lean_nat_dec_lt(v_i_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
uint8_t v___x_1225_; 
lean_dec(v_i_1222_);
v___x_1225_ = 1;
return v___x_1225_;
}
else
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = lean_array_fget_borrowed(v_as_1221_, v_i_1222_);
lean_inc(v_i_1222_);
v___x_1227_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10_spec__12___redArg(v_as_1221_, v___x_1226_, v_i_1222_);
if (v___x_1227_ == 0)
{
lean_dec(v_i_1222_);
return v___x_1227_;
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_unsigned_to_nat(1u);
v___x_1229_ = lean_nat_add(v_i_1222_, v___x_1228_);
lean_dec(v_i_1222_);
v_i_1222_ = v___x_1229_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10___boxed(lean_object* v_as_1231_, lean_object* v_i_1232_){
_start:
{
uint8_t v_res_1233_; lean_object* v_r_1234_; 
v_res_1233_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10(v_as_1231_, v_i_1232_);
lean_dec_ref(v_as_1231_);
v_r_1234_ = lean_box(v_res_1233_);
return v_r_1234_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(lean_object* v_as_1235_){
_start:
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1237_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10(v_as_1235_, v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8___boxed(lean_object* v_as_1238_){
_start:
{
uint8_t v_res_1239_; lean_object* v_r_1240_; 
v_res_1239_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v_as_1238_);
lean_dec_ref(v_as_1238_);
v_r_1240_ = lean_box(v_res_1239_);
return v_r_1240_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1241_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
lean_ctor_set(v___x_1246_, 1, v___x_1244_);
return v___x_1246_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = lean_unsigned_to_nat(32u);
v___x_1248_ = lean_mk_empty_array_with_capacity(v___x_1247_);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
return v___x_1249_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4(void){
_start:
{
size_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1250_ = ((size_t)5ULL);
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = lean_unsigned_to_nat(32u);
v___x_1253_ = lean_mk_empty_array_with_capacity(v___x_1252_);
v___x_1254_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3);
v___x_1255_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v___x_1253_);
lean_ctor_set(v___x_1255_, 2, v___x_1251_);
lean_ctor_set(v___x_1255_, 3, v___x_1251_);
lean_ctor_set_usize(v___x_1255_, 4, v___x_1250_);
return v___x_1255_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4);
v___x_1257_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
lean_ctor_set(v___x_1258_, 2, v___x_1257_);
lean_ctor_set(v___x_1258_, 3, v___x_1256_);
return v___x_1258_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5);
v___x_1260_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
lean_ctor_set(v___x_1261_, 1, v___x_1259_);
return v___x_1261_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7));
v___x_1264_ = l_Lean_stringToMessageData(v___x_1263_);
return v___x_1264_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9));
v___x_1267_ = l_Lean_stringToMessageData(v___x_1266_);
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11));
v___x_1270_ = l_Lean_stringToMessageData(v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13));
v___x_1273_ = l_Lean_stringToMessageData(v___x_1272_);
return v___x_1273_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16));
v___x_1278_ = l_Lean_stringToMessageData(v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(uint8_t v___x_1299_, lean_object* v___f_1300_, uint8_t v___x_1301_, lean_object* v_stx_1302_, lean_object* v___x_1303_, lean_object* v___x_1304_, lean_object* v___x_1305_, lean_object* v___x_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___y_1317_; lean_object* v_subgoals_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; 
if (v___x_1299_ == 0)
{
lean_object* v___x_1407_; 
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
lean_dec_ref(v___x_1304_);
lean_dec_ref(v___x_1303_);
lean_dec_ref(v___f_1300_);
v___x_1407_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1407_;
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; uint8_t v___y_1441_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v_occs_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v_occs_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = lean_unsigned_to_nat(1u);
v___x_1729_ = l_Lean_Syntax_getArg(v_stx_1302_, v___x_1409_);
v___x_1730_ = l_Lean_Syntax_isNone(v___x_1729_);
if (v___x_1730_ == 0)
{
uint8_t v___x_1731_; 
lean_inc(v___x_1729_);
v___x_1731_ = l_Lean_Syntax_matchesNull(v___x_1729_, v___x_1409_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; 
lean_dec(v___x_1729_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
lean_dec_ref(v___x_1304_);
lean_dec_ref(v___x_1303_);
lean_dec_ref(v___f_1300_);
v___x_1732_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1732_;
}
else
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1733_ = l_Lean_Syntax_getArg(v___x_1729_, v___x_1408_);
lean_dec(v___x_1729_);
v___x_1734_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27));
lean_inc_ref(v___x_1306_);
lean_inc_ref(v___x_1305_);
lean_inc_ref(v___x_1304_);
lean_inc_ref(v___x_1303_);
v___x_1735_ = l_Lean_Name_mkStr5(v___x_1303_, v___x_1304_, v___x_1305_, v___x_1306_, v___x_1734_);
lean_inc(v___x_1733_);
v___x_1736_ = l_Lean_Syntax_isOfKind(v___x_1733_, v___x_1735_);
lean_dec(v___x_1735_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; 
lean_dec(v___x_1733_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
lean_dec_ref(v___x_1304_);
lean_dec_ref(v___x_1303_);
lean_dec_ref(v___f_1300_);
v___x_1737_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1737_;
}
else
{
lean_object* v___x_1738_; lean_object* v_occs_1739_; lean_object* v___x_1740_; 
v___x_1738_ = lean_unsigned_to_nat(3u);
v_occs_1739_ = l_Lean_Syntax_getArg(v___x_1733_, v___x_1738_);
lean_dec(v___x_1733_);
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v_occs_1739_);
v_occs_1636_ = v___x_1740_;
v___y_1637_ = v___y_1307_;
v___y_1638_ = v___y_1308_;
v___y_1639_ = v___y_1309_;
v___y_1640_ = v___y_1310_;
v___y_1641_ = v___y_1311_;
v___y_1642_ = v___y_1312_;
v___y_1643_ = v___y_1313_;
v___y_1644_ = v___y_1314_;
goto v___jp_1635_;
}
}
}
else
{
lean_object* v___x_1741_; 
lean_dec(v___x_1729_);
v___x_1741_ = lean_box(0);
v_occs_1636_ = v___x_1741_;
v___y_1637_ = v___y_1307_;
v___y_1638_ = v___y_1308_;
v___y_1639_ = v___y_1309_;
v___y_1640_ = v___y_1310_;
v___y_1641_ = v___y_1311_;
v___y_1642_ = v___y_1312_;
v___y_1643_ = v___y_1313_;
v___y_1644_ = v___y_1314_;
goto v___jp_1635_;
}
v___jp_1410_:
{
lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = lean_array_get_size(v___y_1411_);
v___x_1422_ = lean_nat_dec_eq(v___x_1421_, v___x_1408_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = lean_nat_sub(v___x_1421_, v___x_1409_);
v___x_1424_ = lean_nat_dec_le(v___x_1408_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_inc(v___x_1423_);
v___y_1393_ = v___x_1423_;
v___y_1394_ = v___y_1419_;
v___y_1395_ = v___y_1418_;
v___y_1396_ = v___y_1416_;
v___y_1397_ = v___y_1413_;
v___y_1398_ = v___x_1421_;
v___y_1399_ = v___y_1411_;
v___y_1400_ = v___y_1420_;
v___y_1401_ = v___y_1412_;
v___y_1402_ = v___y_1415_;
v___y_1403_ = v___y_1414_;
v___y_1404_ = v___y_1417_;
v___y_1405_ = v___x_1423_;
goto v___jp_1392_;
}
else
{
v___y_1393_ = v___x_1423_;
v___y_1394_ = v___y_1419_;
v___y_1395_ = v___y_1418_;
v___y_1396_ = v___y_1416_;
v___y_1397_ = v___y_1413_;
v___y_1398_ = v___x_1421_;
v___y_1399_ = v___y_1411_;
v___y_1400_ = v___y_1420_;
v___y_1401_ = v___y_1412_;
v___y_1402_ = v___y_1415_;
v___y_1403_ = v___y_1414_;
v___y_1404_ = v___y_1417_;
v___y_1405_ = v___x_1408_;
goto v___jp_1392_;
}
}
else
{
v___y_1364_ = v___y_1419_;
v___y_1365_ = v___y_1418_;
v___y_1366_ = v___y_1420_;
v___y_1367_ = v___y_1412_;
v___y_1368_ = v___y_1415_;
v___y_1369_ = v___y_1414_;
v___y_1370_ = v___y_1417_;
v___y_1371_ = v___y_1416_;
v___y_1372_ = v___y_1413_;
v___y_1373_ = v___y_1411_;
goto v___jp_1363_;
}
}
v___jp_1425_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1442_ = l_Lean_Meta_Simp_Context_setMemoize(v___y_1427_, v___y_1441_);
v___x_1443_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6);
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1433_);
v___x_1444_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed), 11, 2);
lean_closure_set(v___x_1444_, 0, v___y_1433_);
lean_closure_set(v___x_1444_, 1, v___y_1437_);
v___x_1445_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v___y_1434_);
lean_ctor_set(v___x_1445_, 2, v___y_1438_);
lean_ctor_set(v___x_1445_, 3, v___f_1300_);
lean_ctor_set(v___x_1445_, 4, v___y_1439_);
lean_ctor_set_uint8(v___x_1445_, sizeof(void*)*5, v___x_1301_);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1432_);
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1431_);
v___x_1446_ = l_Lean_Meta_Simp_main(v___y_1428_, v___x_1442_, v___x_1443_, v___x_1445_, v___y_1431_, v___y_1429_, v___y_1432_, v___y_1426_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v_fst_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1523_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref(v___x_1446_);
v_fst_1448_ = lean_ctor_get(v_a_1447_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_a_1447_);
if (v_isSharedCheck_1523_ == 0)
{
lean_object* v_unused_1524_; 
v_unused_1524_ = lean_ctor_get(v_a_1447_, 1);
lean_dec(v_unused_1524_);
v___x_1450_ = v_a_1447_;
v_isShared_1451_ = v_isSharedCheck_1523_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_fst_1448_);
lean_dec(v_a_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1523_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_st_ref_get(v___y_1437_);
lean_dec(v___y_1437_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_subgoals_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v_subgoals_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc_ref(v_subgoals_1453_);
lean_dec_ref(v___x_1452_);
v___x_1454_ = lean_array_get_size(v_subgoals_1453_);
v___x_1455_ = lean_nat_dec_eq(v___x_1454_, v___x_1408_);
if (v___x_1455_ == 0)
{
lean_del_object(v___x_1450_);
lean_dec_ref(v___y_1433_);
v___y_1317_ = v_fst_1448_;
v_subgoals_1318_ = v_subgoals_1453_;
v___y_1319_ = v___y_1440_;
v___y_1320_ = v___y_1430_;
v___y_1321_ = v___y_1436_;
v___y_1322_ = v___y_1435_;
v___y_1323_ = v___y_1431_;
v___y_1324_ = v___y_1429_;
v___y_1325_ = v___y_1432_;
v___y_1326_ = v___y_1426_;
goto v___jp_1316_;
}
else
{
lean_object* v_expr_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
lean_dec_ref(v_subgoals_1453_);
lean_dec(v_fst_1448_);
lean_dec(v___y_1435_);
v_expr_1456_ = lean_ctor_get(v___y_1433_, 2);
lean_inc_ref(v_expr_1456_);
lean_dec_ref(v___y_1433_);
v___x_1457_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1458_ = l_Lean_indentExpr(v_expr_1456_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set_tag(v___x_1450_, 7);
lean_ctor_set(v___x_1450_, 1, v___x_1458_);
lean_ctor_set(v___x_1450_, 0, v___x_1457_);
v___x_1460_ = v___x_1450_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
v___x_1461_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1460_, v___y_1431_, v___y_1429_, v___y_1432_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1431_);
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
else
{
lean_object* v_subgoals_1471_; lean_object* v_idx_1472_; lean_object* v_remaining_1473_; uint8_t v___x_1474_; 
v_subgoals_1471_ = lean_ctor_get(v___x_1452_, 0);
lean_inc_ref(v_subgoals_1471_);
v_idx_1472_ = lean_ctor_get(v___x_1452_, 1);
lean_inc(v_idx_1472_);
v_remaining_1473_ = lean_ctor_get(v___x_1452_, 2);
lean_inc(v_remaining_1473_);
lean_dec_ref(v___x_1452_);
v___x_1474_ = lean_nat_dec_eq(v_idx_1472_, v___x_1408_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; 
lean_dec_ref(v___y_1433_);
v___x_1475_ = l_List_getLast_x3f___redArg(v_remaining_1473_);
lean_dec(v_remaining_1473_);
if (lean_obj_tag(v___x_1475_) == 1)
{
lean_object* v_val_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1507_; 
lean_dec_ref(v_subgoals_1471_);
lean_dec(v_fst_1448_);
lean_dec(v___y_1435_);
v_val_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1507_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_val_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1507_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v_fst_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1505_; 
v_fst_1480_ = lean_ctor_get(v_val_1476_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_val_1476_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v_val_1476_, 1);
lean_dec(v_unused_1506_);
v___x_1482_ = v_val_1476_;
v_isShared_1483_ = v_isSharedCheck_1505_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_fst_1480_);
lean_dec(v_val_1476_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1505_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1484_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10);
v___x_1485_ = l_Nat_reprFast(v_idx_1472_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set_tag(v___x_1478_, 3);
lean_ctor_set(v___x_1478_, 0, v___x_1485_);
v___x_1487_ = v___x_1478_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1488_ = l_Lean_MessageData_ofFormat(v___x_1487_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set_tag(v___x_1482_, 7);
lean_ctor_set(v___x_1482_, 1, v___x_1488_);
lean_ctor_set(v___x_1482_, 0, v___x_1484_);
v___x_1490_ = v___x_1482_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1491_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12);
if (v_isShared_1451_ == 0)
{
lean_ctor_set_tag(v___x_1450_, 7);
lean_ctor_set(v___x_1450_, 1, v___x_1491_);
lean_ctor_set(v___x_1450_, 0, v___x_1490_);
v___x_1493_ = v___x_1450_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1494_ = lean_nat_add(v_fst_1480_, v___x_1409_);
lean_dec(v_fst_1480_);
v___x_1495_ = l_Nat_reprFast(v___x_1494_);
v___x_1496_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
v___x_1497_ = l_Lean_MessageData_ofFormat(v___x_1496_);
v___x_1498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1493_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14);
v___x_1500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1498_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___x_1501_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1500_, v___y_1431_, v___y_1429_, v___y_1432_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1431_);
return v___x_1501_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1475_);
lean_dec(v_idx_1472_);
lean_del_object(v___x_1450_);
v___y_1411_ = v_subgoals_1471_;
v___y_1412_ = v_fst_1448_;
v___y_1413_ = v___y_1440_;
v___y_1414_ = v___y_1430_;
v___y_1415_ = v___y_1436_;
v___y_1416_ = v___y_1435_;
v___y_1417_ = v___y_1431_;
v___y_1418_ = v___y_1429_;
v___y_1419_ = v___y_1432_;
v___y_1420_ = v___y_1426_;
goto v___jp_1410_;
}
}
else
{
lean_object* v_expr_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_dec(v_remaining_1473_);
lean_dec(v_idx_1472_);
lean_dec_ref(v_subgoals_1471_);
lean_dec(v_fst_1448_);
lean_dec(v___y_1435_);
v_expr_1508_ = lean_ctor_get(v___y_1433_, 2);
lean_inc_ref(v_expr_1508_);
lean_dec_ref(v___y_1433_);
v___x_1509_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1510_ = l_Lean_indentExpr(v_expr_1508_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set_tag(v___x_1450_, 7);
lean_ctor_set(v___x_1450_, 1, v___x_1510_);
lean_ctor_set(v___x_1450_, 0, v___x_1509_);
v___x_1512_ = v___x_1450_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
v___x_1513_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1512_, v___y_1431_, v___y_1429_, v___y_1432_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1431_);
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v___y_1437_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1429_);
lean_dec(v___y_1426_);
v_a_1525_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1446_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1446_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
v___jp_1533_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_inc_ref(v_occs_1539_);
v___x_1548_ = lean_st_mk_ref(v_occs_1539_);
v___x_1549_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v___y_1544_, v___y_1546_, v___y_1547_);
if (lean_obj_tag(v___x_1549_) == 0)
{
if (lean_obj_tag(v_occs_1539_) == 0)
{
lean_object* v_a_1550_; 
lean_dec_ref(v_occs_1539_);
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
v___y_1426_ = v___y_1547_;
v___y_1427_ = v_a_1550_;
v___y_1428_ = v___y_1536_;
v___y_1429_ = v___y_1545_;
v___y_1430_ = v___y_1541_;
v___y_1431_ = v___y_1544_;
v___y_1432_ = v___y_1546_;
v___y_1433_ = v___y_1538_;
v___y_1434_ = v___y_1537_;
v___y_1435_ = v___y_1543_;
v___y_1436_ = v___y_1542_;
v___y_1437_ = v___x_1548_;
v___y_1438_ = v___y_1535_;
v___y_1439_ = v___y_1534_;
v___y_1440_ = v___y_1540_;
v___y_1441_ = v___x_1301_;
goto v___jp_1425_;
}
else
{
lean_object* v_a_1551_; uint8_t v___x_1552_; 
lean_dec_ref(v_occs_1539_);
v_a_1551_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1551_);
lean_dec_ref(v___x_1549_);
v___x_1552_ = 0;
v___y_1426_ = v___y_1547_;
v___y_1427_ = v_a_1551_;
v___y_1428_ = v___y_1536_;
v___y_1429_ = v___y_1545_;
v___y_1430_ = v___y_1541_;
v___y_1431_ = v___y_1544_;
v___y_1432_ = v___y_1546_;
v___y_1433_ = v___y_1538_;
v___y_1434_ = v___y_1537_;
v___y_1435_ = v___y_1543_;
v___y_1436_ = v___y_1542_;
v___y_1437_ = v___x_1548_;
v___y_1438_ = v___y_1535_;
v___y_1439_ = v___y_1534_;
v___y_1440_ = v___y_1540_;
v___y_1441_ = v___x_1552_;
goto v___jp_1425_;
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v___x_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v_occs_1539_);
lean_dec_ref(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec_ref(v___f_1300_);
v_a_1553_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1549_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1549_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
v___jp_1561_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15));
v___x_1577_ = lean_array_to_list(v___y_1565_);
v___x_1578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1408_);
lean_ctor_set(v___x_1578_, 2, v___x_1577_);
v___y_1534_ = v___y_1564_;
v___y_1535_ = v___y_1563_;
v___y_1536_ = v___y_1562_;
v___y_1537_ = v___y_1567_;
v___y_1538_ = v___y_1566_;
v_occs_1539_ = v___x_1578_;
v___y_1540_ = v___y_1568_;
v___y_1541_ = v___y_1569_;
v___y_1542_ = v___y_1570_;
v___y_1543_ = v___y_1571_;
v___y_1544_ = v___y_1572_;
v___y_1545_ = v___y_1573_;
v___y_1546_ = v___y_1574_;
v___y_1547_ = v___y_1575_;
goto v___jp_1533_;
}
v___jp_1579_:
{
uint8_t v___x_1594_; 
v___x_1594_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v___y_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec_ref(v___y_1593_);
lean_dec_ref(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec_ref(v___f_1300_);
v___x_1595_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17);
v___x_1596_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1595_, v___y_1591_, v___y_1590_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1591_);
return v___x_1596_;
}
else
{
v___y_1562_ = v___y_1581_;
v___y_1563_ = v___y_1588_;
v___y_1564_ = v___y_1589_;
v___y_1565_ = v___y_1593_;
v___y_1566_ = v___y_1584_;
v___y_1567_ = v___y_1585_;
v___y_1568_ = v___y_1583_;
v___y_1569_ = v___y_1592_;
v___y_1570_ = v___y_1580_;
v___y_1571_ = v___y_1582_;
v___y_1572_ = v___y_1591_;
v___y_1573_ = v___y_1590_;
v___y_1574_ = v___y_1586_;
v___y_1575_ = v___y_1587_;
goto v___jp_1561_;
}
}
v___jp_1597_:
{
lean_object* v___x_1615_; 
lean_dec(v___y_1599_);
v___x_1615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v___y_1612_, v___y_1605_, v___y_1614_);
lean_dec(v___y_1614_);
v___y_1580_ = v___y_1598_;
v___y_1581_ = v___y_1600_;
v___y_1582_ = v___y_1601_;
v___y_1583_ = v___y_1602_;
v___y_1584_ = v___y_1603_;
v___y_1585_ = v___y_1604_;
v___y_1586_ = v___y_1606_;
v___y_1587_ = v___y_1607_;
v___y_1588_ = v___y_1608_;
v___y_1589_ = v___y_1609_;
v___y_1590_ = v___y_1610_;
v___y_1591_ = v___y_1611_;
v___y_1592_ = v___y_1613_;
v___y_1593_ = v___x_1615_;
goto v___jp_1579_;
}
v___jp_1616_:
{
uint8_t v___x_1634_; 
v___x_1634_ = lean_nat_dec_le(v___y_1633_, v___y_1628_);
if (v___x_1634_ == 0)
{
lean_dec(v___y_1628_);
lean_inc(v___y_1633_);
v___y_1598_ = v___y_1617_;
v___y_1599_ = v___y_1618_;
v___y_1600_ = v___y_1619_;
v___y_1601_ = v___y_1620_;
v___y_1602_ = v___y_1621_;
v___y_1603_ = v___y_1622_;
v___y_1604_ = v___y_1623_;
v___y_1605_ = v___y_1633_;
v___y_1606_ = v___y_1624_;
v___y_1607_ = v___y_1625_;
v___y_1608_ = v___y_1626_;
v___y_1609_ = v___y_1627_;
v___y_1610_ = v___y_1629_;
v___y_1611_ = v___y_1631_;
v___y_1612_ = v___y_1630_;
v___y_1613_ = v___y_1632_;
v___y_1614_ = v___y_1633_;
goto v___jp_1597_;
}
else
{
v___y_1598_ = v___y_1617_;
v___y_1599_ = v___y_1618_;
v___y_1600_ = v___y_1619_;
v___y_1601_ = v___y_1620_;
v___y_1602_ = v___y_1621_;
v___y_1603_ = v___y_1622_;
v___y_1604_ = v___y_1623_;
v___y_1605_ = v___y_1633_;
v___y_1606_ = v___y_1624_;
v___y_1607_ = v___y_1625_;
v___y_1608_ = v___y_1626_;
v___y_1609_ = v___y_1627_;
v___y_1610_ = v___y_1629_;
v___y_1611_ = v___y_1631_;
v___y_1612_ = v___y_1630_;
v___y_1613_ = v___y_1632_;
v___y_1614_ = v___y_1628_;
goto v___jp_1597_;
}
}
v___jp_1635_:
{
lean_object* v_declName_x3f_1645_; lean_object* v_macroStack_1646_; uint8_t v_mayPostpone_1647_; uint8_t v_errToSorry_1648_; lean_object* v_autoBoundImplicitContext_1649_; lean_object* v_autoBoundImplicitForbidden_1650_; lean_object* v_sectionVars_1651_; lean_object* v_sectionFVars_1652_; uint8_t v_implicitLambda_1653_; uint8_t v_heedElabAsElim_1654_; uint8_t v_isNoncomputableSection_1655_; uint8_t v_inPattern_1656_; lean_object* v_tacSnap_x3f_1657_; uint8_t v_saveRecAppSyntax_1658_; uint8_t v_holesAsSyntheticOpaque_1659_; uint8_t v_checkDeprecated_1660_; lean_object* v_fixedTermElabs_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___f_1666_; lean_object* v___f_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_declName_x3f_1645_ = lean_ctor_get(v___y_1639_, 0);
v_macroStack_1646_ = lean_ctor_get(v___y_1639_, 1);
v_mayPostpone_1647_ = lean_ctor_get_uint8(v___y_1639_, sizeof(void*)*8);
v_errToSorry_1648_ = lean_ctor_get_uint8(v___y_1639_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1649_ = lean_ctor_get(v___y_1639_, 2);
v_autoBoundImplicitForbidden_1650_ = lean_ctor_get(v___y_1639_, 3);
v_sectionVars_1651_ = lean_ctor_get(v___y_1639_, 4);
v_sectionFVars_1652_ = lean_ctor_get(v___y_1639_, 5);
v_implicitLambda_1653_ = lean_ctor_get_uint8(v___y_1639_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1654_ = lean_ctor_get_uint8(v___y_1639_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1655_ = lean_ctor_get_uint8(v___y_1639_, sizeof(void*)*8 + 4);
v_inPattern_1656_ = lean_ctor_get_uint8(v___y_1639_, sizeof(void*)*8 + 6);
v_tacSnap_x3f_1657_ = lean_ctor_get(v___y_1639_, 6);
v_saveRecAppSyntax_1658_ = lean_ctor_get_uint8(v___y_1639_, sizeof(void*)*8 + 7);
v_holesAsSyntheticOpaque_1659_ = lean_ctor_get_uint8(v___y_1639_, sizeof(void*)*8 + 8);
v_checkDeprecated_1660_ = lean_ctor_get_uint8(v___y_1639_, sizeof(void*)*8 + 9);
v_fixedTermElabs_1661_ = lean_ctor_get(v___y_1639_, 7);
v___x_1662_ = lean_unsigned_to_nat(2u);
v___x_1663_ = l_Lean_Syntax_getArg(v_stx_1302_, v___x_1662_);
v___x_1664_ = lean_box(0);
v___x_1665_ = lean_box(v___x_1301_);
lean_inc(v___x_1663_);
v___f_1666_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1666_, 0, v___x_1663_);
lean_closure_set(v___f_1666_, 1, v___x_1664_);
lean_closure_set(v___f_1666_, 2, v___x_1665_);
v___f_1667_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed), 9, 2);
lean_closure_set(v___f_1667_, 0, v___x_1663_);
lean_closure_set(v___f_1667_, 1, v___f_1666_);
lean_inc_ref(v_fixedTermElabs_1661_);
lean_inc(v_tacSnap_x3f_1657_);
lean_inc(v_sectionFVars_1652_);
lean_inc(v_sectionVars_1651_);
lean_inc_ref(v_autoBoundImplicitForbidden_1650_);
lean_inc(v_autoBoundImplicitContext_1649_);
lean_inc(v_macroStack_1646_);
lean_inc(v_declName_x3f_1645_);
v___x_1668_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_1668_, 0, v_declName_x3f_1645_);
lean_ctor_set(v___x_1668_, 1, v_macroStack_1646_);
lean_ctor_set(v___x_1668_, 2, v_autoBoundImplicitContext_1649_);
lean_ctor_set(v___x_1668_, 3, v_autoBoundImplicitForbidden_1650_);
lean_ctor_set(v___x_1668_, 4, v_sectionVars_1651_);
lean_ctor_set(v___x_1668_, 5, v_sectionFVars_1652_);
lean_ctor_set(v___x_1668_, 6, v_tacSnap_x3f_1657_);
lean_ctor_set(v___x_1668_, 7, v_fixedTermElabs_1661_);
lean_ctor_set_uint8(v___x_1668_, sizeof(void*)*8, v_mayPostpone_1647_);
lean_ctor_set_uint8(v___x_1668_, sizeof(void*)*8 + 1, v_errToSorry_1648_);
lean_ctor_set_uint8(v___x_1668_, sizeof(void*)*8 + 2, v_implicitLambda_1653_);
lean_ctor_set_uint8(v___x_1668_, sizeof(void*)*8 + 3, v_heedElabAsElim_1654_);
lean_ctor_set_uint8(v___x_1668_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1655_);
lean_ctor_set_uint8(v___x_1668_, sizeof(void*)*8 + 5, v___x_1301_);
lean_ctor_set_uint8(v___x_1668_, sizeof(void*)*8 + 6, v_inPattern_1656_);
lean_ctor_set_uint8(v___x_1668_, sizeof(void*)*8 + 7, v_saveRecAppSyntax_1658_);
lean_ctor_set_uint8(v___x_1668_, sizeof(void*)*8 + 8, v_holesAsSyntheticOpaque_1659_);
lean_ctor_set_uint8(v___x_1668_, sizeof(void*)*8 + 9, v_checkDeprecated_1660_);
lean_inc(v___y_1644_);
lean_inc_ref(v___y_1643_);
lean_inc(v___y_1642_);
lean_inc_ref(v___y_1641_);
lean_inc(v___y_1640_);
v___x_1669_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_1667_, v___x_1668_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1671_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref(v___x_1669_);
lean_inc(v___y_1644_);
lean_inc_ref(v___y_1643_);
lean_inc(v___y_1642_);
lean_inc_ref(v___y_1641_);
v___x_1671_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1638_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1673_; lean_object* v___f_1674_; lean_object* v___f_1675_; lean_object* v___f_1676_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref(v___x_1671_);
v___x_1673_ = lean_box(v___x_1301_);
v___f_1674_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed), 11, 2);
lean_closure_set(v___f_1674_, 0, v___x_1664_);
lean_closure_set(v___f_1674_, 1, v___x_1673_);
v___f_1675_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18));
v___f_1676_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19));
if (lean_obj_tag(v_occs_1636_) == 0)
{
lean_object* v___x_1677_; 
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
lean_dec_ref(v___x_1304_);
lean_dec_ref(v___x_1303_);
v___x_1677_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22));
v___y_1534_ = v___f_1676_;
v___y_1535_ = v___f_1675_;
v___y_1536_ = v_a_1672_;
v___y_1537_ = v___f_1674_;
v___y_1538_ = v_a_1670_;
v_occs_1539_ = v___x_1677_;
v___y_1540_ = v___y_1637_;
v___y_1541_ = v___y_1638_;
v___y_1542_ = v___y_1639_;
v___y_1543_ = v___y_1640_;
v___y_1544_ = v___y_1641_;
v___y_1545_ = v___y_1642_;
v___y_1546_ = v___y_1643_;
v___y_1547_ = v___y_1644_;
goto v___jp_1533_;
}
else
{
lean_object* v_val_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v_val_1678_ = lean_ctor_get(v_occs_1636_, 0);
lean_inc(v_val_1678_);
lean_dec_ref(v_occs_1636_);
v___x_1679_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23));
lean_inc_ref(v___x_1306_);
lean_inc_ref(v___x_1305_);
lean_inc_ref(v___x_1304_);
lean_inc_ref(v___x_1303_);
v___x_1680_ = l_Lean_Name_mkStr5(v___x_1303_, v___x_1304_, v___x_1305_, v___x_1306_, v___x_1679_);
lean_inc(v_val_1678_);
v___x_1681_ = l_Lean_Syntax_isOfKind(v_val_1678_, v___x_1680_);
lean_dec(v___x_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1682_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24));
v___x_1683_ = l_Lean_Name_mkStr5(v___x_1303_, v___x_1304_, v___x_1305_, v___x_1306_, v___x_1682_);
lean_inc(v_val_1678_);
v___x_1684_ = l_Lean_Syntax_isOfKind(v_val_1678_, v___x_1683_);
lean_dec(v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_val_1678_);
lean_dec_ref(v___f_1674_);
lean_dec(v_a_1672_);
lean_dec(v_a_1670_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___f_1300_);
v___x_1685_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1694_ = l_Lean_Syntax_getArg(v_val_1678_, v___x_1408_);
lean_dec(v_val_1678_);
v___x_1695_ = l_Lean_Syntax_getArgs(v___x_1694_);
lean_dec(v___x_1694_);
v___x_1696_ = lean_array_get_size(v___x_1695_);
v___x_1697_ = lean_mk_empty_array_with_capacity(v___x_1696_);
lean_inc_ref(v___y_1643_);
v___x_1698_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v___x_1695_, v___x_1696_, v___x_1408_, v___x_1697_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec_ref(v___x_1695_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref(v___x_1698_);
v___x_1700_ = lean_array_get_size(v_a_1699_);
v___x_1701_ = lean_nat_dec_eq(v___x_1700_, v___x_1408_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1702_ = lean_nat_sub(v___x_1700_, v___x_1409_);
v___x_1703_ = lean_nat_dec_le(v___x_1408_, v___x_1702_);
if (v___x_1703_ == 0)
{
lean_inc(v___x_1702_);
v___y_1617_ = v___y_1639_;
v___y_1618_ = v___x_1700_;
v___y_1619_ = v_a_1672_;
v___y_1620_ = v___y_1640_;
v___y_1621_ = v___y_1637_;
v___y_1622_ = v_a_1670_;
v___y_1623_ = v___f_1674_;
v___y_1624_ = v___y_1643_;
v___y_1625_ = v___y_1644_;
v___y_1626_ = v___f_1675_;
v___y_1627_ = v___f_1676_;
v___y_1628_ = v___x_1702_;
v___y_1629_ = v___y_1642_;
v___y_1630_ = v_a_1699_;
v___y_1631_ = v___y_1641_;
v___y_1632_ = v___y_1638_;
v___y_1633_ = v___x_1702_;
goto v___jp_1616_;
}
else
{
v___y_1617_ = v___y_1639_;
v___y_1618_ = v___x_1700_;
v___y_1619_ = v_a_1672_;
v___y_1620_ = v___y_1640_;
v___y_1621_ = v___y_1637_;
v___y_1622_ = v_a_1670_;
v___y_1623_ = v___f_1674_;
v___y_1624_ = v___y_1643_;
v___y_1625_ = v___y_1644_;
v___y_1626_ = v___f_1675_;
v___y_1627_ = v___f_1676_;
v___y_1628_ = v___x_1702_;
v___y_1629_ = v___y_1642_;
v___y_1630_ = v_a_1699_;
v___y_1631_ = v___y_1641_;
v___y_1632_ = v___y_1638_;
v___y_1633_ = v___x_1408_;
goto v___jp_1616_;
}
}
else
{
v___y_1580_ = v___y_1639_;
v___y_1581_ = v_a_1672_;
v___y_1582_ = v___y_1640_;
v___y_1583_ = v___y_1637_;
v___y_1584_ = v_a_1670_;
v___y_1585_ = v___f_1674_;
v___y_1586_ = v___y_1643_;
v___y_1587_ = v___y_1644_;
v___y_1588_ = v___f_1675_;
v___y_1589_ = v___f_1676_;
v___y_1590_ = v___y_1642_;
v___y_1591_ = v___y_1641_;
v___y_1592_ = v___y_1638_;
v___y_1593_ = v_a_1699_;
goto v___jp_1579_;
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec_ref(v___f_1674_);
lean_dec(v_a_1672_);
lean_dec(v_a_1670_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___f_1300_);
v_a_1704_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1698_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1698_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
else
{
lean_object* v___x_1712_; 
lean_dec(v_val_1678_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
lean_dec_ref(v___x_1304_);
lean_dec_ref(v___x_1303_);
v___x_1712_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26));
v___y_1534_ = v___f_1676_;
v___y_1535_ = v___f_1675_;
v___y_1536_ = v_a_1672_;
v___y_1537_ = v___f_1674_;
v___y_1538_ = v_a_1670_;
v_occs_1539_ = v___x_1712_;
v___y_1540_ = v___y_1637_;
v___y_1541_ = v___y_1638_;
v___y_1542_ = v___y_1639_;
v___y_1543_ = v___y_1640_;
v___y_1544_ = v___y_1641_;
v___y_1545_ = v___y_1642_;
v___y_1546_ = v___y_1643_;
v___y_1547_ = v___y_1644_;
goto v___jp_1533_;
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_a_1670_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec(v_occs_1636_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
lean_dec_ref(v___x_1304_);
lean_dec_ref(v___x_1303_);
lean_dec_ref(v___f_1300_);
v_a_1713_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1671_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1671_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec(v_occs_1636_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
lean_dec_ref(v___x_1304_);
lean_dec_ref(v___x_1303_);
lean_dec_ref(v___f_1300_);
v_a_1721_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1669_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1669_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
v___jp_1316_:
{
lean_object* v___x_1327_; 
lean_dec(v___y_1322_);
lean_inc(v___y_1326_);
lean_inc_ref(v___y_1325_);
lean_inc(v___y_1324_);
lean_inc_ref(v___y_1323_);
v___x_1327_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v___y_1320_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v_expr_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref(v___x_1327_);
v_expr_1329_ = lean_ctor_get(v___y_1317_, 0);
v___x_1330_ = l_Lean_Expr_mvarId_x21(v_a_1328_);
lean_dec(v_a_1328_);
lean_inc_ref(v_expr_1329_);
v___x_1331_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v___x_1330_, v_expr_1329_, v___y_1324_);
lean_dec_ref(v___x_1331_);
v___x_1332_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1320_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1334_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref(v___x_1332_);
lean_inc(v___y_1326_);
lean_inc_ref(v___y_1325_);
lean_inc(v___y_1324_);
lean_inc_ref(v___y_1323_);
v___x_1334_ = l_Lean_Meta_Simp_Result_getProof(v___y_1317_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref(v___x_1334_);
v___x_1336_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_a_1333_, v_a_1335_, v___y_1324_);
lean_dec_ref(v___x_1336_);
v___x_1337_ = lean_array_to_list(v_subgoals_1318_);
v___x_1338_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1337_, v___y_1320_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
return v___x_1338_;
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v_a_1333_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec_ref(v_subgoals_1318_);
v_a_1339_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1334_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1334_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec_ref(v_subgoals_1318_);
lean_dec_ref(v___y_1317_);
v_a_1347_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1332_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1332_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec_ref(v_subgoals_1318_);
lean_dec_ref(v___y_1317_);
v_a_1355_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1327_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1327_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
v___jp_1363_:
{
size_t v_sz_1374_; size_t v___x_1375_; lean_object* v___x_1376_; 
v_sz_1374_ = lean_array_size(v___y_1373_);
v___x_1375_ = ((size_t)0ULL);
v___x_1376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_1374_, v___x_1375_, v___y_1373_);
v___y_1317_ = v___y_1367_;
v_subgoals_1318_ = v___x_1376_;
v___y_1319_ = v___y_1372_;
v___y_1320_ = v___y_1369_;
v___y_1321_ = v___y_1368_;
v___y_1322_ = v___y_1371_;
v___y_1323_ = v___y_1370_;
v___y_1324_ = v___y_1365_;
v___y_1325_ = v___y_1364_;
v___y_1326_ = v___y_1366_;
goto v___jp_1316_;
}
v___jp_1377_:
{
lean_object* v___x_1391_; 
lean_dec(v___y_1382_);
v___x_1391_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v___y_1383_, v___y_1385_, v___y_1390_);
lean_dec(v___y_1390_);
v___y_1364_ = v___y_1378_;
v___y_1365_ = v___y_1379_;
v___y_1366_ = v___y_1384_;
v___y_1367_ = v___y_1386_;
v___y_1368_ = v___y_1387_;
v___y_1369_ = v___y_1388_;
v___y_1370_ = v___y_1389_;
v___y_1371_ = v___y_1380_;
v___y_1372_ = v___y_1381_;
v___y_1373_ = v___x_1391_;
goto v___jp_1363_;
}
v___jp_1392_:
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_nat_dec_le(v___y_1405_, v___y_1393_);
if (v___x_1406_ == 0)
{
lean_dec(v___y_1393_);
lean_inc(v___y_1405_);
v___y_1378_ = v___y_1394_;
v___y_1379_ = v___y_1395_;
v___y_1380_ = v___y_1396_;
v___y_1381_ = v___y_1397_;
v___y_1382_ = v___y_1398_;
v___y_1383_ = v___y_1399_;
v___y_1384_ = v___y_1400_;
v___y_1385_ = v___y_1405_;
v___y_1386_ = v___y_1401_;
v___y_1387_ = v___y_1402_;
v___y_1388_ = v___y_1403_;
v___y_1389_ = v___y_1404_;
v___y_1390_ = v___y_1405_;
goto v___jp_1377_;
}
else
{
v___y_1378_ = v___y_1394_;
v___y_1379_ = v___y_1395_;
v___y_1380_ = v___y_1396_;
v___y_1381_ = v___y_1397_;
v___y_1382_ = v___y_1398_;
v___y_1383_ = v___y_1399_;
v___y_1384_ = v___y_1400_;
v___y_1385_ = v___y_1405_;
v___y_1386_ = v___y_1401_;
v___y_1387_ = v___y_1402_;
v___y_1388_ = v___y_1403_;
v___y_1389_ = v___y_1404_;
v___y_1390_ = v___y_1393_;
goto v___jp_1377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed(lean_object** _args){
lean_object* v___x_1742_ = _args[0];
lean_object* v___f_1743_ = _args[1];
lean_object* v___x_1744_ = _args[2];
lean_object* v_stx_1745_ = _args[3];
lean_object* v___x_1746_ = _args[4];
lean_object* v___x_1747_ = _args[5];
lean_object* v___x_1748_ = _args[6];
lean_object* v___x_1749_ = _args[7];
lean_object* v___y_1750_ = _args[8];
lean_object* v___y_1751_ = _args[9];
lean_object* v___y_1752_ = _args[10];
lean_object* v___y_1753_ = _args[11];
lean_object* v___y_1754_ = _args[12];
lean_object* v___y_1755_ = _args[13];
lean_object* v___y_1756_ = _args[14];
lean_object* v___y_1757_ = _args[15];
lean_object* v___y_1758_ = _args[16];
_start:
{
uint8_t v___x_19346__boxed_1759_; uint8_t v___x_19348__boxed_1760_; lean_object* v_res_1761_; 
v___x_19346__boxed_1759_ = lean_unbox(v___x_1742_);
v___x_19348__boxed_1760_ = lean_unbox(v___x_1744_);
v_res_1761_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(v___x_19346__boxed_1759_, v___f_1743_, v___x_19348__boxed_1760_, v_stx_1745_, v___x_1746_, v___x_1747_, v___x_1748_, v___x_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v_stx_1745_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern(lean_object* v_stx_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v___f_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; uint8_t v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___y_1794_; lean_object* v___x_1795_; 
v___f_1784_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__0));
v___x_1785_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1));
v___x_1786_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__2));
v___x_1787_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3));
v___x_1788_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4));
v___x_1789_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
lean_inc(v_stx_1774_);
v___x_1790_ = l_Lean_Syntax_isOfKind(v_stx_1774_, v___x_1789_);
v___x_1791_ = 1;
v___x_1792_ = lean_box(v___x_1790_);
v___x_1793_ = lean_box(v___x_1791_);
v___y_1794_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed), 17, 8);
lean_closure_set(v___y_1794_, 0, v___x_1792_);
lean_closure_set(v___y_1794_, 1, v___f_1784_);
lean_closure_set(v___y_1794_, 2, v___x_1793_);
lean_closure_set(v___y_1794_, 3, v_stx_1774_);
lean_closure_set(v___y_1794_, 4, v___x_1785_);
lean_closure_set(v___y_1794_, 5, v___x_1786_);
lean_closure_set(v___y_1794_, 6, v___x_1787_);
lean_closure_set(v___y_1794_, 7, v___x_1788_);
v___x_1795_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1794_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___boxed(lean_object* v_stx_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_Elab_Tactic_Conv_evalPattern(v_stx_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(lean_object* v_00_u03b1_1807_, lean_object* v_ref_1808_, lean_object* v_msg_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_ref_1808_, v_msg_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___boxed(lean_object* v_00_u03b1_1820_, lean_object* v_ref_1821_, lean_object* v_msg_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(v_00_u03b1_1820_, v_ref_1821_, v_msg_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v_ref_1821_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(lean_object* v_mvarId_1833_, lean_object* v_val_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1833_, v_val_1834_, v___y_1840_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___boxed(lean_object* v_mvarId_1845_, lean_object* v_val_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(v_mvarId_1845_, v_val_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(lean_object* v_00_u03b1_1857_, lean_object* v_msg_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_1858_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___boxed(lean_object* v_00_u03b1_1869_, lean_object* v_msg_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(v_00_u03b1_1869_, v_msg_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(lean_object* v_n_1881_, lean_object* v_as_1882_, lean_object* v_lo_1883_, lean_object* v_hi_1884_, lean_object* v_w_1885_, lean_object* v_hlo_1886_, lean_object* v_hhi_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_as_1882_, v_lo_1883_, v_hi_1884_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___boxed(lean_object* v_n_1889_, lean_object* v_as_1890_, lean_object* v_lo_1891_, lean_object* v_hi_1892_, lean_object* v_w_1893_, lean_object* v_hlo_1894_, lean_object* v_hhi_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(v_n_1889_, v_as_1890_, v_lo_1891_, v_hi_1892_, v_w_1893_, v_hlo_1894_, v_hhi_1895_);
lean_dec(v_hi_1892_);
lean_dec(v_n_1889_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(lean_object* v_as_1897_, lean_object* v_i_1898_, lean_object* v_j_1899_, lean_object* v_inv_1900_, lean_object* v_bs_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_as_1897_, v_i_1898_, v_j_1899_, v_bs_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___boxed(lean_object* v_as_1912_, lean_object* v_i_1913_, lean_object* v_j_1914_, lean_object* v_inv_1915_, lean_object* v_bs_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(v_as_1912_, v_i_1913_, v_j_1914_, v_inv_1915_, v_bs_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec_ref(v_as_1912_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(lean_object* v_n_1927_, lean_object* v_as_1928_, lean_object* v_lo_1929_, lean_object* v_hi_1930_, lean_object* v_w_1931_, lean_object* v_hlo_1932_, lean_object* v_hhi_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_as_1928_, v_lo_1929_, v_hi_1930_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___boxed(lean_object* v_n_1935_, lean_object* v_as_1936_, lean_object* v_lo_1937_, lean_object* v_hi_1938_, lean_object* v_w_1939_, lean_object* v_hlo_1940_, lean_object* v_hhi_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(v_n_1935_, v_as_1936_, v_lo_1937_, v_hi_1938_, v_w_1939_, v_hlo_1940_, v_hhi_1941_);
lean_dec(v_hi_1938_);
lean_dec(v_n_1935_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(lean_object* v_00_u03b2_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_, lean_object* v_x_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_x_1944_, v_x_1945_, v_x_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1948_, lean_object* v_x_1949_, size_t v_x_1950_, size_t v_x_1951_, lean_object* v_x_1952_, lean_object* v_x_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1949_, v_x_1950_, v_x_1951_, v_x_1952_, v_x_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1955_, lean_object* v_x_1956_, lean_object* v_x_1957_, lean_object* v_x_1958_, lean_object* v_x_1959_, lean_object* v_x_1960_){
_start:
{
size_t v_x_20484__boxed_1961_; size_t v_x_20485__boxed_1962_; lean_object* v_res_1963_; 
v_x_20484__boxed_1961_ = lean_unbox_usize(v_x_1957_);
lean_dec(v_x_1957_);
v_x_20485__boxed_1962_ = lean_unbox_usize(v_x_1958_);
lean_dec(v_x_1958_);
v_res_1963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(v_00_u03b2_1955_, v_x_1956_, v_x_20484__boxed_1961_, v_x_20485__boxed_1962_, v_x_1959_, v_x_1960_);
return v_res_1963_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10_spec__12(lean_object* v_as_1964_, lean_object* v_a_1965_, lean_object* v_x_1966_, lean_object* v_x_1967_){
_start:
{
uint8_t v___x_1968_; 
v___x_1968_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10_spec__12___redArg(v_as_1964_, v_a_1965_, v_x_1966_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10_spec__12___boxed(lean_object* v_as_1969_, lean_object* v_a_1970_, lean_object* v_x_1971_, lean_object* v_x_1972_){
_start:
{
uint8_t v_res_1973_; lean_object* v_r_1974_; 
v_res_1973_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__10_spec__12(v_as_1969_, v_a_1970_, v_x_1971_, v_x_1972_);
lean_dec_ref(v_a_1970_);
lean_dec_ref(v_as_1969_);
v_r_1974_ = lean_box(v_res_1973_);
return v_r_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12(lean_object* v_00_u03b2_1975_, lean_object* v_n_1976_, lean_object* v_k_1977_, lean_object* v_v_1978_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v_n_1976_, v_k_1977_, v_v_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(lean_object* v_00_u03b2_1980_, size_t v_depth_1981_, lean_object* v_keys_1982_, lean_object* v_vals_1983_, lean_object* v_heq_1984_, lean_object* v_i_1985_, lean_object* v_entries_1986_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_1981_, v_keys_1982_, v_vals_1983_, v_i_1985_, v_entries_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___boxed(lean_object* v_00_u03b2_1988_, lean_object* v_depth_1989_, lean_object* v_keys_1990_, lean_object* v_vals_1991_, lean_object* v_heq_1992_, lean_object* v_i_1993_, lean_object* v_entries_1994_){
_start:
{
size_t v_depth_boxed_1995_; lean_object* v_res_1996_; 
v_depth_boxed_1995_ = lean_unbox_usize(v_depth_1989_);
lean_dec(v_depth_1989_);
v_res_1996_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(v_00_u03b2_1988_, v_depth_boxed_1995_, v_keys_1990_, v_vals_1991_, v_heq_1992_, v_i_1993_, v_entries_1994_);
lean_dec_ref(v_vals_1991_);
lean_dec_ref(v_keys_1990_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__14(lean_object* v_00_u03b2_1997_, lean_object* v_x_1998_, lean_object* v_x_1999_, lean_object* v_x_2000_, lean_object* v_x_2001_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__14___redArg(v_x_1998_, v_x_1999_, v_x_2000_, v_x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1(){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2012_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2013_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
v___x_2014_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2015_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___boxed), 10, 0);
v___x_2016_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2012_, v___x_2013_, v___x_2014_, v___x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___boxed(lean_object* v_a_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3(){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2046_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6));
v___x_2047_ = l_Lean_addBuiltinDeclarationRanges(v___x_2045_, v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___boxed(lean_object* v_a_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
return v_res_2049_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Pattern(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Conv_Pattern(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Pattern(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Conv_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Conv_Pattern(builtin);
}
#ifdef __cplusplus
}
#endif
