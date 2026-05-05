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
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
uint8_t l_Lean_instBEqHeadIndex_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "positive integer expected"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalPattern"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__3_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 226, 241, 79, 162, 140, 83, 90)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(105) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(142) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(105) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(105) << 1) | 1)),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4_value),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___boxed(lean_object*);
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
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
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
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
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
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
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
lean_dec_ref(v___x_226_);
return v___x_227_;
}
}
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
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
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
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
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
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
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v_b_384_);
return v___x_391_;
}
else
{
lean_object* v_a_392_; lean_object* v___x_393_; 
v_a_392_ = lean_array_uget_borrowed(v_as_381_, v_i_383_);
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
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
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
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
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
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
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
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
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
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
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
v___x_645_ = l_Lean_Elab_Term_elabTerm(v___x_635_, v___x_636_, v___x_637_, v___x_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref(v___x_645_);
v___x_647_ = l_Lean_Meta_abstractMVars(v_a_646_, v___x_637_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
return v___x_647_;
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
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
uint8_t v___x_18448__boxed_666_; lean_object* v_res_667_; 
v___x_18448__boxed_666_ = lean_unbox(v___x_658_);
v_res_667_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(v___x_656_, v___x_657_, v___x_18448__boxed_666_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
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
lean_dec_ref(v___x_698_);
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
lean_dec(v___y_709_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
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
uint8_t v___x_18542__boxed_737_; lean_object* v_res_738_; 
v___x_18542__boxed_737_ = lean_unbox(v___x_727_);
v_res_738_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(v___x_726_, v___x_18542__boxed_737_, v_e_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(lean_object* v_hi_802_, lean_object* v_pivot_803_, lean_object* v_as_804_, lean_object* v_i_805_, lean_object* v_k_806_){
_start:
{
uint8_t v___x_807_; 
v___x_807_ = lean_nat_dec_lt(v_k_806_, v_hi_802_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v_k_806_);
v___x_808_ = lean_array_fswap(v_as_804_, v_i_805_, v_hi_802_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v_i_805_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
return v___x_809_;
}
else
{
lean_object* v___x_810_; lean_object* v_fst_811_; lean_object* v_fst_812_; uint8_t v___x_813_; 
v___x_810_ = lean_array_fget_borrowed(v_as_804_, v_k_806_);
v_fst_811_ = lean_ctor_get(v___x_810_, 0);
v_fst_812_ = lean_ctor_get(v_pivot_803_, 0);
v___x_813_ = lean_nat_dec_lt(v_fst_811_, v_fst_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_815_ = lean_nat_add(v_k_806_, v___x_814_);
lean_dec(v_k_806_);
v_k_806_ = v___x_815_;
goto _start;
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_817_ = lean_array_fswap(v_as_804_, v_i_805_, v_k_806_);
v___x_818_ = lean_unsigned_to_nat(1u);
v___x_819_ = lean_nat_add(v_i_805_, v___x_818_);
lean_dec(v_i_805_);
v___x_820_ = lean_nat_add(v_k_806_, v___x_818_);
lean_dec(v_k_806_);
v_as_804_ = v___x_817_;
v_i_805_ = v___x_819_;
v_k_806_ = v___x_820_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg___boxed(lean_object* v_hi_822_, lean_object* v_pivot_823_, lean_object* v_as_824_, lean_object* v_i_825_, lean_object* v_k_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_822_, v_pivot_823_, v_as_824_, v_i_825_, v_k_826_);
lean_dec_ref(v_pivot_823_);
lean_dec(v_hi_822_);
return v_res_827_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(lean_object* v_x1_828_, lean_object* v_x2_829_){
_start:
{
lean_object* v_fst_830_; lean_object* v_fst_831_; uint8_t v___x_832_; 
v_fst_830_ = lean_ctor_get(v_x1_828_, 0);
v_fst_831_ = lean_ctor_get(v_x2_829_, 0);
v___x_832_ = lean_nat_dec_lt(v_fst_830_, v_fst_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(lean_object* v_x1_833_, lean_object* v_x2_834_){
_start:
{
uint8_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v_x1_833_, v_x2_834_);
lean_dec_ref(v_x2_834_);
lean_dec_ref(v_x1_833_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(lean_object* v_n_837_, lean_object* v_as_838_, lean_object* v_lo_839_, lean_object* v_hi_840_){
_start:
{
lean_object* v___y_842_; uint8_t v___x_852_; 
v___x_852_ = lean_nat_dec_lt(v_lo_839_, v_hi_840_);
if (v___x_852_ == 0)
{
lean_dec(v_lo_839_);
return v_as_838_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v_mid_855_; lean_object* v___y_857_; lean_object* v___y_863_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_853_ = lean_nat_add(v_lo_839_, v_hi_840_);
v___x_854_ = lean_unsigned_to_nat(1u);
v_mid_855_ = lean_nat_shiftr(v___x_853_, v___x_854_);
lean_dec(v___x_853_);
v___x_868_ = lean_array_fget_borrowed(v_as_838_, v_mid_855_);
v___x_869_ = lean_array_fget_borrowed(v_as_838_, v_lo_839_);
v___x_870_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_868_, v___x_869_);
if (v___x_870_ == 0)
{
v___y_863_ = v_as_838_;
goto v___jp_862_;
}
else
{
lean_object* v___x_871_; 
v___x_871_ = lean_array_fswap(v_as_838_, v_lo_839_, v_mid_855_);
v___y_863_ = v___x_871_;
goto v___jp_862_;
}
v___jp_856_:
{
lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_858_ = lean_array_fget_borrowed(v___y_857_, v_mid_855_);
v___x_859_ = lean_array_fget_borrowed(v___y_857_, v_hi_840_);
v___x_860_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_858_, v___x_859_);
if (v___x_860_ == 0)
{
lean_dec(v_mid_855_);
v___y_842_ = v___y_857_;
goto v___jp_841_;
}
else
{
lean_object* v___x_861_; 
v___x_861_ = lean_array_fswap(v___y_857_, v_mid_855_, v_hi_840_);
lean_dec(v_mid_855_);
v___y_842_ = v___x_861_;
goto v___jp_841_;
}
}
v___jp_862_:
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_864_ = lean_array_fget_borrowed(v___y_863_, v_hi_840_);
v___x_865_ = lean_array_fget_borrowed(v___y_863_, v_lo_839_);
v___x_866_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_864_, v___x_865_);
if (v___x_866_ == 0)
{
v___y_857_ = v___y_863_;
goto v___jp_856_;
}
else
{
lean_object* v___x_867_; 
v___x_867_ = lean_array_fswap(v___y_863_, v_lo_839_, v_hi_840_);
v___y_857_ = v___x_867_;
goto v___jp_856_;
}
}
}
v___jp_841_:
{
lean_object* v_pivot_843_; lean_object* v___x_844_; lean_object* v_fst_845_; lean_object* v_snd_846_; uint8_t v___x_847_; 
v_pivot_843_ = lean_array_fget(v___y_842_, v_hi_840_);
lean_inc_n(v_lo_839_, 2);
v___x_844_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_840_, v_pivot_843_, v___y_842_, v_lo_839_, v_lo_839_);
lean_dec(v_pivot_843_);
v_fst_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_fst_845_);
v_snd_846_ = lean_ctor_get(v___x_844_, 1);
lean_inc(v_snd_846_);
lean_dec_ref(v___x_844_);
v___x_847_ = lean_nat_dec_le(v_hi_840_, v_fst_845_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_837_, v_snd_846_, v_lo_839_, v_fst_845_);
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_nat_add(v_fst_845_, v___x_849_);
lean_dec(v_fst_845_);
v_as_838_ = v___x_848_;
v_lo_839_ = v___x_850_;
goto _start;
}
else
{
lean_dec(v_fst_845_);
lean_dec(v_lo_839_);
return v_snd_846_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___boxed(lean_object* v_n_872_, lean_object* v_as_873_, lean_object* v_lo_874_, lean_object* v_hi_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_872_, v_as_873_, v_lo_874_, v_hi_875_);
lean_dec(v_hi_875_);
lean_dec(v_n_872_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(lean_object* v_msgData_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; lean_object* v_env_884_; lean_object* v___x_885_; lean_object* v_mctx_886_; lean_object* v_lctx_887_; lean_object* v_options_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_883_ = lean_st_ref_get(v___y_881_);
v_env_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc_ref(v_env_884_);
lean_dec(v___x_883_);
v___x_885_ = lean_st_ref_get(v___y_879_);
v_mctx_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc_ref(v_mctx_886_);
lean_dec(v___x_885_);
v_lctx_887_ = lean_ctor_get(v___y_878_, 2);
v_options_888_ = lean_ctor_get(v___y_880_, 2);
lean_inc_ref(v_options_888_);
lean_inc_ref(v_lctx_887_);
v___x_889_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_889_, 0, v_env_884_);
lean_ctor_set(v___x_889_, 1, v_mctx_886_);
lean_ctor_set(v___x_889_, 2, v_lctx_887_);
lean_ctor_set(v___x_889_, 3, v_options_888_);
v___x_890_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v_msgData_877_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(lean_object* v_msgData_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msgData_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(lean_object* v_msg_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_ref_905_; lean_object* v___x_906_; lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_915_; 
v_ref_905_ = lean_ctor_get(v___y_902_, 5);
v___x_906_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msg_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_915_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_915_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_915_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
lean_inc(v_ref_905_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_ref_905_);
lean_ctor_set(v___x_911_, 1, v_a_907_);
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 1);
lean_ctor_set(v___x_909_, 0, v___x_911_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg___boxed(lean_object* v_msg_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(lean_object* v_x_923_, lean_object* v_x_924_, lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
lean_object* v_ks_927_; lean_object* v_vs_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_952_; 
v_ks_927_ = lean_ctor_get(v_x_923_, 0);
v_vs_928_ = lean_ctor_get(v_x_923_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v_x_923_);
if (v_isSharedCheck_952_ == 0)
{
v___x_930_ = v_x_923_;
v_isShared_931_ = v_isSharedCheck_952_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_vs_928_);
lean_inc(v_ks_927_);
lean_dec(v_x_923_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_952_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_932_ = lean_array_get_size(v_ks_927_);
v___x_933_ = lean_nat_dec_lt(v_x_924_, v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
lean_dec(v_x_924_);
v___x_934_ = lean_array_push(v_ks_927_, v_x_925_);
v___x_935_ = lean_array_push(v_vs_928_, v_x_926_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_935_);
lean_ctor_set(v___x_930_, 0, v___x_934_);
v___x_937_ = v___x_930_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
else
{
lean_object* v_k_x27_939_; uint8_t v___x_940_; 
v_k_x27_939_ = lean_array_fget_borrowed(v_ks_927_, v_x_924_);
v___x_940_ = l_Lean_instBEqMVarId_beq(v_x_925_, v_k_x27_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_942_; 
if (v_isShared_931_ == 0)
{
v___x_942_ = v___x_930_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_ks_927_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_vs_928_);
v___x_942_ = v_reuseFailAlloc_946_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_nat_add(v_x_924_, v___x_943_);
lean_dec(v_x_924_);
v_x_923_ = v___x_942_;
v_x_924_ = v___x_944_;
goto _start;
}
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_947_ = lean_array_fset(v_ks_927_, v_x_924_, v_x_925_);
v___x_948_ = lean_array_fset(v_vs_928_, v_x_924_, v_x_926_);
lean_dec(v_x_924_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_948_);
lean_ctor_set(v___x_930_, 0, v___x_947_);
v___x_950_ = v___x_930_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_n_953_, lean_object* v_k_954_, lean_object* v_v_955_){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_n_953_, v___x_956_, v_k_954_, v_v_955_);
return v___x_957_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_958_; size_t v___x_959_; size_t v___x_960_; 
v___x_958_ = ((size_t)5ULL);
v___x_959_ = ((size_t)1ULL);
v___x_960_ = lean_usize_shift_left(v___x_959_, v___x_958_);
return v___x_960_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_961_; size_t v___x_962_; size_t v___x_963_; 
v___x_961_ = ((size_t)1ULL);
v___x_962_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_963_ = lean_usize_sub(v___x_962_, v___x_961_);
return v___x_963_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(lean_object* v_x_965_, size_t v_x_966_, size_t v_x_967_, lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
if (lean_obj_tag(v_x_965_) == 0)
{
lean_object* v_es_970_; size_t v___x_971_; size_t v___x_972_; size_t v___x_973_; size_t v___x_974_; lean_object* v_j_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v_es_970_ = lean_ctor_get(v_x_965_, 0);
v___x_971_ = ((size_t)5ULL);
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_974_ = lean_usize_land(v_x_966_, v___x_973_);
v_j_975_ = lean_usize_to_nat(v___x_974_);
v___x_976_ = lean_array_get_size(v_es_970_);
v___x_977_ = lean_nat_dec_lt(v_j_975_, v___x_976_);
if (v___x_977_ == 0)
{
lean_dec(v_j_975_);
lean_dec(v_x_969_);
lean_dec(v_x_968_);
return v_x_965_;
}
else
{
lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1014_; 
lean_inc_ref(v_es_970_);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_x_965_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; 
v_unused_1015_ = lean_ctor_get(v_x_965_, 0);
lean_dec(v_unused_1015_);
v___x_979_ = v_x_965_;
v_isShared_980_ = v_isSharedCheck_1014_;
goto v_resetjp_978_;
}
else
{
lean_dec(v_x_965_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1014_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_v_981_; lean_object* v___x_982_; lean_object* v_xs_x27_983_; lean_object* v___y_985_; 
v_v_981_ = lean_array_fget(v_es_970_, v_j_975_);
v___x_982_ = lean_box(0);
v_xs_x27_983_ = lean_array_fset(v_es_970_, v_j_975_, v___x_982_);
switch(lean_obj_tag(v_v_981_))
{
case 0:
{
lean_object* v_key_990_; lean_object* v_val_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1001_; 
v_key_990_ = lean_ctor_get(v_v_981_, 0);
v_val_991_ = lean_ctor_get(v_v_981_, 1);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_v_981_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_993_ = v_v_981_;
v_isShared_994_ = v_isSharedCheck_1001_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_val_991_);
lean_inc(v_key_990_);
lean_dec(v_v_981_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1001_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
uint8_t v___x_995_; 
v___x_995_ = l_Lean_instBEqMVarId_beq(v_x_968_, v_key_990_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_del_object(v___x_993_);
v___x_996_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_990_, v_val_991_, v_x_968_, v_x_969_);
v___x_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
v___y_985_ = v___x_997_;
goto v___jp_984_;
}
else
{
lean_object* v___x_999_; 
lean_dec(v_val_991_);
lean_dec(v_key_990_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v_x_969_);
lean_ctor_set(v___x_993_, 0, v_x_968_);
v___x_999_ = v___x_993_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_x_968_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_x_969_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
v___y_985_ = v___x_999_;
goto v___jp_984_;
}
}
}
}
case 1:
{
lean_object* v_node_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1012_; 
v_node_1002_ = lean_ctor_get(v_v_981_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_v_981_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1004_ = v_v_981_;
v_isShared_1005_ = v_isSharedCheck_1012_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_node_1002_);
lean_dec(v_v_981_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1012_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
size_t v___x_1006_; size_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1006_ = lean_usize_shift_right(v_x_966_, v___x_971_);
v___x_1007_ = lean_usize_add(v_x_967_, v___x_972_);
v___x_1008_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_node_1002_, v___x_1006_, v___x_1007_, v_x_968_, v_x_969_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1008_);
v___x_1010_ = v___x_1004_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
v___y_985_ = v___x_1010_;
goto v___jp_984_;
}
}
}
default: 
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_x_968_);
lean_ctor_set(v___x_1013_, 1, v_x_969_);
v___y_985_ = v___x_1013_;
goto v___jp_984_;
}
}
v___jp_984_:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_array_fset(v_xs_x27_983_, v_j_975_, v___y_985_);
lean_dec(v_j_975_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_986_);
v___x_988_ = v___x_979_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
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
}
else
{
lean_object* v_ks_1016_; lean_object* v_vs_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1037_; 
v_ks_1016_ = lean_ctor_get(v_x_965_, 0);
v_vs_1017_ = lean_ctor_get(v_x_965_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_x_965_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1019_ = v_x_965_;
v_isShared_1020_ = v_isSharedCheck_1037_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_vs_1017_);
lean_inc(v_ks_1016_);
lean_dec(v_x_965_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1037_;
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
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_ks_1016_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_vs_1017_);
v___x_1022_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v_newNode_1023_; uint8_t v___y_1025_; size_t v___x_1031_; uint8_t v___x_1032_; 
v_newNode_1023_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v___x_1022_, v_x_968_, v_x_969_);
v___x_1031_ = ((size_t)7ULL);
v___x_1032_ = lean_usize_dec_le(v___x_1031_, v_x_967_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1033_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1023_);
v___x_1034_ = lean_unsigned_to_nat(4u);
v___x_1035_ = lean_nat_dec_lt(v___x_1033_, v___x_1034_);
lean_dec(v___x_1033_);
v___y_1025_ = v___x_1035_;
goto v___jp_1024_;
}
else
{
v___y_1025_ = v___x_1032_;
goto v___jp_1024_;
}
v___jp_1024_:
{
if (v___y_1025_ == 0)
{
lean_object* v_ks_1026_; lean_object* v_vs_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_ks_1026_ = lean_ctor_get(v_newNode_1023_, 0);
lean_inc_ref(v_ks_1026_);
v_vs_1027_ = lean_ctor_get(v_newNode_1023_, 1);
lean_inc_ref(v_vs_1027_);
lean_dec_ref(v_newNode_1023_);
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2);
v___x_1030_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_x_967_, v_ks_1026_, v_vs_1027_, v___x_1028_, v___x_1029_);
lean_dec_ref(v_vs_1027_);
lean_dec_ref(v_ks_1026_);
return v___x_1030_;
}
else
{
return v_newNode_1023_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(size_t v_depth_1038_, lean_object* v_keys_1039_, lean_object* v_vals_1040_, lean_object* v_i_1041_, lean_object* v_entries_1042_){
_start:
{
lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = lean_array_get_size(v_keys_1039_);
v___x_1044_ = lean_nat_dec_lt(v_i_1041_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_dec(v_i_1041_);
return v_entries_1042_;
}
else
{
lean_object* v_k_1045_; lean_object* v_v_1046_; uint64_t v___x_1047_; size_t v_h_1048_; size_t v___x_1049_; lean_object* v___x_1050_; size_t v___x_1051_; size_t v___x_1052_; size_t v___x_1053_; size_t v_h_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_k_1045_ = lean_array_fget_borrowed(v_keys_1039_, v_i_1041_);
v_v_1046_ = lean_array_fget_borrowed(v_vals_1040_, v_i_1041_);
v___x_1047_ = l_Lean_instHashableMVarId_hash(v_k_1045_);
v_h_1048_ = lean_uint64_to_usize(v___x_1047_);
v___x_1049_ = ((size_t)5ULL);
v___x_1050_ = lean_unsigned_to_nat(1u);
v___x_1051_ = ((size_t)1ULL);
v___x_1052_ = lean_usize_sub(v_depth_1038_, v___x_1051_);
v___x_1053_ = lean_usize_mul(v___x_1049_, v___x_1052_);
v_h_1054_ = lean_usize_shift_right(v_h_1048_, v___x_1053_);
v___x_1055_ = lean_nat_add(v_i_1041_, v___x_1050_);
lean_dec(v_i_1041_);
lean_inc(v_v_1046_);
lean_inc(v_k_1045_);
v___x_1056_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_entries_1042_, v_h_1054_, v_depth_1038_, v_k_1045_, v_v_1046_);
v_i_1041_ = v___x_1055_;
v_entries_1042_ = v___x_1056_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg___boxed(lean_object* v_depth_1058_, lean_object* v_keys_1059_, lean_object* v_vals_1060_, lean_object* v_i_1061_, lean_object* v_entries_1062_){
_start:
{
size_t v_depth_boxed_1063_; lean_object* v_res_1064_; 
v_depth_boxed_1063_ = lean_unbox_usize(v_depth_1058_);
lean_dec(v_depth_1058_);
v_res_1064_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_boxed_1063_, v_keys_1059_, v_vals_1060_, v_i_1061_, v_entries_1062_);
lean_dec_ref(v_vals_1060_);
lean_dec_ref(v_keys_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_x_1065_, lean_object* v_x_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_){
_start:
{
size_t v_x_18897__boxed_1070_; size_t v_x_18898__boxed_1071_; lean_object* v_res_1072_; 
v_x_18897__boxed_1070_ = lean_unbox_usize(v_x_1066_);
lean_dec(v_x_1066_);
v_x_18898__boxed_1071_ = lean_unbox_usize(v_x_1067_);
lean_dec(v_x_1067_);
v_res_1072_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1065_, v_x_18897__boxed_1070_, v_x_18898__boxed_1071_, v_x_1068_, v_x_1069_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(lean_object* v_x_1073_, lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
uint64_t v___x_1076_; size_t v___x_1077_; size_t v___x_1078_; lean_object* v___x_1079_; 
v___x_1076_ = l_Lean_instHashableMVarId_hash(v_x_1074_);
v___x_1077_ = lean_uint64_to_usize(v___x_1076_);
v___x_1078_ = ((size_t)1ULL);
v___x_1079_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1073_, v___x_1077_, v___x_1078_, v_x_1074_, v_x_1075_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(lean_object* v_mvarId_1080_, lean_object* v_val_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; lean_object* v_mctx_1085_; lean_object* v_cache_1086_; lean_object* v_zetaDeltaFVarIds_1087_; lean_object* v_postponed_1088_; lean_object* v_diag_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1117_; 
v___x_1084_ = lean_st_ref_take(v___y_1082_);
v_mctx_1085_ = lean_ctor_get(v___x_1084_, 0);
v_cache_1086_ = lean_ctor_get(v___x_1084_, 1);
v_zetaDeltaFVarIds_1087_ = lean_ctor_get(v___x_1084_, 2);
v_postponed_1088_ = lean_ctor_get(v___x_1084_, 3);
v_diag_1089_ = lean_ctor_get(v___x_1084_, 4);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1091_ = v___x_1084_;
v_isShared_1092_ = v_isSharedCheck_1117_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_diag_1089_);
lean_inc(v_postponed_1088_);
lean_inc(v_zetaDeltaFVarIds_1087_);
lean_inc(v_cache_1086_);
lean_inc(v_mctx_1085_);
lean_dec(v___x_1084_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1117_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_depth_1093_; lean_object* v_levelAssignDepth_1094_; lean_object* v_lmvarCounter_1095_; lean_object* v_mvarCounter_1096_; lean_object* v_lDecls_1097_; lean_object* v_decls_1098_; lean_object* v_userNames_1099_; lean_object* v_lAssignment_1100_; lean_object* v_eAssignment_1101_; lean_object* v_dAssignment_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1116_; 
v_depth_1093_ = lean_ctor_get(v_mctx_1085_, 0);
v_levelAssignDepth_1094_ = lean_ctor_get(v_mctx_1085_, 1);
v_lmvarCounter_1095_ = lean_ctor_get(v_mctx_1085_, 2);
v_mvarCounter_1096_ = lean_ctor_get(v_mctx_1085_, 3);
v_lDecls_1097_ = lean_ctor_get(v_mctx_1085_, 4);
v_decls_1098_ = lean_ctor_get(v_mctx_1085_, 5);
v_userNames_1099_ = lean_ctor_get(v_mctx_1085_, 6);
v_lAssignment_1100_ = lean_ctor_get(v_mctx_1085_, 7);
v_eAssignment_1101_ = lean_ctor_get(v_mctx_1085_, 8);
v_dAssignment_1102_ = lean_ctor_get(v_mctx_1085_, 9);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_mctx_1085_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1104_ = v_mctx_1085_;
v_isShared_1105_ = v_isSharedCheck_1116_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_dAssignment_1102_);
lean_inc(v_eAssignment_1101_);
lean_inc(v_lAssignment_1100_);
lean_inc(v_userNames_1099_);
lean_inc(v_decls_1098_);
lean_inc(v_lDecls_1097_);
lean_inc(v_mvarCounter_1096_);
lean_inc(v_lmvarCounter_1095_);
lean_inc(v_levelAssignDepth_1094_);
lean_inc(v_depth_1093_);
lean_dec(v_mctx_1085_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1116_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1106_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_eAssignment_1101_, v_mvarId_1080_, v_val_1081_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 8, v___x_1106_);
v___x_1108_ = v___x_1104_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_depth_1093_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_levelAssignDepth_1094_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_lmvarCounter_1095_);
lean_ctor_set(v_reuseFailAlloc_1115_, 3, v_mvarCounter_1096_);
lean_ctor_set(v_reuseFailAlloc_1115_, 4, v_lDecls_1097_);
lean_ctor_set(v_reuseFailAlloc_1115_, 5, v_decls_1098_);
lean_ctor_set(v_reuseFailAlloc_1115_, 6, v_userNames_1099_);
lean_ctor_set(v_reuseFailAlloc_1115_, 7, v_lAssignment_1100_);
lean_ctor_set(v_reuseFailAlloc_1115_, 8, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1115_, 9, v_dAssignment_1102_);
v___x_1108_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1108_);
v___x_1110_ = v___x_1091_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_cache_1086_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_zetaDeltaFVarIds_1087_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_postponed_1088_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_diag_1089_);
v___x_1110_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = lean_st_ref_set(v___y_1082_, v___x_1110_);
v___x_1112_ = lean_box(0);
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
return v___x_1113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(lean_object* v_mvarId_1118_, lean_object* v_val_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1118_, v_val_1119_, v___y_1120_);
lean_dec(v___y_1120_);
return v_res_1122_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(lean_object* v_x1_1123_, lean_object* v_x2_1124_){
_start:
{
lean_object* v_fst_1125_; lean_object* v_fst_1126_; uint8_t v___x_1127_; 
v_fst_1125_ = lean_ctor_get(v_x1_1123_, 0);
v_fst_1126_ = lean_ctor_get(v_x2_1124_, 0);
v___x_1127_ = lean_nat_dec_lt(v_fst_1125_, v_fst_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0___boxed(lean_object* v_x1_1128_, lean_object* v_x2_1129_){
_start:
{
uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v_x1_1128_, v_x2_1129_);
lean_dec_ref(v_x2_1129_);
lean_dec_ref(v_x1_1128_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(lean_object* v_hi_1132_, lean_object* v_pivot_1133_, lean_object* v_as_1134_, lean_object* v_i_1135_, lean_object* v_k_1136_){
_start:
{
uint8_t v___x_1137_; 
v___x_1137_ = lean_nat_dec_lt(v_k_1136_, v_hi_1132_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v_k_1136_);
v___x_1138_ = lean_array_fswap(v_as_1134_, v_i_1135_, v_hi_1132_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_i_1135_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; lean_object* v_fst_1141_; lean_object* v_fst_1142_; uint8_t v___x_1143_; 
v___x_1140_ = lean_array_fget_borrowed(v_as_1134_, v_k_1136_);
v_fst_1141_ = lean_ctor_get(v___x_1140_, 0);
v_fst_1142_ = lean_ctor_get(v_pivot_1133_, 0);
v___x_1143_ = lean_nat_dec_lt(v_fst_1141_, v_fst_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = lean_nat_add(v_k_1136_, v___x_1144_);
lean_dec(v_k_1136_);
v_k_1136_ = v___x_1145_;
goto _start;
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1147_ = lean_array_fswap(v_as_1134_, v_i_1135_, v_k_1136_);
v___x_1148_ = lean_unsigned_to_nat(1u);
v___x_1149_ = lean_nat_add(v_i_1135_, v___x_1148_);
lean_dec(v_i_1135_);
v___x_1150_ = lean_nat_add(v_k_1136_, v___x_1148_);
lean_dec(v_k_1136_);
v_as_1134_ = v___x_1147_;
v_i_1135_ = v___x_1149_;
v_k_1136_ = v___x_1150_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg___boxed(lean_object* v_hi_1152_, lean_object* v_pivot_1153_, lean_object* v_as_1154_, lean_object* v_i_1155_, lean_object* v_k_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1152_, v_pivot_1153_, v_as_1154_, v_i_1155_, v_k_1156_);
lean_dec_ref(v_pivot_1153_);
lean_dec(v_hi_1152_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(lean_object* v_n_1158_, lean_object* v_as_1159_, lean_object* v_lo_1160_, lean_object* v_hi_1161_){
_start:
{
lean_object* v___y_1163_; uint8_t v___x_1173_; 
v___x_1173_ = lean_nat_dec_lt(v_lo_1160_, v_hi_1161_);
if (v___x_1173_ == 0)
{
lean_dec(v_lo_1160_);
return v_as_1159_;
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v_mid_1176_; lean_object* v___y_1178_; lean_object* v___y_1184_; lean_object* v___x_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1174_ = lean_nat_add(v_lo_1160_, v_hi_1161_);
v___x_1175_ = lean_unsigned_to_nat(1u);
v_mid_1176_ = lean_nat_shiftr(v___x_1174_, v___x_1175_);
lean_dec(v___x_1174_);
v___x_1189_ = lean_array_fget_borrowed(v_as_1159_, v_mid_1176_);
v___x_1190_ = lean_array_fget_borrowed(v_as_1159_, v_lo_1160_);
v___x_1191_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1189_, v___x_1190_);
if (v___x_1191_ == 0)
{
v___y_1184_ = v_as_1159_;
goto v___jp_1183_;
}
else
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_array_fswap(v_as_1159_, v_lo_1160_, v_mid_1176_);
v___y_1184_ = v___x_1192_;
goto v___jp_1183_;
}
v___jp_1177_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1179_ = lean_array_fget_borrowed(v___y_1178_, v_mid_1176_);
v___x_1180_ = lean_array_fget_borrowed(v___y_1178_, v_hi_1161_);
v___x_1181_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_dec(v_mid_1176_);
v___y_1163_ = v___y_1178_;
goto v___jp_1162_;
}
else
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_array_fswap(v___y_1178_, v_mid_1176_, v_hi_1161_);
lean_dec(v_mid_1176_);
v___y_1163_ = v___x_1182_;
goto v___jp_1162_;
}
}
v___jp_1183_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1185_ = lean_array_fget_borrowed(v___y_1184_, v_hi_1161_);
v___x_1186_ = lean_array_fget_borrowed(v___y_1184_, v_lo_1160_);
v___x_1187_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1185_, v___x_1186_);
if (v___x_1187_ == 0)
{
v___y_1178_ = v___y_1184_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_array_fswap(v___y_1184_, v_lo_1160_, v_hi_1161_);
v___y_1178_ = v___x_1188_;
goto v___jp_1177_;
}
}
}
v___jp_1162_:
{
lean_object* v_pivot_1164_; lean_object* v___x_1165_; lean_object* v_fst_1166_; lean_object* v_snd_1167_; uint8_t v___x_1168_; 
v_pivot_1164_ = lean_array_fget(v___y_1163_, v_hi_1161_);
lean_inc_n(v_lo_1160_, 2);
v___x_1165_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1161_, v_pivot_1164_, v___y_1163_, v_lo_1160_, v_lo_1160_);
lean_dec(v_pivot_1164_);
v_fst_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_fst_1166_);
v_snd_1167_ = lean_ctor_get(v___x_1165_, 1);
lean_inc(v_snd_1167_);
lean_dec_ref(v___x_1165_);
v___x_1168_ = lean_nat_dec_le(v_hi_1161_, v_fst_1166_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1158_, v_snd_1167_, v_lo_1160_, v_fst_1166_);
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = lean_nat_add(v_fst_1166_, v___x_1170_);
lean_dec(v_fst_1166_);
v_as_1159_ = v___x_1169_;
v_lo_1160_ = v___x_1171_;
goto _start;
}
else
{
lean_dec(v_fst_1166_);
lean_dec(v_lo_1160_);
return v_snd_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___boxed(lean_object* v_n_1193_, lean_object* v_as_1194_, lean_object* v_lo_1195_, lean_object* v_hi_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1193_, v_as_1194_, v_lo_1195_, v_hi_1196_);
lean_dec(v_hi_1196_);
lean_dec(v_n_1193_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(lean_object* v_ref_1198_, lean_object* v_msg_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_fileName_1209_; lean_object* v_fileMap_1210_; lean_object* v_options_1211_; lean_object* v_currRecDepth_1212_; lean_object* v_maxRecDepth_1213_; lean_object* v_ref_1214_; lean_object* v_currNamespace_1215_; lean_object* v_openDecls_1216_; lean_object* v_initHeartbeats_1217_; lean_object* v_maxHeartbeats_1218_; lean_object* v_quotContext_1219_; lean_object* v_currMacroScope_1220_; uint8_t v_diag_1221_; lean_object* v_cancelTk_x3f_1222_; uint8_t v_suppressElabErrors_1223_; lean_object* v_inheritedTraceOptions_1224_; lean_object* v_ref_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_fileName_1209_ = lean_ctor_get(v___y_1206_, 0);
v_fileMap_1210_ = lean_ctor_get(v___y_1206_, 1);
v_options_1211_ = lean_ctor_get(v___y_1206_, 2);
v_currRecDepth_1212_ = lean_ctor_get(v___y_1206_, 3);
v_maxRecDepth_1213_ = lean_ctor_get(v___y_1206_, 4);
v_ref_1214_ = lean_ctor_get(v___y_1206_, 5);
v_currNamespace_1215_ = lean_ctor_get(v___y_1206_, 6);
v_openDecls_1216_ = lean_ctor_get(v___y_1206_, 7);
v_initHeartbeats_1217_ = lean_ctor_get(v___y_1206_, 8);
v_maxHeartbeats_1218_ = lean_ctor_get(v___y_1206_, 9);
v_quotContext_1219_ = lean_ctor_get(v___y_1206_, 10);
v_currMacroScope_1220_ = lean_ctor_get(v___y_1206_, 11);
v_diag_1221_ = lean_ctor_get_uint8(v___y_1206_, sizeof(void*)*14);
v_cancelTk_x3f_1222_ = lean_ctor_get(v___y_1206_, 12);
v_suppressElabErrors_1223_ = lean_ctor_get_uint8(v___y_1206_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1224_ = lean_ctor_get(v___y_1206_, 13);
v_ref_1225_ = l_Lean_replaceRef(v_ref_1198_, v_ref_1214_);
lean_inc_ref(v_inheritedTraceOptions_1224_);
lean_inc(v_cancelTk_x3f_1222_);
lean_inc(v_currMacroScope_1220_);
lean_inc(v_quotContext_1219_);
lean_inc(v_maxHeartbeats_1218_);
lean_inc(v_initHeartbeats_1217_);
lean_inc(v_openDecls_1216_);
lean_inc(v_currNamespace_1215_);
lean_inc(v_maxRecDepth_1213_);
lean_inc(v_currRecDepth_1212_);
lean_inc_ref(v_options_1211_);
lean_inc_ref(v_fileMap_1210_);
lean_inc_ref(v_fileName_1209_);
v___x_1226_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1226_, 0, v_fileName_1209_);
lean_ctor_set(v___x_1226_, 1, v_fileMap_1210_);
lean_ctor_set(v___x_1226_, 2, v_options_1211_);
lean_ctor_set(v___x_1226_, 3, v_currRecDepth_1212_);
lean_ctor_set(v___x_1226_, 4, v_maxRecDepth_1213_);
lean_ctor_set(v___x_1226_, 5, v_ref_1225_);
lean_ctor_set(v___x_1226_, 6, v_currNamespace_1215_);
lean_ctor_set(v___x_1226_, 7, v_openDecls_1216_);
lean_ctor_set(v___x_1226_, 8, v_initHeartbeats_1217_);
lean_ctor_set(v___x_1226_, 9, v_maxHeartbeats_1218_);
lean_ctor_set(v___x_1226_, 10, v_quotContext_1219_);
lean_ctor_set(v___x_1226_, 11, v_currMacroScope_1220_);
lean_ctor_set(v___x_1226_, 12, v_cancelTk_x3f_1222_);
lean_ctor_set(v___x_1226_, 13, v_inheritedTraceOptions_1224_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*14, v_diag_1221_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*14 + 1, v_suppressElabErrors_1223_);
v___x_1227_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_1199_, v___y_1204_, v___y_1205_, v___x_1226_, v___y_1207_);
lean_dec_ref(v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(lean_object* v_ref_1228_, lean_object* v_msg_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_ref_1228_, v_msg_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v_ref_1228_);
return v_res_1239_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0));
v___x_1242_ = l_Lean_stringToMessageData(v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(lean_object* v_as_1243_, lean_object* v_i_1244_, lean_object* v_j_1245_, lean_object* v_bs_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_zero_1256_; uint8_t v_isZero_1257_; 
v_zero_1256_ = lean_unsigned_to_nat(0u);
v_isZero_1257_ = lean_nat_dec_eq(v_i_1244_, v_zero_1256_);
if (v_isZero_1257_ == 1)
{
lean_object* v___x_1258_; 
lean_dec(v_j_1245_);
lean_dec(v_i_1244_);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_bs_1246_);
return v___x_1258_;
}
else
{
lean_object* v_one_1259_; lean_object* v_n_1260_; lean_object* v_a_1262_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v_isZero_1268_; 
v_one_1259_ = lean_unsigned_to_nat(1u);
v_n_1260_ = lean_nat_sub(v_i_1244_, v_one_1259_);
lean_dec(v_i_1244_);
v___x_1266_ = lean_array_fget_borrowed(v_as_1243_, v_j_1245_);
v___x_1267_ = l_Lean_TSyntax_getNat(v___x_1266_);
v_isZero_1268_ = lean_nat_dec_eq(v___x_1267_, v_zero_1256_);
if (v_isZero_1268_ == 1)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec(v___x_1267_);
lean_dec(v_n_1260_);
lean_dec_ref(v_bs_1246_);
lean_dec(v_j_1245_);
v___x_1269_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1);
v___x_1270_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v___x_1266_, v___x_1269_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_object* v_n_1279_; lean_object* v___x_1280_; 
v_n_1279_ = lean_nat_sub(v___x_1267_, v_one_1259_);
lean_dec(v___x_1267_);
lean_inc(v_j_1245_);
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_n_1279_);
lean_ctor_set(v___x_1280_, 1, v_j_1245_);
v_a_1262_ = v___x_1280_;
goto v___jp_1261_;
}
v___jp_1261_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_nat_add(v_j_1245_, v_one_1259_);
lean_dec(v_j_1245_);
v___x_1264_ = lean_array_push(v_bs_1246_, v_a_1262_);
v_i_1244_ = v_n_1260_;
v_j_1245_ = v___x_1263_;
v_bs_1246_ = v___x_1264_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(lean_object* v_as_1281_, lean_object* v_i_1282_, lean_object* v_j_1283_, lean_object* v_bs_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_as_1281_, v_i_1282_, v_j_1283_, v_bs_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec_ref(v_as_1281_);
return v_res_1294_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(lean_object* v_as_1295_, lean_object* v_a_1296_, lean_object* v_x_1297_){
_start:
{
lean_object* v_zero_1298_; uint8_t v_isZero_1299_; 
v_zero_1298_ = lean_unsigned_to_nat(0u);
v_isZero_1299_ = lean_nat_dec_eq(v_x_1297_, v_zero_1298_);
if (v_isZero_1299_ == 1)
{
lean_dec(v_x_1297_);
return v_isZero_1299_;
}
else
{
lean_object* v_fst_1300_; lean_object* v_one_1301_; lean_object* v_n_1302_; lean_object* v___x_1303_; lean_object* v_fst_1304_; uint8_t v___x_1305_; 
v_fst_1300_ = lean_ctor_get(v_a_1296_, 0);
v_one_1301_ = lean_unsigned_to_nat(1u);
v_n_1302_ = lean_nat_sub(v_x_1297_, v_one_1301_);
lean_dec(v_x_1297_);
v___x_1303_ = lean_array_fget_borrowed(v_as_1295_, v_n_1302_);
v_fst_1304_ = lean_ctor_get(v___x_1303_, 0);
v___x_1305_ = lean_nat_dec_eq(v_fst_1300_, v_fst_1304_);
if (v___x_1305_ == 0)
{
v_x_1297_ = v_n_1302_;
goto _start;
}
else
{
lean_dec(v_n_1302_);
return v_isZero_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg___boxed(lean_object* v_as_1307_, lean_object* v_a_1308_, lean_object* v_x_1309_){
_start:
{
uint8_t v_res_1310_; lean_object* v_r_1311_; 
v_res_1310_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1307_, v_a_1308_, v_x_1309_);
lean_dec_ref(v_a_1308_);
lean_dec_ref(v_as_1307_);
v_r_1311_ = lean_box(v_res_1310_);
return v_r_1311_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(lean_object* v_as_1312_, lean_object* v_i_1313_){
_start:
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = lean_array_get_size(v_as_1312_);
v___x_1315_ = lean_nat_dec_lt(v_i_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
uint8_t v___x_1316_; 
lean_dec(v_i_1313_);
v___x_1316_ = 1;
return v___x_1316_;
}
else
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = lean_array_fget_borrowed(v_as_1312_, v_i_1313_);
lean_inc(v_i_1313_);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1312_, v___x_1317_, v_i_1313_);
if (v___x_1318_ == 0)
{
lean_dec(v_i_1313_);
return v___x_1318_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1320_ = lean_nat_add(v_i_1313_, v___x_1319_);
lean_dec(v_i_1313_);
v_i_1313_ = v___x_1320_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11___boxed(lean_object* v_as_1322_, lean_object* v_i_1323_){
_start:
{
uint8_t v_res_1324_; lean_object* v_r_1325_; 
v_res_1324_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1322_, v_i_1323_);
lean_dec_ref(v_as_1322_);
v_r_1325_ = lean_box(v_res_1324_);
return v_r_1325_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(lean_object* v_as_1326_){
_start:
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1326_, v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8___boxed(lean_object* v_as_1329_){
_start:
{
uint8_t v_res_1330_; lean_object* v_r_1331_; 
v_res_1330_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v_as_1329_);
lean_dec_ref(v_as_1329_);
v_r_1331_ = lean_box(v_res_1330_);
return v_r_1331_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1332_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = lean_unsigned_to_nat(0u);
v___x_1336_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v___x_1335_);
return v___x_1337_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = lean_unsigned_to_nat(32u);
v___x_1339_ = lean_mk_empty_array_with_capacity(v___x_1338_);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4(void){
_start:
{
size_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1341_ = ((size_t)5ULL);
v___x_1342_ = lean_unsigned_to_nat(0u);
v___x_1343_ = lean_unsigned_to_nat(32u);
v___x_1344_ = lean_mk_empty_array_with_capacity(v___x_1343_);
v___x_1345_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3);
v___x_1346_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v___x_1344_);
lean_ctor_set(v___x_1346_, 2, v___x_1342_);
lean_ctor_set(v___x_1346_, 3, v___x_1342_);
lean_ctor_set_usize(v___x_1346_, 4, v___x_1341_);
return v___x_1346_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4);
v___x_1348_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
lean_ctor_set(v___x_1349_, 2, v___x_1348_);
lean_ctor_set(v___x_1349_, 3, v___x_1347_);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5);
v___x_1351_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set(v___x_1352_, 1, v___x_1350_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7));
v___x_1355_ = l_Lean_stringToMessageData(v___x_1354_);
return v___x_1355_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9));
v___x_1358_ = l_Lean_stringToMessageData(v___x_1357_);
return v___x_1358_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11));
v___x_1361_ = l_Lean_stringToMessageData(v___x_1360_);
return v___x_1361_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13));
v___x_1364_ = l_Lean_stringToMessageData(v___x_1363_);
return v___x_1364_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16));
v___x_1369_ = l_Lean_stringToMessageData(v___x_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(uint8_t v___x_1390_, lean_object* v___f_1391_, uint8_t v___x_1392_, lean_object* v_stx_1393_, lean_object* v___x_1394_, lean_object* v___x_1395_, lean_object* v___x_1396_, lean_object* v___x_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___y_1408_; lean_object* v_subgoals_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; 
if (v___x_1390_ == 0)
{
lean_object* v___x_1498_; 
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___f_1391_);
v___x_1498_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1498_;
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; uint8_t v___y_1532_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v_occs_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v_occs_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = lean_unsigned_to_nat(1u);
v___x_1821_ = l_Lean_Syntax_getArg(v_stx_1393_, v___x_1500_);
v___x_1822_ = l_Lean_Syntax_isNone(v___x_1821_);
if (v___x_1822_ == 0)
{
uint8_t v___x_1823_; 
lean_inc(v___x_1821_);
v___x_1823_ = l_Lean_Syntax_matchesNull(v___x_1821_, v___x_1500_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
lean_dec(v___x_1821_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___f_1391_);
v___x_1824_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1825_ = l_Lean_Syntax_getArg(v___x_1821_, v___x_1499_);
lean_dec(v___x_1821_);
v___x_1826_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27));
lean_inc_ref(v___x_1397_);
lean_inc_ref(v___x_1396_);
lean_inc_ref(v___x_1395_);
lean_inc_ref(v___x_1394_);
v___x_1827_ = l_Lean_Name_mkStr5(v___x_1394_, v___x_1395_, v___x_1396_, v___x_1397_, v___x_1826_);
lean_inc(v___x_1825_);
v___x_1828_ = l_Lean_Syntax_isOfKind(v___x_1825_, v___x_1827_);
lean_dec(v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; 
lean_dec(v___x_1825_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___f_1391_);
v___x_1829_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1829_;
}
else
{
lean_object* v___x_1830_; lean_object* v_occs_1831_; lean_object* v___x_1832_; 
v___x_1830_ = lean_unsigned_to_nat(3u);
v_occs_1831_ = l_Lean_Syntax_getArg(v___x_1825_, v___x_1830_);
lean_dec(v___x_1825_);
v___x_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1832_, 0, v_occs_1831_);
v_occs_1727_ = v___x_1832_;
v___y_1728_ = v___y_1398_;
v___y_1729_ = v___y_1399_;
v___y_1730_ = v___y_1400_;
v___y_1731_ = v___y_1401_;
v___y_1732_ = v___y_1402_;
v___y_1733_ = v___y_1403_;
v___y_1734_ = v___y_1404_;
v___y_1735_ = v___y_1405_;
goto v___jp_1726_;
}
}
}
else
{
lean_object* v___x_1833_; 
lean_dec(v___x_1821_);
v___x_1833_ = lean_box(0);
v_occs_1727_ = v___x_1833_;
v___y_1728_ = v___y_1398_;
v___y_1729_ = v___y_1399_;
v___y_1730_ = v___y_1400_;
v___y_1731_ = v___y_1401_;
v___y_1732_ = v___y_1402_;
v___y_1733_ = v___y_1403_;
v___y_1734_ = v___y_1404_;
v___y_1735_ = v___y_1405_;
goto v___jp_1726_;
}
v___jp_1501_:
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = lean_array_get_size(v___y_1502_);
v___x_1513_ = lean_nat_dec_eq(v___x_1512_, v___x_1499_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = lean_nat_sub(v___x_1512_, v___x_1500_);
v___x_1515_ = lean_nat_dec_le(v___x_1499_, v___x_1514_);
if (v___x_1515_ == 0)
{
lean_inc(v___x_1514_);
v___y_1484_ = v___y_1502_;
v___y_1485_ = v___y_1503_;
v___y_1486_ = v___x_1514_;
v___y_1487_ = v___y_1508_;
v___y_1488_ = v___y_1506_;
v___y_1489_ = v___y_1511_;
v___y_1490_ = v___y_1504_;
v___y_1491_ = v___y_1510_;
v___y_1492_ = v___y_1509_;
v___y_1493_ = v___x_1512_;
v___y_1494_ = v___y_1507_;
v___y_1495_ = v___y_1505_;
v___y_1496_ = v___x_1514_;
goto v___jp_1483_;
}
else
{
v___y_1484_ = v___y_1502_;
v___y_1485_ = v___y_1503_;
v___y_1486_ = v___x_1514_;
v___y_1487_ = v___y_1508_;
v___y_1488_ = v___y_1506_;
v___y_1489_ = v___y_1511_;
v___y_1490_ = v___y_1504_;
v___y_1491_ = v___y_1510_;
v___y_1492_ = v___y_1509_;
v___y_1493_ = v___x_1512_;
v___y_1494_ = v___y_1507_;
v___y_1495_ = v___y_1505_;
v___y_1496_ = v___x_1499_;
goto v___jp_1483_;
}
}
else
{
v___y_1455_ = v___y_1510_;
v___y_1456_ = v___y_1503_;
v___y_1457_ = v___y_1509_;
v___y_1458_ = v___y_1508_;
v___y_1459_ = v___y_1507_;
v___y_1460_ = v___y_1506_;
v___y_1461_ = v___y_1505_;
v___y_1462_ = v___y_1511_;
v___y_1463_ = v___y_1504_;
v___y_1464_ = v___y_1502_;
goto v___jp_1454_;
}
}
v___jp_1516_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1533_ = l_Lean_Meta_Simp_Context_setMemoize(v___y_1517_, v___y_1532_);
v___x_1534_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6);
lean_inc(v___y_1524_);
lean_inc_ref(v___y_1528_);
v___x_1535_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed), 11, 2);
lean_closure_set(v___x_1535_, 0, v___y_1528_);
lean_closure_set(v___x_1535_, 1, v___y_1524_);
lean_inc_ref(v___y_1525_);
lean_inc_ref(v___y_1520_);
v___x_1536_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v___y_1526_);
lean_ctor_set(v___x_1536_, 2, v___y_1520_);
lean_ctor_set(v___x_1536_, 3, v___f_1391_);
lean_ctor_set(v___x_1536_, 4, v___y_1525_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*5, v___x_1392_);
v___x_1537_ = l_Lean_Meta_Simp_main(v___y_1522_, v___x_1533_, v___x_1534_, v___x_1536_, v___y_1527_, v___y_1518_, v___y_1529_, v___y_1531_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v_fst_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1614_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref(v___x_1537_);
v_fst_1539_ = lean_ctor_get(v_a_1538_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_a_1538_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; 
v_unused_1615_ = lean_ctor_get(v_a_1538_, 1);
lean_dec(v_unused_1615_);
v___x_1541_ = v_a_1538_;
v_isShared_1542_ = v_isSharedCheck_1614_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_fst_1539_);
lean_dec(v_a_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1614_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_st_ref_get(v___y_1524_);
lean_dec(v___y_1524_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_subgoals_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v_subgoals_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc_ref(v_subgoals_1544_);
lean_dec_ref(v___x_1543_);
v___x_1545_ = lean_array_get_size(v_subgoals_1544_);
v___x_1546_ = lean_nat_dec_eq(v___x_1545_, v___x_1499_);
if (v___x_1546_ == 0)
{
lean_del_object(v___x_1541_);
lean_dec_ref(v___y_1528_);
v___y_1408_ = v_fst_1539_;
v_subgoals_1409_ = v_subgoals_1544_;
v___y_1410_ = v___y_1519_;
v___y_1411_ = v___y_1523_;
v___y_1412_ = v___y_1521_;
v___y_1413_ = v___y_1530_;
v___y_1414_ = v___y_1527_;
v___y_1415_ = v___y_1518_;
v___y_1416_ = v___y_1529_;
v___y_1417_ = v___y_1531_;
goto v___jp_1407_;
}
else
{
lean_object* v_expr_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
lean_dec_ref(v_subgoals_1544_);
lean_dec(v_fst_1539_);
v_expr_1547_ = lean_ctor_get(v___y_1528_, 2);
lean_inc_ref(v_expr_1547_);
lean_dec_ref(v___y_1528_);
v___x_1548_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1549_ = l_Lean_indentExpr(v_expr_1547_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set_tag(v___x_1541_, 7);
lean_ctor_set(v___x_1541_, 1, v___x_1549_);
lean_ctor_set(v___x_1541_, 0, v___x_1548_);
v___x_1551_ = v___x_1541_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1552_; lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
v___x_1552_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1551_, v___y_1527_, v___y_1518_, v___y_1529_, v___y_1531_);
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
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
}
else
{
lean_object* v_subgoals_1562_; lean_object* v_idx_1563_; lean_object* v_remaining_1564_; uint8_t v___x_1565_; 
v_subgoals_1562_ = lean_ctor_get(v___x_1543_, 0);
lean_inc_ref(v_subgoals_1562_);
v_idx_1563_ = lean_ctor_get(v___x_1543_, 1);
lean_inc(v_idx_1563_);
v_remaining_1564_ = lean_ctor_get(v___x_1543_, 2);
lean_inc(v_remaining_1564_);
lean_dec_ref(v___x_1543_);
v___x_1565_ = lean_nat_dec_eq(v_idx_1563_, v___x_1499_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; 
lean_dec_ref(v___y_1528_);
v___x_1566_ = l_List_getLast_x3f___redArg(v_remaining_1564_);
lean_dec(v_remaining_1564_);
if (lean_obj_tag(v___x_1566_) == 1)
{
lean_object* v_val_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1598_; 
lean_dec_ref(v_subgoals_1562_);
lean_dec(v_fst_1539_);
v_val_1567_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1598_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_val_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1598_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v_fst_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1596_; 
v_fst_1571_ = lean_ctor_get(v_val_1567_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_val_1567_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; 
v_unused_1597_ = lean_ctor_get(v_val_1567_, 1);
lean_dec(v_unused_1597_);
v___x_1573_ = v_val_1567_;
v_isShared_1574_ = v_isSharedCheck_1596_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_fst_1571_);
lean_dec(v_val_1567_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1596_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1575_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10);
v___x_1576_ = l_Nat_reprFast(v_idx_1563_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set_tag(v___x_1569_, 3);
lean_ctor_set(v___x_1569_, 0, v___x_1576_);
v___x_1578_ = v___x_1569_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = l_Lean_MessageData_ofFormat(v___x_1578_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 7);
lean_ctor_set(v___x_1573_, 1, v___x_1579_);
lean_ctor_set(v___x_1573_, 0, v___x_1575_);
v___x_1581_ = v___x_1573_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1575_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1582_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12);
if (v_isShared_1542_ == 0)
{
lean_ctor_set_tag(v___x_1541_, 7);
lean_ctor_set(v___x_1541_, 1, v___x_1582_);
lean_ctor_set(v___x_1541_, 0, v___x_1581_);
v___x_1584_ = v___x_1541_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1585_ = lean_nat_add(v_fst_1571_, v___x_1500_);
lean_dec(v_fst_1571_);
v___x_1586_ = l_Nat_reprFast(v___x_1585_);
v___x_1587_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
v___x_1588_ = l_Lean_MessageData_ofFormat(v___x_1587_);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1584_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1591_, v___y_1527_, v___y_1518_, v___y_1529_, v___y_1531_);
return v___x_1592_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1566_);
lean_dec(v_idx_1563_);
lean_del_object(v___x_1541_);
v___y_1502_ = v_subgoals_1562_;
v___y_1503_ = v_fst_1539_;
v___y_1504_ = v___y_1519_;
v___y_1505_ = v___y_1523_;
v___y_1506_ = v___y_1521_;
v___y_1507_ = v___y_1530_;
v___y_1508_ = v___y_1527_;
v___y_1509_ = v___y_1518_;
v___y_1510_ = v___y_1529_;
v___y_1511_ = v___y_1531_;
goto v___jp_1501_;
}
}
else
{
lean_object* v_expr_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; 
lean_dec(v_remaining_1564_);
lean_dec(v_idx_1563_);
lean_dec_ref(v_subgoals_1562_);
lean_dec(v_fst_1539_);
v_expr_1599_ = lean_ctor_get(v___y_1528_, 2);
lean_inc_ref(v_expr_1599_);
lean_dec_ref(v___y_1528_);
v___x_1600_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1601_ = l_Lean_indentExpr(v_expr_1599_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set_tag(v___x_1541_, 7);
lean_ctor_set(v___x_1541_, 1, v___x_1601_);
lean_ctor_set(v___x_1541_, 0, v___x_1600_);
v___x_1603_ = v___x_1541_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v___x_1604_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1603_, v___y_1527_, v___y_1518_, v___y_1529_, v___y_1531_);
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1524_);
v_a_1616_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1537_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1537_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
v___jp_1624_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_inc_ref(v_occs_1630_);
v___x_1639_ = lean_st_mk_ref(v_occs_1630_);
v___x_1640_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v___y_1635_, v___y_1637_, v___y_1638_);
if (lean_obj_tag(v___x_1640_) == 0)
{
if (lean_obj_tag(v_occs_1630_) == 0)
{
lean_object* v_a_1641_; 
lean_dec_ref(v_occs_1630_);
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref(v___x_1640_);
v___y_1517_ = v_a_1641_;
v___y_1518_ = v___y_1636_;
v___y_1519_ = v___y_1631_;
v___y_1520_ = v___y_1625_;
v___y_1521_ = v___y_1633_;
v___y_1522_ = v___y_1626_;
v___y_1523_ = v___y_1632_;
v___y_1524_ = v___x_1639_;
v___y_1525_ = v___y_1627_;
v___y_1526_ = v___y_1628_;
v___y_1527_ = v___y_1635_;
v___y_1528_ = v___y_1629_;
v___y_1529_ = v___y_1637_;
v___y_1530_ = v___y_1634_;
v___y_1531_ = v___y_1638_;
v___y_1532_ = v___x_1392_;
goto v___jp_1516_;
}
else
{
lean_object* v_a_1642_; uint8_t v___x_1643_; 
lean_dec_ref(v_occs_1630_);
v_a_1642_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1642_);
lean_dec_ref(v___x_1640_);
v___x_1643_ = 0;
v___y_1517_ = v_a_1642_;
v___y_1518_ = v___y_1636_;
v___y_1519_ = v___y_1631_;
v___y_1520_ = v___y_1625_;
v___y_1521_ = v___y_1633_;
v___y_1522_ = v___y_1626_;
v___y_1523_ = v___y_1632_;
v___y_1524_ = v___x_1639_;
v___y_1525_ = v___y_1627_;
v___y_1526_ = v___y_1628_;
v___y_1527_ = v___y_1635_;
v___y_1528_ = v___y_1629_;
v___y_1529_ = v___y_1637_;
v___y_1530_ = v___y_1634_;
v___y_1531_ = v___y_1638_;
v___y_1532_ = v___x_1643_;
goto v___jp_1516_;
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v___x_1639_);
lean_dec_ref(v_occs_1630_);
lean_dec_ref(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v___y_1626_);
lean_dec_ref(v___f_1391_);
v_a_1644_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1640_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1640_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
v___jp_1652_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15));
v___x_1668_ = lean_array_to_list(v___y_1656_);
v___x_1669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1499_);
lean_ctor_set(v___x_1669_, 2, v___x_1668_);
v___y_1625_ = v___y_1653_;
v___y_1626_ = v___y_1654_;
v___y_1627_ = v___y_1655_;
v___y_1628_ = v___y_1657_;
v___y_1629_ = v___y_1658_;
v_occs_1630_ = v___x_1669_;
v___y_1631_ = v___y_1659_;
v___y_1632_ = v___y_1660_;
v___y_1633_ = v___y_1661_;
v___y_1634_ = v___y_1662_;
v___y_1635_ = v___y_1663_;
v___y_1636_ = v___y_1664_;
v___y_1637_ = v___y_1665_;
v___y_1638_ = v___y_1666_;
goto v___jp_1624_;
}
v___jp_1670_:
{
uint8_t v___x_1685_; 
v___x_1685_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v___y_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec_ref(v___y_1684_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec_ref(v___y_1675_);
lean_dec_ref(v___f_1391_);
v___x_1686_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17);
v___x_1687_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1686_, v___y_1671_, v___y_1683_, v___y_1678_, v___y_1682_);
return v___x_1687_;
}
else
{
v___y_1653_ = v___y_1673_;
v___y_1654_ = v___y_1675_;
v___y_1655_ = v___y_1677_;
v___y_1656_ = v___y_1684_;
v___y_1657_ = v___y_1679_;
v___y_1658_ = v___y_1680_;
v___y_1659_ = v___y_1681_;
v___y_1660_ = v___y_1674_;
v___y_1661_ = v___y_1672_;
v___y_1662_ = v___y_1676_;
v___y_1663_ = v___y_1671_;
v___y_1664_ = v___y_1683_;
v___y_1665_ = v___y_1678_;
v___y_1666_ = v___y_1682_;
goto v___jp_1652_;
}
}
v___jp_1688_:
{
lean_object* v___x_1706_; 
v___x_1706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v___y_1691_, v___y_1690_, v___y_1693_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec(v___y_1691_);
v___y_1671_ = v___y_1689_;
v___y_1672_ = v___y_1692_;
v___y_1673_ = v___y_1694_;
v___y_1674_ = v___y_1695_;
v___y_1675_ = v___y_1696_;
v___y_1676_ = v___y_1697_;
v___y_1677_ = v___y_1698_;
v___y_1678_ = v___y_1699_;
v___y_1679_ = v___y_1700_;
v___y_1680_ = v___y_1702_;
v___y_1681_ = v___y_1701_;
v___y_1682_ = v___y_1703_;
v___y_1683_ = v___y_1704_;
v___y_1684_ = v___x_1706_;
goto v___jp_1670_;
}
v___jp_1707_:
{
uint8_t v___x_1725_; 
v___x_1725_ = lean_nat_dec_le(v___y_1724_, v___y_1711_);
if (v___x_1725_ == 0)
{
lean_dec(v___y_1711_);
lean_inc(v___y_1724_);
v___y_1689_ = v___y_1708_;
v___y_1690_ = v___y_1709_;
v___y_1691_ = v___y_1710_;
v___y_1692_ = v___y_1712_;
v___y_1693_ = v___y_1724_;
v___y_1694_ = v___y_1713_;
v___y_1695_ = v___y_1714_;
v___y_1696_ = v___y_1715_;
v___y_1697_ = v___y_1716_;
v___y_1698_ = v___y_1717_;
v___y_1699_ = v___y_1718_;
v___y_1700_ = v___y_1719_;
v___y_1701_ = v___y_1721_;
v___y_1702_ = v___y_1720_;
v___y_1703_ = v___y_1722_;
v___y_1704_ = v___y_1723_;
v___y_1705_ = v___y_1724_;
goto v___jp_1688_;
}
else
{
v___y_1689_ = v___y_1708_;
v___y_1690_ = v___y_1709_;
v___y_1691_ = v___y_1710_;
v___y_1692_ = v___y_1712_;
v___y_1693_ = v___y_1724_;
v___y_1694_ = v___y_1713_;
v___y_1695_ = v___y_1714_;
v___y_1696_ = v___y_1715_;
v___y_1697_ = v___y_1716_;
v___y_1698_ = v___y_1717_;
v___y_1699_ = v___y_1718_;
v___y_1700_ = v___y_1719_;
v___y_1701_ = v___y_1721_;
v___y_1702_ = v___y_1720_;
v___y_1703_ = v___y_1722_;
v___y_1704_ = v___y_1723_;
v___y_1705_ = v___y_1711_;
goto v___jp_1688_;
}
}
v___jp_1726_:
{
lean_object* v_declName_x3f_1736_; lean_object* v_macroStack_1737_; uint8_t v_mayPostpone_1738_; uint8_t v_errToSorry_1739_; lean_object* v_autoBoundImplicitContext_1740_; lean_object* v_autoBoundImplicitForbidden_1741_; lean_object* v_sectionVars_1742_; lean_object* v_sectionFVars_1743_; uint8_t v_implicitLambda_1744_; uint8_t v_heedElabAsElim_1745_; uint8_t v_isNoncomputableSection_1746_; uint8_t v_isMetaSection_1747_; uint8_t v_inPattern_1748_; lean_object* v_tacSnap_x3f_1749_; uint8_t v_saveRecAppSyntax_1750_; uint8_t v_holesAsSyntheticOpaque_1751_; uint8_t v_checkDeprecated_1752_; lean_object* v_fixedTermElabs_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___f_1758_; lean_object* v___f_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_declName_x3f_1736_ = lean_ctor_get(v___y_1730_, 0);
v_macroStack_1737_ = lean_ctor_get(v___y_1730_, 1);
v_mayPostpone_1738_ = lean_ctor_get_uint8(v___y_1730_, sizeof(void*)*8);
v_errToSorry_1739_ = lean_ctor_get_uint8(v___y_1730_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1740_ = lean_ctor_get(v___y_1730_, 2);
v_autoBoundImplicitForbidden_1741_ = lean_ctor_get(v___y_1730_, 3);
v_sectionVars_1742_ = lean_ctor_get(v___y_1730_, 4);
v_sectionFVars_1743_ = lean_ctor_get(v___y_1730_, 5);
v_implicitLambda_1744_ = lean_ctor_get_uint8(v___y_1730_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1745_ = lean_ctor_get_uint8(v___y_1730_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1746_ = lean_ctor_get_uint8(v___y_1730_, sizeof(void*)*8 + 4);
v_isMetaSection_1747_ = lean_ctor_get_uint8(v___y_1730_, sizeof(void*)*8 + 5);
v_inPattern_1748_ = lean_ctor_get_uint8(v___y_1730_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1749_ = lean_ctor_get(v___y_1730_, 6);
v_saveRecAppSyntax_1750_ = lean_ctor_get_uint8(v___y_1730_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1751_ = lean_ctor_get_uint8(v___y_1730_, sizeof(void*)*8 + 9);
v_checkDeprecated_1752_ = lean_ctor_get_uint8(v___y_1730_, sizeof(void*)*8 + 10);
v_fixedTermElabs_1753_ = lean_ctor_get(v___y_1730_, 7);
v___x_1754_ = lean_unsigned_to_nat(2u);
v___x_1755_ = l_Lean_Syntax_getArg(v_stx_1393_, v___x_1754_);
v___x_1756_ = lean_box(0);
v___x_1757_ = lean_box(v___x_1392_);
lean_inc(v___x_1755_);
v___f_1758_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1758_, 0, v___x_1755_);
lean_closure_set(v___f_1758_, 1, v___x_1756_);
lean_closure_set(v___f_1758_, 2, v___x_1757_);
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed), 9, 2);
lean_closure_set(v___f_1759_, 0, v___x_1755_);
lean_closure_set(v___f_1759_, 1, v___f_1758_);
lean_inc_ref(v_fixedTermElabs_1753_);
lean_inc(v_tacSnap_x3f_1749_);
lean_inc(v_sectionFVars_1743_);
lean_inc(v_sectionVars_1742_);
lean_inc_ref(v_autoBoundImplicitForbidden_1741_);
lean_inc(v_autoBoundImplicitContext_1740_);
lean_inc(v_macroStack_1737_);
lean_inc(v_declName_x3f_1736_);
v___x_1760_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1760_, 0, v_declName_x3f_1736_);
lean_ctor_set(v___x_1760_, 1, v_macroStack_1737_);
lean_ctor_set(v___x_1760_, 2, v_autoBoundImplicitContext_1740_);
lean_ctor_set(v___x_1760_, 3, v_autoBoundImplicitForbidden_1741_);
lean_ctor_set(v___x_1760_, 4, v_sectionVars_1742_);
lean_ctor_set(v___x_1760_, 5, v_sectionFVars_1743_);
lean_ctor_set(v___x_1760_, 6, v_tacSnap_x3f_1749_);
lean_ctor_set(v___x_1760_, 7, v_fixedTermElabs_1753_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*8, v_mayPostpone_1738_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*8 + 1, v_errToSorry_1739_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*8 + 2, v_implicitLambda_1744_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*8 + 3, v_heedElabAsElim_1745_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1746_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*8 + 5, v_isMetaSection_1747_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*8 + 6, v___x_1392_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*8 + 7, v_inPattern_1748_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1750_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_1751_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*8 + 10, v_checkDeprecated_1752_);
v___x_1761_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_1759_, v___x_1760_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec_ref(v___x_1760_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1729_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; lean_object* v___f_1766_; lean_object* v___f_1767_; lean_object* v___f_1768_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref(v___x_1763_);
v___x_1765_ = lean_box(v___x_1392_);
v___f_1766_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed), 11, 2);
lean_closure_set(v___f_1766_, 0, v___x_1756_);
lean_closure_set(v___f_1766_, 1, v___x_1765_);
v___f_1767_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18));
v___f_1768_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19));
if (lean_obj_tag(v_occs_1727_) == 0)
{
lean_object* v___x_1769_; 
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1394_);
v___x_1769_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22));
v___y_1625_ = v___f_1767_;
v___y_1626_ = v_a_1764_;
v___y_1627_ = v___f_1768_;
v___y_1628_ = v___f_1766_;
v___y_1629_ = v_a_1762_;
v_occs_1630_ = v___x_1769_;
v___y_1631_ = v___y_1728_;
v___y_1632_ = v___y_1729_;
v___y_1633_ = v___y_1730_;
v___y_1634_ = v___y_1731_;
v___y_1635_ = v___y_1732_;
v___y_1636_ = v___y_1733_;
v___y_1637_ = v___y_1734_;
v___y_1638_ = v___y_1735_;
goto v___jp_1624_;
}
else
{
lean_object* v_val_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_val_1770_ = lean_ctor_get(v_occs_1727_, 0);
lean_inc_n(v_val_1770_, 2);
lean_dec_ref(v_occs_1727_);
v___x_1771_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23));
lean_inc_ref(v___x_1397_);
lean_inc_ref(v___x_1396_);
lean_inc_ref(v___x_1395_);
lean_inc_ref(v___x_1394_);
v___x_1772_ = l_Lean_Name_mkStr5(v___x_1394_, v___x_1395_, v___x_1396_, v___x_1397_, v___x_1771_);
v___x_1773_ = l_Lean_Syntax_isOfKind(v_val_1770_, v___x_1772_);
lean_dec(v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1774_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24));
v___x_1775_ = l_Lean_Name_mkStr5(v___x_1394_, v___x_1395_, v___x_1396_, v___x_1397_, v___x_1774_);
lean_inc(v_val_1770_);
v___x_1776_ = l_Lean_Syntax_isOfKind(v_val_1770_, v___x_1775_);
lean_dec(v___x_1775_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec(v_val_1770_);
lean_dec_ref(v___f_1766_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
lean_dec_ref(v___f_1391_);
v___x_1777_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1786_ = l_Lean_Syntax_getArg(v_val_1770_, v___x_1499_);
lean_dec(v_val_1770_);
v___x_1787_ = l_Lean_Syntax_getArgs(v___x_1786_);
lean_dec(v___x_1786_);
v___x_1788_ = lean_array_get_size(v___x_1787_);
v___x_1789_ = lean_mk_empty_array_with_capacity(v___x_1788_);
v___x_1790_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v___x_1787_, v___x_1788_, v___x_1499_, v___x_1789_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec_ref(v___x_1787_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref(v___x_1790_);
v___x_1792_ = lean_array_get_size(v_a_1791_);
v___x_1793_ = lean_nat_dec_eq(v___x_1792_, v___x_1499_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1794_ = lean_nat_sub(v___x_1792_, v___x_1500_);
v___x_1795_ = lean_nat_dec_le(v___x_1499_, v___x_1794_);
if (v___x_1795_ == 0)
{
lean_inc(v___x_1794_);
v___y_1708_ = v___y_1732_;
v___y_1709_ = v_a_1791_;
v___y_1710_ = v___x_1792_;
v___y_1711_ = v___x_1794_;
v___y_1712_ = v___y_1730_;
v___y_1713_ = v___f_1767_;
v___y_1714_ = v___y_1729_;
v___y_1715_ = v_a_1764_;
v___y_1716_ = v___y_1731_;
v___y_1717_ = v___f_1768_;
v___y_1718_ = v___y_1734_;
v___y_1719_ = v___f_1766_;
v___y_1720_ = v_a_1762_;
v___y_1721_ = v___y_1728_;
v___y_1722_ = v___y_1735_;
v___y_1723_ = v___y_1733_;
v___y_1724_ = v___x_1794_;
goto v___jp_1707_;
}
else
{
v___y_1708_ = v___y_1732_;
v___y_1709_ = v_a_1791_;
v___y_1710_ = v___x_1792_;
v___y_1711_ = v___x_1794_;
v___y_1712_ = v___y_1730_;
v___y_1713_ = v___f_1767_;
v___y_1714_ = v___y_1729_;
v___y_1715_ = v_a_1764_;
v___y_1716_ = v___y_1731_;
v___y_1717_ = v___f_1768_;
v___y_1718_ = v___y_1734_;
v___y_1719_ = v___f_1766_;
v___y_1720_ = v_a_1762_;
v___y_1721_ = v___y_1728_;
v___y_1722_ = v___y_1735_;
v___y_1723_ = v___y_1733_;
v___y_1724_ = v___x_1499_;
goto v___jp_1707_;
}
}
else
{
v___y_1671_ = v___y_1732_;
v___y_1672_ = v___y_1730_;
v___y_1673_ = v___f_1767_;
v___y_1674_ = v___y_1729_;
v___y_1675_ = v_a_1764_;
v___y_1676_ = v___y_1731_;
v___y_1677_ = v___f_1768_;
v___y_1678_ = v___y_1734_;
v___y_1679_ = v___f_1766_;
v___y_1680_ = v_a_1762_;
v___y_1681_ = v___y_1728_;
v___y_1682_ = v___y_1735_;
v___y_1683_ = v___y_1733_;
v___y_1684_ = v_a_1791_;
goto v___jp_1670_;
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref(v___f_1766_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
lean_dec_ref(v___f_1391_);
v_a_1796_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1790_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1790_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
else
{
lean_object* v___x_1804_; 
lean_dec(v_val_1770_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1394_);
v___x_1804_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26));
v___y_1625_ = v___f_1767_;
v___y_1626_ = v_a_1764_;
v___y_1627_ = v___f_1768_;
v___y_1628_ = v___f_1766_;
v___y_1629_ = v_a_1762_;
v_occs_1630_ = v___x_1804_;
v___y_1631_ = v___y_1728_;
v___y_1632_ = v___y_1729_;
v___y_1633_ = v___y_1730_;
v___y_1634_ = v___y_1731_;
v___y_1635_ = v___y_1732_;
v___y_1636_ = v___y_1733_;
v___y_1637_ = v___y_1734_;
v___y_1638_ = v___y_1735_;
goto v___jp_1624_;
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v_a_1762_);
lean_dec(v_occs_1727_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___f_1391_);
v_a_1805_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1763_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1763_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec(v_occs_1727_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___f_1391_);
v_a_1813_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1761_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1761_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
v___jp_1407_:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v___y_1411_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v_expr_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref(v___x_1418_);
v_expr_1420_ = lean_ctor_get(v___y_1408_, 0);
v___x_1421_ = l_Lean_Expr_mvarId_x21(v_a_1419_);
lean_dec(v_a_1419_);
lean_inc_ref(v_expr_1420_);
v___x_1422_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v___x_1421_, v_expr_1420_, v___y_1415_);
lean_dec_ref(v___x_1422_);
v___x_1423_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1411_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1425_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref(v___x_1423_);
v___x_1425_ = l_Lean_Meta_Simp_Result_getProof(v___y_1408_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_a_1424_, v_a_1426_, v___y_1415_);
lean_dec_ref(v___x_1427_);
v___x_1428_ = lean_array_to_list(v_subgoals_1409_);
v___x_1429_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1428_, v___y_1411_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
return v___x_1429_;
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec(v_a_1424_);
lean_dec_ref(v_subgoals_1409_);
v_a_1430_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1425_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1425_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v_subgoals_1409_);
lean_dec_ref(v___y_1408_);
v_a_1438_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1423_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1423_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec_ref(v_subgoals_1409_);
lean_dec_ref(v___y_1408_);
v_a_1446_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1418_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1418_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
v___jp_1454_:
{
size_t v_sz_1465_; size_t v___x_1466_; lean_object* v___x_1467_; 
v_sz_1465_ = lean_array_size(v___y_1464_);
v___x_1466_ = ((size_t)0ULL);
v___x_1467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_1465_, v___x_1466_, v___y_1464_);
v___y_1408_ = v___y_1456_;
v_subgoals_1409_ = v___x_1467_;
v___y_1410_ = v___y_1463_;
v___y_1411_ = v___y_1461_;
v___y_1412_ = v___y_1460_;
v___y_1413_ = v___y_1459_;
v___y_1414_ = v___y_1458_;
v___y_1415_ = v___y_1457_;
v___y_1416_ = v___y_1455_;
v___y_1417_ = v___y_1462_;
goto v___jp_1407_;
}
v___jp_1468_:
{
lean_object* v___x_1482_; 
v___x_1482_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v___y_1478_, v___y_1469_, v___y_1475_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec(v___y_1478_);
v___y_1455_ = v___y_1476_;
v___y_1456_ = v___y_1470_;
v___y_1457_ = v___y_1477_;
v___y_1458_ = v___y_1471_;
v___y_1459_ = v___y_1479_;
v___y_1460_ = v___y_1472_;
v___y_1461_ = v___y_1480_;
v___y_1462_ = v___y_1473_;
v___y_1463_ = v___y_1474_;
v___y_1464_ = v___x_1482_;
goto v___jp_1454_;
}
v___jp_1483_:
{
uint8_t v___x_1497_; 
v___x_1497_ = lean_nat_dec_le(v___y_1496_, v___y_1486_);
if (v___x_1497_ == 0)
{
lean_dec(v___y_1486_);
lean_inc(v___y_1496_);
v___y_1469_ = v___y_1484_;
v___y_1470_ = v___y_1485_;
v___y_1471_ = v___y_1487_;
v___y_1472_ = v___y_1488_;
v___y_1473_ = v___y_1489_;
v___y_1474_ = v___y_1490_;
v___y_1475_ = v___y_1496_;
v___y_1476_ = v___y_1491_;
v___y_1477_ = v___y_1492_;
v___y_1478_ = v___y_1493_;
v___y_1479_ = v___y_1494_;
v___y_1480_ = v___y_1495_;
v___y_1481_ = v___y_1496_;
goto v___jp_1468_;
}
else
{
v___y_1469_ = v___y_1484_;
v___y_1470_ = v___y_1485_;
v___y_1471_ = v___y_1487_;
v___y_1472_ = v___y_1488_;
v___y_1473_ = v___y_1489_;
v___y_1474_ = v___y_1490_;
v___y_1475_ = v___y_1496_;
v___y_1476_ = v___y_1491_;
v___y_1477_ = v___y_1492_;
v___y_1478_ = v___y_1493_;
v___y_1479_ = v___y_1494_;
v___y_1480_ = v___y_1495_;
v___y_1481_ = v___y_1486_;
goto v___jp_1468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed(lean_object** _args){
lean_object* v___x_1834_ = _args[0];
lean_object* v___f_1835_ = _args[1];
lean_object* v___x_1836_ = _args[2];
lean_object* v_stx_1837_ = _args[3];
lean_object* v___x_1838_ = _args[4];
lean_object* v___x_1839_ = _args[5];
lean_object* v___x_1840_ = _args[6];
lean_object* v___x_1841_ = _args[7];
lean_object* v___y_1842_ = _args[8];
lean_object* v___y_1843_ = _args[9];
lean_object* v___y_1844_ = _args[10];
lean_object* v___y_1845_ = _args[11];
lean_object* v___y_1846_ = _args[12];
lean_object* v___y_1847_ = _args[13];
lean_object* v___y_1848_ = _args[14];
lean_object* v___y_1849_ = _args[15];
lean_object* v___y_1850_ = _args[16];
_start:
{
uint8_t v___x_19478__boxed_1851_; uint8_t v___x_19480__boxed_1852_; lean_object* v_res_1853_; 
v___x_19478__boxed_1851_ = lean_unbox(v___x_1834_);
v___x_19480__boxed_1852_ = lean_unbox(v___x_1836_);
v_res_1853_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(v___x_19478__boxed_1851_, v___f_1835_, v___x_19480__boxed_1852_, v_stx_1837_, v___x_1838_, v___x_1839_, v___x_1840_, v___x_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v_stx_1837_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern(lean_object* v_stx_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v___f_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; uint8_t v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___y_1886_; lean_object* v___x_1887_; 
v___f_1876_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__0));
v___x_1877_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1));
v___x_1878_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__2));
v___x_1879_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3));
v___x_1880_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4));
v___x_1881_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
lean_inc(v_stx_1866_);
v___x_1882_ = l_Lean_Syntax_isOfKind(v_stx_1866_, v___x_1881_);
v___x_1883_ = 1;
v___x_1884_ = lean_box(v___x_1882_);
v___x_1885_ = lean_box(v___x_1883_);
v___y_1886_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed), 17, 8);
lean_closure_set(v___y_1886_, 0, v___x_1884_);
lean_closure_set(v___y_1886_, 1, v___f_1876_);
lean_closure_set(v___y_1886_, 2, v___x_1885_);
lean_closure_set(v___y_1886_, 3, v_stx_1866_);
lean_closure_set(v___y_1886_, 4, v___x_1877_);
lean_closure_set(v___y_1886_, 5, v___x_1878_);
lean_closure_set(v___y_1886_, 6, v___x_1879_);
lean_closure_set(v___y_1886_, 7, v___x_1880_);
v___x_1887_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1886_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___boxed(lean_object* v_stx_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_Elab_Tactic_Conv_evalPattern(v_stx_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(lean_object* v_00_u03b1_1899_, lean_object* v_ref_1900_, lean_object* v_msg_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_ref_1900_, v_msg_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___boxed(lean_object* v_00_u03b1_1912_, lean_object* v_ref_1913_, lean_object* v_msg_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(v_00_u03b1_1912_, v_ref_1913_, v_msg_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v_ref_1913_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(lean_object* v_mvarId_1925_, lean_object* v_val_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1925_, v_val_1926_, v___y_1932_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___boxed(lean_object* v_mvarId_1937_, lean_object* v_val_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(v_mvarId_1937_, v_val_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(lean_object* v_00_u03b1_1949_, lean_object* v_msg_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_1950_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___boxed(lean_object* v_00_u03b1_1961_, lean_object* v_msg_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(v_00_u03b1_1961_, v_msg_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(lean_object* v_n_1973_, lean_object* v_as_1974_, lean_object* v_lo_1975_, lean_object* v_hi_1976_, lean_object* v_w_1977_, lean_object* v_hlo_1978_, lean_object* v_hhi_1979_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_1973_, v_as_1974_, v_lo_1975_, v_hi_1976_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___boxed(lean_object* v_n_1981_, lean_object* v_as_1982_, lean_object* v_lo_1983_, lean_object* v_hi_1984_, lean_object* v_w_1985_, lean_object* v_hlo_1986_, lean_object* v_hhi_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(v_n_1981_, v_as_1982_, v_lo_1983_, v_hi_1984_, v_w_1985_, v_hlo_1986_, v_hhi_1987_);
lean_dec(v_hi_1984_);
lean_dec(v_n_1981_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(lean_object* v_as_1989_, lean_object* v_i_1990_, lean_object* v_j_1991_, lean_object* v_inv_1992_, lean_object* v_bs_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_as_1989_, v_i_1990_, v_j_1991_, v_bs_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___boxed(lean_object* v_as_2004_, lean_object* v_i_2005_, lean_object* v_j_2006_, lean_object* v_inv_2007_, lean_object* v_bs_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(v_as_2004_, v_i_2005_, v_j_2006_, v_inv_2007_, v_bs_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec_ref(v_as_2004_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(lean_object* v_n_2019_, lean_object* v_as_2020_, lean_object* v_lo_2021_, lean_object* v_hi_2022_, lean_object* v_w_2023_, lean_object* v_hlo_2024_, lean_object* v_hhi_2025_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_2019_, v_as_2020_, v_lo_2021_, v_hi_2022_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___boxed(lean_object* v_n_2027_, lean_object* v_as_2028_, lean_object* v_lo_2029_, lean_object* v_hi_2030_, lean_object* v_w_2031_, lean_object* v_hlo_2032_, lean_object* v_hhi_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(v_n_2027_, v_as_2028_, v_lo_2029_, v_hi_2030_, v_w_2031_, v_hlo_2032_, v_hhi_2033_);
lean_dec(v_hi_2030_);
lean_dec(v_n_2027_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(lean_object* v_00_u03b2_2035_, lean_object* v_x_2036_, lean_object* v_x_2037_, lean_object* v_x_2038_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_x_2036_, v_x_2037_, v_x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(lean_object* v_n_2040_, lean_object* v_lo_2041_, lean_object* v_hi_2042_, lean_object* v_hhi_2043_, lean_object* v_pivot_2044_, lean_object* v_as_2045_, lean_object* v_i_2046_, lean_object* v_k_2047_, lean_object* v_ilo_2048_, lean_object* v_ik_2049_, lean_object* v_w_2050_){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_2042_, v_pivot_2044_, v_as_2045_, v_i_2046_, v_k_2047_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___boxed(lean_object* v_n_2052_, lean_object* v_lo_2053_, lean_object* v_hi_2054_, lean_object* v_hhi_2055_, lean_object* v_pivot_2056_, lean_object* v_as_2057_, lean_object* v_i_2058_, lean_object* v_k_2059_, lean_object* v_ilo_2060_, lean_object* v_ik_2061_, lean_object* v_w_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(v_n_2052_, v_lo_2053_, v_hi_2054_, v_hhi_2055_, v_pivot_2056_, v_as_2057_, v_i_2058_, v_k_2059_, v_ilo_2060_, v_ik_2061_, v_w_2062_);
lean_dec_ref(v_pivot_2056_);
lean_dec(v_hi_2054_);
lean_dec(v_lo_2053_);
lean_dec(v_n_2052_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(lean_object* v_n_2064_, lean_object* v_lo_2065_, lean_object* v_hi_2066_, lean_object* v_hhi_2067_, lean_object* v_pivot_2068_, lean_object* v_as_2069_, lean_object* v_i_2070_, lean_object* v_k_2071_, lean_object* v_ilo_2072_, lean_object* v_ik_2073_, lean_object* v_w_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_2066_, v_pivot_2068_, v_as_2069_, v_i_2070_, v_k_2071_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___boxed(lean_object* v_n_2076_, lean_object* v_lo_2077_, lean_object* v_hi_2078_, lean_object* v_hhi_2079_, lean_object* v_pivot_2080_, lean_object* v_as_2081_, lean_object* v_i_2082_, lean_object* v_k_2083_, lean_object* v_ilo_2084_, lean_object* v_ik_2085_, lean_object* v_w_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(v_n_2076_, v_lo_2077_, v_hi_2078_, v_hhi_2079_, v_pivot_2080_, v_as_2081_, v_i_2082_, v_k_2083_, v_ilo_2084_, v_ik_2085_, v_w_2086_);
lean_dec_ref(v_pivot_2080_);
lean_dec(v_hi_2078_);
lean_dec(v_lo_2077_);
lean_dec(v_n_2076_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_2088_, lean_object* v_x_2089_, size_t v_x_2090_, size_t v_x_2091_, lean_object* v_x_2092_, lean_object* v_x_2093_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_2089_, v_x_2090_, v_x_2091_, v_x_2092_, v_x_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_, lean_object* v_x_2098_, lean_object* v_x_2099_, lean_object* v_x_2100_){
_start:
{
size_t v_x_20596__boxed_2101_; size_t v_x_20597__boxed_2102_; lean_object* v_res_2103_; 
v_x_20596__boxed_2101_ = lean_unbox_usize(v_x_2097_);
lean_dec(v_x_2097_);
v_x_20597__boxed_2102_ = lean_unbox_usize(v_x_2098_);
lean_dec(v_x_2098_);
v_res_2103_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(v_00_u03b2_2095_, v_x_2096_, v_x_20596__boxed_2101_, v_x_20597__boxed_2102_, v_x_2099_, v_x_2100_);
return v_res_2103_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(lean_object* v_as_2104_, lean_object* v_a_2105_, lean_object* v_x_2106_, lean_object* v_x_2107_){
_start:
{
uint8_t v___x_2108_; 
v___x_2108_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_2104_, v_a_2105_, v_x_2106_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___boxed(lean_object* v_as_2109_, lean_object* v_a_2110_, lean_object* v_x_2111_, lean_object* v_x_2112_){
_start:
{
uint8_t v_res_2113_; lean_object* v_r_2114_; 
v_res_2113_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(v_as_2109_, v_a_2110_, v_x_2111_, v_x_2112_);
lean_dec_ref(v_a_2110_);
lean_dec_ref(v_as_2109_);
v_r_2114_ = lean_box(v_res_2113_);
return v_r_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12(lean_object* v_00_u03b2_2115_, lean_object* v_n_2116_, lean_object* v_k_2117_, lean_object* v_v_2118_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v_n_2116_, v_k_2117_, v_v_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(lean_object* v_00_u03b2_2120_, size_t v_depth_2121_, lean_object* v_keys_2122_, lean_object* v_vals_2123_, lean_object* v_heq_2124_, lean_object* v_i_2125_, lean_object* v_entries_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_2121_, v_keys_2122_, v_vals_2123_, v_i_2125_, v_entries_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___boxed(lean_object* v_00_u03b2_2128_, lean_object* v_depth_2129_, lean_object* v_keys_2130_, lean_object* v_vals_2131_, lean_object* v_heq_2132_, lean_object* v_i_2133_, lean_object* v_entries_2134_){
_start:
{
size_t v_depth_boxed_2135_; lean_object* v_res_2136_; 
v_depth_boxed_2135_ = lean_unbox_usize(v_depth_2129_);
lean_dec(v_depth_2129_);
v_res_2136_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(v_00_u03b2_2128_, v_depth_boxed_2135_, v_keys_2130_, v_vals_2131_, v_heq_2132_, v_i_2133_, v_entries_2134_);
lean_dec_ref(v_vals_2131_);
lean_dec_ref(v_keys_2130_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16(lean_object* v_00_u03b2_2137_, lean_object* v_x_2138_, lean_object* v_x_2139_, lean_object* v_x_2140_, lean_object* v_x_2141_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_x_2138_, v_x_2139_, v_x_2140_, v_x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1(){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2152_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2153_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
v___x_2154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2155_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___boxed), 10, 0);
v___x_2156_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2152_, v___x_2153_, v___x_2154_, v___x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___boxed(lean_object* v_a_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3(){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6));
v___x_2187_ = l_Lean_addBuiltinDeclarationRanges(v___x_2185_, v___x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___boxed(lean_object* v_a_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
return v_res_2189_;
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
res = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
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
